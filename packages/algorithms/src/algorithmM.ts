// Algorithm M: top-down type inference (Lee & Yi, 1998).
//
// Unlike W, which synthesises types bottom-up and returns (Subst, Type),
// M *checks* each node against an expected type passed down from the parent.
// The signature is M(Γ, e, τ) → σ where τ is the expected type.
//
// Key differences from W:
//   Var:  after instantiating the scheme, unify with τ immediately.
//   Lam:  decompose τ = α → β by unifying, then check body against β.
//   App:  allocate only a fresh α for the argument; check fn against α → τ.
//         No fresh result variable needed — τ IS the result.
//   Let:  fresh α for the value; after generalizing, check body against σ(τ).
//   If:   check cond against Bool; check both branches against σ(τ).

import {
  type Env,
  type Expr,
  type Subst,
  type Type,
  applySubstEnv,
  applySubstType,
  emptySubst,
  FreshSupply,
  generalize,
  instantiate,
  showExpr,
  showScheme,
  showType,
  tBool,
  tFun,
  tInt,
} from "@infer-tutor/lang";
import type { InferResult } from "./step";
import {
  Tracer,
  doUnify,
  errorResult,
  finalize,
  freshTV,
  truncate,
} from "./tracer";

type OnBeforeExit = (type: Type, subst: Subst) => void;

// Algorithm M: check `expr` has type `expected` under `env`.
// Returns the final substitution. The type of `expr` is
// applySubstType(returnedSubst, expected).
function check(
  env: Env,
  expr: Expr,
  expected: Type,
  subst: Subst,
  tr: Tracer,
  fresh: FreshSupply,
  role: string,
  onBeforeExit?: OnBeforeExit,
): Subst {
  const exp0 = applySubstType(subst, expected);
  tr.setExpected(expr.id, exp0);
  tr.push({
    kind: "check-enter",
    nodeId: expr.id,
    env,
    subst,
    message: `check ${role} ⇐ ${showType(exp0)}: ⟦${truncate(showExpr(expr))}⟧`,
  });

  switch (expr.kind) {
    case "Lit": {
      const t = expr.lit.kind === "Int" ? tInt : tBool;
      tr.recordNodeType(expr.id, t);
      const exp = applySubstType(subst, expected);
      const s1 = doUnify(exp, t, subst, tr, env, expr.id,
        `unify expected ${showType(exp)} = literal ${showType(t)}`,
        `literal matches expected type`,
      );
      const resolved = applySubstType(s1, expected);
      tr.recordNodeType(expr.id, resolved);
      tr.clearExpected(expr.id);
      onBeforeExit?.(resolved, s1);
      tr.push({ kind: "check-exit", nodeId: expr.id, env, subst: s1,
        message: `Literal ⊢ ${showType(resolved)}` });
      return s1;
    }

    case "Var": {
      const sc = env.get(expr.name);
      if (!sc) throw new Error(`unbound variable: ${expr.name}`);
      tr.recordVarScheme(expr.id, sc);
      tr.push({ kind: "lookup", nodeId: expr.id, env, subst,
        message: `look up ${expr.name} in env: ${showScheme(sc)}`,
        detail: { name: expr.name, type: sc.body },
      });
      const inst = instantiate(sc, fresh);
      for (const t of inst.mapping.values()) {
        if (t.kind === "TVar") tr.introduceVar(t.name);
      }
      tr.clearVarScheme(expr.id);
      tr.recordNodeType(expr.id, inst.type);
      tr.push({ kind: "instantiate", nodeId: expr.id, env, subst,
        message: `${expr.name} : ${showScheme(sc)} ⇒ ${showType(inst.type)}`,
        detail: { name: expr.name, type: inst.type },
      });
      const exp = applySubstType(subst, expected);
      const s1 = doUnify(exp, inst.type, subst, tr, env, expr.id,
        `unify expected ${showType(exp)} = ${showType(inst.type)}`,
        `${expr.name} ⊢ ${showType(exp)}`,
      );
      const resolved = applySubstType(s1, expected);
      tr.recordNodeType(expr.id, resolved);
      tr.clearExpected(expr.id);
      onBeforeExit?.(resolved, s1);
      tr.push({ kind: "check-exit", nodeId: expr.id, env, subst: s1,
        message: `Var ${expr.name} ⊢ ${showType(resolved)}` });
      return s1;
    }

    case "Lam": {
      // Decompose expected: unify τ = α → β, then check body against β with x:α.
      const tParam = freshTV(tr, fresh);
      const tBody = freshTV(tr, fresh);
      tr.recordParamType(expr.id, tParam);
      // Record tBody as the body-type slot immediately so fresh-param shows
      // \(x : α) → β rather than \(x : α) → ?. M allocates both together.
      tr.recordLamBodyType(expr.id, tBody);
      tr.push({ kind: "fresh-param", nodeId: expr.id, env, subst,
        message: `fresh ${showType(tParam)} → ${showType(tBody)} for lambda; decomposing expected type`,
      });
      const exp = applySubstType(subst, expected);
      const s1 = doUnify(exp, tFun(tParam, tBody), subst, tr, env, expr.id,
        `decompose expected ${showType(exp)} = ${showType(tParam)} → ${showType(tBody)}`,
        `expected type decomposed`,
      );
      const paramResolved = applySubstType(s1, tParam);
      const bodyExpected = applySubstType(s1, tBody);
      tr.recordParamType(expr.id, paramResolved);
      tr.recordLamBodyType(expr.id, bodyExpected);
      tr.pushSubstApply({ nodeId: expr.id, env, subst: s1, input: tParam, output: paramResolved, where: "param type" });
      tr.pushSubstApply({ nodeId: expr.id, env, subst: s1, input: tBody, output: bodyExpected, where: "body expected" });
      const env2: Env = new Map(applySubstEnv(s1, env));
      env2.set(expr.param, { vars: [], body: paramResolved });
      tr.push({ kind: "env-extend", nodeId: expr.id, env: env2, subst: s1,
        message: `extend env with ${expr.param} : ${showType(paramResolved)}`,
        detail: { name: expr.param, type: paramResolved },
      });
      // No onBeforeExit for lamBodyType — leave it as bodyExpected (e.g. t3)
      // until the parent explicitly applies σ. The subst-apply step below
      // makes the transition `t3 ⇒ t2` visible rather than silent.
      const s2 = check(env2, expr.body, bodyExpected, s1, tr, fresh, "body of lambda");
      const bodyResolved = applySubstType(s2, bodyExpected);
      tr.recordLamBodyType(expr.id, bodyResolved);
      tr.pushSubstApply({ nodeId: expr.id, env, subst: s2, input: bodyExpected, output: bodyResolved, where: "lambda return type" });
      const finalParam = applySubstType(s2, paramResolved);
      tr.recordParamType(expr.id, finalParam);
      tr.pushSubstApply({ nodeId: expr.id, env, subst: s2, input: paramResolved, output: finalParam, where: "param type after body check" });
      const lamType = applySubstType(s2, expected);
      tr.recordNodeType(expr.id, lamType);
      tr.clearExpected(expr.id);
      tr.pushSubstApply({ nodeId: expr.id, env, subst: s2, input: expected, output: lamType, where: "lam type" });
      onBeforeExit?.(lamType, s2);
      tr.push({ kind: "check-exit", nodeId: expr.id, env, subst: s2,
        message: `Lam ⊢ ${showType(lamType)}` });
      return s2;
    }

    case "App": {
      // M(Γ, e1 e2, τ): fresh α for argument; check fn against α → τ, then arg against σ1(α).
      // No fresh result variable needed — τ IS the result.
      const tArg = freshTV(tr, fresh);
      const exp = applySubstType(subst, expected);
      tr.setExpected(expr.arg.id, tArg);
      tr.push({ kind: "fresh-app", nodeId: expr.id, env, subst,
        message: `fresh ${showType(tArg)} for argument; fn checked against ${showType(tArg)} → ${showType(exp)}`,
      });
      const s1 = check(env, expr.fn, tFun(tArg, exp), subst, tr, fresh, "function of application");
      const tArgResolved = applySubstType(s1, tArg);
      tr.setExpected(expr.arg.id, tArgResolved);
      tr.pushSubstApply({ nodeId: expr.id, env, subst: s1, input: tArg, output: tArgResolved, where: "arg type after fn check" });
      const s2 = check(applySubstEnv(s1, env), expr.arg, tArgResolved, s1, tr, fresh, "argument of application");
      const result = applySubstType(s2, expected);
      tr.recordNodeType(expr.id, result);
      tr.clearExpected(expr.id);
      onBeforeExit?.(result, s2);
      tr.pushSubstApply({ nodeId: expr.id, env, subst: s2, input: exp, output: result, where: "result type after arg check" });
      tr.push({ kind: "check-exit", nodeId: expr.id, env, subst: s2,
        message: `App ⊢ ${showType(result)}` });
      return s2;
    }

    case "Let": {
      // M(Γ, let x = e1 in e2, τ): fresh α; check e1 against α; generalize; check e2 against σ1(τ).
      const tVal = freshTV(tr, fresh);
      // Show tVal in the binding-scheme slot immediately so the Let node
      // displays `let id : t1 in ?` while the value is being checked,
      // before generalize adds the forall.
      tr.recordBindingScheme(expr.id, { vars: [], body: tVal });
      // No onBeforeExit for bindingScheme — leave it as t1 until the parent
      // explicitly applies σ. That makes the subst-apply step below
      // visible: bindingScheme transitions from `t1` to `t2 → t2` AT that
      // step, rather than silently during the value's check-exit.
      const s1 = check(env, expr.value, tVal, subst, tr, fresh, `value bound to ${expr.name}`);
      const env1 = applySubstEnv(s1, env);
      const t1Resolved = applySubstType(s1, tVal);
      tr.recordBindingScheme(expr.id, { vars: [], body: t1Resolved });
      tr.pushSubstApply({ nodeId: expr.id, env: env1, subst: s1, input: tVal, output: t1Resolved, where: "value type for generalize" });
      const sc = generalize(env1, t1Resolved);
      tr.recordBindingScheme(expr.id, sc);
      tr.push({ kind: "generalize", nodeId: expr.id, env: env1, subst: s1,
        message: `generalize ${expr.name} : ${showScheme(sc)}`,
        detail: { name: expr.name, type: sc.body },
      });
      const env2: Env = new Map(env1);
      env2.set(expr.name, sc);
      tr.push({ kind: "env-extend", nodeId: expr.id, env: env2, subst: s1,
        message: `extend env with ${expr.name} : ${showScheme(sc)}`,
        detail: { name: expr.name, type: sc.body },
      });
      const bodyExpected = applySubstType(s1, expected);
      tr.pushSubstApply({ nodeId: expr.id, env: env2, subst: s1, input: expected, output: bodyExpected, where: "body expected" });
      // No onBeforeExit for letBodyType — apply σ explicitly after the body
      // check returns so the transition is a visible step.
      const s2 = check(env2, expr.body, bodyExpected, s1, tr, fresh, "body of let");
      const letBodyResolved = applySubstType(s2, bodyExpected);
      tr.recordLetBodyType(expr.id, letBodyResolved);
      tr.pushSubstApply({ nodeId: expr.id, env, subst: s2, input: bodyExpected, output: letBodyResolved, where: "let body type" });
      const result = applySubstType(s2, expected);
      tr.recordNodeType(expr.id, result);
      tr.clearExpected(expr.id);
      onBeforeExit?.(result, s2);
      tr.push({ kind: "check-exit", nodeId: expr.id, env, subst: s2,
        message: `Let ⊢ ${showType(result)}` });
      return s2;
    }

    case "If": {
      const s1 = check(env, expr.cond, tBool, subst, tr, fresh, "condition of if");
      const exp = applySubstType(s1, expected);
      tr.pushSubstApply({ nodeId: expr.id, env: applySubstEnv(s1, env), subst: s1, input: expected, output: exp, where: "then-branch expected" });
      const s2 = check(applySubstEnv(s1, env), expr.then, exp, s1, tr, fresh, "then-branch of if");
      const expElse = applySubstType(s2, exp);
      tr.pushSubstApply({ nodeId: expr.id, env: applySubstEnv(s2, env), subst: s2, input: exp, output: expElse, where: "else-branch expected" });
      const s3 = check(applySubstEnv(s2, env), expr.else, expElse, s2, tr, fresh, "else-branch of if");
      const result = applySubstType(s3, expected);
      tr.recordNodeType(expr.id, result);
      tr.clearExpected(expr.id);
      onBeforeExit?.(result, s3);
      tr.push({ kind: "check-exit", nodeId: expr.id, env: applySubstEnv(s3, env), subst: s3,
        message: `If ⊢ ${showType(result)}` });
      return s3;
    }
  }
}

export function inferM(env: Env, expr: Expr): InferResult {
  const tracer = new Tracer();
  const fresh = new FreshSupply();
  // Start with a fresh root expected type. The final program type is
  // applySubstType(subst, rootExpected) after checking.
  const rootExpected = freshTV(tracer, fresh);
  try {
    const subst = check(env, expr, rootExpected, emptySubst(), tracer, fresh, "root expression");
    return finalize(tracer, env, expr, subst, applySubstType(subst, rootExpected));
  } catch (e) {
    return errorResult(tracer, e);
  }
}
