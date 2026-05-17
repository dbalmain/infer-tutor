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
  unify,
  UnifyError,
} from "@infer-tutor/lang";
import type { Constraint, InferResult } from "./step";
import {
  Tracer,
  errorResult,
  finalize,
  freshTV,
  makeUnifyOpts,
  truncate,
} from "./tracer";

// W' separates type inference into two phases:
//   1. Generation: walk the AST, assign fresh TVars, emit equality constraints.
//      No unification happens here — constraints are deferred.
//   2. Solving: work through the constraint list, unifying each equation.
//
// Exception: let-bindings must solve their value's constraints inline before
// generalizing (you need the solved type to compute a correct forall scheme).
// This embedded solve is shown as a nested "solve-phase" within generation.

// Solve one constraint. Updates tr.solvedConstraintIds and applies the new
// subst to all recorded node types so the AST view stays current.
function solveSingle(
  c: Constraint,
  subst: Subst,
  tr: Tracer,
  env: Env,
): Subst {
  tr.activeConstraintId = c.id;
  const left = applySubstType(subst, c.left);
  const right = applySubstType(subst, c.right);
  tr.push({
    kind: "solve-constraint",
    env,
    subst,
    message: `solve [${c.id}]: ${showType(left)} = ${showType(right)}  (${c.reason})`,
    detail: { left, right },
  });
  try {
    const newSubst = unify(left, right, subst, makeUnifyOpts(tr, env));
    tr.solvedConstraintIds = [...tr.solvedConstraintIds, c.id];
    tr.activeConstraintId = undefined;
    tr.applySubstToAll(newSubst);
    tr.push({
      kind: "unify-success",
      env: applySubstEnv(newSubst, env),
      subst: newSubst,
      message: `constraint [${c.id}] solved`,
    });
    return newSubst;
  } catch (e) {
    if (e instanceof UnifyError) {
      tr.push({
        kind: "unify-fail",
        env,
        subst,
        message: `constraint [${c.id}] failed: ${e.message}`,
        detail: { left: e.left, right: e.right },
      });
    }
    throw e;
  }
}

type OnBeforeExit = (type: Type, subst: Subst) => void;

// Generation phase: walk expr, assign types, emit constraints.
// Returns the type assigned to expr and the (possibly-grown) substitution
// (grows only when a let-binding forces an embedded solve).
//
// onBeforeExit fires just before the infer-exit step is pushed, letting
// the parent record derived state (e.g. binding schemes, lam body types)
// in the same step snapshot — identical to W's onBeforeExit mechanism.
function generate(
  env: Env,
  expr: Expr,
  subst: Subst,
  tr: Tracer,
  fresh: FreshSupply,
  role: string,
  onBeforeExit?: OnBeforeExit,
): { type: Type; subst: Subst } {
  tr.push({
    kind: "gen-enter",
    nodeId: expr.id,
    env,
    subst,
    message: `gen ${role}: ⟦${truncate(showExpr(expr))}⟧`,
  });

  switch (expr.kind) {
    case "Lit": {
      const t = expr.lit.kind === "Int" ? tInt : tBool;
      tr.recordNodeType(expr.id, t);
      onBeforeExit?.(t, subst);
      tr.push({
        kind: "gen-exit",
        nodeId: expr.id,
        env,
        subst,
        message: `Literal ⊢ ${showType(t)}`,
      });
      return { type: t, subst };
    }

    case "Var": {
      const sc = env.get(expr.name);
      if (!sc) throw new Error(`unbound variable: ${expr.name}`);
      tr.recordVarScheme(expr.id, sc);
      tr.push({
        kind: "lookup",
        nodeId: expr.id,
        env,
        subst,
        message: `look up ${expr.name}: ${showScheme(sc)}`,
        detail: { name: expr.name, type: sc.body },
      });
      const inst = instantiate(sc, fresh);
      for (const t of inst.mapping.values()) {
        if (t.kind === "TVar") tr.introduceVar(t.name);
      }
      tr.clearVarScheme(expr.id);
      tr.recordNodeType(expr.id, inst.type);
      tr.push({
        kind: "instantiate",
        nodeId: expr.id,
        env,
        subst,
        message: `${expr.name} : ${showScheme(sc)} ⇒ ${showType(inst.type)}`,
        detail: { name: expr.name, type: inst.type },
      });
      onBeforeExit?.(inst.type, subst);
      tr.push({
        kind: "gen-exit",
        nodeId: expr.id,
        env,
        subst,
        message: `Var ${expr.name} ⊢ ${showType(inst.type)}`,
      });
      return { type: inst.type, subst };
    }

    case "Lam": {
      const tv = freshTV(tr, fresh);
      tr.recordParamType(expr.id, tv);
      tr.push({
        kind: "fresh-param",
        nodeId: expr.id,
        env,
        subst,
        message: `fresh ${showType(tv)} for parameter ${expr.param}`,
      });
      const env2: Env = new Map(env);
      env2.set(expr.param, { vars: [], body: tv });
      tr.push({
        kind: "env-extend",
        nodeId: expr.id,
        env: env2,
        subst,
        message: `extend env with ${expr.param} : ${showType(tv)}`,
        detail: { name: expr.param, type: tv },
      });
      const { type: tBody, subst: s1 } = generate(
        env2,
        expr.body,
        subst,
        tr,
        fresh,
        "body of lambda",
        // Record the Lam's body-type slot at the body's infer-exit so the
        // Lam display shows `\(x : t0) -> Bool` at that step, not one step later.
        () => {
          const t = tr.nodeTypes.get(expr.body.id);
          if (t) tr.recordLamBodyType(expr.id, t);
        },
      );
      // s1 may differ from subst if the body contained a let-binding.
      const paramResolved = applySubstType(s1, tv);
      tr.recordParamType(expr.id, paramResolved);
      // lamBodyTypes already set by onBeforeExit above; ensure it reflects
      // any subst growth that happened after (edge case: nested let in body).
      tr.recordLamBodyType(expr.id, tBody);
      const tFunType = tFun(paramResolved, tBody);
      tr.recordNodeType(expr.id, tFunType);
      onBeforeExit?.(tFunType, s1);
      tr.push({
        kind: "gen-exit",
        nodeId: expr.id,
        env,
        subst: s1,
        message: `Lam ⊢ ${showType(tFunType)}`,
      });
      return { type: tFunType, subst: s1 };
    }

    case "App": {
      const { type: t1, subst: s1 } = generate(
        env,
        expr.fn,
        subst,
        tr,
        fresh,
        "function of application",
      );
      const { type: t2, subst: s2 } = generate(
        env,
        expr.arg,
        s1,
        tr,
        fresh,
        "argument of application",
      );
      const tv = freshTV(tr, fresh);
      tr.recordNodeType(expr.id, tv);
      tr.push({
        kind: "fresh-app",
        nodeId: expr.id,
        env,
        subst: s2,
        message: `fresh ${showType(tv)} for application result`,
      });
      // Defer unification: emit a constraint instead of unifying now.
      tr.emitConstraint(t1, tFun(t2, tv), "fn type = arg → result", expr.id, env, s2);
      onBeforeExit?.(tv, s2);
      tr.push({
        kind: "gen-exit",
        nodeId: expr.id,
        env,
        subst: s2,
        message: `App ⊢ ${showType(tv)} (constraint deferred)`,
      });
      return { type: tv, subst: s2 };
    }

    case "Let": {
      // Record how many constraints exist before generating the value.
      // After generation, everything newer (and unsolved) needs to be solved
      // before we can generalize.
      const countBefore = tr.constraints.length;
      const { type: t1, subst: s1 } = generate(
        env,
        expr.value,
        subst,
        tr,
        fresh,
        `value bound to ${expr.name}`,
        // At the value's infer-exit, record the unquantified type as a
        // preliminary binding scheme — same trick as W. This makes the Let
        // node show `let x : t0 -> t0` before generalize adds the forall.
        (t) => {
          tr.recordBindingScheme(expr.id, { vars: [], body: t });
        },
      );
      // Constraints emitted while generating the value, minus any already
      // solved by nested let-bindings inside the value.
      const toSolve = tr.constraints
        .slice(countBefore)
        .filter((c) => !tr.solvedConstraintIds.includes(c.id));
      // Solve them now so we can generalize the type properly.
      tr.push({
        kind: "solve-phase",
        nodeId: expr.id,
        env,
        subst: s1,
        message: `solve ${toSolve.length} value constraint${toSolve.length !== 1 ? "s" : ""} before generalizing ${expr.name}`,
      });
      let s2 = s1;
      for (const c of toSolve) {
        s2 = solveSingle(c, s2, tr, env);
      }
      const t1Resolved = applySubstType(s2, t1);
      tr.recordNodeType(expr.value.id, t1Resolved);
      tr.recordBindingScheme(expr.id, { vars: [], body: t1Resolved });
      const sc = generalize(applySubstEnv(s2, env), t1Resolved);
      tr.recordBindingScheme(expr.id, sc);
      tr.push({
        kind: "generalize",
        nodeId: expr.id,
        env: applySubstEnv(s2, env),
        subst: s2,
        message: `generalize ${expr.name} : ${showScheme(sc)}`,
        detail: { name: expr.name, type: sc.body },
      });
      const env2: Env = new Map(applySubstEnv(s2, env));
      env2.set(expr.name, sc);
      tr.push({
        kind: "env-extend",
        nodeId: expr.id,
        env: env2,
        subst: s2,
        message: `extend env with ${expr.name} : ${showScheme(sc)}`,
        detail: { name: expr.name, type: sc.body },
      });
      const { type: t2, subst: s3 } = generate(
        env2,
        expr.body,
        s2,
        tr,
        fresh,
        `body of let ${expr.name}`,
        () => {
          const t = tr.nodeTypes.get(expr.body.id);
          if (t) tr.recordLetBodyType(expr.id, t);
        },
      );
      tr.recordNodeType(expr.id, applySubstType(s3, t2));
      onBeforeExit?.(t2, s3);
      tr.push({
        kind: "gen-exit",
        nodeId: expr.id,
        env,
        subst: s3,
        message: `Let ⊢ ${showType(applySubstType(s3, t2))}`,
      });
      return { type: t2, subst: s3 };
    }

    case "If": {
      const { type: tc, subst: s1 } = generate(env, expr.cond, subst, tr, fresh, "condition of if");
      const { type: tThen, subst: s2 } = generate(env, expr.then, s1, tr, fresh, "then-branch of if");
      const { type: tElse, subst: s3 } = generate(env, expr.else, s2, tr, fresh, "else-branch of if");
      tr.emitConstraint(tc, tBool, "condition must be Bool", expr.cond.id, env, s3);
      tr.emitConstraint(tThen, tElse, "branches must agree", expr.id, env, s3);
      tr.recordNodeType(expr.id, tThen);
      onBeforeExit?.(tThen, s3);
      tr.push({
        kind: "gen-exit",
        nodeId: expr.id,
        env,
        subst: s3,
        message: `If ⊢ ${showType(tThen)} (2 constraints deferred)`,
      });
      return { type: tThen, subst: s3 };
    }
  }
}

export function inferWprime(env: Env, expr: Expr): InferResult {
  const tracer = new Tracer();
  const fresh = new FreshSupply();
  try {
    const { type, subst: genSubst } = generate(
      env,
      expr,
      emptySubst(),
      tracer,
      fresh,
      "root expression",
    );
    // Remaining constraints not yet solved by embedded let-solves.
    const toSolve = tracer.constraints.filter(
      (c) => !tracer.solvedConstraintIds.includes(c.id),
    );
    tracer.push({
      kind: "solve-phase",
      nodeId: expr.id,
      env,
      subst: genSubst,
      message: `Generation complete — solving ${toSolve.length} remaining constraint${toSolve.length !== 1 ? "s" : ""}`,
    });
    let subst = genSubst;
    for (const c of toSolve) {
      subst = solveSingle(c, subst, tracer, env);
    }
    return finalize(tracer, env, expr, subst, applySubstType(subst, type));
  } catch (e) {
    return errorResult(tracer, e);
  }
}
