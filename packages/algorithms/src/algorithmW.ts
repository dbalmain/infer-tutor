import {
  type Env,
  type Expr,
  type Scheme,
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
import type { InferResult } from "./step";
import {
  Tracer,
  errorResult,
  finalize,
  freshTV,
  makeUnifyOpts,
  truncate,
} from "./tracer";

export function inferW(env: Env, expr: Expr): InferResult {
  const tracer = new Tracer();
  const fresh = new FreshSupply();
  try {
    const { subst, type } = infer(env, expr, emptySubst(), tracer, fresh, "root expression");
    return finalize(tracer, env, expr, subst, applySubstType(subst, type));
  } catch (e) {
    return errorResult(tracer, e);
  }
}

type OnBeforeExit = (type: Type, subst: Subst) => void;

function infer(
  env: Env,
  expr: Expr,
  s0: Subst,
  tr: Tracer,
  fresh: FreshSupply,
  role: string,
  onBeforeExit?: OnBeforeExit,
): { subst: Subst; type: Type } {
  tr.push({
    kind: "infer-enter",
    nodeId: expr.id,
    env,
    subst: s0,
    message: `infer ${role}: ⟦${truncate(showExpr(expr))}⟧`,
  });

  switch (expr.kind) {
    case "Lit": {
      const t = expr.lit.kind === "Int" ? tInt : tBool;
      tr.recordNodeType(expr.id, t);
      onBeforeExit?.(t, s0);
      tr.push({
        kind: "infer-exit",
        nodeId: expr.id,
        env,
        subst: s0,
        message: `Literal ⊢ ${showType(t)}`,
      });
      return { subst: s0, type: t };
    }

    case "Var": {
      const sc = env.get(expr.name);
      if (!sc) throw new Error(`unbound variable: ${expr.name}`);
      // Surface the full scheme (forall and all) on the Var node so the
      // user sees `forall t0. t0 -> t0` here; instantiate will clear this
      // and record the freshly-renamed type.
      tr.recordVarScheme(expr.id, sc);
      tr.push({
        kind: "lookup",
        nodeId: expr.id,
        env,
        subst: s0,
        message: `look up ${expr.name} in env: ${showScheme(sc)}`,
        detail: { name: expr.name, type: sc.body },
      });
      const inst = instantiate(sc, fresh);
      // Register the freshly-introduced TVars from instantiation so the
      // "free" list in the SUBSTITUTION header tracks them.
      for (const t of inst.mapping.values()) {
        if (t.kind === "TVar") tr.introduceVar(t.name);
      }
      tr.clearVarScheme(expr.id);
      tr.recordNodeType(expr.id, inst.type);
      tr.push({
        kind: "instantiate",
        nodeId: expr.id,
        env,
        subst: s0,
        message: `${expr.name} : ${showScheme(sc)} ⇒ ${showType(inst.type)}`,
        detail: { name: expr.name, type: inst.type },
      });
      onBeforeExit?.(inst.type, s0);
      tr.push({
        kind: "infer-exit",
        nodeId: expr.id,
        env,
        subst: s0,
        message: `Var ${expr.name} ⊢ ${showType(inst.type)}`,
      });
      return { subst: s0, type: inst.type };
    }

    case "Lam": {
      const tv = freshTV(tr, fresh);
      // Surface the param type on the Lam node immediately so the AST can
      // render `\(x : t0) -> ?` from this step on.
      tr.recordParamType(expr.id, tv);
      tr.push({
        kind: "fresh-param",
        nodeId: expr.id,
        env,
        subst: s0,
        message: `fresh ${showType(tv)} for parameter ${expr.param}`,
      });
      const env2: Env = new Map(env);
      env2.set(expr.param, { vars: [], body: tv });
      tr.push({
        kind: "env-extend",
        nodeId: expr.id,
        env: env2,
        subst: s0,
        message: `extend env with ${expr.param} : ${showType(tv)}`,
        detail: { name: expr.param, type: tv },
      });
      const { subst: s1, type: tBody } = infer(
        env2,
        expr.body,
        s0,
        tr,
        fresh,
        "body of lambda",
        // At the body's infer-exit step, attach the body's displayed type
        // to the Lam's body slot. Before this step, the Lam's body slot
        // shows `?` even if the body's own node has a recorded type.
        () => {
          const t = tr.nodeTypes.get(expr.body.id);
          if (t) tr.recordLamBodyType(expr.id, t);
        },
      );
      const paramResolved = applySubstType(s1, tv);
      // Update paramTypes BEFORE pushing the subst-apply step so the AST
      // visibly transitions at this step (rather than auto-applying
      // invisibly elsewhere).
      tr.recordParamType(expr.id, paramResolved);
      tr.pushSubstApply({
        nodeId: expr.id,
        env,
        subst: s1,
        input: tv,
        output: paramResolved,
        where: `resolve param ${expr.param}`,
      });
      const tFunType = tFun(paramResolved, tBody);
      tr.recordNodeType(expr.id, tFunType);
      onBeforeExit?.(tFunType, s1);
      tr.push({
        kind: "infer-exit",
        nodeId: expr.id,
        env,
        subst: s1,
        message: `Lam ⊢ ${showType(tFunType)}`,
      });
      return { subst: s1, type: tFunType };
    }

    case "App": {
      const { subst: s1, type: t1 } = infer(env, expr.fn, s0, tr, fresh, "function of application");
      const env2 = applySubstEnv(s1, env);
      const { subst: s2, type: t2 } = infer(env2, expr.arg, s1, tr, fresh, "argument of application");
      const tv = freshTV(tr, fresh);
      // Record the fresh var as the App node's tentative type now, so the AST
      // view shows it immediately. Once unification adds `tv ↦ ...` to the
      // subst, the view auto-resolves it without us needing to re-record.
      tr.recordNodeType(expr.id, tv);
      tr.push({
        kind: "fresh-app",
        nodeId: expr.id,
        env: env2,
        subst: s2,
        message: `fresh ${showType(tv)} for application result`,
      });
      const left = applySubstType(s2, t1);
      // Make the resolution visible: update the function expression's
      // recorded type at this step.
      tr.recordNodeType(expr.fn.id, left);
      tr.pushSubstApply({
        nodeId: expr.fn.id,
        env: env2,
        subst: s2,
        input: t1,
        output: left,
        where: "function type before unify",
      });
      const right = tFun(t2, tv);
      tr.push({
        kind: "unify-enter",
        nodeId: expr.id,
        env: env2,
        subst: s2,
        message: `unify ${showType(left)} with ${showType(right)}`,
        detail: { left, right },
      });
      try {
        const s3 = unify(left, right, s2, makeUnifyOpts(tr, env2, expr.id));
        tr.push({
          kind: "unify-success",
          nodeId: expr.id,
          env: applySubstEnv(s3, env),
          subst: s3,
          message: `unified`,
        });
        const resolvedResult = applySubstType(s3, tv);
        // Update App's own recorded type and also the function node, both
        // of which may still show stale TVars (e.g. t1 → t1 after t1 ↦ Int).
        tr.recordNodeType(expr.id, resolvedResult);
        tr.recordNodeType(expr.fn.id, applySubstType(s3, left));
        tr.pushSubstApply({
          nodeId: expr.id,
          env: applySubstEnv(s3, env),
          subst: s3,
          input: tv,
          output: resolvedResult,
          where: `resolve App result ${showType(tv)}`,
        });
        onBeforeExit?.(tv, s3);
        tr.push({
          kind: "infer-exit",
          nodeId: expr.id,
          env: applySubstEnv(s3, env),
          subst: s3,
          message: `App ⊢ ${showType(resolvedResult)}`,
        });
        return { subst: s3, type: tv };
      } catch (e) {
        if (e instanceof UnifyError) {
          tr.push({
            kind: "unify-fail",
            nodeId: expr.id,
            env: env2,
            subst: s2,
            message: `unification failed: ${e.message}`,
            detail: { left: e.left, right: e.right },
          });
        }
        throw e;
      }
    }

    case "Let": {
      const { subst: s1, type: t1 } = infer(
        env,
        expr.value,
        s0,
        tr,
        fresh,
        `value bound to ${expr.name}`,
        // At the value's infer-exit, drop the value's type into the Let's
        // binding slot as an unquantified scheme. Generalize will later
        // add the `forall` once we know which TVars are safe to close.
        (t) => {
          tr.recordBindingScheme(expr.id, { vars: [], body: t });
        },
      );
      const env1 = applySubstEnv(s1, env);
      const t1Resolved = applySubstType(s1, t1);
      tr.recordNodeType(expr.value.id, t1Resolved);
      tr.recordBindingScheme(expr.id, { vars: [], body: t1Resolved });
      tr.pushSubstApply({
        nodeId: expr.value.id,
        env: env1,
        subst: s1,
        input: t1,
        output: t1Resolved,
        where: `value type for ${expr.name} before generalize`,
      });
      const sc = generalize(env1, t1Resolved);
      tr.recordBindingScheme(expr.id, sc);
      tr.push({
        kind: "generalize",
        nodeId: expr.id,
        env: env1,
        subst: s1,
        message: `generalize ${expr.name} : ${showScheme(sc)}`,
        detail: { name: expr.name, type: sc.body },
      });
      const env2: Env = new Map(env1);
      env2.set(expr.name, sc);
      tr.push({
        kind: "env-extend",
        nodeId: expr.id,
        env: env2,
        subst: s1,
        message: `extend env with ${expr.name} : ${showScheme(sc)}`,
        detail: { name: expr.name, type: sc.body },
      });
      const { subst: s2, type: t2 } = infer(env2, expr.body, s1, tr, fresh, "body of let",
        () => {
          const t = tr.nodeTypes.get(expr.body.id);
          if (t) tr.recordLetBodyType(expr.id, t);
        },
      );
      tr.recordNodeType(expr.id, applySubstType(s2, t2));
      onBeforeExit?.(t2, s2);
      tr.push({
        kind: "infer-exit",
        nodeId: expr.id,
        env,
        subst: s2,
        message: `Let ⊢ ${showType(applySubstType(s2, t2))}`,
      });
      return { subst: s2, type: t2 };
    }

    case "If": {
      const { subst: s1, type: tc } = infer(env, expr.cond, s0, tr, fresh, "condition of if");
      const tcResolved = applySubstType(s1, tc);
      tr.recordNodeType(expr.cond.id, tcResolved);
      tr.pushSubstApply({
        nodeId: expr.cond.id,
        env,
        subst: s1,
        input: tc,
        output: tcResolved,
        where: "condition type before unify with Bool",
      });
      tr.push({
        kind: "unify-enter",
        nodeId: expr.cond.id,
        env,
        subst: s1,
        message: `condition must be Bool: unify ${showType(tcResolved)} with Bool`,
        detail: { left: tcResolved, right: tBool },
      });
      const sCond = unify(tcResolved, tBool, s1, makeUnifyOpts(tr, env, expr.cond.id));
      tr.push({
        kind: "unify-success",
        nodeId: expr.cond.id,
        env,
        subst: sCond,
        message: `condition unified to Bool`,
      });
      const env2 = applySubstEnv(sCond, env);
      const { subst: s2, type: tThen } = infer(env2, expr.then, sCond, tr, fresh, "then-branch of if");
      const env3 = applySubstEnv(s2, env);
      const { subst: s3, type: tElse } = infer(env3, expr.else, s2, tr, fresh, "else-branch of if");
      const left = applySubstType(s3, tThen);
      tr.recordNodeType(expr.then.id, left);
      tr.pushSubstApply({
        nodeId: expr.then.id,
        env: applySubstEnv(s3, env),
        subst: s3,
        input: tThen,
        output: left,
        where: "then-branch type before unify",
      });
      const right = applySubstType(s3, tElse);
      tr.recordNodeType(expr.else.id, right);
      tr.pushSubstApply({
        nodeId: expr.else.id,
        env: applySubstEnv(s3, env),
        subst: s3,
        input: tElse,
        output: right,
        where: "else-branch type before unify",
      });
      tr.push({
        kind: "unify-enter",
        nodeId: expr.id,
        env: applySubstEnv(s3, env),
        subst: s3,
        message: `branches must agree: unify ${showType(left)} with ${showType(right)}`,
        detail: { left, right },
      });
      const s4 = unify(left, right, s3, makeUnifyOpts(tr, applySubstEnv(s3, env), expr.id));
      const result = applySubstType(s4, tElse);
      tr.recordNodeType(expr.id, result);
      tr.push({
        kind: "unify-success",
        nodeId: expr.id,
        env: applySubstEnv(s4, env),
        subst: s4,
        message: `branches agree on ${showType(result)}`,
      });
      onBeforeExit?.(result, s4);
      tr.push({
        kind: "infer-exit",
        nodeId: expr.id,
        env: applySubstEnv(s4, env),
        subst: s4,
        message: `If ⊢ ${showType(result)}`,
      });
      return { subst: s4, type: result };
    }
  }
}

// Convenience: a small default env with a couple of built-ins.
export function defaultEnv(): Env {
  const env: Env = new Map();
  env.set("add", scheme0(tFun(tInt, tFun(tInt, tInt))));
  env.set("mul", scheme0(tFun(tInt, tFun(tInt, tInt))));
  env.set("sub", scheme0(tFun(tInt, tFun(tInt, tInt))));
  env.set("not", scheme0(tFun(tBool, tBool)));
  // eq : forall a. a -> a -> Bool
  env.set("eq", { vars: ["a"], body: tFun({ kind: "TVar", name: "a" }, tFun({ kind: "TVar", name: "a" }, tBool)) });
  return env;
}

function scheme0(t: Type): Scheme {
  return { vars: [], body: t };
}
