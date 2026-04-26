import {
  type Env,
  type Expr,
  type NodeId,
  type Scheme,
  type Subst,
  type Type,
  FreshSupply,
  applySubstEnv,
  applySubstType,
  composeSubst,
  emptySubst,
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
import type { InferResult, Step, StepKind } from "./step";

class Tracer {
  steps: Step[] = [];
  nodeTypes: Map<NodeId, Type> = new Map();

  push(args: {
    kind: StepKind;
    nodeId?: NodeId;
    env: Env;
    subst: Subst;
    message: string;
    detail?: Step["detail"];
  }): void {
    this.steps.push({
      index: this.steps.length,
      kind: args.kind,
      nodeId: args.nodeId,
      env: cloneEnv(args.env),
      subst: cloneSubst(args.subst),
      nodeTypes: cloneNodeTypes(this.nodeTypes),
      message: args.message,
      detail: args.detail,
    });
  }

  recordNodeType(id: NodeId, t: Type): void {
    this.nodeTypes.set(id, t);
  }
}

export function inferW(env: Env, expr: Expr): InferResult {
  const tracer = new Tracer();
  const fresh = new FreshSupply();
  try {
    const { subst, type } = infer(env, expr, emptySubst(), tracer, fresh);
    tracer.push({
      kind: "done",
      nodeId: expr.id,
      env,
      subst,
      message: `Final type: ${showType(applySubstType(subst, type))}`,
    });
    return { type: applySubstType(subst, type), subst, steps: tracer.steps };
  } catch (e) {
    const msg = e instanceof Error ? e.message : String(e);
    return {
      type: { kind: "TVar", name: "?" },
      subst: emptySubst(),
      steps: tracer.steps,
      error: msg,
    };
  }
}

function infer(
  env: Env,
  expr: Expr,
  s0: Subst,
  tr: Tracer,
  fresh: FreshSupply,
): { subst: Subst; type: Type } {
  tr.push({
    kind: "infer-enter",
    nodeId: expr.id,
    env,
    subst: s0,
    message: `infer ⟦${truncate(showExpr(expr))}⟧`,
  });

  switch (expr.kind) {
    case "Lit": {
      const t = expr.lit.kind === "Int" ? tInt : tBool;
      tr.recordNodeType(expr.id, t);
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
      const inst = instantiate(sc, fresh);
      tr.recordNodeType(expr.id, inst.type);
      tr.push({
        kind: "instantiate",
        nodeId: expr.id,
        env,
        subst: s0,
        message: `${expr.name} : ${showScheme(sc)} ⇒ ${showType(inst.type)}`,
        detail: { name: expr.name, type: inst.type },
      });
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
      const tv = fresh.fresh();
      tr.push({
        kind: "fresh",
        nodeId: expr.id,
        env,
        subst: s0,
        message: `fresh ${showType(tv)} for parameter ${expr.param}`,
      });
      const env2: Env = new Map(env);
      env2.set(expr.param, { vars: [], body: tv });
      const { subst: s1, type: tBody } = infer(env2, expr.body, s0, tr, fresh);
      const tFunType = tFun(applySubstType(s1, tv), tBody);
      tr.recordNodeType(expr.id, tFunType);
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
      const { subst: s1, type: t1 } = infer(env, expr.fn, s0, tr, fresh);
      const env2 = applySubstEnv(s1, env);
      const { subst: s2, type: t2 } = infer(env2, expr.arg, s1, tr, fresh);
      const tv = fresh.fresh();
      tr.push({
        kind: "fresh",
        nodeId: expr.id,
        env: env2,
        subst: s2,
        message: `fresh ${showType(tv)} for application result`,
      });
      const left = applySubstType(s2, t1);
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
        const s3 = unify(left, right, s2);
        tr.recordNodeType(expr.id, applySubstType(s3, tv));
        tr.push({
          kind: "unify-success",
          nodeId: expr.id,
          env: applySubstEnv(s3, env),
          subst: s3,
          message: `unified — application has type ${showType(applySubstType(s3, tv))}`,
        });
        tr.push({
          kind: "infer-exit",
          nodeId: expr.id,
          env: applySubstEnv(s3, env),
          subst: s3,
          message: `App ⊢ ${showType(applySubstType(s3, tv))}`,
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
      const { subst: s1, type: t1 } = infer(env, expr.value, s0, tr, fresh);
      const env1 = applySubstEnv(s1, env);
      const sc = generalize(env1, applySubstType(s1, t1));
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
      const { subst: s2, type: t2 } = infer(env2, expr.body, s1, tr, fresh);
      tr.recordNodeType(expr.id, t2);
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
      const { subst: s1, type: tc } = infer(env, expr.cond, s0, tr, fresh);
      tr.push({
        kind: "unify-enter",
        nodeId: expr.cond.id,
        env,
        subst: s1,
        message: `condition must be Bool: unify ${showType(applySubstType(s1, tc))} with Bool`,
        detail: { left: applySubstType(s1, tc), right: tBool },
      });
      const sCond = unify(applySubstType(s1, tc), tBool, s1);
      tr.push({
        kind: "unify-success",
        nodeId: expr.cond.id,
        env,
        subst: sCond,
        message: `condition unified to Bool`,
      });
      const env2 = applySubstEnv(sCond, env);
      const { subst: s2, type: tThen } = infer(env2, expr.then, sCond, tr, fresh);
      const env3 = applySubstEnv(s2, env);
      const { subst: s3, type: tElse } = infer(env3, expr.else, s2, tr, fresh);
      const left = applySubstType(s3, tThen);
      const right = applySubstType(s3, tElse);
      tr.push({
        kind: "unify-enter",
        nodeId: expr.id,
        env: applySubstEnv(s3, env),
        subst: s3,
        message: `branches must agree: unify ${showType(left)} with ${showType(right)}`,
        detail: { left, right },
      });
      const s4 = unify(left, right, s3);
      const result = applySubstType(s4, tElse);
      tr.recordNodeType(expr.id, result);
      tr.push({
        kind: "unify-success",
        nodeId: expr.id,
        env: applySubstEnv(s4, env),
        subst: s4,
        message: `branches agree on ${showType(result)}`,
      });
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

function truncate(s: string, n = 40): string {
  return s.length > n ? s.slice(0, n - 1) + "…" : s;
}

function cloneEnv(env: Env): Env {
  return new Map(env);
}

function cloneSubst(s: Subst): Subst {
  return new Map(s);
}

function cloneNodeTypes(m: Map<NodeId, Type>): Map<NodeId, Type> {
  return new Map(m);
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
  // pair : forall a b. a -> b -> Pair a b   (skip until we have type apps; placeholder)
  return env;
}

function scheme0(t: Type): Scheme {
  return { vars: [], body: t };
}
