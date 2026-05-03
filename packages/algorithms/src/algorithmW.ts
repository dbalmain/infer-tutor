import {
  type Env,
  type Expr,
  type NodeId,
  type Scheme,
  type Subst,
  type TVarName,
  type Type,
  type UnifyOpts,
  applySubstScheme,
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
  typeEquals,
  unify,
  UnifyError,
} from "@infer-tutor/lang";
import type { InferResult, Step, StepKind } from "./step";

class Tracer {
  steps: Step[] = [];
  nodeTypes: Map<NodeId, Type> = new Map();
  paramTypes: Map<NodeId, Type> = new Map();
  bindingSchemes: Map<NodeId, Scheme> = new Map();
  lamBodyTypes: Map<NodeId, Type> = new Map();
  letBodyTypes: Map<NodeId, Type> = new Map();
  varSchemes: Map<NodeId, Scheme> = new Map();
  introducedVars: Set<TVarName> = new Set();

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
      paramTypes: cloneNodeTypes(this.paramTypes),
      bindingSchemes: new Map(this.bindingSchemes),
      lamBodyTypes: cloneNodeTypes(this.lamBodyTypes),
      letBodyTypes: cloneNodeTypes(this.letBodyTypes),
      varSchemes: new Map(this.varSchemes),
      expectedTypes: new Map(),
      introducedVars: new Set(this.introducedVars),
      message: args.message,
      detail: args.detail,
      constraints: [],
      solvedConstraintIds: [],
    });
  }

  recordNodeType(id: NodeId, t: Type): void {
    this.nodeTypes.set(id, t);
  }

  recordParamType(id: NodeId, t: Type): void {
    this.paramTypes.set(id, t);
  }

  recordBindingScheme(id: NodeId, sc: Scheme): void {
    this.bindingSchemes.set(id, sc);
  }

  recordLamBodyType(id: NodeId, t: Type): void {
    this.lamBodyTypes.set(id, t);
  }

  recordLetBodyType(id: NodeId, t: Type): void {
    this.letBodyTypes.set(id, t);
  }

  recordVarScheme(id: NodeId, sc: Scheme): void {
    this.varSchemes.set(id, sc);
  }

  clearVarScheme(id: NodeId): void {
    this.varSchemes.delete(id);
  }

  introduceVar(name: TVarName): void {
    this.introducedVars.add(name);
  }

  // Emit a subst-apply step. Used both at canonical W-rule sites and inside
  // unify (via the onApplySubst callback). The UI can filter out no-ops.
  pushSubstApply(args: {
    nodeId?: NodeId;
    env: Env;
    subst: Subst;
    input: Type;
    output: Type;
    where: string;
  }): void {
    const noop = typeEquals(args.input, args.output);
    this.push({
      kind: "subst-apply",
      nodeId: args.nodeId,
      env: args.env,
      subst: args.subst,
      message: noop
        ? `apply σ to ${showType(args.input)} (${args.where}, no change)`
        : `apply σ to ${showType(args.input)} ⇒ ${showType(args.output)} (${args.where})`,
      detail: { input: args.input, output: args.output, where: args.where },
    });
  }
}

function unifyOpts(tr: Tracer, env: Env, nodeId?: NodeId): UnifyOpts {
  return {
    onApplySubst: (input, output, subst) => {
      tr.pushSubstApply({
        nodeId,
        env,
        subst,
        input,
        output,
        where: "top of unify",
      });
    },
    onRecurse: (side, t1, t2, subst) => {
      tr.push({
        kind: "unify-recurse",
        nodeId,
        env,
        subst,
        message: `recurse into ${side} of ->: unify ${showType(t1)} with ${showType(t2)}`,
        detail: { left: t1, right: t2 },
      });
    },
    onBind: (varName, t, substBefore, substAfter) => {
      const rawSubst: Subst = new Map(substBefore);
      rawSubst.set(varName, t);
      tr.push({
        kind: "bind-var",
        nodeId,
        env,
        subst: rawSubst,
        message: `bind ${varName} ↦ ${showType(t)}`,
        detail: { name: varName, type: t },
      });
      let changed = false;
      for (const [k, v] of substBefore) {
        const after = substAfter.get(k);
        if (after && !typeEquals(v, after)) { changed = true; break; }
      }
      if (changed) {
        tr.push({
          kind: "subst-compose",
          nodeId,
          env,
          subst: substAfter,
          message: `compose: apply ${varName} ↦ ${showType(t)} to existing σ entries`,
          detail: { name: varName, type: t },
        });
      }
    },
  };
}

function freshTV(tr: Tracer, fresh: FreshSupply): Type {
  const t = fresh.fresh();
  if (t.kind === "TVar") tr.introduceVar(t.name);
  return t;
}

export function inferW(env: Env, expr: Expr): InferResult {
  const tracer = new Tracer();
  const fresh = new FreshSupply();
  try {
    const { subst, type } = infer(env, expr, emptySubst(), tracer, fresh, "root expression");
    // Final resolve: walk all recorded types/schemes and apply σ. Silent
    // (no per-node steps) — the user already knows σ; the done snapshot
    // just shows everything finalized.
    for (const [id, t] of tracer.nodeTypes) {
      tracer.nodeTypes.set(id, applySubstType(subst, t));
    }
    for (const [id, t] of tracer.paramTypes) {
      tracer.paramTypes.set(id, applySubstType(subst, t));
    }
    for (const [id, sc] of tracer.bindingSchemes) {
      tracer.bindingSchemes.set(id, applySubstScheme(subst, sc));
    }
    for (const [id, t] of tracer.letBodyTypes) {
      tracer.letBodyTypes.set(id, applySubstType(subst, t));
    }
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
        const s3 = unify(left, right, s2, unifyOpts(tr, env2, expr.id));
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
      const sCond = unify(tcResolved, tBool, s1, unifyOpts(tr, env, expr.cond.id));
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
      const s4 = unify(left, right, s3, unifyOpts(tr, applySubstEnv(s3, env), expr.id));
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
