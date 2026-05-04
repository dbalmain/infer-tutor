import {
  type Env,
  type Expr,
  type NodeId,
  type Scheme,
  type Subst,
  type TVarName,
  type Type,
  type UnifyOpts,
  applySubstEnv,
  applySubstScheme,
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
  typeEquals,
  unify,
  UnifyError,
} from "@infer-tutor/lang";
import type { InferResult, Step, StepKind } from "./step";

class BDTracer {
  steps: Step[] = [];
  nodeTypes: Map<NodeId, Type> = new Map();
  paramTypes: Map<NodeId, Type> = new Map();
  bindingSchemes: Map<NodeId, Scheme> = new Map();
  lamBodyTypes: Map<NodeId, Type> = new Map();
  letBodyTypes: Map<NodeId, Type> = new Map();
  varSchemes: Map<NodeId, Scheme> = new Map();
  expectedTypes: Map<NodeId, Type> = new Map();
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
      env: new Map(args.env),
      subst: new Map(args.subst),
      nodeTypes: new Map(this.nodeTypes),
      paramTypes: new Map(this.paramTypes),
      bindingSchemes: new Map(this.bindingSchemes),
      lamBodyTypes: new Map(this.lamBodyTypes),
      letBodyTypes: new Map(this.letBodyTypes),
      varSchemes: new Map(this.varSchemes),
      expectedTypes: new Map(this.expectedTypes),
      introducedVars: new Set(this.introducedVars),
      message: args.message,
      detail: args.detail,
      constraints: [],
      solvedConstraintIds: [],
    });
  }

  recordNodeType(id: NodeId, t: Type): void { this.nodeTypes.set(id, t); }
  recordParamType(id: NodeId, t: Type): void { this.paramTypes.set(id, t); }
  recordBindingScheme(id: NodeId, sc: Scheme): void { this.bindingSchemes.set(id, sc); }
  recordLamBodyType(id: NodeId, t: Type): void { this.lamBodyTypes.set(id, t); }
  recordLetBodyType(id: NodeId, t: Type): void { this.letBodyTypes.set(id, t); }
  recordVarScheme(id: NodeId, sc: Scheme): void { this.varSchemes.set(id, sc); }
  clearVarScheme(id: NodeId): void { this.varSchemes.delete(id); }
  setExpected(id: NodeId, t: Type): void { this.expectedTypes.set(id, t); }
  clearExpected(id: NodeId): void { this.expectedTypes.delete(id); }
  introduceVar(name: TVarName): void { this.introducedVars.add(name); }

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

function unifyOpts(tr: BDTracer, env: Env, nodeId?: NodeId): UnifyOpts {
  return {
    onApplySubst: (input, output, subst) => {
      tr.pushSubstApply({ nodeId, env, subst, input, output, where: "top of unify" });
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

function doUnify(
  left: Type,
  right: Type,
  subst: Subst,
  tr: BDTracer,
  env: Env,
  nodeId: NodeId | undefined,
  enterMsg: string,
  successMsg: string,
): Subst {
  tr.push({ kind: "unify-enter", nodeId, env, subst, message: enterMsg, detail: { left, right } });
  try {
    const s = unify(left, right, subst, unifyOpts(tr, env, nodeId));
    tr.push({ kind: "unify-success", nodeId, env: applySubstEnv(s, env), subst: s, message: successMsg });
    return s;
  } catch (e) {
    if (e instanceof UnifyError) {
      tr.push({ kind: "unify-fail", nodeId, env, subst,
        message: `unification failed: ${e.message}`, detail: { left: e.left, right: e.right } });
    }
    throw e;
  }
}

type OnBeforeExit = (type: Type, subst: Subst) => void;

function synth(
  env: Env,
  expr: Expr,
  subst: Subst,
  tr: BDTracer,
  fresh: FreshSupply,
  role: string,
  origin?: "check-fallback",
  onBeforeExit?: OnBeforeExit,
): { type: Type; subst: Subst } {
  const detail = origin ? { origin } : undefined;
  tr.push({
    kind: "synth-enter",
    nodeId: expr.id,
    env,
    subst,
    message: `synth ${role}: ⟦${truncate(showExpr(expr))}⟧`,
    detail,
  });

  switch (expr.kind) {
    case "Lit": {
      const t = expr.lit.kind === "Int" ? tInt : tBool;
      tr.recordNodeType(expr.id, t);
      onBeforeExit?.(t, subst);
      tr.push({ kind: "synth-exit", nodeId: expr.id, env, subst, message: `Literal ⇒ ${showType(t)}`, detail });
      return { type: t, subst };
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
      onBeforeExit?.(inst.type, subst);
      tr.push({ kind: "synth-exit", nodeId: expr.id, env, subst,
        message: `Var ${expr.name} ⇒ ${showType(inst.type)}`, detail });
      return { type: inst.type, subst };
    }

    case "Lam": {
      if (!expr.paramAnn) {
        throw new Error(`bidirectional synth needs a parameter annotation for lambda ${showExpr(expr)}`);
      }
      const paramT = expr.paramAnn;
      tr.recordParamType(expr.id, paramT);
      tr.push({ kind: "use-annot", nodeId: expr.id, env, subst,
        message: `use annotated parameter ${expr.param} : ${showType(paramT)}`,
        detail: { name: expr.param, type: paramT },
      });
      const env2: Env = new Map(env);
      env2.set(expr.param, { vars: [], body: paramT });
      tr.push({ kind: "env-extend", nodeId: expr.id, env: env2, subst,
        message: `extend env with ${expr.param} : ${showType(paramT)}`,
        detail: { name: expr.param, type: paramT },
      });
      const body = synth(env2, expr.body, subst, tr, fresh, "lambda body", undefined, (_t, s) => {
        const t = tr.nodeTypes.get(expr.body.id);
        if (t) tr.recordLamBodyType(expr.id, applySubstType(s, t));
      });
      const bodyT = applySubstType(body.subst, body.type);
      tr.recordLamBodyType(expr.id, bodyT);
      const lamT = tFun(paramT, bodyT);
      tr.recordNodeType(expr.id, lamT);
      onBeforeExit?.(lamT, body.subst);
      tr.push({ kind: "synth-exit", nodeId: expr.id, env, subst: body.subst,
        message: `Lam ⇒ ${showType(lamT)}`, detail });
      return { type: lamT, subst: body.subst };
    }

    case "App": {
      const fn = synth(env, expr.fn, subst, tr, fresh, "function of application", undefined, (t, s) => {
        const fnAtExit = applySubstType(s, t);
        if (fnAtExit.kind === "TFun") tr.recordNodeType(expr.id, fnAtExit.to);
      });
      const fnT = applySubstType(fn.subst, fn.type);
      if (fnT.kind !== "TFun") {
        throw new Error(`cannot apply non-function type ${showType(fnT)}`);
      }
      tr.recordNodeType(expr.id, fnT.to);
      tr.setExpected(expr.arg.id, fnT.from);
      const s2 = check(applySubstEnv(fn.subst, env), expr.arg, fnT.from, fn.subst, tr, fresh, "argument of application");
      const result = applySubstType(s2, fnT.to);
      tr.recordNodeType(expr.id, result);
      tr.clearExpected(expr.arg.id);
      onBeforeExit?.(result, s2);
      tr.push({ kind: "synth-exit", nodeId: expr.id, env, subst: s2,
        message: `App ⇒ ${showType(result)}`, detail });
      return { type: result, subst: s2 };
    }

    case "Let": {
      const value = synth(env, expr.value, subst, tr, fresh, `value bound to ${expr.name}`, undefined, (t, s) => {
        tr.recordBindingScheme(expr.id, { vars: [], body: applySubstType(s, t) });
      });
      const env1 = applySubstEnv(value.subst, env);
      const valueT = applySubstType(value.subst, value.type);
      tr.recordBindingScheme(expr.id, { vars: [], body: valueT });
      const sc = generalize(env1, valueT);
      tr.recordBindingScheme(expr.id, sc);
      tr.push({ kind: "generalize", nodeId: expr.id, env: env1, subst: value.subst,
        message: `generalize ${expr.name} : ${showScheme(sc)}`,
        detail: { name: expr.name, type: sc.body },
      });
      const env2: Env = new Map(env1);
      env2.set(expr.name, sc);
      tr.push({ kind: "env-extend", nodeId: expr.id, env: env2, subst: value.subst,
        message: `extend env with ${expr.name} : ${showScheme(sc)}`,
        detail: { name: expr.name, type: sc.body },
      });
      const body = synth(env2, expr.body, value.subst, tr, fresh, "body of let", undefined, (t, s) => {
        tr.recordLetBodyType(expr.id, applySubstType(s, t));
      });
      const bodyT = applySubstType(body.subst, body.type);
      tr.recordLetBodyType(expr.id, bodyT);
      tr.recordNodeType(expr.id, bodyT);
      onBeforeExit?.(bodyT, body.subst);
      tr.push({ kind: "synth-exit", nodeId: expr.id, env, subst: body.subst,
        message: `Let ⇒ ${showType(bodyT)}`, detail });
      return { type: bodyT, subst: body.subst };
    }

    case "If": {
      const s1 = check(env, expr.cond, tBool, subst, tr, fresh, "condition of if");
      const thenResult = synth(applySubstEnv(s1, env), expr.then, s1, tr, fresh, "then branch");
      const elseResult = synth(applySubstEnv(thenResult.subst, env), expr.else, thenResult.subst, tr, fresh, "else branch");
      const s3 = doUnify(
        applySubstType(elseResult.subst, thenResult.type),
        elseResult.type,
        elseResult.subst,
        tr,
        env,
        expr.id,
        `unify if branches ${showType(thenResult.type)} = ${showType(elseResult.type)}`,
        "if branches match",
      );
      const result = applySubstType(s3, elseResult.type);
      tr.recordNodeType(expr.id, result);
      onBeforeExit?.(result, s3);
      tr.push({ kind: "synth-exit", nodeId: expr.id, env, subst: s3,
        message: `If ⇒ ${showType(result)}`, detail });
      return { type: result, subst: s3 };
    }
  }
}

function check(
  env: Env,
  expr: Expr,
  expected: Type,
  subst: Subst,
  tr: BDTracer,
  fresh: FreshSupply,
  role: string,
): Subst {
  const exp = applySubstType(subst, expected);
  tr.setExpected(expr.id, exp);
  tr.push({
    kind: "check-enter",
    nodeId: expr.id,
    env,
    subst,
    message: `check ${role} ⇐ ${showType(exp)}: ⟦${truncate(showExpr(expr))}⟧`,
  });

  switch (expr.kind) {
    case "Lam": {
      if (exp.kind !== "TFun") {
        throw new Error(`lambda can only check against a function type, got ${showType(exp)}`);
      }
      let s0 = subst;
      if (expr.paramAnn) {
        s0 = doUnify(expr.paramAnn, exp.from, subst, tr, env, expr.id,
          `unify annotated parameter ${showType(expr.paramAnn)} = expected ${showType(exp.from)}`,
          "lambda parameter annotation matches expected type");
      }
      const paramT = applySubstType(s0, exp.from);
      const bodyExpected = applySubstType(s0, exp.to);
      tr.recordParamType(expr.id, paramT);
      tr.recordLamBodyType(expr.id, bodyExpected);
      const env2: Env = new Map(env);
      env2.set(expr.param, { vars: [], body: paramT });
      tr.push({ kind: "env-extend", nodeId: expr.id, env: env2, subst: s0,
        message: `extend env with ${expr.param} : ${showType(paramT)}`,
        detail: { name: expr.param, type: paramT },
      });
      const s1 = check(env2, expr.body, bodyExpected, s0, tr, fresh, "lambda body");
      const bodyT = applySubstType(s1, bodyExpected);
      const lamT = tFun(applySubstType(s1, paramT), bodyT);
      tr.recordLamBodyType(expr.id, bodyT);
      tr.recordNodeType(expr.id, lamT);
      tr.clearExpected(expr.id);
      tr.push({ kind: "check-exit", nodeId: expr.id, env, subst: s1,
        message: `Lam ⇐ ${showType(lamT)}` });
      return s1;
    }

    case "If": {
      const s1 = check(env, expr.cond, tBool, subst, tr, fresh, "condition of if");
      const s2 = check(applySubstEnv(s1, env), expr.then, applySubstType(s1, expected), s1, tr, fresh, "then branch");
      const s3 = check(applySubstEnv(s2, env), expr.else, applySubstType(s2, expected), s2, tr, fresh, "else branch");
      const result = applySubstType(s3, expected);
      tr.recordNodeType(expr.id, result);
      tr.clearExpected(expr.id);
      tr.push({ kind: "check-exit", nodeId: expr.id, env, subst: s3,
        message: `If ⇐ ${showType(result)}` });
      return s3;
    }

    default: {
      const got = synth(env, expr, subst, tr, fresh, role, "check-fallback");
      const actual = applySubstType(got.subst, got.type);
      const wanted = applySubstType(got.subst, expected);
      const s1 = doUnify(wanted, actual, got.subst, tr, env, expr.id,
        `unify synthesized ${showType(actual)} = expected ${showType(wanted)}`,
        "synthesized type matches expected type");
      const result = applySubstType(s1, expected);
      tr.recordNodeType(expr.id, result);
      tr.clearExpected(expr.id);
      tr.push({ kind: "check-exit", nodeId: expr.id, env, subst: s1,
        message: `${expr.kind} ⇐ ${showType(result)}` });
      return s1;
    }
  }
}

export function inferBD(env: Env, expr: Expr): InferResult {
  const tracer = new BDTracer();
  const fresh = new FreshSupply();
  try {
    const result = synth(env, expr, emptySubst(), tracer, fresh, "root expression");
    const finalType = applySubstType(result.subst, result.type);
    for (const [id, t] of tracer.nodeTypes)
      tracer.nodeTypes.set(id, applySubstType(result.subst, t));
    for (const [id, t] of tracer.paramTypes)
      tracer.paramTypes.set(id, applySubstType(result.subst, t));
    for (const [id, sc] of tracer.bindingSchemes)
      tracer.bindingSchemes.set(id, applySubstScheme(result.subst, sc));
    for (const [id, t] of tracer.lamBodyTypes)
      tracer.lamBodyTypes.set(id, applySubstType(result.subst, t));
    for (const [id, t] of tracer.letBodyTypes)
      tracer.letBodyTypes.set(id, applySubstType(result.subst, t));
    tracer.push({ kind: "done", nodeId: expr.id, env, subst: result.subst,
      message: `Final type: ${showType(finalType)}` });
    return { type: finalType, subst: result.subst, steps: tracer.steps };
  } catch (e) {
    const msg = e instanceof Error ? e.message : String(e);
    return { type: { kind: "TVar", name: "?" }, subst: emptySubst(), steps: tracer.steps, error: msg };
  }
}

function truncate(s: string, n = 40): string {
  return s.length > n ? s.slice(0, n - 1) + "…" : s;
}
