import {
  type Env,
  type Expr,
  type FreshSupply,
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
  showType,
  typeEquals,
  unify,
  UnifyError,
} from "@infer-tutor/lang";
import type { Constraint, InferResult, Step, StepKind } from "./step";

// Shared step recorder for all four algorithms. Carries every field a
// step may need; algorithms only touch the fields relevant to them
// (e.g. W never sets expectedTypes; W/M/BD never emit constraints).
export class Tracer {
  steps: Step[] = [];
  nodeTypes: Map<NodeId, Type> = new Map();
  paramTypes: Map<NodeId, Type> = new Map();
  bindingSchemes: Map<NodeId, Scheme> = new Map();
  lamBodyTypes: Map<NodeId, Type> = new Map();
  letBodyTypes: Map<NodeId, Type> = new Map();
  varSchemes: Map<NodeId, Scheme> = new Map();
  expectedTypes: Map<NodeId, Type> = new Map();
  introducedVars: Set<TVarName> = new Set();
  constraints: Constraint[] = [];
  solvedConstraintIds: number[] = [];
  activeConstraintId?: number;
  private nextConstraintId = 0;

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
      constraints: [...this.constraints],
      solvedConstraintIds: [...this.solvedConstraintIds],
      activeConstraintId: this.activeConstraintId,
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

  // W' only: record a deferred equation and emit an emit-constraint step.
  emitConstraint(
    left: Type,
    right: Type,
    reason: string,
    nodeId: NodeId | undefined,
    env: Env,
    subst: Subst,
  ): Constraint {
    const c: Constraint = { id: this.nextConstraintId++, left, right, reason };
    this.constraints.push(c);
    this.push({
      kind: "emit-constraint",
      nodeId,
      env,
      subst,
      message: `emit [${c.id}]: ${showType(left)} = ${showType(right)}  (${reason})`,
      detail: { left, right },
    });
    return c;
  }

  // Walk every recorded slot and rewrite through `subst`. Used by W' after
  // each constraint solve, and by finalize() at the done step.
  applySubstToAll(subst: Subst): void {
    for (const [id, t] of this.nodeTypes) this.nodeTypes.set(id, applySubstType(subst, t));
    for (const [id, t] of this.paramTypes) this.paramTypes.set(id, applySubstType(subst, t));
    for (const [id, t] of this.lamBodyTypes) this.lamBodyTypes.set(id, applySubstType(subst, t));
    for (const [id, t] of this.letBodyTypes) this.letBodyTypes.set(id, applySubstType(subst, t));
    for (const [id, sc] of this.bindingSchemes)
      this.bindingSchemes.set(id, applySubstScheme(subst, sc));
  }
}

export function freshTV(tr: Tracer, fresh: FreshSupply): Type {
  const t = fresh.fresh();
  if (t.kind === "TVar") tr.introduceVar(t.name);
  return t;
}

// Standard unify hooks used by every algorithm: turn each event inside
// `unify` into a step (subst-apply / unify-recurse / bind-var / subst-compose).
export function makeUnifyOpts(tr: Tracer, env: Env, nodeId?: NodeId): UnifyOpts {
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
      // bind-var shows σ with the new binding naively inserted (no
      // composition into existing RHS yet) so the next step can highlight
      // the composition itself as a distinct event.
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

// Brackets a unification with enter/success/fail steps. Used by M and BD
// where unification sites have meaningful per-call messages; W/W' call
// unify() directly with makeUnifyOpts because their messaging happens at
// the site that invokes unify (App's unify-enter etc.).
export function doUnify(
  left: Type,
  right: Type,
  subst: Subst,
  tr: Tracer,
  env: Env,
  nodeId: NodeId | undefined,
  enterMsg: string,
  successMsg: string,
): Subst {
  tr.push({ kind: "unify-enter", nodeId, env, subst, message: enterMsg, detail: { left, right } });
  try {
    const s = unify(left, right, subst, makeUnifyOpts(tr, env, nodeId));
    tr.push({ kind: "unify-success", nodeId, env: applySubstEnv(s, env), subst: s, message: successMsg });
    return s;
  } catch (e) {
    if (e instanceof UnifyError) {
      tr.push({
        kind: "unify-fail",
        nodeId,
        env,
        subst,
        message: `unification failed: ${e.message}`,
        detail: { left: e.left, right: e.right },
      });
    }
    throw e;
  }
}

export function truncate(s: string, n = 40): string {
  return s.length > n ? s.slice(0, n - 1) + "…" : s;
}

// Standard success finalization: rewrite all recorded slots through the
// final substitution and emit the done step.
export function finalize(
  tr: Tracer,
  env: Env,
  expr: Expr,
  subst: Subst,
  finalType: Type,
): InferResult {
  tr.applySubstToAll(subst);
  tr.push({
    kind: "done",
    nodeId: expr.id,
    env,
    subst,
    message: `Final type: ${showType(finalType)}`,
  });
  return { type: finalType, subst, steps: tr.steps };
}

export function errorResult(tr: Tracer, e: unknown): InferResult {
  return {
    type: { kind: "TVar", name: "?" },
    subst: emptySubst(),
    steps: tr.steps,
    error: e instanceof Error ? e.message : String(e),
  };
}
