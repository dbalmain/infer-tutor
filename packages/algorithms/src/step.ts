import type { Env, NodeId, Scheme, Subst, TVarName, Type } from "@infer-tutor/lang";

export type StepKind =
  | "infer-enter"
  | "infer-exit"
  | "synth-enter"       // BD: synthesize a type upward
  | "synth-exit"
  | "unify-enter"
  | "unify-recurse"
  | "unify-success"
  | "unify-fail"
  | "bind-var"
  | "subst-compose"     // applying a new binding into the RHS of existing σ entries
  | "lookup"
  | "instantiate"
  | "generalize"
  | "use-annot"         // BD: consume a programmer-written type annotation
  | "fresh-param"
  | "fresh-app"
  | "subst-apply"
  | "env-extend"
  | "done"
  // W' only:
  | "gen-enter"         // entering a node during constraint generation
  | "gen-exit"          // leaving a node during constraint generation
  | "emit-constraint"   // record a new constraint (deferred unification)
  | "solve-phase"       // transition from generation to solving
  | "solve-constraint"  // begin solving one constraint
  // M only:
  | "check-enter"       // entering a node with an expected type (top-down)
  | "check-exit";       // leaving a node after checking against expected type

// A constraint is an equation between two types that must be satisfied.
// W' collects these during generation, then solves them in a separate phase.
export type Constraint = {
  id: number;
  left: Type;
  right: Type;
  reason: string;
};

// A snapshot of algorithm state after one notable event. The UI is a pure
// function of this list + a current index, so renders are reproducible and
// going prev/next is just an index decrement/increment.
export type Step = {
  index: number;
  kind: StepKind;
  nodeId?: NodeId; // AST node this step concerns
  env: Env; // env *at* this point
  subst: Subst; // composed subst *at* this point
  // per-node type knowledge — what type each AST node currently has assigned.
  // `applySubstType(step.subst, step.nodeTypes.get(id))` is what to display.
  nodeTypes: Map<NodeId, Type>;
  // Per-node parameter type. Used for Lam nodes so the param annotation can
  // appear (`\(x : t0) -> ?`) before the body has been inferred.
  paramTypes: Map<NodeId, Type>;
  // Per-Let-node scheme of the bound name. Set at the value's infer-exit
  // (with empty `vars`) so the Let can display the unquantified type before
  // generalize, then updated at generalize with the full forall scheme.
  bindingSchemes: Map<NodeId, Scheme>;
  // Per-Lam-node body type. Decoupled from the body node's own recorded
  // type so the Lam display only "sees" its body type at the body's
  // infer-exit step, not at intermediate steps inside the body.
  lamBodyTypes: Map<NodeId, Type>;
  // Per-Let-node body type. Same decoupling as lamBodyTypes: the Let's
  // "in <type>" slot stays ? until the body's infer-exit/gen-exit fires.
  letBodyTypes: Map<NodeId, Type>;
  // Per-Var-node scheme. Set at the lookup step so the Var displays the
  // full looked-up scheme (e.g. `forall t0. t0 -> t0`); cleared at
  // instantiate so the freshly-renamed type takes over.
  varSchemes: Map<NodeId, Scheme>;
  // M only: the expected type passed down to each node. Set at check-enter,
  // cleared at check-exit. Lets the AST view show "⇐ T" before the actual
  // type is known, making M's top-down flow visible.
  expectedTypes: Map<NodeId, Type>;
  // Every fresh type variable introduced by the algorithm so far. The UI
  // computes the "still open" set as introducedVars \ subst.keys().
  introducedVars: Set<TVarName>;
  message: string;
  detail?:
    | { left: Type; right: Type }
    | { name: string; type: Type }
    | { input: Type; output: Type; where?: string }
    | { origin: "check-fallback" };
  // W' only (empty arrays for W):
  constraints: Constraint[];
  solvedConstraintIds: number[];
  activeConstraintId?: number;
};

export type InferResult = {
  type: Type;
  subst: Subst;
  steps: Step[];
  error?: string;
};
