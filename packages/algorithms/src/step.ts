import type { Env, NodeId, Subst, Type } from "@infer-tutor/lang";

export type StepKind =
  | "infer-enter"
  | "infer-exit"
  | "unify-enter"
  | "unify-success"
  | "unify-fail"
  | "instantiate"
  | "generalize"
  | "fresh"
  | "done";

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
  message: string;
  detail?: { left: Type; right: Type } | { name: string; type: Type };
};

export type InferResult = {
  type: Type;
  subst: Subst;
  steps: Step[];
  error?: string;
};
