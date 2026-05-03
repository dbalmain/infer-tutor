import {
  type Subst,
  type Type,
  type TVarName,
  applySubstType,
  composeSubst,
  emptySubst,
  freeTypeVars,
  showType,
  singletonSubst,
} from "./types";

export class UnifyError extends Error {
  constructor(message: string, public left: Type, public right: Type) {
    super(message);
  }
}

// Hooks let the caller observe unify's internal events: each substitution
// application, each recursive descent, and each variable binding.
export type UnifyOpts = {
  onApplySubst?: (input: Type, output: Type, subst: Subst) => void;
  onRecurse?: (side: "left" | "right", t1: Type, t2: Type, subst: Subst) => void;
  // substBefore is σ before this bind; substAfter is the result of
  // composeSubst({varName↦t}, substBefore). The composition step is what
  // updates the RHS of existing entries that mention varName.
  onBind?: (varName: TVarName, t: Type, substBefore: Subst, substAfter: Subst) => void;
};

// Unify two types under the running substitution `s`. Returns the *composed*
// substitution. Throws UnifyError on occurs-check or constructor mismatch.
export function unify(
  t1: Type,
  t2: Type,
  s: Subst = emptySubst(),
  opts: UnifyOpts = {},
): Subst {
  const a = applySubstType(s, t1);
  opts.onApplySubst?.(t1, a, s);
  const b = applySubstType(s, t2);
  opts.onApplySubst?.(t2, b, s);
  if (a.kind === "TVar" && b.kind === "TVar" && a.name === b.name) return s;
  if (a.kind === "TVar") {
    const next = composeSubst(bind(a.name, b), s);
    if (next !== s) opts.onBind?.(a.name, b, s, next);
    return next;
  }
  if (b.kind === "TVar") {
    const next = composeSubst(bind(b.name, a), s);
    if (next !== s) opts.onBind?.(b.name, a, s, next);
    return next;
  }
  if (a.kind === "TCon" && b.kind === "TCon" && a.name === b.name) return s;
  if (a.kind === "TFun" && b.kind === "TFun") {
    opts.onRecurse?.("left", a.from, b.from, s);
    const s1 = unify(a.from, b.from, s, opts);
    opts.onRecurse?.("right", a.to, b.to, s1);
    const s2 = unify(a.to, b.to, s1, opts);
    return s2;
  }
  throw new UnifyError(`cannot unify ${showType(a)} with ${showType(b)}`, a, b);
}

function bind(v: TVarName, t: Type): Subst {
  if (t.kind === "TVar" && t.name === v) return emptySubst();
  if (freeTypeVars(t).has(v)) {
    throw new UnifyError(`occurs check: ${v} appears in ${showType(t)}`, { kind: "TVar", name: v }, t);
  }
  return singletonSubst(v, t);
}
