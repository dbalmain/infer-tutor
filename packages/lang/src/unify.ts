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

// Unify two types under the running substitution `s`. Returns the *composed*
// substitution. Throws UnifyError on occurs-check or constructor mismatch.
export function unify(t1: Type, t2: Type, s: Subst = emptySubst()): Subst {
  const a = applySubstType(s, t1);
  const b = applySubstType(s, t2);
  if (a.kind === "TVar" && b.kind === "TVar" && a.name === b.name) return s;
  if (a.kind === "TVar") return composeSubst(bind(a.name, b), s);
  if (b.kind === "TVar") return composeSubst(bind(b.name, a), s);
  if (a.kind === "TCon" && b.kind === "TCon" && a.name === b.name) return s;
  if (a.kind === "TFun" && b.kind === "TFun") {
    const s1 = unify(a.from, b.from, s);
    const s2 = unify(a.to, b.to, s1);
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
