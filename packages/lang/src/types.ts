export type TVarName = string;

export type Type =
  | { kind: "TVar"; name: TVarName }
  | { kind: "TCon"; name: string }
  | { kind: "TFun"; from: Type; to: Type };

export type Scheme = { vars: TVarName[]; body: Type };

export type Subst = Map<TVarName, Type>;

export type Env = Map<string, Scheme>;

export const tInt: Type = { kind: "TCon", name: "Int" };
export const tBool: Type = { kind: "TCon", name: "Bool" };

export function tVar(name: TVarName): Type {
  return { kind: "TVar", name };
}

export function tFun(from: Type, to: Type): Type {
  return { kind: "TFun", from, to };
}

export function tFuns(...ts: Type[]): Type {
  if (ts.length < 2) throw new Error("tFuns needs at least 2 types");
  let acc = ts[ts.length - 1]!;
  for (let i = ts.length - 2; i >= 0; i--) acc = tFun(ts[i]!, acc);
  return acc;
}

export function emptySubst(): Subst {
  return new Map();
}

export function singletonSubst(v: TVarName, t: Type): Subst {
  return new Map([[v, t]]);
}

// Apply a substitution to a type. Walks until a fixed point on each TVar so
// chained mappings (a -> b, b -> Int) collapse to (a -> Int).
export function applySubstType(s: Subst, t: Type): Type {
  switch (t.kind) {
    case "TVar": {
      const r = s.get(t.name);
      if (!r) return t;
      return applySubstType(s, r);
    }
    case "TCon":
      return t;
    case "TFun":
      return tFun(applySubstType(s, t.from), applySubstType(s, t.to));
  }
}

export function applySubstScheme(s: Subst, sc: Scheme): Scheme {
  if (sc.vars.length === 0) return { vars: [], body: applySubstType(s, sc.body) };
  // Remove bound variables from the substitution before applying.
  const filtered: Subst = new Map();
  for (const [k, v] of s) if (!sc.vars.includes(k)) filtered.set(k, v);
  return { vars: sc.vars, body: applySubstType(filtered, sc.body) };
}

export function applySubstEnv(s: Subst, env: Env): Env {
  const out: Env = new Map();
  for (const [k, sc] of env) out.set(k, applySubstScheme(s, sc));
  return out;
}

// composeSubst(s1, s2) = "apply s2 first, then s1". The result satisfies
// applySubstType(composeSubst(s1, s2), t) === applySubstType(s1, applySubstType(s2, t)).
export function composeSubst(s1: Subst, s2: Subst): Subst {
  const out: Subst = new Map();
  for (const [k, v] of s2) out.set(k, applySubstType(s1, v));
  for (const [k, v] of s1) if (!out.has(k)) out.set(k, v);
  return out;
}

export function freeTypeVars(t: Type): Set<TVarName> {
  const out = new Set<TVarName>();
  const go = (t: Type) => {
    switch (t.kind) {
      case "TVar":
        out.add(t.name);
        return;
      case "TCon":
        return;
      case "TFun":
        go(t.from);
        go(t.to);
        return;
    }
  };
  go(t);
  return out;
}

export function freeTypeVarsScheme(sc: Scheme): Set<TVarName> {
  const fvs = freeTypeVars(sc.body);
  for (const v of sc.vars) fvs.delete(v);
  return fvs;
}

export function freeTypeVarsEnv(env: Env): Set<TVarName> {
  const out = new Set<TVarName>();
  for (const sc of env.values()) for (const v of freeTypeVarsScheme(sc)) out.add(v);
  return out;
}

export function generalize(env: Env, t: Type): Scheme {
  const envFvs = freeTypeVarsEnv(env);
  const tFvs = freeTypeVars(t);
  const vars: TVarName[] = [];
  for (const v of tFvs) if (!envFvs.has(v)) vars.push(v);
  return { vars, body: t };
}

export class FreshSupply {
  private counter = 0;
  fresh(prefix = "t"): Type {
    return { kind: "TVar", name: `${prefix}${this.counter++}` };
  }
  freshName(prefix = "t"): TVarName {
    return `${prefix}${this.counter++}`;
  }
  reset(): void {
    this.counter = 0;
  }
}

export function instantiate(sc: Scheme, fresh: FreshSupply): { type: Type; mapping: Map<TVarName, Type> } {
  const mapping = new Map<TVarName, Type>();
  for (const v of sc.vars) mapping.set(v, fresh.fresh());
  return { type: applySubstType(mapping, sc.body), mapping };
}

export function showType(t: Type, paren = false): string {
  switch (t.kind) {
    case "TVar":
      return t.name;
    case "TCon":
      return t.name;
    case "TFun": {
      const inner = `${showType(t.from, true)} -> ${showType(t.to, false)}`;
      return paren ? `(${inner})` : inner;
    }
  }
}

export function showScheme(sc: Scheme): string {
  if (sc.vars.length === 0) return showType(sc.body);
  return `forall ${sc.vars.join(" ")}. ${showType(sc.body)}`;
}

export function showSubst(s: Subst): string {
  if (s.size === 0) return "{}";
  const parts: string[] = [];
  for (const [k, v] of s) parts.push(`${k} ↦ ${showType(v)}`);
  return `{ ${parts.join(", ")} }`;
}

export function showEnv(env: Env): string {
  if (env.size === 0) return "{}";
  const parts: string[] = [];
  for (const [k, sc] of env) parts.push(`${k}: ${showScheme(sc)}`);
  return `{ ${parts.join(", ")} }`;
}
