import { showType, type Type } from "./types";

export type NodeId = number;

export type Expr =
  | { kind: "Var"; id: NodeId; name: string }
  | { kind: "Lit"; id: NodeId; lit: Literal }
  | { kind: "Lam"; id: NodeId; param: string; paramAnn?: Type; body: Expr }
  | { kind: "App"; id: NodeId; fn: Expr; arg: Expr }
  | { kind: "Let"; id: NodeId; name: string; value: Expr; body: Expr }
  | { kind: "If"; id: NodeId; cond: Expr; then: Expr; else: Expr };

export type Literal =
  | { kind: "Int"; value: number }
  | { kind: "Bool"; value: boolean };

// Build a map from each node's id to its immediate parent expression. Useful
// for "show me the surrounding context of this node".
export function buildParentMap(root: Expr): Map<NodeId, Expr> {
  const m = new Map<NodeId, Expr>();
  const walk = (e: Expr) => {
    for (const c of children(e)) {
      m.set(c.id, e);
      walk(c);
    }
  };
  walk(root);
  return m;
}

export function children(e: Expr): Expr[] {
  switch (e.kind) {
    case "Var":
    case "Lit":
      return [];
    case "Lam":
      return [e.body];
    case "App":
      return [e.fn, e.arg];
    case "Let":
      return [e.value, e.body];
    case "If":
      return [e.cond, e.then, e.else];
  }
}

export function showExpr(e: Expr): string {
  switch (e.kind) {
    case "Var":
      return e.name;
    case "Lit":
      return e.lit.kind === "Int" ? String(e.lit.value) : e.lit.value ? "True" : "False";
    case "Lam":
      return e.paramAnn
        ? `\\(${e.param} : ${showType(e.paramAnn)}) -> ${showExpr(e.body)}`
        : `\\${e.param} -> ${showExpr(e.body)}`;
    case "App":
      return `(${showExpr(e.fn)} ${showExpr(e.arg)})`;
    case "Let":
      return `let ${e.name} = ${showExpr(e.value)} in ${showExpr(e.body)}`;
    case "If":
      return `if ${showExpr(e.cond)} then ${showExpr(e.then)} else ${showExpr(e.else)}`;
  }
}
