export type NodeId = number;

export type Expr =
  | { kind: "Var"; id: NodeId; name: string }
  | { kind: "Lit"; id: NodeId; lit: Literal }
  | { kind: "Lam"; id: NodeId; param: string; body: Expr }
  | { kind: "App"; id: NodeId; fn: Expr; arg: Expr }
  | { kind: "Let"; id: NodeId; name: string; value: Expr; body: Expr }
  | { kind: "If"; id: NodeId; cond: Expr; then: Expr; else: Expr };

export type Literal =
  | { kind: "Int"; value: number }
  | { kind: "Bool"; value: boolean };

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
      return `\\${e.param} -> ${showExpr(e.body)}`;
    case "App":
      return `(${showExpr(e.fn)} ${showExpr(e.arg)})`;
    case "Let":
      return `let ${e.name} = ${showExpr(e.value)} in ${showExpr(e.body)}`;
    case "If":
      return `if ${showExpr(e.cond)} then ${showExpr(e.then)} else ${showExpr(e.else)}`;
  }
}
