import { type Expr, type NodeId } from "@infer-tutor/lang";

type Props = { expr: Expr; focusId?: NodeId };

// Renders the expression in source-like syntax, with everything greyed
// out except the subtree rooted at `focusId`. No container — callers wrap
// in whatever class they want (`.expr-focus`, etc.).
export function ExprFocusView({ expr, focusId }: Props): JSX.Element {
  return <>{renderExpr(expr, focusId, focusId === undefined)}</>;
}

function renderExpr(
  e: Expr,
  focusId: NodeId | undefined,
  inFocus: boolean,
): JSX.Element {
  const isFocus = focusId !== undefined && e.id === focusId;
  const focused = inFocus || isFocus;
  // Three classes: focus-root (the actual focus subtree's root, gets the
  // box), in-focus (descendants of focus, default color), out-of-focus
  // (everything else, dimmed).
  const cls = isFocus ? "focus-root" : focused ? "in-focus" : "out-of-focus";

  switch (e.kind) {
    case "Var":
      return <span className={cls}>{e.name}</span>;
    case "Lit":
      return (
        <span className={cls}>
          {e.lit.kind === "Int"
            ? String(e.lit.value)
            : e.lit.value
              ? "True"
              : "False"}
        </span>
      );
    case "Lam":
      return (
        <span className={cls}>
          \{e.param} -&gt; {renderExpr(e.body, focusId, focused)}
        </span>
      );
    case "App":
      return (
        <span className={cls}>
          ({renderExpr(e.fn, focusId, focused)}{" "}
          {renderExpr(e.arg, focusId, focused)})
        </span>
      );
    case "Let":
      return (
        <span className={cls}>
          let {e.name} = {renderExpr(e.value, focusId, focused)} in{" "}
          {renderExpr(e.body, focusId, focused)}
        </span>
      );
    case "If":
      return (
        <span className={cls}>
          if {renderExpr(e.cond, focusId, focused)} then{" "}
          {renderExpr(e.then, focusId, focused)} else{" "}
          {renderExpr(e.else, focusId, focused)}
        </span>
      );
  }
}
