import { type Expr, type NodeId } from "@infer-tutor/lang";

export type FocusMode = "default" | "enter" | "exit";

type Props = { expr: Expr; focusId?: NodeId; mode?: FocusMode };

// Renders the expression in source-like syntax, with the subtree rooted
// at `focusId` highlighted and everything else dimmed. The exact colors
// depend on `mode`:
//   - default: focus = white, surrounding = dark grey  (full-context view)
//   - enter:   focus = white, surrounding = secondary  (just-entered child)
//   - exit:    focus = secondary, surrounding = white  (just-exited child)
// No container — callers wrap in whatever class they want.
export function ExprFocusView({
  expr,
  focusId,
  mode = "default",
}: Props): JSX.Element {
  // If the rendered expression IS the focus (root case), there's no
  // surrounding to contrast against; fall back to default so the whole
  // thing reads as primary.
  const effectiveMode: FocusMode =
    focusId !== undefined && expr.id === focusId ? "default" : mode;
  return <>{renderExpr(expr, focusId, focusId === undefined, effectiveMode)}</>;
}

function renderExpr(
  e: Expr,
  focusId: NodeId | undefined,
  inFocus: boolean,
  mode: FocusMode,
): JSX.Element {
  const isFocus = focusId !== undefined && e.id === focusId;
  const focused = inFocus || isFocus;
  const cls = classFor(focused, isFocus, mode);

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
          \{e.param} -&gt; {renderExpr(e.body, focusId, focused, mode)}
        </span>
      );
    case "App":
      return (
        <span className={cls}>
          ({renderExpr(e.fn, focusId, focused, mode)}{" "}
          {renderExpr(e.arg, focusId, focused, mode)})
        </span>
      );
    case "Let":
      return (
        <span className={cls}>
          let {e.name} = {renderExpr(e.value, focusId, focused, mode)} in{" "}
          {renderExpr(e.body, focusId, focused, mode)}
        </span>
      );
    case "If":
      return (
        <span className={cls}>
          if {renderExpr(e.cond, focusId, focused, mode)} then{" "}
          {renderExpr(e.then, focusId, focused, mode)} else{" "}
          {renderExpr(e.else, focusId, focused, mode)}
        </span>
      );
  }
}

function classFor(focused: boolean, isFocus: boolean, mode: FocusMode): string {
  if (mode === "exit") {
    // We're exiting from the focus subtree to the surrounding context —
    // the surrounding is "where we are now", focus is "where we just were".
    return focused ? "secondary-focus" : "in-focus";
  }
  if (mode === "enter") {
    // The surrounding context is what we're leaving; focus is the new spot.
    return focused ? (isFocus ? "focus-root" : "in-focus") : "secondary-focus";
  }
  // default — high contrast between focus and everything else.
  return focused ? (isFocus ? "focus-root" : "in-focus") : "out-of-focus";
}
