import {
  type Expr,
  type NodeId,
  type Subst,
  type Type,
  applySubstType,
  showExpr,
  showType,
} from "@infer-tutor/lang";

type Props = {
  expr: Expr;
  nodeTypes: Map<NodeId, Type>;
  subst: Subst;
  focusId?: NodeId;
};

export function AstView({ expr, nodeTypes, subst, focusId }: Props): JSX.Element {
  return <div className="ast">{renderNode(expr, nodeTypes, subst, focusId)}</div>;
}

function renderNode(
  e: Expr,
  nodeTypes: Map<NodeId, Type>,
  subst: Subst,
  focusId: NodeId | undefined,
): JSX.Element {
  const known = nodeTypes.get(e.id);
  const display = known ? applySubstType(subst, known) : undefined;
  const focused = e.id === focusId;
  const label = nodeLabel(e);
  const kind = nodeKind(e);

  return (
    <div key={e.id}>
      <div className="ast-line">
        <span className={"ast-node" + (focused ? " focus" : "")}>
          <span className="ast-kind">{kind}</span>
          <span className="ast-label">{label}</span>
          {display ? (
            <span className="ast-type">: {showType(display)}</span>
          ) : (
            <span className="ast-type unknown">: ?</span>
          )}
        </span>
      </div>
      {childExprs(e).length > 0 && (
        <div className="ast-children">
          {childExprs(e).map((c) => renderNode(c, nodeTypes, subst, focusId))}
        </div>
      )}
    </div>
  );
}

function nodeKind(e: Expr): string {
  return e.kind;
}

function nodeLabel(e: Expr): string {
  switch (e.kind) {
    case "Var":
      return e.name;
    case "Lit":
      return e.lit.kind === "Int" ? String(e.lit.value) : e.lit.value ? "True" : "False";
    case "Lam":
      return `\\${e.param}`;
    case "App":
      return "@";
    case "Let":
      return `let ${e.name}`;
    case "If":
      return "if";
  }
}

function childExprs(e: Expr): Expr[] {
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

// kept for debugging; not used
export function _showExpr(e: Expr): string {
  return showExpr(e);
}
