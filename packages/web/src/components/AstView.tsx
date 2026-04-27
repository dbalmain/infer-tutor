import {
  type Expr,
  type NodeId,
  type Scheme,
  type Type,
  showScheme,
  showType,
} from "@infer-tutor/lang";

type Props = {
  expr: Expr;
  nodeTypes: Map<NodeId, Type>;
  paramTypes: Map<NodeId, Type>;
  bindingSchemes: Map<NodeId, Scheme>;
  lamBodyTypes: Map<NodeId, Type>;
  varSchemes: Map<NodeId, Scheme>;
  focusId?: NodeId;
  secondaryId?: NodeId;
};

export function AstView(props: Props): JSX.Element {
  return <div className="ast">{renderNode(props.expr, props)}</div>;
}

function renderNode(e: Expr, ctx: Props): JSX.Element {
  const focused = e.id === ctx.focusId;
  const secondary = !focused && e.id === ctx.secondaryId;
  const kind = nodeKind(e);

  const className =
    "ast-node" + (focused ? " focus" : "") + (secondary ? " secondary" : "");

  return (
    <div key={e.id}>
      <div className="ast-line">
        <span className={className}>
          <span className="ast-kind">{kind}</span>
          {renderLabelAndType(e, ctx)}
        </span>
      </div>
      {childExprs(e).length > 0 && (
        <div className="ast-children">
          {childExprs(e).map((c) => renderNode(c, ctx))}
        </div>
      )}
    </div>
  );
}

function renderLabelAndType(e: Expr, ctx: Props): JSX.Element {
  // Lam gets an inline annotation: `\(x : t0) -> Bool`. Skip the trailing
  // `: type` since the function-type parts are already shown inline.
  if (e.kind === "Lam") {
    const paramT = ctx.paramTypes.get(e.id);
    // Use lamBodyTypes (set at body's infer-exit) rather than the body
    // node's own type — those update at different times.
    const bodyT = ctx.lamBodyTypes.get(e.id);
    return (
      <span className="ast-label">
        \({e.param} : <Slot t={paramT} />) -&gt; <Slot t={bodyT} />
      </span>
    );
  }

  // Let displays the bound name's scheme inline + the body's type:
  //   `let id : forall t0. t0 -> t0 in Bool`
  if (e.kind === "Let") {
    const sc = ctx.bindingSchemes.get(e.id);
    const bodyT = ctx.nodeTypes.get(e.body.id);
    return (
      <span className="ast-label">
        let {e.name} : <SchemeSlot sc={sc} /> in <Slot t={bodyT} />
      </span>
    );
  }

  // Var prefers the looked-up scheme (with `forall`) when present —
  // visible between lookup and instantiate.
  if (e.kind === "Var") {
    const sc = ctx.varSchemes.get(e.id);
    if (sc) {
      return (
        <>
          <span className="ast-label">{e.name}</span>{" "}
          <span className="ast-type">: {showScheme(sc)}</span>
        </>
      );
    }
  }

  const display = ctx.nodeTypes.get(e.id);
  return (
    <>
      <span className="ast-label">{nodeLabel(e)}</span>{" "}
      {display ? (
        <span className="ast-type">: {showType(display)}</span>
      ) : (
        <span className="ast-type unknown">: ?</span>
      )}
    </>
  );
}

function SchemeSlot({ sc }: { sc: Scheme | undefined }): JSX.Element {
  if (!sc) return <span className="ast-type unknown">?</span>;
  return <span className="ast-type">{showScheme(sc)}</span>;
}

function Slot({ t }: { t: Type | undefined }): JSX.Element {
  if (!t) return <span className="ast-type unknown">?</span>;
  return <span className="ast-type">{showType(t)}</span>;
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
