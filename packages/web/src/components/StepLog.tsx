import React, { useEffect, useRef } from "react";
import type { Expr, NodeId } from "@infer-tutor/lang";
import type { Step } from "@infer-tutor/algorithms";
import { ExprFocusView } from "./ExprFocusView";

type Props = {
  steps: Step[];
  visibleIxs: number[];
  current: number;
  rootExpr: Expr | undefined;
  parentMap: Map<NodeId, Expr>;
  onSelect: (i: number) => void;
};

export function StepLog({
  steps,
  visibleIxs,
  current,
  rootExpr,
  parentMap,
  onSelect,
}: Props): JSX.Element {
  const containerRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    const el = containerRef.current?.querySelector<HTMLDivElement>(".row.current");
    el?.scrollIntoView({ block: "nearest" });
  }, [current]);

  return (
    <div className="steplog" ref={containerRef}>
      {visibleIxs.map((i) => {
        const s = steps[i]!;
        return (
          <div
            key={i}
            className={"row" + (i === current ? " current" : "")}
            onClick={() => onSelect(i)}
          >
            <span className="ix">{i}</span>
            <span className="kind">{s.kind}</span>
            <span className="msg">{renderMessage(s, rootExpr, parentMap)}</span>
          </div>
        );
      })}
    </div>
  );
}

// Render the step's message, but if it contains an expression in
// double-square brackets ⟦…⟧, substitute that portion with a focused
// rendering of the immediate parent context.
function renderMessage(
  step: Step,
  rootExpr: Expr | undefined,
  parentMap: Map<NodeId, Expr>,
): React.ReactNode {
  const m = /^(.*⟦)(.*?)(⟧.*)$/s.exec(step.message);
  if (!m || step.nodeId === undefined || !rootExpr) return step.message;
  const contextExpr = parentMap.get(step.nodeId) ?? rootExpr;
  return (
    <>
      {m[1]}
      <ExprFocusView expr={contextExpr} focusId={step.nodeId} />
      {m[3]}
    </>
  );
}
