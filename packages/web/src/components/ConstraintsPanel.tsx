import { showType } from "@infer-tutor/lang";
import type { Constraint } from "@infer-tutor/algorithms";

type Props = {
  constraints: Constraint[];
  solvedConstraintIds: number[];
  activeConstraintId?: number;
};

export function ConstraintsPanel({
  constraints,
  solvedConstraintIds,
  activeConstraintId,
}: Props): JSX.Element {
  if (constraints.length === 0) {
    return <div className="empty">no constraints yet</div>;
  }
  const solvedSet = new Set(solvedConstraintIds);
  return (
    <div className="constraints-list">
      {constraints.map((c) => {
        const solved = solvedSet.has(c.id);
        const active = c.id === activeConstraintId;
        const cls =
          "constraint-row" + (solved ? " solved" : active ? " active" : "");
        return (
          <div key={c.id} className={cls}>
            <span className="constraint-id">[{c.id}]</span>
            <span className="constraint-body">
              {showType(c.left)} = {showType(c.right)}
            </span>
            <span className="constraint-reason">{c.reason}</span>
          </div>
        );
      })}
    </div>
  );
}
