import { type Subst, showType } from "@infer-tutor/lang";

export function SubstPanel({ subst }: { subst: Subst }): JSX.Element {
  if (subst.size === 0) return <div className="empty">∅</div>;
  return (
    <div>
      {[...subst.entries()].map(([k, t]) => (
        <div key={k} className="subst-row">
          <span className="key">{k}</span>↦<span>{showType(t)}</span>
        </div>
      ))}
    </div>
  );
}
