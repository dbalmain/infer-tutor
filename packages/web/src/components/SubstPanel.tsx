import { type Subst, type TVarName, showType } from "@infer-tutor/lang";

type Props = {
  subst: Subst;
  liveVars: Set<TVarName>;
  highlights?: Set<TVarName>;
};

export function SubstPanel({ subst, liveVars, highlights }: Props): JSX.Element {
  if (subst.size === 0) return <div className="empty">∅</div>;
  return (
    <div>
      {[...subst.entries()].map(([k, t]) => {
        const dead = !liveVars.has(k);
        const isHighlight = highlights?.has(k) ?? false;
        return (
          <div
            key={k}
            className={
              "subst-row" +
              (dead ? " subst-row-dead" : "") +
              (isHighlight ? " subst-row-highlight" : "")
            }
            title={dead ? "fully applied — no longer appears in any displayed type" : undefined}
          >
            <span className="key">{k}</span>↦<span>{showType(t)}</span>
          </div>
        );
      })}
    </div>
  );
}
