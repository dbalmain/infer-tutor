import { type Env, showScheme } from "@infer-tutor/lang";

export function EnvPanel({
  env,
  highlight,
}: {
  env: Env;
  highlight?: string;
}): JSX.Element {
  if (env.size === 0) return <div className="empty">empty</div>;
  return (
    <div>
      {[...env.entries()].map(([k, sc]) => (
        <div
          key={k}
          className={"env-row" + (k === highlight ? " env-row-highlight" : "")}
        >
          <span className="key">{k}</span>:<span>{showScheme(sc)}</span>
        </div>
      ))}
    </div>
  );
}
