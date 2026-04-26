import { type Env, showScheme } from "@infer-tutor/lang";

export function EnvPanel({ env }: { env: Env }): JSX.Element {
  if (env.size === 0) return <div className="empty">empty</div>;
  return (
    <div>
      {[...env.entries()].map(([k, sc]) => (
        <div key={k} className="env-row">
          <span className="key">{k}</span>:<span>{showScheme(sc)}</span>
        </div>
      ))}
    </div>
  );
}
