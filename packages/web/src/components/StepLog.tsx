import { useEffect, useRef } from "react";
import type { Step } from "@infer-tutor/algorithms";

type Props = {
  steps: Step[];
  current: number;
  onSelect: (i: number) => void;
};

export function StepLog({ steps, current, onSelect }: Props): JSX.Element {
  const containerRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    const el = containerRef.current?.querySelector<HTMLDivElement>(".row.current");
    el?.scrollIntoView({ block: "nearest" });
  }, [current]);

  return (
    <div className="steplog" ref={containerRef}>
      {steps.map((s, i) => (
        <div
          key={i}
          className={"row" + (i === current ? " current" : "")}
          onClick={() => onSelect(i)}
        >
          <span className="ix">{i}</span>
          <span className="kind">{s.kind}</span>
          <span className="msg">{s.message}</span>
        </div>
      ))}
    </div>
  );
}
