import { useEffect, useMemo, useState } from "react";
import { type Expr, parse, ParseError } from "@infer-tutor/lang";
import { defaultEnv, inferW, type InferResult } from "@infer-tutor/algorithms";
import { AstView } from "./components/AstView";
import { EnvPanel } from "./components/EnvPanel";
import { SubstPanel } from "./components/SubstPanel";
import { StepLog } from "./components/StepLog";

const DEFAULT_EXPR = "let id = \\x -> x in id (add 1 2)";

export function App(): JSX.Element {
  const [src, setSrc] = useState(DEFAULT_EXPR);
  const [submitted, setSubmitted] = useState(DEFAULT_EXPR);
  const [stepIx, setStepIx] = useState(0);

  const parseResult = useMemo<{ expr?: Expr; error?: string }>(() => {
    try {
      return { expr: parse(submitted) };
    } catch (e) {
      if (e instanceof ParseError) return { error: e.message };
      return { error: e instanceof Error ? e.message : String(e) };
    }
  }, [submitted]);

  const inferResult = useMemo<InferResult | undefined>(() => {
    if (!parseResult.expr) return undefined;
    return inferW(defaultEnv(), parseResult.expr);
  }, [parseResult.expr]);

  const steps = inferResult?.steps ?? [];
  const currentStep = steps[stepIx];
  const focusId = currentStep?.nodeId;

  useEffect(() => {
    setStepIx(0);
  }, [submitted]);

  useEffect(() => {
    function onKey(ev: KeyboardEvent) {
      if (ev.target instanceof HTMLInputElement || ev.target instanceof HTMLTextAreaElement) return;
      if (ev.key === "ArrowRight" || ev.key === "j" || ev.key === "n") {
        setStepIx((i) => Math.min(steps.length - 1, i + 1));
      } else if (ev.key === "ArrowLeft" || ev.key === "k" || ev.key === "p") {
        setStepIx((i) => Math.max(0, i - 1));
      } else if (ev.key === "Home" || ev.key === "g") {
        setStepIx(0);
      } else if (ev.key === "End" || ev.key === "G") {
        setStepIx(Math.max(0, steps.length - 1));
      }
    }
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [steps.length]);

  function run(): void {
    setSubmitted(src);
  }

  return (
    <div className="app">
      <div className="topbar">
        <h1>infer-tutor</h1>
        <input
          className="input"
          value={src}
          spellCheck={false}
          onChange={(e) => setSrc(e.target.value)}
          onKeyDown={(e) => {
            if (e.key === "Enter") run();
          }}
        />
        <button onClick={run}>Run</button>
      </div>

      {parseResult.error && <div className="error-banner">parse error: {parseResult.error}</div>}
      {inferResult?.error && <div className="error-banner">type error: {inferResult.error}</div>}

      <div className="workspace">
        <div className="col">
          <div className="panel" style={{ flex: 1 }}>
            <div className="panel-header">AST · types update as the algorithm runs</div>
            <div className="panel-body">
              {parseResult.expr && currentStep && (
                <AstView
                  expr={parseResult.expr}
                  nodeTypes={currentStep.nodeTypes}
                  subst={currentStep.subst}
                  focusId={focusId}
                />
              )}
            </div>
          </div>
          <div className="panel" style={{ flex: 1 }}>
            <div className="panel-header">Step log · click a row to jump</div>
            <div className="panel-body" style={{ padding: 0 }}>
              <StepLog steps={steps} current={stepIx} onSelect={setStepIx} />
            </div>
          </div>
        </div>

        <div className="col">
          <div className="panel" style={{ flex: 1 }}>
            <div className="panel-header">Environment</div>
            <div className="panel-body">
              {currentStep && <EnvPanel env={currentStep.env} />}
            </div>
          </div>
          <div className="panel" style={{ flex: 1 }}>
            <div className="panel-header">Substitution</div>
            <div className="panel-body">
              {currentStep && <SubstPanel subst={currentStep.subst} />}
            </div>
          </div>
          <div className="panel" style={{ flex: 0.6 }}>
            <div className="panel-header">Current step</div>
            <div className="panel-body">
              {currentStep ? (
                <div>
                  <div style={{ color: "var(--accent-2)", marginBottom: 6 }}>{currentStep.kind}</div>
                  <div>{currentStep.message}</div>
                </div>
              ) : (
                <div className="empty">no steps</div>
              )}
            </div>
          </div>
        </div>
      </div>

      <div className="bottombar">
        <button disabled={stepIx <= 0} onClick={() => setStepIx(0)}>
          ⏮
        </button>
        <button disabled={stepIx <= 0} onClick={() => setStepIx(stepIx - 1)}>
          ◀ prev
        </button>
        <span className="step-position">
          {steps.length === 0 ? "0 / 0" : `${stepIx + 1} / ${steps.length}`}
        </span>
        <button disabled={stepIx >= steps.length - 1} onClick={() => setStepIx(stepIx + 1)}>
          next ▶
        </button>
        <button
          disabled={stepIx >= steps.length - 1}
          onClick={() => setStepIx(steps.length - 1)}
        >
          ⏭
        </button>
        <span className="keyhints">←/→ or j/k step · g/G start/end</span>
      </div>
    </div>
  );
}
