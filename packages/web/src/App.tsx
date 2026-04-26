import { useEffect, useMemo, useState } from "react";
import {
  type Expr,
  type NodeId,
  type Scheme,
  type TVarName,
  type Type,
  buildParentMap,
  freeTypeVars,
  freeTypeVarsScheme,
  parse,
  ParseError,
  typeEquals,
} from "@infer-tutor/lang";
import { defaultEnv, inferW, type InferResult, type Step } from "@infer-tutor/algorithms";
import { AstView } from "./components/AstView";
import { EnvPanel } from "./components/EnvPanel";
import { SubstPanel } from "./components/SubstPanel";
import { StepLog } from "./components/StepLog";
import { UnifyDisplay } from "./components/UnifyDisplay";
import { StepExplanation } from "./components/StepExplanation";
import { ExprFocusView } from "./components/ExprFocusView";

const DEFAULT_EXPR = "let id = \\x -> x in id (add 1 2)";

function isNoopSubstApply(s: Step): boolean {
  if (s.kind !== "subst-apply") return false;
  if (!s.detail || !("input" in s.detail)) return false;
  return typeEquals(s.detail.input, s.detail.output);
}

// "Live" = appears as a raw TVar anywhere visible — node types, param
// types, schemes, env schemes, or σ RHS. A σ entry whose key isn't live
// has been fully consumed and can be greyed out. (We use raw types
// because the AST view no longer auto-applies σ.)
function computeLiveVars(step: Step): Set<TVarName> {
  const out = new Set<TVarName>();
  const addType = (t: Type) => {
    for (const v of freeTypeVars(t)) out.add(v);
  };
  const addScheme = (sc: Scheme) => {
    for (const v of freeTypeVarsScheme(sc)) out.add(v);
  };
  for (const t of step.nodeTypes.values()) addType(t);
  for (const t of step.paramTypes.values()) addType(t);
  for (const t of step.lamBodyTypes.values()) addType(t);
  for (const sc of step.bindingSchemes.values()) addScheme(sc);
  for (const sc of step.varSchemes.values()) addScheme(sc);
  for (const sc of step.env.values()) addScheme(sc);
  for (const t of step.subst.values()) addType(t);
  return out;
}

function naturalVarCompare(a: string, b: string): number {
  const ma = /^([a-zA-Z]+)(\d+)$/.exec(a);
  const mb = /^([a-zA-Z]+)(\d+)$/.exec(b);
  if (ma && mb && ma[1] === mb[1]) return Number(ma[2]) - Number(mb[2]);
  return a.localeCompare(b);
}

export function App(): JSX.Element {
  const [src, setSrc] = useState(DEFAULT_EXPR);
  const [submitted, setSubmitted] = useState(DEFAULT_EXPR);
  const [stepIx, setStepIx] = useState(0);
  const [hideNoops, setHideNoops] = useState(true);

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

  const parentMap = useMemo<Map<NodeId, Expr>>(() => {
    if (!parseResult.expr) return new Map();
    return buildParentMap(parseResult.expr);
  }, [parseResult.expr]);

  const steps = inferResult?.steps ?? [];

  const visibleIxs = useMemo(() => {
    if (!hideNoops) return steps.map((_, i) => i);
    const out: number[] = [];
    steps.forEach((s, i) => {
      if (isNoopSubstApply(s)) return;
      out.push(i);
    });
    return out;
  }, [steps, hideNoops]);

  // Snap stepIx to a visible step whenever the visibility set changes.
  useEffect(() => {
    if (visibleIxs.length === 0) return;
    if (visibleIxs.includes(stepIx)) return;
    // pick the nearest visible step to the current position
    let best = visibleIxs[0]!;
    let bestDist = Math.abs(best - stepIx);
    for (const i of visibleIxs) {
      const d = Math.abs(i - stepIx);
      if (d < bestDist) {
        best = i;
        bestDist = d;
      }
    }
    setStepIx(best);
  }, [visibleIxs, stepIx]);

  const currentStep = steps[stepIx];
  const focusId = currentStep?.nodeId;
  const visiblePos = visibleIxs.indexOf(stepIx);

  const liveVars = useMemo(() => {
    if (!currentStep) return new Set<TVarName>();
    return computeLiveVars(currentStep);
  }, [currentStep]);
  const freeVars = useMemo(() => {
    if (!currentStep) return [] as TVarName[];
    const result: TVarName[] = [];
    for (const v of currentStep.introducedVars) {
      if (!currentStep.subst.has(v)) result.push(v);
    }
    result.sort(naturalVarCompare);
    return result;
  }, [currentStep]);

  const goNext = () => {
    const idx = visibleIxs.findIndex((i) => i > stepIx);
    if (idx >= 0) setStepIx(visibleIxs[idx]!);
  };
  const goPrev = () => {
    let target = -1;
    for (const i of visibleIxs) {
      if (i < stepIx) target = i;
      else break;
    }
    if (target >= 0) setStepIx(target);
  };
  const goFirst = () => visibleIxs[0] !== undefined && setStepIx(visibleIxs[0]);
  const goLast = () => {
    const last = visibleIxs[visibleIxs.length - 1];
    if (last !== undefined) setStepIx(last);
  };

  const unifyDetail =
    currentStep &&
    (currentStep.kind === "unify-enter" || currentStep.kind === "unify-fail") &&
    currentStep.detail &&
    "left" in currentStep.detail
      ? currentStep.detail
      : undefined;
  const lookupName =
    currentStep &&
    currentStep.kind === "lookup" &&
    currentStep.detail &&
    "name" in currentStep.detail
      ? currentStep.detail.name
      : undefined;

  useEffect(() => {
    setStepIx(0);
  }, [submitted]);

  useEffect(() => {
    function onKey(ev: KeyboardEvent) {
      if (ev.target instanceof HTMLInputElement || ev.target instanceof HTMLTextAreaElement) return;
      if (ev.key === "ArrowRight" || ev.key === "j" || ev.key === "n") goNext();
      else if (ev.key === "ArrowLeft" || ev.key === "k" || ev.key === "p") goPrev();
      else if (ev.key === "Home" || ev.key === "g") goFirst();
      else if (ev.key === "End" || ev.key === "G") goLast();
    }
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [visibleIxs, stepIx]);

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
                  paramTypes={currentStep.paramTypes}
                  bindingSchemes={currentStep.bindingSchemes}
                  lamBodyTypes={currentStep.lamBodyTypes}
                  varSchemes={currentStep.varSchemes}
                  focusId={focusId}
                />
              )}
            </div>
          </div>
          <div className="panel" style={{ flex: 1 }}>
            <div className="panel-header panel-header-row">
              <span>Step log · click a row to jump</span>
              <label className="panel-header-toggle">
                <input
                  type="checkbox"
                  checked={hideNoops}
                  onChange={(e) => setHideNoops(e.target.checked)}
                />
                hide no-op σ
              </label>
            </div>
            <div className="panel-body" style={{ padding: 0 }}>
              <StepLog
                steps={steps}
                visibleIxs={visibleIxs}
                current={stepIx}
                rootExpr={parseResult.expr}
                parentMap={parentMap}
                onSelect={setStepIx}
              />
            </div>
          </div>
        </div>

        <div className="col">
          <div className="panel" style={{ flex: 1 }}>
            <div className="panel-header">Environment</div>
            <div className="panel-body">
              {currentStep && <EnvPanel env={currentStep.env} highlight={lookupName} />}
            </div>
          </div>
          <div className="panel" style={{ flex: 1 }}>
            <div className="panel-header panel-header-row">
              <span>Substitution</span>
              {freeVars.length > 0 && (
                <span className="panel-header-meta">
                  free: {freeVars.join(", ")}
                </span>
              )}
            </div>
            <div className="panel-body">
              {currentStep && (
                <SubstPanel subst={currentStep.subst} liveVars={liveVars} />
              )}
            </div>
          </div>
          <div className="panel" style={{ flex: 1.4 }}>
            <div className="panel-header">Current step</div>
            <div className="panel-body">
              {currentStep ? (
                <div>
                  <div style={{ color: "var(--accent-2)", marginBottom: 6 }}>{currentStep.kind}</div>
                  <div>{currentStep.message}</div>
                  {currentStep.kind === "infer-enter" && parseResult.expr && (
                    <div className="expr-focus" style={{ marginTop: 10 }}>
                      <ExprFocusView expr={parseResult.expr} focusId={focusId} />
                    </div>
                  )}
                  {unifyDetail && (
                    <div style={{ marginTop: 10 }}>
                      <UnifyDisplay left={unifyDetail.left} right={unifyDetail.right} />
                    </div>
                  )}
                  <StepExplanation step={currentStep} />
                </div>
              ) : (
                <div className="empty">no steps</div>
              )}
            </div>
          </div>
        </div>
      </div>

      <div className="bottombar">
        <button disabled={visiblePos <= 0} onClick={goFirst}>
          ⏮
        </button>
        <button disabled={visiblePos <= 0} onClick={goPrev}>
          ◀ prev
        </button>
        <span className="step-position">
          {visibleIxs.length === 0
            ? "0 / 0"
            : `${visiblePos + 1} / ${visibleIxs.length}`}
          {hideNoops && visibleIxs.length < steps.length && (
            <span style={{ color: "var(--muted)", marginLeft: 6 }}>
              ({steps.length - visibleIxs.length} hidden)
            </span>
          )}
        </span>
        <button
          disabled={visiblePos < 0 || visiblePos >= visibleIxs.length - 1}
          onClick={goNext}
        >
          next ▶
        </button>
        <button
          disabled={visiblePos < 0 || visiblePos >= visibleIxs.length - 1}
          onClick={goLast}
        >
          ⏭
        </button>
        <span className="keyhints">←/→ or j/k step · g/G start/end</span>
      </div>
    </div>
  );
}
