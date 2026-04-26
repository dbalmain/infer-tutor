import { type Type, showType } from "@infer-tutor/lang";

// Curated palette — distinct hues, readable on dark background.
const PALETTE = [
  "#2d4f8a", // blue
  "#8a5a2d", // amber
  "#3d7a3d", // green
  "#7a3d5e", // magenta
  "#52527a", // indigo
  "#7a4a4a", // rust
  "#2d6f6f", // teal
];

type Props = { left: Type; right: Type };

// Pair structurally: when both sides are TFun we descend; otherwise the
// position is a leaf pair (a unification subgoal) that gets its own color.
// Rendering each side with its own counter works because the structural
// decomposition is symmetric in both arguments — leaf order matches.
export function UnifyDisplay({ left, right }: Props): JSX.Element {
  return (
    <div style={{ display: "flex", flexDirection: "column", gap: 4 }}>
      <div>
        <span style={{ color: "var(--muted)", marginRight: 6 }}>unify</span>
        {renderSide(left, right, { i: 0 }, false)}
      </div>
      <div>
        <span style={{ color: "var(--muted)", marginRight: 6 }}>with </span>
        {renderSide(right, left, { i: 0 }, false)}
      </div>
    </div>
  );
}

function renderSide(
  self: Type,
  other: Type,
  counter: { i: number },
  parenIfFun: boolean,
): JSX.Element {
  if (self.kind === "TFun" && other.kind === "TFun") {
    const inner = (
      <>
        {renderSide(self.from, other.from, counter, true)}
        <span style={{ color: "var(--muted)" }}> -&gt; </span>
        {renderSide(self.to, other.to, counter, false)}
      </>
    );
    return parenIfFun ? (
      <>
        <span style={{ color: "var(--muted)" }}>(</span>
        {inner}
        <span style={{ color: "var(--muted)" }}>)</span>
      </>
    ) : (
      inner
    );
  }
  const color = PALETTE[counter.i++ % PALETTE.length]!;
  return (
    <span
      style={{
        background: color,
        padding: "1px 6px",
        borderRadius: 3,
        margin: "0 1px",
      }}
    >
      {showType(self, false)}
    </span>
  );
}
