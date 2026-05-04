import { describe, expect, test } from "bun:test";
import { applySubstType, parse, showType } from "@infer-tutor/lang";
import { defaultEnv, inferBD } from "../src";

function inferType(src: string): string {
  const r = inferBD(defaultEnv(), parse(src));
  if (r.error) throw new Error(r.error);
  return showType(applySubstType(r.subst, r.type));
}

describe("Bidirectional", () => {
  test("annotated lambda synthesizes", () => {
    expect(inferType("\\(x : Int) -> x")).toBe("Int -> Int");
  });

  test("annotated let-bound identity can be applied", () => {
    expect(inferType("let id = \\(x : Int) -> x in id 3")).toBe("Int");
  });

  test("bare lambda cannot synthesize at root", () => {
    const r = inferBD(defaultEnv(), parse("\\x -> x"));
    expect(r.error).toContain("parameter annotation");
  });

  test("application argument is checked against synthesized function input", () => {
    const r = inferBD(defaultEnv(), parse("(\\(x : Int) -> x) True"));
    expect(r.error).toBeDefined();
  });

  test("child synth-exit updates enclosing lambda body slot", () => {
    const expr = parse("\\(x : Int) -> x");
    if (expr.kind !== "Lam") throw new Error("expected lambda");
    const r = inferBD(defaultEnv(), expr);
    if (r.error) throw new Error(r.error);

    const bodyExit = r.steps.find((s) => s.kind === "synth-exit" && s.nodeId === expr.body.id);
    expect(bodyExit).toBeDefined();
    expect(showType(bodyExit!.lamBodyTypes.get(expr.id)!)).toBe("Int");
  });

  test("function synth-exit updates enclosing application result slot", () => {
    const expr = parse("let id = \\(x : Int) -> x in id 3");
    if (expr.kind !== "Let" || expr.body.kind !== "App") throw new Error("expected let/app");
    const r = inferBD(defaultEnv(), expr);
    if (r.error) throw new Error(r.error);

    const fnExit = r.steps.find((s) => s.kind === "synth-exit" && s.nodeId === expr.body.fn.id);
    expect(fnExit).toBeDefined();
    expect(showType(fnExit!.nodeTypes.get(expr.body.id)!)).toBe("Int");
  });
});
