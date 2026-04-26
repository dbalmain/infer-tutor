import { describe, expect, test } from "bun:test";
import { applySubstType, parse, showType } from "@infer-tutor/lang";
import { defaultEnv, inferW } from "../src";

function inferType(src: string): string {
  const r = inferW(defaultEnv(), parse(src));
  if (r.error) throw new Error(r.error);
  return showType(applySubstType(r.subst, r.type));
}

describe("Algorithm W", () => {
  test("integer literal", () => {
    expect(inferType("42")).toBe("Int");
  });
  test("boolean literal", () => {
    expect(inferType("True")).toBe("Bool");
  });
  test("identity", () => {
    // result type uses fresh names; just check it's a -> a-shaped
    const t = inferType("\\x -> x");
    expect(t).toMatch(/^(t\d+) -> \1$/);
  });
  test("add 1 2", () => {
    expect(inferType("add 1 2")).toBe("Int");
  });
  test("partial application", () => {
    expect(inferType("add 1")).toBe("Int -> Int");
  });
  test("let polymorphism", () => {
    // let id = \x -> x in id id  — should type check
    expect(inferType("let id = \\x -> x in id id")).toMatch(/^(t\d+) -> \1$/);
  });
  test("if branches must match", () => {
    expect(inferType("if True then 1 else 2")).toBe("Int");
  });
  test("type error: condition not bool", () => {
    const r = inferW(defaultEnv(), parse("if 1 then 1 else 2"));
    expect(r.error).toBeDefined();
  });
  test("type error: branches disagree", () => {
    const r = inferW(defaultEnv(), parse("if True then 1 else False"));
    expect(r.error).toBeDefined();
  });
  test("occurs check: self-application", () => {
    const r = inferW(defaultEnv(), parse("\\x -> x x"));
    expect(r.error).toMatch(/occurs/);
  });
  test("steps are emitted", () => {
    const r = inferW(defaultEnv(), parse("add 1 2"));
    expect(r.steps.length).toBeGreaterThan(5);
    expect(r.steps[r.steps.length - 1]!.kind).toBe("done");
  });
});
