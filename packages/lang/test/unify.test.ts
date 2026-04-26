import { describe, expect, test } from "bun:test";
import {
  applySubstType,
  emptySubst,
  showSubst,
  showType,
  tBool,
  tFun,
  tInt,
  tVar,
  unify,
  UnifyError,
} from "../src";

describe("unify", () => {
  test("identical concrete types", () => {
    const s = unify(tInt, tInt);
    expect(s.size).toBe(0);
  });
  test("var with concrete", () => {
    const s = unify(tVar("a"), tInt);
    expect(showType(applySubstType(s, tVar("a")))).toBe("Int");
  });
  test("two vars", () => {
    const s = unify(tVar("a"), tVar("b"));
    expect(showSubst(s)).toMatch(/(a ↦ b|b ↦ a)/);
  });
  test("function types", () => {
    const s = unify(tFun(tVar("a"), tVar("b")), tFun(tInt, tBool));
    expect(showType(applySubstType(s, tVar("a")))).toBe("Int");
    expect(showType(applySubstType(s, tVar("b")))).toBe("Bool");
  });
  test("constructor mismatch", () => {
    expect(() => unify(tInt, tBool)).toThrow(UnifyError);
  });
  test("occurs check", () => {
    expect(() => unify(tVar("a"), tFun(tVar("a"), tInt))).toThrow(/occurs/);
  });
  test("composition is correct", () => {
    let s = emptySubst();
    s = unify(tVar("a"), tFun(tVar("b"), tVar("c")), s);
    s = unify(tVar("b"), tInt, s);
    s = unify(tVar("c"), tBool, s);
    expect(showType(applySubstType(s, tVar("a")))).toBe("Int -> Bool");
  });
});
