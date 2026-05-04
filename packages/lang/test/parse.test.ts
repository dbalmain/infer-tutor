import { describe, expect, test } from "bun:test";
import { parse, showExpr } from "../src";

describe("parser", () => {
  test("integer literal", () => {
    expect(showExpr(parse("42"))).toBe("42");
  });
  test("application is left-associative", () => {
    expect(showExpr(parse("f x y"))).toBe("((f x) y)");
  });
  test("lambda", () => {
    expect(showExpr(parse("\\x -> x"))).toBe("\\x -> x");
  });
  test("annotated lambda parameter", () => {
    expect(showExpr(parse("\\(x : Int) -> x"))).toBe("\\(x : Int) -> x");
  });
  test("function type annotation is right-associative", () => {
    expect(showExpr(parse("\\(f : Int -> Int -> Int) -> f"))).toBe(
      "\\(f : Int -> Int -> Int) -> f",
    );
  });
  test("multi-arg lambda desugars", () => {
    expect(showExpr(parse("\\x y -> x"))).toBe("\\x -> \\y -> x");
  });
  test("let with sugar", () => {
    expect(showExpr(parse("let id x = x in id"))).toBe("let id = \\x -> x in id");
  });
  test("if", () => {
    expect(showExpr(parse("if True then 1 else 2"))).toBe("if True then 1 else 2");
  });
  test("parens", () => {
    expect(showExpr(parse("f (g x)"))).toBe("(f (g x))");
  });
});
