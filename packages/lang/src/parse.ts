import type { Expr, NodeId } from "./ast";
import { type Token, lex } from "./lex";
import { tBool, tFun, tInt, type Type } from "./types";

export class ParseError extends Error {
  constructor(message: string, public pos: number) {
    super(`${message} (at ${pos})`);
  }
}

class Parser {
  private i = 0;
  private nextId: NodeId = 0;
  constructor(private tokens: Token[]) {}

  private peek(): Token {
    return this.tokens[this.i]!;
  }
  private eat(): Token {
    return this.tokens[this.i++]!;
  }
  private expectSym(s: string): Token {
    const t = this.peek();
    if (t.kind !== "sym" || t.value !== s) throw new ParseError(`expected ${JSON.stringify(s)}`, t.pos);
    return this.eat();
  }
  private expectKw(k: string): Token {
    const t = this.peek();
    if (t.kind !== "kw" || t.value !== k) throw new ParseError(`expected '${k}'`, t.pos);
    return this.eat();
  }
  private id(): NodeId {
    return this.nextId++;
  }

  parse(): Expr {
    const e = this.parseExpr();
    const t = this.peek();
    if (t.kind !== "eof") throw new ParseError(`unexpected ${describe(t)}`, t.pos);
    return e;
  }

  // Top-level: lambda | let | if | application
  private parseExpr(): Expr {
    const t = this.peek();
    if (t.kind === "sym" && t.value === "\\") return this.parseLam();
    if (t.kind === "kw" && t.value === "let") return this.parseLet();
    if (t.kind === "kw" && t.value === "if") return this.parseIf();
    return this.parseApp();
  }

  private parseLam(): Expr {
    this.expectSym("\\");
    const params: { name: string; ann?: Type }[] = [];
    while (true) {
      const t = this.peek();
      if (t.kind === "ident") {
        params.push({ name: t.value });
        this.eat();
      } else if (t.kind === "sym" && t.value === "(") {
        params.push(this.parseAnnotatedParam());
      } else break;
    }
    if (params.length === 0) throw new ParseError("expected parameter after '\\\\'", this.peek().pos);
    this.expectSym("->");
    let body = this.parseExpr();
    for (let k = params.length - 1; k >= 0; k--) {
      const param = params[k]!;
      body = { kind: "Lam", id: this.id(), param: param.name, paramAnn: param.ann, body };
    }
    return body;
  }

  private parseAnnotatedParam(): { name: string; ann?: Type } {
    this.expectSym("(");
    const name = this.peek();
    if (name.kind !== "ident") throw new ParseError("expected parameter name", name.pos);
    this.eat();
    this.expectSym(":");
    const ann = this.parseType();
    this.expectSym(")");
    return { name: name.value, ann };
  }

  private parseLet(): Expr {
    this.expectKw("let");
    const t = this.peek();
    if (t.kind !== "ident") throw new ParseError("expected identifier after 'let'", t.pos);
    const name = t.value;
    this.eat();
    // sugar: let f x y = ... in ...  desugars to let f = \x y -> ... in ...
    const params: string[] = [];
    while (true) {
      const tt = this.peek();
      if (tt.kind === "ident") {
        params.push(tt.value);
        this.eat();
      } else break;
    }
    this.expectSym("=");
    let value = this.parseExpr();
    for (let k = params.length - 1; k >= 0; k--) {
      value = { kind: "Lam", id: this.id(), param: params[k]!, body: value };
    }
    this.expectKw("in");
    const body = this.parseExpr();
    return { kind: "Let", id: this.id(), name, value, body };
  }

  private parseIf(): Expr {
    this.expectKw("if");
    const cond = this.parseExpr();
    this.expectKw("then");
    const then = this.parseExpr();
    this.expectKw("else");
    const els = this.parseExpr();
    return { kind: "If", id: this.id(), cond, then, else: els };
  }

  private parseApp(): Expr {
    let head = this.parseAtom();
    while (this.canStartAtom()) {
      const arg = this.parseAtom();
      head = { kind: "App", id: this.id(), fn: head, arg };
    }
    return head;
  }

  private canStartAtom(): boolean {
    const t = this.peek();
    return (
      t.kind === "ident" ||
      t.kind === "int" ||
      (t.kind === "sym" && t.value === "(") ||
      (t.kind === "kw" && (t.value === "True" || t.value === "False"))
    );
  }

  private parseAtom(): Expr {
    const t = this.peek();
    if (t.kind === "ident") {
      this.eat();
      return { kind: "Var", id: this.id(), name: t.value };
    }
    if (t.kind === "int") {
      this.eat();
      return { kind: "Lit", id: this.id(), lit: { kind: "Int", value: t.value } };
    }
    if (t.kind === "kw" && (t.value === "True" || t.value === "False")) {
      this.eat();
      return { kind: "Lit", id: this.id(), lit: { kind: "Bool", value: t.value === "True" } };
    }
    if (t.kind === "sym" && t.value === "(") {
      this.eat();
      const e = this.parseExpr();
      this.expectSym(")");
      return e;
    }
    throw new ParseError(`unexpected ${describe(t)}`, t.pos);
  }

  private parseType(): Type {
    const from = this.parseTypeAtom();
    const t = this.peek();
    if (t.kind === "sym" && t.value === "->") {
      this.eat();
      return tFun(from, this.parseType());
    }
    return from;
  }

  private parseTypeAtom(): Type {
    const t = this.peek();
    if (t.kind === "ident") {
      this.eat();
      if (t.value === "Int") return tInt;
      if (t.value === "Bool") return tBool;
      throw new ParseError(`unknown type ${JSON.stringify(t.value)}`, t.pos);
    }
    if (t.kind === "sym" && t.value === "(") {
      this.eat();
      const ty = this.parseType();
      this.expectSym(")");
      return ty;
    }
    throw new ParseError("expected type", t.pos);
  }
}

function describe(t: Token): string {
  switch (t.kind) {
    case "ident":
      return `identifier '${t.value}'`;
    case "int":
      return `integer ${t.value}`;
    case "kw":
      return `keyword '${t.value}'`;
    case "sym":
      return `'${t.value}'`;
    case "eof":
      return "end of input";
  }
}

export function parse(src: string): Expr {
  return new Parser(lex(src)).parse();
}
