export type Token =
  | { kind: "ident"; value: string; pos: number }
  | { kind: "int"; value: number; pos: number }
  | { kind: "kw"; value: Keyword; pos: number }
  | { kind: "sym"; value: Symbol_; pos: number }
  | { kind: "eof"; pos: number };

export type Keyword = "let" | "in" | "if" | "then" | "else" | "True" | "False";
export type Symbol_ = "(" | ")" | "\\" | "->" | "=" | ":";

const KEYWORDS = new Set<string>(["let", "in", "if", "then", "else", "True", "False"]);

export class LexError extends Error {
  constructor(message: string, public pos: number) {
    super(`${message} (at ${pos})`);
  }
}

export function lex(src: string): Token[] {
  const out: Token[] = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i]!;
    if (c === " " || c === "\t" || c === "\n" || c === "\r") {
      i++;
      continue;
    }
    if (c === "(" || c === ")" || c === "\\" || c === "=" || c === ":") {
      out.push({ kind: "sym", value: c as Symbol_, pos: i });
      i++;
      continue;
    }
    if (c === "-" && src[i + 1] === ">") {
      out.push({ kind: "sym", value: "->", pos: i });
      i += 2;
      continue;
    }
    if (isDigit(c)) {
      let j = i;
      while (j < src.length && isDigit(src[j]!)) j++;
      out.push({ kind: "int", value: Number(src.slice(i, j)), pos: i });
      i = j;
      continue;
    }
    if (isIdentStart(c)) {
      let j = i;
      while (j < src.length && isIdentPart(src[j]!)) j++;
      const word = src.slice(i, j);
      if (KEYWORDS.has(word)) {
        out.push({ kind: "kw", value: word as Keyword, pos: i });
      } else {
        out.push({ kind: "ident", value: word, pos: i });
      }
      i = j;
      continue;
    }
    throw new LexError(`unexpected character ${JSON.stringify(c)}`, i);
  }
  out.push({ kind: "eof", pos: src.length });
  return out;
}

function isDigit(c: string): boolean {
  return c >= "0" && c <= "9";
}

function isIdentStart(c: string): boolean {
  return (c >= "a" && c <= "z") || (c >= "A" && c <= "Z") || c === "_";
}

function isIdentPart(c: string): boolean {
  return isIdentStart(c) || isDigit(c) || c === "'";
}
