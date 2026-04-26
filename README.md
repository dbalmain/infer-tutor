# infer-tutor

An interactive web app for learning Hindley-Milner type inference. You watch the algorithm step by step, predict what comes next, and the app reveals the answer.

Companion to [HindleyMilnerByExample.md](https://github.com/dbalmain/clex-project) — the paper-and-pencil tutorial; this is the interactive version.

## Status

Phase A (v0.1): free-input mode, Algorithm W only.

Planned: quiz mode, curated tour, Algorithms W' / M / BD.

## Develop

```sh
bun install
bun run dev      # vite dev server
bun test         # algorithm + lang unit tests
```

## Layout

- `packages/lang` — surface syntax, types, substitution, unification
- `packages/algorithms` — one module per algorithm (currently W)
- `packages/web` — React UI

## License

MIT
