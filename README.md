# infer-tutor

An interactive web app for learning type inference. You watch the algorithm step by step, predict what comes next, and the app reveals the answer.

This repo contains the interactive tutor that accompanies the written tutorial.

## Status

Current: free-input mode with Algorithms W, W', M, and bidirectional checking/synthesis.

Planned: quiz mode, curated tour, richer trace explanations, and more examples.

## Develop

```sh
bun install
bun run dev      # vite dev server
bun test         # algorithm + lang unit tests
```

## Layout

- `packages/lang` — surface syntax, types, substitution, unification
- `packages/algorithms` — one module per algorithm
- `packages/web` — React UI

## License

MIT
