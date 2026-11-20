# Lean Snake

A small canvas game starter using [Lasm](https://github.com/Millillion/lasm).
`Snake.lean` holds the game scene and rectangle data; `Main.lean` creates the
browser canvas and renders that scene.

## Run

Use Node.js 24 or newer, then:

```sh
npm install
npm run dev
```

For a production build:

```sh
npm run build
```

The browser build is written to `dist/`.

## Development workflow

See [AGENTS.md](./AGENTS.md) for the verification-driven development process.
