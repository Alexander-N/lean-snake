# Lean Snake

A canvas implementation of Snake using [Lasm](https://github.com/Millillion/lasm).
Use the arrow keys to steer, collect food to grow, and avoid the snake's body.
The board wraps at its edges. Press Enter after winning or losing to restart.

`Snake.lean` contains the game state and transition logic; `Main.lean` handles
input, animation, and rendering.

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

See the [vericoding skill](./.agents/skills/vericoding/SKILL.md) for the
verification-driven development process.
