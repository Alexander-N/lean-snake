# Lean Snake verification summary

## Goal

Check whether the concrete implementation in `Snake.lean` satisfies the formal requirements in `Spec.lean`, and prove those requirements in `Proofs.lean`.

## What was inspected

- `Spec.lean`: 365 lines of domain definitions and named behavioral requirements.
- `Snake.lean`: concrete game state transitions, food placement, collision handling, and win/loss behavior.
- `Main.lean`: browser input, animation, and rendering.
- `Proofs.lean`: Lean proofs connecting the concrete transition function to the specification.

The runtime uses `Snake.step` directly, so the verified transition function and the gameplay implementation are the same function; no separate runtime model currently needs to be connected to the proofs.

## First verification result

The first proof pass found a genuine implementation/spec mismatch in the food-placement rule `foodChangesBothCoordinatesWhenPossible`.

A collision could also be an eating step. In that case, the old collision branch selected a replacement food position that was merely different from the previous food position. It did not ensure that both the `x` and `y` coordinates changed when such a free position existed.

### Counterexample shape

- Snake direction: left
- Head: `(1, 1)`
- Body: `[(0, 1)]`
- Food: `(0, 1)`
- Input: no key

The next position was `(0, 1)`, so the move simultaneously collided with the body and reached the food. A free in-area position with both coordinates different existed, but the old selection logic could produce a replacement such as `(0, 0)`, violating the required `x ≠ oldFood.x` condition.

## Corrective work

The collision/eating path was updated to use the same snake-aware food selection strategy as a normal eating step:

1. Prefer an unoccupied position whose `x` and `y` both differ from the old food coordinates.
2. Fall back to another unoccupied position when no two-coordinate-different choice exists.
3. Preserve the existing win/full-board and loss behavior.

The collision path is also written to use a fallback `differentFoodPosition` helper when no snake-aware position is available.

## Proof work

`Proofs.lean` was expanded to prove and support properties around:

- Arrow-key steering and reversal rejection.
- Movement in the current direction away from edges.
- Wrapped movement at all four board edges.
- Food remaining in the play area.
- Membership of generated board positions.
- Food-position availability and full-board equivalence.
- Food movement when eaten.
- Initial state invariants and invariant induction over reachable states.

The existing `gameStateInvariant_holdsForReachableStates` and `gameRequirements_implyInvariantForReachableStates` lemmas establish that a proved initial invariant plus one-step preservation applies to every reachable state.

At the time of this summary, work is still in progress to assemble and type-check the complete theorem:

```lean
theorem gameRequirements :
  Spec.gameRequirements Snake.initialState Snake.step Snake.playArea
```

A successful type-check of that theorem is the final proof target; merely compiling individual files is not sufficient.

## Validation commands and limitations

`lake env lean Proofs.lean` is being used to type-check the specification, implementation, and proofs without invoking the browser executable's C linking stage.

A full `lake build` currently reaches the C compilation stage but fails because `lean/lean.h` is absent from the configured include path. This is a toolchain/build-environment problem rather than a Lean proof error.

## Current conclusion

The specification and implementation did **not** initially match in the simultaneous collision-and-eating case. That mismatch has been identified and an implementation correction is being proved. Final conformance has not yet been claimed because the aggregate `gameRequirements` theorem is still being completed and verified.

## Working-tree status

This verification began with pre-existing uncommitted changes in several project files. The current work also touches proof and implementation files, but no commit was created.
