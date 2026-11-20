/-!
# Specification

Describe the behavior independently of its implementation.

-/

namespace Spec

/-!
## Domain Concepts


Helper functions for the propositions are not part of the Domain model and have
to go after `Requirements` where they are used.
-/

structure Snake where
  x : Int
  y : Int

inductive Direction where
  | left
  | up
  | right
  | down
  deriving DecidableEq

inductive PlayerInput where
  | keyLeft
  | keyUp
  | keyRight
  | keyDown
  deriving DecidableEq

structure GameState where
  snake : Snake
  direction : Direction

structure PlayArea where
  leftEdge : Int
  rightEdge : Int
  topEdge : Int
  bottomEdge : Int

abbrev Step := Option PlayerInput → GameState → GameState

/-
## Requirements
-/


/-!
### Requirement: Moving in the current direction
On each game step, the snake moves in its current direction unless it is at
the edge it is moving toward.

Example:
- A snake heading left moves left on the next step.
-/
def movesInDirection (direction : Direction) (before after : GameState) : Prop :=
  match direction with
  | .left => after.snake.x < before.snake.x
  | .up => after.snake.y < before.snake.y
  | .right => before.snake.x < after.snake.x
  | .down => before.snake.y < after.snake.y

def isAtEdge (direction : Direction) (area : PlayArea) (state : GameState) : Prop :=
  match direction with
  | .left => state.snake.x = area.leftEdge
  | .up => state.snake.y = area.topEdge
  | .right => state.snake.x = area.rightEdge
  | .down => state.snake.y = area.bottomEdge

def movesInDirectionIfNotAtEdge(step : Step) (area : PlayArea) : Prop :=
  ∀ input state,
    let nextState := step input state
    ¬ isAtEdge nextState.direction area state →
      movesInDirection nextState.direction state nextState



/-!
### Requirement: Steering the snake with arrow keys
An arrow-key input sets the direction to the corresponding direction, unless
that direction is opposite the snake's current direction.

Example:
- The left arrow sets the direction to left.
- A snake heading left remains heading left when the right arrow is pressed.
- No user input leaves the direction unchanged.
-/
def oppositeDirection (direction : Direction) : Direction :=
  match direction with
  | .left => .right
  | .up => .down
  | .right => .left
  | .down => .up

def arrowInputSetsDirection (step : Step) : Prop :=
  ∀ (input : Option PlayerInput) (state : GameState),
    let nextState := step input state
    let requestedDirection :=
      match input with
      | none => state.direction
      | some .keyLeft => .left
      | some .keyUp => .up
      | some .keyRight => .right
      | some .keyDown => .down
    nextState.direction =
      if requestedDirection = oppositeDirection state.direction then
        state.direction
      else
        requestedDirection

/-!
### Requirement: Wrapping at the play-area edges
On a game step taken while the snake is at the edge it is heading toward, its
position reappears at the opposite edge, preserving its other coordinate.

Example:
- Moving left from the left edge wraps to the right edge.
-/
def wrapsAtEdge (step : Step) (area : PlayArea) : Prop :=
  ∀ (input : Option PlayerInput) (state : GameState),
    let nextState := step input state
    isAtEdge nextState.direction area state →
      match nextState.direction with
    | .left =>
        nextState.snake.x = area.rightEdge ∧
          nextState.snake.y = state.snake.y
    | .up =>
        nextState.snake.y = area.bottomEdge ∧
          nextState.snake.x = state.snake.x
    | .right =>
        nextState.snake.x = area.leftEdge ∧
          nextState.snake.y = state.snake.y
    | .down =>
        nextState.snake.y = area.topEdge ∧
          nextState.snake.x = state.snake.x


end Spec
