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

/-!
Coordinates are expressed in grid cells, not pixels. The rendering layer
determines how many pixels each cell occupies.
-/
structure Position where
  x : Nat
  y : Nat
  deriving DecidableEq

/-!
The snake's position is the position of its head. Its remaining body
positions follow in `segments`.
-/
structure Snake where
  position : Position
  segments : List Position

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
  food : Position
  direction : Direction

structure PlayArea where
  leftEdge : Nat
  rightEdge : Nat
  topEdge : Nat
  bottomEdge : Nat

abbrev Step := Option PlayerInput → GameState → GameState

/-
## Requirements

Add new ones at the bottom.
-/

inductive Reachable (step : Step) (initialState : GameState) : GameState → Prop where
  | initial : Reachable step initialState initialState
  | next {state : GameState} (input : Option PlayerInput)
      (reachable : Reachable step initialState state) :
      Reachable step initialState (step input state)


/-!
### Requirement: Moving in the current direction
On each game step, the snake moves in its current direction unless it is at
the edge it is moving toward.

Example:
- A snake heading left moves left on the next step.
-/
def movesInDirection (direction : Direction) (beforeState afterState : GameState) : Prop :=
  let before := beforeState.snake.position
  let after := afterState.snake.position
  match direction with
  | .left => after.x < before.x
  | .up => after.y < before.y
  | .right => before.x < after.x
  | .down => before.y < after.y

def isAtEdge (direction : Direction) (area : PlayArea) (state : GameState) : Prop :=
  let position := state.snake.position
  match direction with
  | .left => position.x = area.leftEdge
  | .up => position.y = area.topEdge
  | .right => position.x = area.rightEdge
  | .down => position.y = area.bottomEdge

def movesInDirectionIfNotAtEdge(step : Step) (area : PlayArea) : Prop :=
  ∀ input state,
    let nextState := step input state
    let direction := nextState.direction
    ¬ isAtEdge direction area state →
      movesInDirection direction state nextState



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
    let before := state.direction
    let after := (step input state).direction
    let requestedDirection :=
      match input with
      | none => before
      | some .keyLeft => .left
      | some .keyUp => .up
      | some .keyRight => .right
      | some .keyDown => .down
    after =
      if requestedDirection = oppositeDirection before then
        before
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
    let direction := nextState.direction
    let before := state.snake.position
    let after := nextState.snake.position
    isAtEdge direction area state →
      match direction with
    | .left =>
        after.x = area.rightEdge ∧
          after.y = before.y
    | .up =>
        after.y = area.bottomEdge ∧
          after.x = before.x
    | .right =>
        after.x = area.leftEdge ∧
          after.y = before.y
    | .down =>
        after.y = area.topEdge ∧
          after.x = before.x

/-!
### Requirement: Food is in the play area
In any game state, there is food within the play area.
-/
def foodIsInPlayArea (state : GameState) (area : PlayArea) : Prop :=
  let food := state.food
  area.leftEdge ≤ food.x ∧
    food.x ≤ area.rightEdge ∧
    area.topEdge ≤ food.y ∧
    food.y ≤ area.bottomEdge

/-!
### Requirement: Food moves when eaten
If the snake is at the food's position, then the food moves to a new position.
-/
def foodIsEaten (before after : GameState) : Prop :=
  after.snake.position = before.food

def foodMovesWhenEaten (step : Step) : Prop :=
  ∀ input state,
    let nextState := step input state
    foodIsEaten state nextState →
      nextState.food ≠ state.food

/-!
### Requirement: Food is never the same position as the snake
-/
def foodIsNotOnSnake (state : GameState) : Prop :=
  state.food ≠ state.snake.position ∧
    state.food ∉ state.snake.segments

/-!
### Requirement: The snake grows when it eats food
When the snake is at the food's position, the snake grows by one segment.
-/
def snakeGrowsWhenEating (step : Step) : Prop :=
  ∀ input state,
    let nextState := step input state
    foodIsEaten state nextState →
      nextState.snake.segments.length = state.snake.segments.length + 1

/-!
### Requirement: The snake dies when it collides with itself
When the snake's head is at the same position as one of its segments, the game ends.
-/
def snakeCollides (before after : GameState) : Prop :=
  after.snake.position ∈ before.snake.segments

def stepDoesNotChangeOnSelfCollision (step : Step) : Prop :=
  ∀ input state,
    let nextState := step input state
    snakeCollides state nextState →
      nextState = state

/-!
### Requirement: The snake is connected
The snakes head and its segments must be connected. Each segment must be adjacent to the previous segment.
-/
def positionsAreHorizontallyAdjacent (left right : Position) : Prop :=
  left.y = right.y ∧
    (left.x + 1 = right.x ∨ right.x + 1 = left.x)

def positionsAreVerticallyAdjacent (left right : Position) : Prop :=
  left.x = right.x ∧
    (left.y + 1 = right.y ∨ right.y + 1 = left.y)

def positionsAreAdjacent (left right : Position) : Prop :=
  positionsAreHorizontallyAdjacent left right ∨
    positionsAreVerticallyAdjacent left right

def segmentsAreConnected (previous : Position) : List Position → Prop
  | [] => True
  | segment :: remaining =>
      positionsAreAdjacent previous segment ∧
        segmentsAreConnected segment remaining

def snakeIsConnected (snake : Snake) : Prop :=
  segmentsAreConnected snake.position snake.segments

/-!
### All game requirements
-/
def gameStateInvariant (area : PlayArea) (state : GameState) : Prop :=
  foodIsInPlayArea state area ∧
    foodIsNotOnSnake state ∧
    snakeIsConnected state.snake

def gameStepRequirements (step : Step) (area : PlayArea) : Prop :=
  movesInDirectionIfNotAtEdge step area ∧
    arrowInputSetsDirection step ∧
    wrapsAtEdge step area ∧
    foodMovesWhenEaten step ∧
    snakeGrowsWhenEating step ∧
    stepDoesNotChangeOnSelfCollision step

def gameRequirements (initialState : GameState) (step : Step)
    (area : PlayArea) : Prop :=
  gameStateInvariant area initialState ∧
    (∀ input state, gameStateInvariant area state →
      gameStateInvariant area (step input state)) ∧
    gameStepRequirements step area

def alwaysOnReachableStates (step : Step) (initialState : GameState)
    (property : GameState → Prop) : Prop :=
  ∀ state, Reachable step initialState state → property state


end Spec
