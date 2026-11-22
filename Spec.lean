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
positions follow in `body`.
-/
structure Snake where
  position : Position
  body : List Position

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

inductive GamePhase where
  | playing
  | won
  | lost
  deriving DecidableEq

structure GameState where
  snake : Snake
  food : Position
  direction : Direction
  phase : GamePhase
  /-- A uniformly drawn natural number used to choose the next food position.
  It is drawn from `0 … n-1`, where `n` is the number of free positions after
  the snake eats. -/
  random : Nat

structure PlayArea where
  leftEdge : Nat
  rightEdge : Nat
  topEdge : Nat
  bottomEdge : Nat

/-- A game step returns its unique successor. -/
abbrev Step := Option PlayerInput → GameState → GameState

/-
## Requirements

Add new ones at the bottom.
-/

def isWithinPlayArea (area : PlayArea) (position : Position) : Prop :=
  area.leftEdge ≤ position.x ∧
    position.x ≤ area.rightEdge ∧
    area.topEdge ≤ position.y ∧
    position.y ≤ area.bottomEdge

def oppositeDirection (direction : Direction) : Direction :=
  match direction with
  | .left => .right
  | .up => .down
  | .right => .left
  | .down => .up

def snakeCollides (snake : Snake) (position : Position) : Prop :=
  position ∈ snake.body

def gameIsRunning (state : GameState) : Prop :=
  state.phase = .playing

inductive Reachable (step : Step) (initialState : GameState) : GameState → Prop where
  | initial : Reachable step initialState initialState
  | next {state : GameState} (input : Option PlayerInput)
      (reachable : Reachable step initialState state) :
      Reachable step initialState (step input state)


/-!
### Moving in the current direction
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
    gameIsRunning state →
      let nextState := step input state
      ¬ isAtEdge nextState.direction area state →
        movesInDirection nextState.direction state nextState

/-!
### Steering the snake with arrow keys
An arrow-key input sets the direction to the corresponding direction, unless
that direction is opposite the snake's current direction.

Example:
- The left arrow sets the direction to left.
- A snake heading left remains heading left when the right arrow is pressed.
- No user input leaves the direction unchanged.
-/
def arrowInputSetsDirection (step : Step) : Prop :=
  ∀ (input : Option PlayerInput) (state : GameState),
    gameIsRunning state →
      let nextState := step input state
      let before := state.direction
      let after := nextState.direction
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
### Wrapping at the play-area edges
On a game step taken while the snake is at the edge it is heading toward, its
position reappears at the opposite edge, preserving its other coordinate.

Example:
- Moving left from the left edge wraps to the right edge.
-/
def wrapsAtEdge (step : Step) (area : PlayArea) : Prop :=
  ∀ input state,
    gameIsRunning state →
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
### Food is in the play area
In any game state, there is food within the play area.
-/
def foodIsInPlayArea (state : GameState) (area : PlayArea) : Prop :=
  isWithinPlayArea area state.food


/-!
### Snake is in play area
The snake's head and body positions must be within the play area.
-/
def snakeIsInPlayArea (area : PlayArea) (snake : Snake) : Prop :=
  isWithinPlayArea area snake.position ∧
    ∀ position ∈ snake.body,
      isWithinPlayArea area position

def boardIsFull (area : PlayArea) (snake : Snake) : Prop :=
  ∀ position, isWithinPlayArea area position →
    position = snake.position ∨ position ∈ snake.body

/-!
### Food moves when eaten
If the snake is at the food's position, the food moves to a new position unless
the game is won, in which case the food stays in place.
-/
def foodIsEaten (before after : GameState) : Prop :=
  after.snake.position = before.food

def foodMovesWhenEaten (step : Step) : Prop :=
  ∀ input state,
    gameIsRunning state →
      let nextState := step input state
      foodIsEaten state nextState →
        if nextState.phase = .won then
          nextState.food = state.food
        else
          nextState.food ≠ state.food

/-!
### Food is never the same position as the snake
-/
def foodIsNotOnSnake (state : GameState) : Prop :=
  state.phase = .won ∨
    (state.food ≠ state.snake.position ∧ state.food ∉ state.snake.body)

/-!
### The snake grows when it eats food
When the snake is at the food's position, the snake grows by one segment.
-/
def snakeGrowsWhenEating (step : Step) : Prop :=
  ∀ input state,
    gameIsRunning state →
      let nextState := step input state
      foodIsEaten state nextState →
        nextState.snake.body.length = state.snake.body.length + 1

/-!
### The snake dies when it collides with itself
When the snake's head moves to the same position as one of its body positions,
the game is lost.
-/
def gameEndsOnSelfCollision (step : Step) : Prop :=
  ∀ input state,
    gameIsRunning state →
      let nextState := step input state
      snakeCollides state.snake nextState.snake.position →
        nextState.phase = .lost

/-!
### The game is won when the play area is full
After a safe active step, the game is won exactly when the snake occupies
every position in the play area. Otherwise, it remains active.
-/
def gameEndsWhenPlayAreaIsFull (step : Step) (area : PlayArea) : Prop :=
  ∀ input state,
    gameIsRunning state →
      let nextState := step input state
      ¬ snakeCollides state.snake nextState.snake.position →
        (nextState.phase = .won ↔ boardIsFull area nextState.snake)
          ∧ nextState.phase ≠ .lost

/-!
### The game has no step after it ends
The game stops after it is won or lost.
-/
def gameHasNoStepAfterEnd (step : Step) : Prop :=
  ∀ input state,
    ¬ gameIsRunning state →
      step input state = state

/-!
### The snake is connected
The snake's head and consecutive segments must be adjacent on the play area's
wrapped grid. Positions on opposite edges of the same row or column are adjacent.
-/
def positionsAreAdjacent (area : PlayArea) (left right : Position) : Prop :=
  (left.y = right.y ∧
    (left.x + 1 = right.x ∨
      right.x + 1 = left.x ∨
      (left.x = area.leftEdge ∧ right.x = area.rightEdge) ∨
      (left.x = area.rightEdge ∧ right.x = area.leftEdge))) ∨
  (left.x = right.x ∧
    (left.y + 1 = right.y ∨
      right.y + 1 = left.y ∨
      (left.y = area.topEdge ∧ right.y = area.bottomEdge) ∨
      (left.y = area.bottomEdge ∧ right.y = area.topEdge)))

def segmentsAreConnected (area : PlayArea) (previous : Position) : List Position → Prop
  | [] => True
  | segment :: remaining =>
      positionsAreAdjacent area previous segment ∧
        segmentsAreConnected area segment remaining

def snakeIsConnected (area : PlayArea) (snake : Snake) : Prop :=
  segmentsAreConnected area snake.position snake.body

/-!
### Food is placed fairly
When the snake eats food, every free position is equally likely to become the
next food position.
-/

/-- All positions of the play area. -/
def positionsInPlayArea (area : PlayArea) : List Position :=
  (List.range (area.bottomEdge - area.topEdge + 1)).flatMap fun y =>
    (List.range (area.rightEdge - area.leftEdge + 1)).map fun x =>
      { x := area.leftEdge + x, y := area.topEdge + y }

/-- A position in the play area that the snake does not occupy. -/
def isFree (area : PlayArea) (snake : Snake) (position : Position) : Prop :=
  isWithinPlayArea area position ∧
    position ≠ snake.position ∧
    position ∉ snake.body

instance (area : PlayArea) (snake : Snake) (position : Position) :
    Decidable (isFree area snake position) := by
  unfold isFree isWithinPlayArea
  infer_instance

def numberOfFreePositions (area : PlayArea) (snake : Snake) : Nat :=
  ((positionsInPlayArea area).filter fun position =>
    decide (isFree area snake position)).length

/-- Exactly one number satisfies `property`. -/
def ExactlyOne (property : Nat → Prop) : Prop :=
  ∃ number, property number ∧ ∀ other, property other → other = number

/-- The food the step would produce if the random number were `random`. -/
def nextFoodForRandom (step : Step) (input : Option PlayerInput)
    (state : GameState) (random : Nat) : Position :=
  (step input { state with random := random }).food

/-
With n free positions, the random numbers 0 to n-1 are the possible outcomes.
The environment draws one of them with equal probability. Each free position
is the new food for exactly one of these random numbers, so each is equally
likely. If no position is free the game is won and there is nothing to show.
-/
def foodIsPlacedFairly (step : Step) (area : PlayArea) : Prop :=
  ∀ input state,
    -- for any player input and any running game
    gameIsRunning state →
      -- look at the state after the step
      let nextState := step input state
      -- if the snake ate the food in this step
      foodIsEaten state nextState →
        -- then for every free position
        ∀ position, isFree area nextState.snake position →
          -- there is exactly one random number, among the possible ones,
          ExactlyOne fun random =>
            random < numberOfFreePositions area nextState.snake ∧
              -- that puts the next food at that position
              nextFoodForRandom step input state random = position


/-!
### All game requirements
-/
def gameStateInvariant (area : PlayArea) (state : GameState) : Prop :=
  foodIsInPlayArea state area ∧
    foodIsNotOnSnake state ∧
    snakeIsInPlayArea area state.snake ∧
    (state.phase = .won → boardIsFull area state.snake) ∧
    snakeIsConnected area state.snake

def gameStepRequirements (step : Step) (area : PlayArea) : Prop :=
  movesInDirectionIfNotAtEdge step area ∧
    arrowInputSetsDirection step ∧
    wrapsAtEdge step area ∧
    foodMovesWhenEaten step ∧
    foodIsPlacedFairly step area ∧
    snakeGrowsWhenEating step ∧
    gameEndsOnSelfCollision step ∧
    gameEndsWhenPlayAreaIsFull step area ∧
    gameHasNoStepAfterEnd step

def gameRequirements (initialState : GameState) (step : Step)
    (area : PlayArea) : Prop :=
  gameStateInvariant area initialState ∧
    (∀ input state,
      gameStateInvariant area state →
        gameStateInvariant area (step input state)) ∧
    gameStepRequirements step area

def alwaysOnReachableStates (step : Step) (initialState : GameState)
    (property : GameState → Prop) : Prop :=
  ∀ state, Reachable step initialState state → property state


end Spec
