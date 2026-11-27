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

inductive Direction where
  | left
  | up
  | right
  | down
  deriving DecidableEq

/-!
The snake's head and remaining body positions are grid cells, and its
direction is its current heading.
-/
structure Snake where
  head : Position
  body : List Position
  direction : Direction

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
  phase : GamePhase

structure PlayArea where
  leftEdge : Nat
  rightEdge : Nat
  topEdge : Nat
  bottomEdge : Nat

abbrev MoveSnake := Option PlayerInput → GameState → Snake
abbrev UpdateGame := GameState → Snake → Option Position → GameState

/-
## Requirements

Add new ones at the bottom.
-/

/-!
### Moving in the current direction
On each game step, the snake moves in its current direction unless it is at
the edge it is moving toward.

Example:
- A snake heading left moves left on the next step.
-/
def movesInDirection (direction : Direction) (beforeState afterState : GameState) : Prop :=
  let before := beforeState.snake.head
  let after := afterState.snake.head
  match direction with
  | .left => after.x + 1 = before.x ∧ after.y = before.y
  | .up => after.y + 1 = before.y ∧ after.x = before.x
  | .right => after.x = before.x + 1 ∧ after.y = before.y
  | .down => after.y = before.y + 1 ∧ after.x = before.x

def isAtEdge (direction : Direction) (area : PlayArea) (state : GameState) : Prop :=
  let position := state.snake.head
  match direction with
  | .left => position.x = area.leftEdge
  | .up => position.y = area.topEdge
  | .right => position.x = area.rightEdge
  | .down => position.y = area.bottomEdge

def gameIsRunning (state : GameState) : Prop :=
  state.phase = .playing

def movesInDirectionIfNotAtEdge (area : PlayArea) (state nextState : GameState) : Prop :=
  ¬ isAtEdge nextState.snake.direction area state →
    movesInDirection nextState.snake.direction state nextState

/-!
### Steering the snake with arrow keys
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

def arrowInputSetsDirection (input : Option PlayerInput) (state nextState : GameState) : Prop :=
  let before := state.snake.direction
  let requestedDirection :=
    match input with
    | none => before
    | some .keyLeft => .left
    | some .keyUp => .up
    | some .keyRight => .right
    | some .keyDown => .down
  nextState.snake.direction =
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
def wrapsAtEdge (area : PlayArea) (state nextState : GameState) : Prop :=
  let direction := nextState.snake.direction
  let before := state.snake.head
  let after := nextState.snake.head
  isAtEdge direction area state →
    match direction with
    | .left => after.x = area.rightEdge ∧ after.y = before.y
    | .up => after.y = area.bottomEdge ∧ after.x = before.x
    | .right => after.x = area.leftEdge ∧ after.y = before.y
    | .down => after.y = area.topEdge ∧ after.x = before.x

/-!
### Food is in the play area
In any game state, there is food within the play area.
-/
def isWithinPlayArea (area : PlayArea) (position : Position) : Prop :=
  area.leftEdge ≤ position.x ∧
    position.x ≤ area.rightEdge ∧
    area.topEdge ≤ position.y ∧
    position.y ≤ area.bottomEdge

def foodIsInPlayArea (state : GameState) (area : PlayArea) : Prop :=
  isWithinPlayArea area state.food

/-!
### Snake is in play area
The snake's head and body positions must be within the play area.
-/
def snakeIsInPlayArea (area : PlayArea) (snake : Snake) : Prop :=
  isWithinPlayArea area snake.head ∧
    ∀ position ∈ snake.body,
      isWithinPlayArea area position

/-!
### Food is never the same position as the snake
-/
def foodIsNotOnSnake (state : GameState) : Prop :=
  state.phase = .won ∨
    (state.food ≠ state.snake.head ∧ state.food ∉ state.snake.body)

/-!
### The snake grows when it eats food
When the snake is at the food's position, the snake grows by one segment.
-/

def foodIsEaten (before after : GameState) : Prop :=
  after.snake.head = before.food

def snakeGrowsWhenEating (state nextState : GameState) : Prop :=
  foodIsEaten state nextState →
    nextState.snake.body = state.snake.head :: state.snake.body

/-!
### The snake's body follows its head
When food is not eaten, the head's previous position becomes the first body
segment and the last segment is removed.
-/
def snakeBodyMoves (state nextState : GameState) : Prop :=
  ¬ foodIsEaten state nextState →
    nextState.snake.body =
      if state.snake.body.isEmpty then []
      else state.snake.head :: state.snake.body.dropLast

/-!
### The game is lost when the snake collides with itself
The game is lost when the head overlaps the body after movement. Moving into
the tail's previous position is safe if the tail has moved away.
-/
def snakeCollides (snake : Snake) (position : Position) : Prop :=
  position ∈ snake.body

def gameEndsOnSelfCollision (_state nextState : GameState) : Prop :=
  nextState.phase = .lost ↔ snakeCollides nextState.snake nextState.snake.head

/-!
### The game is won when the play area is full
The game is won when the snake occupies every position in the play area
-/

/-- The board is full when the snake occupies every position in the play area. -/
def boardIsFull (area : PlayArea) (snake : Snake) : Prop :=
  ∀ position, isWithinPlayArea area position →
    position = snake.head ∨ position ∈ snake.body

def gameIsWonWhenPlayAreaIsFull (area : PlayArea) (_state nextState : GameState) : Prop :=
  nextState.phase = .won ↔
    boardIsFull area nextState.snake ∧
      ¬ snakeCollides nextState.snake nextState.snake.head

/-!
### The game stops after it is won or lost.
-/
def gameHasNoStepAfterEnd (update : UpdateGame) : Prop :=
  ∀ nextMove nextFood state,
    ¬ gameIsRunning state →
      update state nextMove nextFood = state

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
  segmentsAreConnected area snake.head snake.body

/-!
### Food is placed randomly
-/

/-- A position in the play area that the snake does not occupy. -/
def isFree (area : PlayArea) (snake : Snake) (position : Position) : Prop :=
  isWithinPlayArea area position ∧
    position ≠ snake.head ∧
    position ∉ snake.body

def randomPosition (positions : List Position) : BaseIO (Option Position) :=
  if positions.isEmpty then
    pure none
  else do
    let index ← IO.rand 0 (positions.length - 1)
    pure positions[index]?

def foodIsPlacedRandomly (area : PlayArea) (snake : Snake)
    (nextFoodPosition : BaseIO (Option Position)) : Prop :=
  ∃ freePositions : List Position,
    (∀ position, position ∈ freePositions ↔ isFree area snake position) ∧
    freePositions.Nodup ∧
    nextFoodPosition = randomPosition freePositions

/-!
### Food moves to the next food position
When food is eaten and the game is not won, the candidate provided to that step
becomes the food position. Otherwise the food position remains unchanged.
-/
def foodMovesToNextPosition (nextFood : Option Position) (state nextState : GameState) : Prop :=
  (foodIsEaten state nextState → nextState.phase ≠ .won →
    nextFood = some nextState.food) ∧
  ((¬ foodIsEaten state nextState ∨ nextState.phase = .won) →
    nextState.food = state.food)

def initialFoodUsesChosenPosition (makeInitialState : Position → GameState) : Prop :=
  ∀ position, (makeInitialState position).food = position

/-!
### The snake does not overlap itself
-/
def snakeDoesNotOverlapItself (snake : Snake) : Prop :=
  (snake.head :: snake.body).Nodup

/-!
### All game requirements
-/
def playAreaIsValid (area : PlayArea) : Prop :=
  area.leftEdge ≤ area.rightEdge ∧ area.topEdge ≤ area.bottomEdge

def gameStateInvariant (area : PlayArea) (state : GameState) : Prop :=
  foodIsInPlayArea state area ∧
    foodIsNotOnSnake state ∧
    snakeIsInPlayArea area state.snake ∧
    (state.phase = .won → boardIsFull area state.snake) ∧
    snakeIsConnected area state.snake ∧
    (state.phase ≠ .lost → snakeDoesNotOverlapItself state.snake)

/-- A replacement is free after the move, or absent when the board is full. -/
def foodChoiceIsValid (area : PlayArea) (snake : Snake) (nextFood : Option Position) : Prop :=
  match nextFood with
  | some position => isFree area snake position
  | none => ∀ position, ¬ isFree area snake position

def gameStepRequirements (move : MoveSnake) (update : UpdateGame) (area : PlayArea) : Prop :=
  gameHasNoStepAfterEnd update ∧
    ∀ input state,
      gameStateInvariant area state →
      gameIsRunning state →
        let moved := move input state
        let movedState := { state with snake := moved }
        movesInDirectionIfNotAtEdge area state movedState ∧
        arrowInputSetsDirection input state movedState ∧
        wrapsAtEdge area state movedState ∧
        snakeGrowsWhenEating state movedState ∧
        snakeBodyMoves state movedState ∧
        (∀ nextFood,
          (foodIsEaten state movedState → foodChoiceIsValid area moved nextFood) →
            let nextState := update state moved nextFood
            nextState.snake = moved ∧
            foodMovesToNextPosition nextFood state nextState ∧
            gameEndsOnSelfCollision state nextState ∧
            gameIsWonWhenPlayAreaIsFull area state nextState ∧
            gameStateInvariant area nextState)

def gameRequirements (initialSnake : Snake) (makeInitialState : Position → GameState)
    (move : MoveSnake) (update : UpdateGame) (area : PlayArea)
    (nextFoodPosition : Snake → BaseIO (Option Position)) : Prop :=
  playAreaIsValid area ∧
    (∃ position, isFree area initialSnake position) ∧
    initialFoodUsesChosenPosition makeInitialState ∧
    (∀ position, (makeInitialState position).snake = initialSnake) ∧
    (∀ position, isFree area initialSnake position →
      gameIsRunning (makeInitialState position) ∧
        gameStateInvariant area (makeInitialState position)) ∧
    gameStepRequirements move update area ∧
    (∀ snake, foodIsPlacedRandomly area snake (nextFoodPosition snake))


end Spec
