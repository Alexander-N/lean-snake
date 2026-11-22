import Spec

namespace Snake

open Spec

def initialSnake : Spec.Snake :=
  { position := { x := 7, y := 4 }, body := [] }

def playArea : PlayArea :=
  { leftEdge := 0, rightEdge := 29, topEdge := 0, bottomEdge := 19 }

def cellSizePixels : Nat := 20

def moveIntervalMilliseconds : Nat := 150

def canvasWidthPixels : Nat := (playArea.rightEdge + 1) * cellSizePixels

def canvasHeightPixels : Nat := (playArea.bottomEdge + 1) * cellSizePixels

def directionAfterInput (input : Option PlayerInput) (current : Direction) : Direction :=
  let requested :=
    match input with
    | none => current
    | some .keyLeft => .left
    | some .keyUp => .up
    | some .keyRight => .right
    | some .keyDown => .down
  if requested = oppositeDirection current then current else requested

def positionAfterMove (area : PlayArea) (direction : Direction) (position : Position) :
    Position :=
  match direction with
  | .left =>
      { position with
        x := if position.x = area.leftEdge then area.rightEdge else position.x - 1 }
  | .up =>
      { position with
        y := if position.y = area.topEdge then area.bottomEdge else position.y - 1 }
  | .right =>
      { position with
        x := if position.x = area.rightEdge then area.leftEdge else position.x + 1 }
  | .down =>
      { position with
        y := if position.y = area.bottomEdge then area.topEdge else position.y + 1 }

def isFreeForSnake (position : Position) (snake : Spec.Snake) : Bool :=
  decide (position ≠ snake.position ∧ position ∉ snake.body)

def freeFoodPositions (area : PlayArea) (snake : Spec.Snake) : List Position :=
  (Spec.positionsInPlayArea area).filter (isFreeForSnake · snake)

def nextFoodPosition (area : PlayArea) (random : Nat) (snake : Spec.Snake) :
    Option Position :=
  let positions := freeFoodPositions area snake
  positions[random % positions.length]?

def initialState (random : Nat) : GameState :=
  let food := (nextFoodPosition playArea random initialSnake).getD initialSnake.position
  { snake := initialSnake,
    food := food,
    direction := .right,
    phase := .playing,
    random := random }

def differentFoodPosition (area : PlayArea) (food : Position) : Position :=
  let positions := Spec.positionsInPlayArea area
  (positions.find? (fun position =>
        decide (position.x ≠ food.x ∧ position.y ≠ food.y)) <|>
      positions.find? (fun position => decide (position ≠ food))).getD
    { x := area.leftEdge, y := area.topEdge }

def snakeFillsPlayArea (area : PlayArea) (snake : Spec.Snake) : Bool :=
  (Spec.positionsInPlayArea area).all fun position =>
    decide (position = snake.position ∨ position ∈ snake.body)

def snakeAfterEating (input : Option PlayerInput) (state : GameState) : Spec.Snake :=
  let direction := directionAfterInput input state.direction
  { position := positionAfterMove playArea direction state.snake.position,
    body := state.snake.position :: state.snake.body }

def numberOfFreePositionsForStep (input : Option PlayerInput) (state : GameState) : Nat :=
  let direction := directionAfterInput input state.direction
  let intendedPosition := positionAfterMove playArea direction state.snake.position
  let body :=
    if intendedPosition = state.food then
      state.snake.position :: state.snake.body
    else if state.snake.body.isEmpty then
      []
    else
      state.snake.position :: state.snake.body.dropLast
  Spec.numberOfFreePositions playArea { position := intendedPosition, body := body }

def step (input : Option PlayerInput) (state : GameState) : GameState :=
  if state.phase ≠ .playing then
    state
  else
    let direction := directionAfterInput input state.direction
    let intendedPosition := positionAfterMove playArea direction state.snake.position
    let eating := intendedPosition = state.food
    let body :=
      if eating then
        state.snake.position :: state.snake.body
      else if state.snake.body.isEmpty then
        []
      else
        state.snake.position :: state.snake.body.dropLast
    let snake := { position := intendedPosition, body := body }
    if intendedPosition ∈ state.snake.body then
      { state with
        snake := snake,
        food := if eating then
          (nextFoodPosition playArea state.random snake).getD
            (differentFoodPosition playArea state.food)
          else state.food,
        direction := direction,
        phase := .lost }
    else if eating then
      match nextFoodPosition playArea state.random snake with
      | some food =>
        { state with snake := snake, food := food, direction := direction }
      | none =>
        { state with snake := snake, direction := direction, phase := .won }
    else
      { state with
        snake := snake,
        direction := direction,
        phase := if snakeFillsPlayArea playArea snake then .won else .playing }

end Snake
