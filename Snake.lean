import Spec

namespace Snake

open Spec

def initialState : GameState :=
  { snake := { position := { x := 7, y := 4 }, body := [] },
    food := { x := 20, y := 14 },
    direction := .right,
    phase := .playing }

def playArea : PlayArea :=
  { leftEdge := 0, rightEdge := 39, topEdge := 0, bottomEdge := 29 }

def cellSizePixels : Nat := 10

def canvasWidthPixels : Nat := (playArea.rightEdge + 1) * cellSizePixels

def canvasHeightPixels : Nat := (playArea.bottomEdge + 1) * cellSizePixels

def positionsInPlayArea (area : PlayArea) : List Position :=
  (List.range (area.bottomEdge - area.topEdge + 1)).flatMap fun y =>
    (List.range (area.rightEdge - area.leftEdge + 1)).map fun x =>
      { x := area.leftEdge + x, y := area.topEdge + y }

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

def moveSnake (area : PlayArea) (direction : Direction) (snake : Spec.Snake) : Spec.Snake :=
  { snake with position := positionAfterMove area direction snake.position }

def isFreeForSnake (position : Position) (snake : Spec.Snake) : Bool :=
  decide (position ≠ snake.position ∧ position ∉ snake.body)

def availableFoodPositionForSnake (area : PlayArea) (food : Position)
    (snake : Spec.Snake) : Option Position :=
  let positions := positionsInPlayArea area
  positions.find? (fun position =>
      isFreeForSnake position snake &&
        decide (position.x ≠ food.x ∧ position.y ≠ food.y)) <|>
    positions.find? (isFreeForSnake · snake)

def differentFoodPosition (area : PlayArea) (food : Position) : Position :=
  let positions := positionsInPlayArea area
  (positions.find? (fun position =>
        decide (position.x ≠ food.x ∧ position.y ≠ food.y)) <|>
      positions.find? (fun position => decide (position ≠ food))).getD
    { x := area.leftEdge, y := area.topEdge }

def snakeFillsPlayArea (area : PlayArea) (snake : Spec.Snake) : Bool :=
  (positionsInPlayArea area).all fun position =>
    decide (position = snake.position ∨ position ∈ snake.body)

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
          (availableFoodPositionForSnake playArea state.food snake).getD
            (differentFoodPosition playArea state.food)
          else state.food,
        direction := direction,
        phase := .lost }
    else if eating then
      match availableFoodPositionForSnake playArea state.food snake with
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
