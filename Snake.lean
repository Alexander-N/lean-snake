import Spec

namespace Snake

open Spec

def initialSnake : Spec.Snake :=
  { head := { x := 7, y := 4 }, body := [], direction := .right }

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
  decide (position ≠ snake.head ∧ position ∉ snake.body)

def freeFoodPositions (area : PlayArea) (snake : Spec.Snake) : List Position :=
  let positions := (List.range (area.bottomEdge + 1 - area.topEdge)).flatMap fun y =>
    (List.range (area.rightEdge + 1 - area.leftEdge)).map fun x =>
      { x := area.leftEdge + x, y := area.topEdge + y : Position }
  positions.filter (isFreeForSnake · snake)

def nextFoodPosition (area : PlayArea) (snake : Spec.Snake) : BaseIO (Option Position) :=
  Spec.randomPosition (freeFoodPositions area snake)

def initialState (food : Position) : GameState :=
  { snake := initialSnake,
    food := food,
    phase := .playing }

def snakeFillsPlayArea (area : PlayArea) (snake : Spec.Snake) : Bool :=
  (freeFoodPositions area snake).isEmpty

def moveSnake (input : Option PlayerInput) (state : GameState) : Spec.Snake :=
  let direction := directionAfterInput input state.snake.direction
  let position := positionAfterMove playArea direction state.snake.head
  let body :=
    if position = state.food then
      state.snake.head :: state.snake.body
    else if state.snake.body.isEmpty then
      []
    else
      state.snake.head :: state.snake.body.dropLast
  { head := position, body := body, direction := direction }

def updateGame (state : GameState) (snake : Spec.Snake)
    (nextFood : Option Position) : GameState :=
  if state.phase ≠ .playing then
    state
  else if snake.head ∈ snake.body then
    { state with snake := snake, phase := .lost }
  else if snake.head = state.food then
    match nextFood with
    | some food =>
      { state with snake := snake, food := food }
    | none =>
      { state with snake := snake, phase := .won }
  else
    { state with
      snake := snake,
      phase := if snakeFillsPlayArea playArea snake then .won else .playing }

end Snake
