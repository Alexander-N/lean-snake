import Spec

namespace Snake

open Spec

def initialState : GameState :=
  { snake := { position := { x := 7, y := 4 }, segments := [] },
    food := { x := 20, y := 14 },
    direction := .right }

def playArea : PlayArea :=
  { leftEdge := 0, rightEdge := 39, topEdge := 0, bottomEdge := 29 }

def cellSizePixels : Nat := 10

def canvasWidthPixels : Nat := (playArea.rightEdge + 1) * cellSizePixels

def canvasHeightPixels : Nat := (playArea.bottomEdge + 1) * cellSizePixels

def positionsInPlayArea (area : PlayArea) : List Position :=
  (List.range (area.bottomEdge - area.topEdge + 1)).flatMap fun y =>
    (List.range (area.rightEdge - area.leftEdge + 1)).map fun x =>
      { x := area.leftEdge + x, y := area.topEdge + y }

def availableFoodPosition (area : PlayArea) (food : Position) : Option Position :=
  (positionsInPlayArea area).find? fun position =>
    decide
      (area.leftEdge ≤ position.x ∧
        position.x ≤ area.rightEdge ∧
        area.topEdge ≤ position.y ∧
        position.y ≤ area.bottomEdge ∧
        position ≠ food)

def directionAfterInput (input : Option PlayerInput) (current : Direction) : Direction :=
  let requestedDirection :=
    match input with
    | none => current
    | some .keyLeft => .left
    | some .keyUp => .up
    | some .keyRight => .right
    | some .keyDown => .down
  if requestedDirection = oppositeDirection current then current else requestedDirection

def moveSnake (area : PlayArea) (direction : Direction) (snake : Spec.Snake) : Spec.Snake :=
  match direction with
  | .left =>
    { snake with position :=
      { snake.position with
        x := if snake.position.x = area.leftEdge then area.rightEdge else snake.position.x - 1 } }
  | .up =>
    { snake with position :=
      { snake.position with
        y := if snake.position.y = area.topEdge then area.bottomEdge else snake.position.y - 1 } }
  | .right =>
    { snake with position :=
      { snake.position with
        x := if snake.position.x = area.rightEdge then area.leftEdge else snake.position.x + 1 } }
  | .down =>
    { snake with position :=
      { snake.position with
        y := if snake.position.y = area.bottomEdge then area.topEdge else snake.position.y + 1 } }

def step (input : Option PlayerInput) (state : GameState) : GameState :=
  let direction := directionAfterInput input state.direction
  let snake := moveSnake playArea direction state.snake
  let food :=
    if snake.position = state.food then
      (availableFoodPosition playArea state.food).getD state.food
    else
      state.food
  { state with
    snake := snake,
    food := food,
    direction := direction }

end Snake
