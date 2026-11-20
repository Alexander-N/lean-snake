import Spec

namespace Snake

open Spec

def initialState : GameState :=
  { snake := { x := 70, y := 40 }, direction := .right }

def playArea : PlayArea :=
  { leftEdge := 0, rightEdge := 390, topEdge := 0, bottomEdge := 290 }

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
    { x := if snake.x = area.leftEdge then area.rightEdge else snake.x - 10, y := snake.y }
  | .up =>
    { x := snake.x, y := if snake.y = area.topEdge then area.bottomEdge else snake.y - 10 }
  | .right =>
    { x := if snake.x = area.rightEdge then area.leftEdge else snake.x + 10, y := snake.y }
  | .down =>
    { x := snake.x, y := if snake.y = area.bottomEdge then area.topEdge else snake.y + 10 }

def step (input : Option PlayerInput) (state : GameState) : GameState :=
  let direction := directionAfterInput input state.direction
  { snake := moveSnake playArea direction state.snake, direction := direction }

end Snake
