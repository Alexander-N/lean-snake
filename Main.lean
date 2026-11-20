import Lasm.Web
import Snake
open Lasm.Web
open Spec

def main : IO Unit := do
  let canvas ← createElement "canvas"
  canvas.setAttributes #[("width", "400"), ("height", "300")]
  canvas.setStyles #[("border", "2px solid #333")]
  (← document).body >>= (·.appendChild canvas)
  let context ← canvas.context2d

  let state ← IO.mkRef Snake.initialState
  let previousSnake ← IO.mkRef Snake.initialState.snake
  let lastMoveTime ← IO.mkRef (← now)

  let render (timestamp : Float) : IO Unit := do
    let current ← state.get
    let previous ← previousSnake.get
    let moveTime ← lastMoveTime.get
    let progress := min 1.0 ((timestamp - moveTime) / 120.0)
    let deltaX := current.snake.x.toFloat - previous.x.toFloat
    let deltaY := current.snake.y.toFloat - previous.y.toFloat
    let wrappedX := deltaX > 10.0 || deltaX < -10.0
    let wrappedY := deltaY > 10.0 || deltaY < -10.0
    let deltaX := if wrappedX then
        match current.direction with
        | .left => -10.0
        | .right => 10.0
        | _ => deltaX
      else
        deltaX
    let deltaY := if wrappedY then
        match current.direction with
        | .up => -10.0
        | .down => 10.0
        | _ => deltaY
      else
        deltaY
    let x := previous.x.toFloat + deltaX * progress
    let y := previous.y.toFloat + deltaY * progress
    context.draw #[
      .clearRect 0 0 400 300,
      .fillStyle "green",
      .fillRect x y 10 10
    ]
    if wrappedX then
      let offset := if deltaX > 0 then -400.0 else 400.0
      context.draw #[.fillRect (x + offset) y 10 10]
    if wrappedY then
      let offset := if deltaY > 0 then -300.0 else 300.0
      context.draw #[.fillRect x (y + offset) 10 10]

  let steer (input : PlayerInput) : IO Unit := do
    state.modify fun current =>
      { current with
        direction := Snake.directionAfterInput (some input) current.direction }

  let window ← window
  _ ← window.toEventTarget.on "keydown" fun event => do
    let key ← event.key
    if key == "ArrowLeft" then
      event.preventDefault
      steer .keyLeft
    else if key == "ArrowUp" then
      event.preventDefault
      steer .keyUp
    else if key == "ArrowRight" then
      event.preventDefault
      steer .keyRight
    else if key == "ArrowDown" then
      event.preventDefault
      steer .keyDown

  _ ← setInterval 120 do
    let current ← state.get
    previousSnake.set current.snake
    state.set (Snake.step none current)
    lastMoveTime.set (← now)

  _ ← setInterval 16 do
    render (← now)
