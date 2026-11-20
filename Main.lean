import Lasm.Web
import Snake
open Lasm.Web
open Spec

def main : IO Unit := do
  let canvas ← createElement "canvas"
  canvas.setAttributes #[
    ("width", toString Snake.canvasWidthPixels),
    ("height", toString Snake.canvasHeightPixels)
  ]
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
    let deltaX := current.snake.position.x.toFloat - previous.position.x.toFloat
    let deltaY := current.snake.position.y.toFloat - previous.position.y.toFloat
    let wrappedX := deltaX > 1.0 || deltaX < -1.0
    let wrappedY := deltaY > 1.0 || deltaY < -1.0
    let deltaX := if wrappedX then
        match current.direction with
        | .left => -1.0
        | .right => 1.0
        | _ => deltaX
      else
        deltaX
    let deltaY := if wrappedY then
        match current.direction with
        | .up => -1.0
        | .down => 1.0
        | _ => deltaY
      else
        deltaY
    let cellSize := Snake.cellSizePixels.toFloat
    let x := (previous.position.x.toFloat + deltaX * progress) * cellSize
    let y := (previous.position.y.toFloat + deltaY * progress) * cellSize
    context.draw #[
      .clearRect 0 0 Snake.canvasWidthPixels.toFloat Snake.canvasHeightPixels.toFloat,
      .fillStyle "green",
      .fillRect x y cellSize cellSize,
      .fillStyle "red",
      .fillRect (current.food.x.toFloat * cellSize)
        (current.food.y.toFloat * cellSize) cellSize cellSize
    ]
    if wrappedX then
      let offset := if deltaX > 0 then
          -(Snake.canvasWidthPixels.toFloat)
        else
          Snake.canvasWidthPixels.toFloat
      context.draw #[.fillRect (x + offset) y cellSize cellSize]
    if wrappedY then
      let offset := if deltaY > 0 then
          -(Snake.canvasHeightPixels.toFloat)
        else
          Snake.canvasHeightPixels.toFloat
      context.draw #[.fillRect x (y + offset) cellSize cellSize]

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
