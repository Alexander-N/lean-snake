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
  IO.setRandSeed (← now).toUInt64.toNat

  let state ← IO.mkRef Snake.initialState
  let pendingInput ← IO.mkRef (none : Option PlayerInput)
  let previousSnake ← IO.mkRef Snake.initialState.snake
  let lastMoveTime ← IO.mkRef (← now)

  let render (timestamp : Float) : IO Unit := do
    let current ← state.get
    let previous ← previousSnake.get
    let moveTime ← lastMoveTime.get
    let progress := min 1.0 ((timestamp - moveTime) / 120.0)
    let cellSize := Snake.cellSizePixels.toFloat
    let snakeColor := "#3fb950"
    let drawMovingSegment (fromPosition toPosition : Position) : IO Unit := do
      let rawDeltaX := toPosition.x.toFloat - fromPosition.x.toFloat
      let rawDeltaY := toPosition.y.toFloat - fromPosition.y.toFloat
      let wrappedX := rawDeltaX > 1.0 || rawDeltaX < -1.0
      let wrappedY := rawDeltaY > 1.0 || rawDeltaY < -1.0
      let deltaX := if wrappedX then
          if rawDeltaX > 0.0 then -1.0 else 1.0
        else
          rawDeltaX
      let deltaY := if wrappedY then
          if rawDeltaY > 0.0 then -1.0 else 1.0
        else
          rawDeltaY
      let x := ((fromPosition.x.toFloat + deltaX * progress) * cellSize).round
      let y := ((fromPosition.y.toFloat + deltaY * progress) * cellSize).round
      context.draw #[
        .fillStyle snakeColor,
        .fillRect x y cellSize cellSize
      ]
      if wrappedX then
        let offset := if deltaX > 0.0 then
            -(Snake.canvasWidthPixels.toFloat)
          else
            Snake.canvasWidthPixels.toFloat
        context.draw #[
          .fillStyle snakeColor,
          .fillRect (x + offset) y cellSize cellSize
        ]
      if wrappedY then
        let offset := if deltaY > 0.0 then
            -(Snake.canvasHeightPixels.toFloat)
          else
            Snake.canvasHeightPixels.toFloat
        context.draw #[
          .fillStyle snakeColor,
          .fillRect x (y + offset) cellSize cellSize
        ]
    context.draw #[
      .fillStyle "#102018",
      .fillRect 0 0 Snake.canvasWidthPixels.toFloat Snake.canvasHeightPixels.toFloat
    ]
    for (fromPosition, toPosition) in previous.body.zip current.snake.body do
      drawMovingSegment fromPosition toPosition
    for newSegment in current.snake.body.drop previous.body.length do
      drawMovingSegment newSegment newSegment
    drawMovingSegment previous.position current.snake.position
    context.draw #[
      .fillStyle "#ff5d5d",
      .fillRect (current.food.x.toFloat * cellSize)
        (current.food.y.toFloat * cellSize) cellSize cellSize
    ]
    match current.phase with
    | .playing => pure ()
    | .won =>
      context.draw #[
        .fillStyle "rgba(0, 0, 0, 0.7)",
        .fillRect 0 0 Snake.canvasWidthPixels.toFloat Snake.canvasHeightPixels.toFloat,
        .fillStyle "white",
        .font "bold 28px sans-serif",
        .textAlign "center",
        .fillText "You won" (Snake.canvasWidthPixels.toFloat / 2.0) 150.0,
        .font "16px sans-serif",
        .fillText "Press Enter to play again"
          (Snake.canvasWidthPixels.toFloat / 2.0) 180.0
      ]
    | .lost =>
      context.draw #[
        .fillStyle "rgba(0, 0, 0, 0.7)",
        .fillRect 0 0 Snake.canvasWidthPixels.toFloat Snake.canvasHeightPixels.toFloat,
        .fillStyle "white",
        .font "bold 28px sans-serif",
        .textAlign "center",
        .fillText "Game over" (Snake.canvasWidthPixels.toFloat / 2.0) 150.0,
        .font "16px sans-serif",
        .fillText "Press Enter to play again"
          (Snake.canvasWidthPixels.toFloat / 2.0) 180.0
      ]

  let steer (input : PlayerInput) : IO Unit :=
    pendingInput.set (some input)

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
    else if key == "Enter" then
      event.preventDefault
      pendingInput.set none
      state.set Snake.initialState
      previousSnake.set Snake.initialState.snake
      lastMoveTime.set (← now)

  _ ← setInterval 120 do
    let current ← state.get
    let input ← pendingInput.get
    pendingInput.set none
    let numberOfFreePositions := Snake.numberOfFreePositionsForStep input current
    let random ← if numberOfFreePositions = 0 then
        pure 0
      else
        IO.rand 0 (numberOfFreePositions - 1)
    let nextState := Snake.step input { current with random := random }
    previousSnake.set current.snake
    state.set nextState
    lastMoveTime.set (← now)

  _ ← setInterval 16 do
    render (← now)
