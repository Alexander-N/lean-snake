import GameFlow
import Snake
import Plausible

open Spec GameFlow Plausible

deriving instance Repr, Arbitrary, Shrinkable for Direction, PlayerInput
deriving instance Repr, Arbitrary, Shrinkable for Position, Snake, GamePhase, GameState

/-! Test steering from the initial snake with every representable heading. -/
set_option warn.sorry false in
example (input : Option PlayerInput) (direction : Direction) :
    let state := { Snake.initialState ⟨0, 0⟩ with
      snake := { Snake.initialSnake with direction := direction } }
    arrowInputSetsDirection input state { state with snake := Snake.moveSnake input state } := by
  unfold arrowInputSetsDirection Snake.moveSnake Snake.directionAfterInput oppositeDirection
  plausible

/-! Search all representable running states, moved snakes, and food choices. -/
set_option warn.sorry false in
example (state : GameState) (snake : Snake) (food : Option Position) :
    gameIsRunning state →
      gameEndsOnSelfCollision state (Snake.updateGame state snake food) := by
  unfold gameIsRunning gameEndsOnSelfCollision snakeCollides Snake.updateGame
  plausible (config := { numInst := 100, maxSize := 5, numRetries := 500 })

/-! Start with a unique snake and free food, then test its moved body. -/
set_option warn.sorry false in
set_option synthInstance.maxSize 100000 in
example (state : GameState) (input : Option PlayerInput) (food : Option Position) :
    snakeDoesNotOverlapItself state.snake →
      foodIsNotOnSnake state →
      gameIsRunning state →
      let next := Snake.updateGame state (Snake.moveSnake input state) food
      next.phase ≠ .lost →
        snakeDoesNotOverlapItself next.snake := by
  unfold snakeDoesNotOverlapItself foodIsNotOnSnake gameIsRunning
  plausible (config := { numInst := 100, maxSize := 5, numRetries := 1000 })

/-! Search arbitrary representable states for body regressions. -/
set_option warn.sorry false in
example (state : GameState) (input : Option PlayerInput) :
    snakeGrowsWhenEating state
      { state with snake := Snake.moveSnake input state } := by
  unfold snakeGrowsWhenEating foodIsEaten Snake.moveSnake Snake.directionAfterInput
    Snake.positionAfterMove
  plausible

set_option warn.sorry false in
example (state : GameState) (input : Option PlayerInput) :
    snakeBodyMoves state
      { state with snake := Snake.moveSnake input state } := by
  unfold snakeBodyMoves foodIsEaten Snake.moveSnake Snake.directionAfterInput
    Snake.positionAfterMove
  plausible

private def p0 : Position := ⟨0, 0⟩
private def p1 : Position := ⟨1, 0⟩
private def p2 : Position := ⟨2, 0⟩
private def area : PlayArea := ⟨0, 2, 0, 0⟩
private def initial : GameState := ⟨⟨p0, [], .right⟩, p1, .playing⟩
private def moved : Snake := ⟨p1, [p0], .right⟩

private def tailState : GameState :=
  ⟨⟨⟨1, 1⟩, [⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], .left⟩, ⟨5, 5⟩, .playing⟩

example : snakeDoesNotOverlapItself (Snake.moveSnake none tailState) := by
  simp [snakeDoesNotOverlapItself, Snake.moveSnake, Snake.directionAfterInput,
    Snake.positionAfterMove, Snake.playArea, oppositeDirection, tailState, Position.mk.injEq]

example : ¬ snakeDoesNotOverlapItself ⟨p0, [p1, p1], .right⟩ := by
  simp [snakeDoesNotOverlapItself, p0, p1, Position.mk.injEq]

example : ¬ snakeDoesNotOverlapItself ⟨p0, [p1, p0], .right⟩ := by
  simp [snakeDoesNotOverlapItself, p0, p1, Position.mk.injEq]

example : foodChoiceIsValid area moved (some p2) := by
  simp [foodChoiceIsValid, isFree, isWithinPlayArea, area, moved, p0, p1, p2,
    Position.mk.injEq]

example : ¬ foodChoiceIsValid area moved (some p1) := by
  simp [foodChoiceIsValid, isFree, moved]

example : foodChoiceIsValid area ⟨p2, [p1, p0], .right⟩ none := by
  intro ⟨x, y⟩
  simp [isFree, isWithinPlayArea, area, p0, p1, p2]
  omega

private def update (state : GameState) (next : Snake)
    (food : Option Position) : GameState :=
  { state with
    snake := next
    food := food.getD state.food
    phase := if next.head == state.food && food.isNone then .won else state.phase }

private def check (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

#eval (show IO Unit from do
  let seen ← IO.mkRef ([] : List Snake)
  let choose (snake : Snake) : BaseIO (Option Position) := do
    seen.modify (snake :: ·)
    pure (some p2)
  let makeInitial (food : Position) : GameState := { initial with food := food }
  let initialResult ← initialStateWithRandomFood initial.snake makeInitial choose
  check (initialResult.map (fun state : GameState => state.food) == some p2)
    "initial food was not selected"
  let initialCalls ← seen.get
  check (initialCalls.map (fun snake => snake.head) == [p0])
    "initial selection did not use the initial snake"
  seen.set []
  let result ← stepWithRandomFood (fun _ _ => moved) update choose none initial
  let calls ← seen.get
  check (calls.map (fun snake => (snake.head, snake.body.length)) == [(p1, 1)])
    "replacement was not chosen after growth"
  check (result.food == p2) "the chosen replacement was not used"
  let turnState := { Snake.initialState p2 with snake := { initial.snake with direction := .right } }
  let turn ← stepWithRandomFood Snake.moveSnake Snake.updateGame choose (some .keyDown) turnState
  check (turn.snake.direction == .down && turn.snake.head == ⟨0, 1⟩)
    "the moved snake did not retain the requested heading"
  seen.set []
  let noFood := { initial with food := p2 }
  let result ← stepWithRandomFood (fun _ _ => moved) update choose none noFood
  let calls ← seen.get
  check (calls.isEmpty && result.food == p2 && result.phase == .playing)
    "food was selected without eating"
  let ended := { initial with phase := .lost }
  let result ← stepWithRandomFood (fun _ _ => moved) update choose none ended
  let calls ← seen.get
  check (calls.isEmpty && result.phase == .lost && result.snake.head == p0)
    "a finished game changed"
  let lastFood : Snake → BaseIO (Option Position) := fun _ => pure none
  let result ← stepWithRandomFood (fun _ _ => moved) update lastFood none initial
  check (result.phase == .won && result.food == p1) "the final move was not won"
  let tailMove := Snake.moveSnake none tailState
  let tailResult := Snake.updateGame tailState tailMove none
  check (tailMove.head == ⟨0, 1⟩ && tailMove.head ∉ tailMove.body &&
    tailResult.phase == .playing) "moving into the vacated tail should be safe"
  let tailStep ← stepWithRandomFood Snake.moveSnake Snake.updateGame choose none tailState
  check (tailStep.phase == .playing && tailStep.snake.head == ⟨0, 1⟩)
    "a game step into the vacated tail should continue"
  let bodyMove := Snake.moveSnake (some .keyUp) tailState
  let bodyResult := Snake.updateGame tailState bodyMove none
  check (bodyMove.head == ⟨1, 0⟩ && bodyMove.head ∈ bodyMove.body &&
    bodyResult.phase == .lost) "moving into a remaining body segment should be lost"
  -- Food on the old tail is not a valid running state, but exercises growth.
  let eatingTail := { tailState with food := ⟨0, 1⟩ }
  let grown := Snake.moveSnake none eatingTail
  let eatingResult := Snake.updateGame eatingTail grown (some ⟨5, 5⟩)
  check (grown.head == ⟨0, 1⟩ && grown.head ∈ grown.body &&
    eatingResult.phase == .lost) "a retained tail should still cause a collision"
  let fullBody := (List.range 20).flatMap fun y =>
    (List.range 30).filterMap fun x =>
      let position : Position := ⟨x, y⟩
      if position == tailMove.head then none else some position
  let fullSnake := { tailMove with body := fullBody }
  check ((Snake.updateGame tailState fullSnake none).phase == .won)
    "a full board without a collision should be won"
  let overlappingSnake := { fullSnake with body := fullSnake.head :: fullBody }
  check ((Snake.updateGame tailState overlappingSnake none).phase == .lost)
    "a collision should take priority over a full board"
  IO.println "GameFlow checks passed")
