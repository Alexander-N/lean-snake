import Plausible
import Spec
import Snake

namespace Tests

set_option warn.sorry false
set_option synthInstance.maxSize 100000

open Plausible Spec

deriving instance Repr for
  Position, Spec.Snake, Direction, PlayerInput, GamePhase, GameState

deriving instance Arbitrary for
  Position, Spec.Snake, Direction, PlayerInput, GamePhase, GameState

deriving instance Shrinkable for
  Position, Spec.Snake, Direction, PlayerInput, GamePhase, GameState

instance {α : Type} [Repr α] (x : α) (xs : List α) :
    PrintableProp (x ∈ xs) where
  printProp := s!"{repr x} ∈ {repr xs}"

/-! These examples use Plausible as a counterexample search before proof. -/

example : Spec.gameEndsOnSelfCollision Snake.step := by
  unfold Spec.gameEndsOnSelfCollision Spec.gameIsRunning Spec.snakeCollides
  dsimp only
  plausible (config := { numInst := 20, maxSize := 5, numRetries := 100 })

example : Spec.arrowInputSetsDirection Snake.step := by
  unfold Spec.arrowInputSetsDirection Spec.gameIsRunning
  plausible

example : ∀ (input : Option PlayerInput) (state : GameState),
    Spec.gameIsRunning state →
      let nextState := Snake.step input state
      ¬ Spec.snakeCollides state.snake nextState.snake.position →
        (nextState.phase = .won ↔
            Snake.snakeFillsPlayArea Snake.playArea nextState.snake = true) ∧
          nextState.phase ≠ .lost := by
  unfold Spec.gameIsRunning Spec.snakeCollides
  dsimp only
  intro input state hRunning hSafe
  plausible (config := { numInst := 20, maxSize := 5, numRetries := 100 })

example : ∀ (input : Option PlayerInput) (state : GameState),
    Spec.foodIsNotOnSnake state → Spec.foodIsNotOnSnake (Snake.step input state) := by
  unfold Spec.foodIsNotOnSnake
  intro input state hFood
  plausible (config := { numInst := 20, maxSize := 5, numRetries := 100 })

end Tests
