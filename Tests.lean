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

example : Spec.arrowInputSetsDirection Snake.step := by
  unfold Spec.arrowInputSetsDirection Spec.gameIsRunning
  plausible

example : Spec.foodChangesBothCoordinatesWhenPossible Snake.step Snake.playArea := by
  unfold Spec.foodChangesBothCoordinatesWhenPossible Spec.foodIsEaten
    Spec.gameIsRunning Spec.isWithinPlayArea
  dsimp only
  intro input state hRunning hEaten hNotWon hPossible
  rcases hPossible with ⟨position, hWithin, hHead, hBody, hx, hy⟩
  plausible (config := { numInst := 20, maxSize := 5, numRetries := 10000 })

end Tests
