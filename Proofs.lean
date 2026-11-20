import Spec
import Snake

/-!
Theorems are named after the propositions they prove.
-/
namespace Proofs

open Spec

theorem arrowInputSetsDirection :
    Spec.arrowInputSetsDirection Snake.step := by
  intro input state
  cases input with
  | none => rfl
  | some key =>
    cases key <;> rfl

theorem movesInDirectionIfNotAtEdge :
    Spec.movesInDirectionIfNotAtEdge Snake.step Snake.playArea := by
  intro input state
  rcases state with ⟨snake, direction⟩
  cases input with
  | none =>
    cases direction <;>
      dsimp [Snake.step, Snake.directionAfterInput, Snake.moveSnake,
        Snake.playArea, Spec.oppositeDirection, Spec.isAtEdge,
        Spec.movesInDirection] at *
      <;> omega
  | some key =>
    cases key <;> cases direction <;>
      dsimp [Snake.step, Snake.directionAfterInput, Snake.moveSnake,
        Snake.playArea, Spec.oppositeDirection, Spec.isAtEdge,
        Spec.movesInDirection] at *
      <;> omega

theorem wrapsAtEdge :
    Spec.wrapsAtEdge Snake.step Snake.playArea := by
  intro input state
  rcases state with ⟨snake, direction⟩
  cases input with
  | none =>
    cases direction <;>
      simp_all [Snake.step, Snake.directionAfterInput, Snake.moveSnake,
        Snake.playArea, Spec.oppositeDirection, Spec.isAtEdge]
  | some key =>
    cases key <;> cases direction <;>
      simp_all [Snake.step, Snake.directionAfterInput, Snake.moveSnake,
        Snake.playArea, Spec.oppositeDirection, Spec.isAtEdge]

end Proofs
