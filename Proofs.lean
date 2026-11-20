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
  rcases state with ⟨⟨⟨x, y⟩, segments⟩, food, direction⟩
  cases input with
  | none =>
    cases direction <;>
      dsimp [Snake.step, Snake.directionAfterInput, Snake.moveSnake,
        Snake.playArea, Spec.oppositeDirection, Spec.isAtEdge,
        Spec.movesInDirection] at *
      <;> simp_all <;> omega
  | some key =>
    cases key <;> cases direction <;>
      dsimp [Snake.step, Snake.directionAfterInput, Snake.moveSnake,
        Snake.playArea, Spec.oppositeDirection, Spec.isAtEdge,
        Spec.movesInDirection] at *
      <;> simp_all <;> omega

theorem wrapsAtEdge :
    Spec.wrapsAtEdge Snake.step Snake.playArea := by
  intro input state
  rcases state with ⟨⟨⟨x, y⟩, segments⟩, food, direction⟩
  cases input with
  | none =>
    cases direction <;>
      simp_all [Snake.step, Snake.directionAfterInput, Snake.moveSnake,
        Snake.playArea, Spec.oppositeDirection, Spec.isAtEdge] <;> omega
  | some key =>
    cases key <;> cases direction <;>
      simp_all [Snake.step, Snake.directionAfterInput, Snake.moveSnake,
        Snake.playArea, Spec.oppositeDirection, Spec.isAtEdge] <;> omega

theorem foodIsInPlayArea_initial :
    Spec.foodIsInPlayArea Snake.initialState Snake.playArea := by
  simp [Spec.foodIsInPlayArea, Snake.initialState, Snake.playArea]

private theorem availableFoodPosition_isInPlayArea
    (area : PlayArea) (food position : Position)
    (h : Snake.availableFoodPosition area food = some position) :
    area.leftEdge ≤ position.x ∧
      position.x ≤ area.rightEdge ∧
      area.topEdge ≤ position.y ∧
      position.y ≤ area.bottomEdge := by
  unfold Snake.availableFoodPosition at h
  have hAvailable := List.find?_some h
  have hPosition := of_decide_eq_true hAvailable
  rcases hPosition with ⟨hLeft, hRight, hTop, hBottom, _⟩
  exact ⟨hLeft, hRight, hTop, hBottom⟩

private theorem position_mem_positionsInPlayArea (position : Position)
    (hRight : position.x ≤ 39) (hBottom : position.y ≤ 29) :
    position ∈ Snake.positionsInPlayArea Snake.playArea := by
  simp only [Snake.positionsInPlayArea, List.mem_flatMap]
  refine ⟨position.y, ?_, ?_⟩
  · simp [Snake.playArea]
    omega
  · simp only [List.mem_map]
    refine ⟨position.x, ?_, ?_⟩
    · simp [Snake.playArea]
      omega
    · simp [Snake.playArea]

private theorem availableFoodPosition_exists
    (food : Position) :
    ∃ position,
      Snake.availableFoodPosition Snake.playArea food = some position ∧
        position ≠ food := by
  let origin : Position := { x := 0, y := 0 }
  let alternate : Position := { x := 1, y := 0 }
  let candidate := if food = origin then alternate else origin
  have hCandidateRight : candidate.x ≤ 39 := by
    by_cases hFood : food = origin <;>
      simp [candidate, hFood, origin, alternate]
  have hCandidateBottom : candidate.y ≤ 29 := by
    by_cases hFood : food = origin <;>
      simp [candidate, hFood, origin, alternate]
  have hCandidateMem :=
    position_mem_positionsInPlayArea candidate hCandidateRight hCandidateBottom
  have hCandidateNe : candidate ≠ food := by
    by_cases hFood : food = origin
    · simp [candidate, hFood, alternate, origin]
    · simp [candidate, hFood, origin, ne_comm]
  have hCandidateTest :
      decide
        (Snake.playArea.leftEdge ≤ candidate.x ∧
          candidate.x ≤ Snake.playArea.rightEdge ∧
          Snake.playArea.topEdge ≤ candidate.y ∧
          candidate.y ≤ Snake.playArea.bottomEdge ∧
          candidate ≠ food) = true := by
    apply decide_eq_true
    exact ⟨by simp [Snake.playArea], hCandidateRight,
      by simp [Snake.playArea], hCandidateBottom, hCandidateNe⟩
  have hSome :
      (Snake.availableFoodPosition Snake.playArea food).isSome = true := by
    apply List.find?_isSome.mpr
    exact ⟨candidate, hCandidateMem, hCandidateTest⟩
  obtain ⟨position, hPosition⟩ := Option.isSome_iff_exists.mp hSome
  have hDifferent := List.find?_some hPosition
  have hDifferent := of_decide_eq_true hDifferent
  exact ⟨position, hPosition, hDifferent.2.2.2.2⟩

theorem foodIsInPlayArea_step (input : Option PlayerInput) (state : GameState)
    (h : Spec.foodIsInPlayArea state Snake.playArea) :
    Spec.foodIsInPlayArea (Snake.step input state) Snake.playArea := by
  unfold Snake.step
  dsimp only
  simp only [Spec.foodIsInPlayArea] at h ⊢
  by_cases hEaten :
      (Snake.moveSnake Snake.playArea
        (Snake.directionAfterInput input state.direction) state.snake).position =
          state.food
  · cases hAvailable : Snake.availableFoodPosition Snake.playArea state.food with
    | none =>
      simpa [hEaten, hAvailable] using h
    | some position =>
      have hPosition := availableFoodPosition_isInPlayArea
        Snake.playArea state.food position hAvailable
      simpa [hEaten, hAvailable] using hPosition
  · simpa [hEaten] using h

theorem foodMovesWhenEaten :
    Spec.foodMovesWhenEaten Snake.step := by
  intro input state
  dsimp only [Spec.foodMovesWhenEaten, Spec.foodIsEaten, Snake.step]
  let direction := Snake.directionAfterInput input state.direction
  let snake := Snake.moveSnake Snake.playArea direction state.snake
  change
    snake.position = state.food →
      (if snake.position = state.food then
        (Snake.availableFoodPosition Snake.playArea state.food).getD state.food
      else state.food) ≠ state.food
  intro hEaten
  simp only [if_pos hEaten]
  obtain ⟨position, hPosition, hDifferent⟩ :=
    availableFoodPosition_exists state.food
  rw [hPosition]
  exact hDifferent

theorem gameStateInvariant_holdsForReachableStates
    (step : Step) (area : PlayArea) (initialState : GameState)
    (initialInvariant : Spec.gameStateInvariant area initialState)
    (preserved : ∀ input state,
      Spec.gameStateInvariant area state →
        Spec.gameStateInvariant area (step input state)) :
    ∀ state, Spec.Reachable step initialState state →
      Spec.gameStateInvariant area state := by
  intro state reachable
  induction reachable with
  | initial => exact initialInvariant
  | next input _ inductionHypothesis =>
      exact preserved input _ inductionHypothesis

theorem gameRequirements_implyInvariantForReachableStates
    (initialState : GameState) (area : PlayArea)
    (h : Spec.gameRequirements initialState Snake.step area) :
    Spec.alwaysOnReachableStates Snake.step initialState
      (Spec.gameStateInvariant area) := by
  rcases h with ⟨initialInvariant, preserved, _⟩
  exact gameStateInvariant_holdsForReachableStates
    Snake.step area initialState initialInvariant preserved

end Proofs
