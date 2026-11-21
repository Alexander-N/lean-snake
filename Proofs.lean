import Spec
import Snake

/-!
Theorems are named after the propositions they prove.
-/
namespace Proofs

open Spec

private theorem step_some_direction_and_position (input : Option PlayerInput)
    (state nextState : GameState) (hRunning : Spec.gameIsRunning state)
    (h : Snake.step input state = nextState) :
    nextState.direction = Snake.directionAfterInput input state.direction ∧
      nextState.snake.position =
        Snake.positionAfterMove Snake.playArea nextState.direction state.snake.position := by
  unfold Snake.step at h
  have hEnded : ¬ state.phase ≠ .playing := by
    simpa [Spec.gameIsRunning] using hRunning
  rw [ite_eq_right hEnded] at h
  by_cases hCollision :
      Snake.positionAfterMove Snake.playArea
          (Snake.directionAfterInput input state.direction) state.snake.position ∈
        state.snake.body
  · rw [ite_eq_left hCollision] at h
    cases h
    simp
  · rw [ite_eq_right hCollision] at h
    by_cases hEating :
        Snake.positionAfterMove Snake.playArea
            (Snake.directionAfterInput input state.direction) state.snake.position =
          state.food
    · rw [ite_eq_left hEating] at h
      simp only [hEating, ite_true] at h
      split at h <;> cases h
      · constructor
        · rfl
        · exact hEating.symm
      · constructor
        · rfl
        · exact hEating.symm
    · rw [ite_eq_right hEating] at h
      cases h
      simp

theorem arrowInputSetsDirection :
    Spec.arrowInputSetsDirection Snake.step := by
  intro input state hRunning
  let nextState := Snake.step input state
  have hDirection :=
    (step_some_direction_and_position input state nextState hRunning rfl).1
  cases input with
  | none =>
    cases direction : state.direction <;>
      simp [nextState, hDirection, direction, Snake.directionAfterInput]
  | some key =>
    cases key <;> cases direction : state.direction <;>
      simp [nextState, hDirection, direction, Snake.directionAfterInput,
        Spec.oppositeDirection]

private theorem positionAfterMove_moves (direction : Direction) (state : GameState) :
    ¬ Spec.isAtEdge direction Snake.playArea state →
      Spec.movesInDirection direction state
        { state with snake :=
          { state.snake with
            position := Snake.positionAfterMove Snake.playArea direction
              state.snake.position } } := by
  cases direction
  · intro h
    by_cases hx : state.snake.position.x = 0 <;>
      simp [Snake.positionAfterMove, Snake.playArea, Spec.isAtEdge,
        Spec.movesInDirection, hx] at h ⊢ <;> omega
  · intro h
    by_cases hy : state.snake.position.y = 0 <;>
      simp [Snake.positionAfterMove, Snake.playArea, Spec.isAtEdge,
        Spec.movesInDirection, hy] at h ⊢ <;> omega
  · intro h
    by_cases hx : state.snake.position.x = 39 <;>
      simp [Snake.positionAfterMove, Snake.playArea, Spec.isAtEdge,
        Spec.movesInDirection, hx] at h ⊢ <;> omega
  · intro h
    by_cases hy : state.snake.position.y = 29 <;>
      simp [Snake.positionAfterMove, Snake.playArea, Spec.isAtEdge,
        Spec.movesInDirection, hy] at h ⊢ <;> omega

theorem movesInDirectionIfNotAtEdge :
    Spec.movesInDirectionIfNotAtEdge Snake.step Snake.playArea := by
  intro input state hRunning
  let nextState := Snake.step input state
  rcases step_some_direction_and_position input state nextState hRunning rfl with
    ⟨hDirection, hPosition⟩
  dsimp only
  intro hNotAtEdge
  have hStepDirection : (Snake.step input state).direction =
      Snake.directionAfterInput input state.direction := by
    exact hDirection
  simp only [hStepDirection] at hNotAtEdge
  have hMoved := positionAfterMove_moves
    (Snake.directionAfterInput input state.direction) state hNotAtEdge
  simpa [nextState, Spec.movesInDirection, hDirection, hPosition] using hMoved

theorem wrapsAtEdge :
    Spec.wrapsAtEdge Snake.step Snake.playArea := by
  intro input state hRunning
  let nextState := Snake.step input state
  rcases step_some_direction_and_position input state nextState hRunning rfl with
    ⟨hDirection, hPosition⟩
  dsimp only
  intro hAtEdge
  cases input with
  | none =>
    cases direction : state.direction <;>
      simp [nextState, hDirection, hPosition, direction, Snake.directionAfterInput,
        Snake.positionAfterMove, Snake.playArea, Spec.isAtEdge] at hAtEdge ⊢ <;>
      first | simp_all | (split at hPosition <;> simp_all)
  | some key =>
    cases key <;> cases direction : state.direction <;>
      simp [nextState, hDirection, hPosition, direction, Snake.directionAfterInput,
        Spec.oppositeDirection, Snake.positionAfterMove, Snake.playArea,
        Spec.isAtEdge] at hAtEdge ⊢ <;>
      first | simp_all | (split at hPosition <;> simp_all)

theorem foodIsInPlayArea_initial :
    Spec.foodIsInPlayArea Snake.initialState Snake.playArea := by
  simp [Spec.foodIsInPlayArea, Spec.isWithinPlayArea,
    Snake.initialState, Snake.playArea]

theorem gameStateInvariant_initial :
    Spec.gameStateInvariant Snake.playArea Snake.initialState := by
  simp [Spec.gameStateInvariant, Spec.foodIsInPlayArea,
    Spec.foodIsNotOnSnake, Spec.snakeIsInPlayArea, Spec.boardIsFull,
    Spec.snakeIsConnected, Spec.segmentsAreConnected,
    Spec.isWithinPlayArea, Snake.initialState, Snake.playArea]

private theorem position_mem_positionsInPlayArea_early (position : Position)
    (hRight : position.x ≤ 39) (hBottom : position.y ≤ 29) :
    position ∈ Snake.positionsInPlayArea Snake.playArea := by
  simp only [Snake.positionsInPlayArea, List.mem_flatMap]
  refine ⟨position.y, by simp [Snake.playArea]; omega, ?_⟩
  refine List.mem_map.mpr ⟨position.x, by simp [Snake.playArea]; omega, ?_⟩
  simp [Snake.playArea]

private theorem positionsInPlayArea_within (position : Position)
    (h : position ∈ Snake.positionsInPlayArea Snake.playArea) :
    Spec.isWithinPlayArea Snake.playArea position := by
  simp only [Snake.positionsInPlayArea, List.mem_flatMap, List.mem_map,
    List.mem_range] at h
  rcases h with ⟨y, hy, x, hx, rfl⟩
  simp only [Snake.playArea] at hy hx ⊢
  simp [Spec.isWithinPlayArea]
  omega

private theorem availableFoodPositionForSnake_spec
    (food position : Position) (snake : Spec.Snake)
    (h : Snake.availableFoodPositionForSnake Snake.playArea food snake =
      some position) :
    Spec.isWithinPlayArea Snake.playArea position ∧
      position ≠ snake.position ∧ position ∉ snake.body := by
  unfold Snake.availableFoodPositionForSnake at h
  let positions := Snake.positionsInPlayArea Snake.playArea
  change
    (positions.find? (fun candidate =>
          Snake.isFreeForSnake candidate snake &&
            decide (candidate.x ≠ food.x ∧ candidate.y ≠ food.y)) <|>
        positions.find? (Snake.isFreeForSnake · snake)) = some position at h
  cases hPreferred :
      positions.find? (fun candidate =>
        Snake.isFreeForSnake candidate snake &&
          decide (candidate.x ≠ food.x ∧ candidate.y ≠ food.y)) with
  | none =>
    have hFallback : positions.find? (Snake.isFreeForSnake · snake) = some position := by
      rw [hPreferred] at h
      simpa [Option.instOrElse, OrElse.orElse, Option.orElse] using h
    have hMem := List.mem_of_find?_eq_some hFallback
    have hPredicate := List.find?_some hFallback
    have hFree := of_decide_eq_true (by simpa [Snake.isFreeForSnake] using hPredicate)
    exact ⟨positionsInPlayArea_within position hMem, hFree⟩
  | some preferred =>
    have hPosition : preferred = position := by
      rw [hPreferred] at h
      simpa [Option.instOrElse, OrElse.orElse, Option.orElse] using h
    subst position
    have hMem := List.mem_of_find?_eq_some hPreferred
    have hPredicate := List.find?_some hPreferred
    have hFree := of_decide_eq_true
      ((Bool.and_eq_true _ _).mp hPredicate).1
    exact ⟨positionsInPlayArea_within preferred hMem,
      by simpa [Snake.isFreeForSnake] using hFree⟩

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

private theorem differentFoodPosition_ne (food : Position) :
    Snake.differentFoodPosition Snake.playArea food ≠ food := by
  let origin : Position := { x := 0, y := 0 }
  let alternate : Position := { x := 1, y := 0 }
  let candidate := if food = origin then alternate else origin
  have hCandidateMem := position_mem_positionsInPlayArea candidate
    (by by_cases hFood : food = origin <;>
      simp [candidate, hFood, origin, alternate])
    (by by_cases hFood : food = origin <;>
      simp [candidate, hFood, origin, alternate])
  have hCandidateNe : candidate ≠ food := by
    by_cases hFood : food = origin
    · simp [candidate, hFood, origin, alternate]
    · intro hEq
      apply hFood
      simpa [candidate, hFood, origin] using hEq.symm
  have hPositionSome :
      ∃ position,
        (Snake.positionsInPlayArea Snake.playArea).find?
          (fun position => decide (position ≠ food)) = some position :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr
      ⟨candidate, hCandidateMem, decide_eq_true hCandidateNe⟩)
  obtain ⟨position, hPosition⟩ := hPositionSome
  simp only [Snake.differentFoodPosition]
  cases hPreferred :
      (Snake.positionsInPlayArea Snake.playArea).find?
        (fun candidate => decide (candidate.x ≠ food.x ∧ candidate.y ≠ food.y)) with
  | some preferred =>
    have hPredicate : preferred.x ≠ food.x ∧ preferred.y ≠ food.y := by
      have hBoolean := List.find?_some
        (p := fun (candidate : Position) =>
          decide (candidate.x ≠ food.x ∧ candidate.y ≠ food.y)) hPreferred
      exact of_decide_eq_true hBoolean
    simp [Option.orElse]
    intro hEqual
    exact hPredicate.1 (congrArg Position.x hEqual)
  | none =>
    have hBoolean := List.find?_some
      (p := fun (candidate : Position) => decide (candidate ≠ food)) hPosition
    have hDifferent := of_decide_eq_true hBoolean
    rw [hPosition]
    exact hDifferent

private theorem differentFoodPosition_inPlayArea (food : Position) :
    Spec.isWithinPlayArea Snake.playArea
      (Snake.differentFoodPosition Snake.playArea food) := by
  simp only [Snake.differentFoodPosition]
  cases hPreferred :
      (Snake.positionsInPlayArea Snake.playArea).find?
        (fun position => decide (position.x ≠ food.x ∧ position.y ≠ food.y)) with
  | some preferred =>
    have hPreferred' :
        (Snake.positionsInPlayArea Snake.playArea).find?
          (fun position =>
            !decide (position.x = food.x) && !decide (position.y = food.y)) =
          some preferred := by simpa using hPreferred
    change Spec.isWithinPlayArea Snake.playArea preferred
    exact positionsInPlayArea_within preferred
      (List.mem_of_find?_eq_some hPreferred)
  | none =>
    have hPreferred' :
        (Snake.positionsInPlayArea Snake.playArea).find?
          (fun position =>
            !decide (position.x = food.x) && !decide (position.y = food.y)) = none := by
      simpa using hPreferred
    cases hFallback :
        (Snake.positionsInPlayArea Snake.playArea).find?
          (fun position => decide (position ≠ food)) with
    | none =>
      have hFallback' :
          (Snake.positionsInPlayArea Snake.playArea).find?
            (fun position => !decide (position = food)) = none := by
        simpa using hFallback
      change Spec.isWithinPlayArea Snake.playArea
        { x := Snake.playArea.leftEdge, y := Snake.playArea.topEdge }
      simp [Spec.isWithinPlayArea, Snake.playArea]
    | some position =>
      have hFallback' :
          (Snake.positionsInPlayArea Snake.playArea).find?
            (fun position => !decide (position = food)) = some position := by
        simpa using hFallback
      change Spec.isWithinPlayArea Snake.playArea position
      exact positionsInPlayArea_within position
        (List.mem_of_find?_eq_some hFallback)

private theorem availableFoodPosition_changesBoth
    (food position : Position) (snake : Spec.Snake)
    (hSelected : Snake.availableFoodPositionForSnake Snake.playArea food snake = some position)
    (hPossible : ∃ candidate,
      Spec.isWithinPlayArea Snake.playArea candidate ∧
      candidate ≠ snake.position ∧ candidate ∉ snake.body ∧
      candidate.x ≠ food.x ∧ candidate.y ≠ food.y) :
    position.x ≠ food.x ∧ position.y ≠ food.y := by
  rcases hPossible with ⟨candidate, hWithin, hHead, hBody, hx, hy⟩
  simp only [Snake.availableFoodPositionForSnake] at hSelected
  cases hPreferred :
      (Snake.positionsInPlayArea Snake.playArea).find?
        (fun candidate => Snake.isFreeForSnake candidate snake &&
          decide (candidate.x ≠ food.x ∧ candidate.y ≠ food.y)) with
  | some preferred =>
    have hPosition : preferred = position := by
      rw [hPreferred] at hSelected
      simp [Option.orElse] at hSelected
      exact hSelected
    subst preferred
    have hPredicate := List.find?_some
      (p := fun (candidate : Position) =>
        Snake.isFreeForSnake candidate snake &&
          decide (candidate.x ≠ food.x ∧ candidate.y ≠ food.y)) hPreferred
    exact of_decide_eq_true ((Bool.and_eq_true _ _).mp hPredicate).2
  | none =>
    have hMem : candidate ∈ Snake.positionsInPlayArea Snake.playArea :=
      position_mem_positionsInPlayArea candidate
        (by simpa [Spec.isWithinPlayArea, Snake.playArea] using hWithin.2.1)
        (by simpa [Spec.isWithinPlayArea, Snake.playArea] using hWithin.2.2.2)
    have hPredicate :
        Snake.isFreeForSnake candidate snake &&
          decide (candidate.x ≠ food.x ∧ candidate.y ≠ food.y) = true := by
      simp [Snake.isFreeForSnake, hHead, hBody, hx, hy]
    have hImpossible := List.find?_eq_none.mp hPreferred candidate hMem hPredicate
    contradiction

private theorem positionAfterMove_within (direction : Direction)
    (position : Position) (h : Spec.isWithinPlayArea Snake.playArea position) :
    Spec.isWithinPlayArea Snake.playArea
      (Snake.positionAfterMove Snake.playArea direction position) := by
  change 0 ≤ position.x ∧ position.x ≤ 39 ∧ 0 ≤ position.y ∧ position.y ≤ 29 at h
  cases direction
  · by_cases hEdge : position.x = 0 <;>
      simp [Spec.isWithinPlayArea, Snake.positionAfterMove,
        Snake.playArea, hEdge] <;> omega
  · by_cases hEdge : position.y = 0 <;>
      simp [Spec.isWithinPlayArea, Snake.positionAfterMove,
        Snake.playArea, hEdge] <;> omega
  · by_cases hEdge : position.x = 39 <;>
      simp [Spec.isWithinPlayArea, Snake.positionAfterMove,
        Snake.playArea, hEdge] <;> omega
  · by_cases hEdge : position.y = 29 <;>
      simp [Spec.isWithinPlayArea, Snake.positionAfterMove,
        Snake.playArea, hEdge] <;> omega

private theorem positionAfterMove_adjacent (direction : Direction)
    (position : Position) :
    Spec.positionsAreAdjacent Snake.playArea position
      (Snake.positionAfterMove Snake.playArea direction position) := by
  cases direction
  · by_cases hEdge : position.x = 0 <;>
      simp [Spec.positionsAreAdjacent, Snake.positionAfterMove,
        Snake.playArea, hEdge] <;> omega
  · by_cases hEdge : position.y = 0 <;>
      simp [Spec.positionsAreAdjacent, Snake.positionAfterMove,
        Snake.playArea, hEdge] <;> omega
  · by_cases hEdge : position.x = 39 <;>
      simp [Spec.positionsAreAdjacent, Snake.positionAfterMove,
        Snake.playArea, hEdge] <;> omega
  · by_cases hEdge : position.y = 29 <;>
      simp [Spec.positionsAreAdjacent, Snake.positionAfterMove,
        Snake.playArea, hEdge] <;> omega

private theorem segmentsAreConnected_dropLast
    (previous : Position) (segments : List Position)
    (h : Spec.segmentsAreConnected Snake.playArea previous segments) :
    Spec.segmentsAreConnected Snake.playArea previous segments.dropLast := by
  induction segments generalizing previous with
  | nil => simp [Spec.segmentsAreConnected]
  | cons segment remaining ih =>
    cases remaining with
    | nil => simp [Spec.segmentsAreConnected]
    | cons next rest =>
      rcases h with ⟨hFirst, hRest⟩
      simp only [List.dropLast_cons_cons, Spec.segmentsAreConnected]
      exact ⟨hFirst, ih segment hRest⟩

private theorem positionsAreAdjacent_symm
    (area : PlayArea) (left right : Position)
    (h : Spec.positionsAreAdjacent area left right) :
    Spec.positionsAreAdjacent area right left := by
  unfold Spec.positionsAreAdjacent at h ⊢
  rcases h with ⟨hSameY, hX⟩ | ⟨hSameX, hY⟩
  · left
    exact ⟨hSameY.symm, hX.elim (fun h => Or.inr (Or.inl h))
      (fun h => h.elim (fun h => Or.inl h) (fun h => h.elim
        (fun h => Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩)))
        (fun h => Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩)))))⟩
  · right
    exact ⟨hSameX.symm, hY.elim (fun h => Or.inr (Or.inl h))
      (fun h => h.elim (fun h => Or.inl h) (fun h => h.elim
        (fun h => Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩)))
        (fun h => Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩)))))⟩

private theorem snakeAfterMove_inPlayArea
    (direction : Direction) (snake : Spec.Snake) (eating : Bool)
    (h : Spec.snakeIsInPlayArea Snake.playArea snake) :
    Spec.snakeIsInPlayArea Snake.playArea
      { position := Snake.positionAfterMove Snake.playArea direction snake.position,
        body := if eating then snake.position :: snake.body
          else if snake.body.isEmpty then []
          else snake.position :: snake.body.dropLast } := by
  refine ⟨positionAfterMove_within direction snake.position h.1, ?_⟩
  intro position hPosition
  by_cases hEating : eating
  · simp only [ite_eq_left hEating, List.mem_cons] at hPosition
    rcases hPosition with rfl | hPosition
    · exact h.1
    · exact h.2 position hPosition
  · simp only [ite_eq_right hEating] at hPosition
    by_cases hEmpty : snake.body.isEmpty
    · simp [hEmpty] at hPosition
    · simp only [ite_eq_right hEmpty, List.mem_cons] at hPosition
      rcases hPosition with rfl | hPosition
      · exact h.1
      · exact h.2 position (List.dropLast_subset snake.body hPosition)

private theorem snakeAfterMove_connected
    (direction : Direction) (snake : Spec.Snake) (eating : Bool)
    (h : Spec.snakeIsConnected Snake.playArea snake) :
    Spec.snakeIsConnected Snake.playArea
      { position := Snake.positionAfterMove Snake.playArea direction snake.position,
        body := if eating then snake.position :: snake.body
          else if snake.body.isEmpty then []
          else snake.position :: snake.body.dropLast } := by
  by_cases hEating : eating
  · simp only [ite_eq_left hEating, Spec.snakeIsConnected, Spec.segmentsAreConnected]
    exact ⟨positionsAreAdjacent_symm Snake.playArea snake.position
      (Snake.positionAfterMove Snake.playArea direction snake.position)
      (positionAfterMove_adjacent direction snake.position), h⟩
  · simp only [ite_eq_right hEating]
    by_cases hEmpty : snake.body.isEmpty
    · simp [hEmpty, Spec.snakeIsConnected, Spec.segmentsAreConnected]
    · simp only [ite_eq_right hEmpty, Spec.snakeIsConnected, Spec.segmentsAreConnected]
      exact ⟨positionsAreAdjacent_symm Snake.playArea snake.position
        (Snake.positionAfterMove Snake.playArea direction snake.position)
        (positionAfterMove_adjacent direction snake.position),
        segmentsAreConnected_dropLast snake.position snake.body h⟩

private theorem snakeFillsPlayArea_iff
    (snake : Spec.Snake) :
    Snake.snakeFillsPlayArea Snake.playArea snake = true ↔
      Spec.boardIsFull Snake.playArea snake := by
  unfold Snake.snakeFillsPlayArea Spec.boardIsFull
  rw [List.all_eq_true]
  constructor
  · intro hAll position hWithin
    exact of_decide_eq_true (hAll position
      (position_mem_positionsInPlayArea position
        (by simpa [Spec.isWithinPlayArea, Snake.playArea] using hWithin.2.1)
        (by simpa [Spec.isWithinPlayArea, Snake.playArea] using hWithin.2.2.2)))
  · intro hFull position hMem
    apply decide_eq_true
    exact hFull position (positionsInPlayArea_within position hMem)

private theorem availableFoodPosition_none_iff_full
    (food : Position) (snake : Spec.Snake) :
    Snake.availableFoodPositionForSnake Snake.playArea food snake = none ↔
      Spec.boardIsFull Snake.playArea snake := by
  let positions := Snake.positionsInPlayArea Snake.playArea
  constructor
  · intro hNone position hWithin
    have hMem := position_mem_positionsInPlayArea position
      (by simpa [Spec.isWithinPlayArea, Snake.playArea] using hWithin.2.1)
      (by simpa [Spec.isWithinPlayArea, Snake.playArea] using hWithin.2.2.2)
    have hFallbackNone : positions.find? (Snake.isFreeForSnake · snake) = none := by
      unfold Snake.availableFoodPositionForSnake at hNone
      change
        (positions.find? (fun candidate =>
              Snake.isFreeForSnake candidate snake &&
                decide (candidate.x ≠ food.x ∧ candidate.y ≠ food.y)) <|>
            positions.find? (Snake.isFreeForSnake · snake)) = none at hNone
      cases hPreferred :
          positions.find? (fun candidate =>
            Snake.isFreeForSnake candidate snake &&
              decide (candidate.x ≠ food.x ∧ candidate.y ≠ food.y)) with
      | none =>
        rw [hPreferred] at hNone
        simpa [Option.instOrElse, OrElse.orElse, Option.orElse] using hNone
      | some preferred =>
        rw [hPreferred] at hNone
        simp [Option.orElse] at hNone
    rw [List.find?_eq_none] at hFallbackNone
    have hNotFree := hFallbackNone position hMem
    by_cases hHead : position = snake.position
    · exact Or.inl hHead
    · by_cases hBody : position ∈ snake.body
      · exact Or.inr hBody
      · exfalso
        apply hNotFree
        simp [Snake.isFreeForSnake, hHead, hBody]
  · intro hFull
    have hNoFree (position : Position) (hMem : position ∈ positions) :
        ¬ Snake.isFreeForSnake position snake = true := by
      have hWithin := positionsInPlayArea_within position hMem
      intro hFree
      have hFreeProp := of_decide_eq_true
        (by simpa [Snake.isFreeForSnake] using hFree)
      rcases hFull position hWithin with hHead | hBody
      · exact hFreeProp.1 hHead
      · exact hFreeProp.2 hBody
    have hPreferredNone :
        positions.find? (fun candidate =>
          Snake.isFreeForSnake candidate snake &&
            decide (candidate.x ≠ food.x ∧ candidate.y ≠ food.y)) = none := by
      rw [List.find?_eq_none]
      intro position hMem hPredicate
      have hFree := ((Bool.and_eq_true _ _).mp hPredicate).1
      exact hNoFree position hMem hFree
    have hFallbackNone :
        positions.find? (Snake.isFreeForSnake · snake) = none := by
      rw [List.find?_eq_none]
      exact hNoFree
    unfold Snake.availableFoodPositionForSnake
    change
      (positions.find? (fun candidate =>
            Snake.isFreeForSnake candidate snake &&
              decide (candidate.x ≠ food.x ∧ candidate.y ≠ food.y)) <|>
          positions.find? (Snake.isFreeForSnake · snake)) = none
    rw [hPreferredNone, hFallbackNone]
    rfl

theorem foodIsInPlayArea_step (input : Option PlayerInput) (state : GameState)
    (h : Spec.foodIsInPlayArea state Snake.playArea) :
    Spec.foodIsInPlayArea (Snake.step input state) Snake.playArea := by
  unfold Snake.step
  by_cases hEnded : state.phase ≠ .playing
  · simpa [hEnded] using h
  simp only [ite_eq_right hEnded]
  let direction := Snake.directionAfterInput input state.direction
  let intendedPosition :=
    Snake.positionAfterMove Snake.playArea direction state.snake.position
  let body := if intendedPosition = state.food then
      state.snake.position :: state.snake.body
    else if state.snake.body.isEmpty then [] else
      state.snake.position :: state.snake.body.dropLast
  let snake : Spec.Snake := { position := intendedPosition, body := body }
  by_cases hCollision : intendedPosition ∈ state.snake.body
  · rw [ite_eq_left hCollision]
    by_cases hEating : intendedPosition = state.food
    · have hEatingRaw :
        Snake.positionAfterMove Snake.playArea
          (Snake.directionAfterInput input state.direction) state.snake.position = state.food :=
        by simpa [direction, intendedPosition] using hEating
      cases hAvailable :
        Snake.availableFoodPositionForSnake Snake.playArea state.food snake with
      | none =>
        simpa [Spec.foodIsInPlayArea, direction, intendedPosition, body, snake,
          hEatingRaw, hAvailable] using differentFoodPosition_inPlayArea state.food
      | some food =>
        simpa [Spec.foodIsInPlayArea, direction, intendedPosition, body, snake,
          hEatingRaw, hAvailable] using
          (availableFoodPositionForSnake_spec state.food food snake hAvailable).1
    · have hEatingRaw :
        Snake.positionAfterMove Snake.playArea
          (Snake.directionAfterInput input state.direction) state.snake.position ≠ state.food :=
        by simpa [direction, intendedPosition] using hEating
      simpa [Spec.foodIsInPlayArea, hEatingRaw] using h
  · rw [ite_eq_right hCollision]
    by_cases hEating : intendedPosition = state.food
    · have hEatingRaw :
        Snake.positionAfterMove Snake.playArea
          (Snake.directionAfterInput input state.direction) state.snake.position = state.food :=
        by simpa [direction, intendedPosition] using hEating
      cases hAvailable :
        Snake.availableFoodPositionForSnake Snake.playArea state.food snake with
      | none => simpa [Spec.foodIsInPlayArea, hEatingRaw, hAvailable] using h
      | some food =>
        simpa [Spec.foodIsInPlayArea, hEatingRaw, hAvailable] using
          (availableFoodPositionForSnake_spec state.food food snake hAvailable).1
    · have hEatingRaw :
        Snake.positionAfterMove Snake.playArea
          (Snake.directionAfterInput input state.direction) state.snake.position ≠ state.food :=
        by simpa [direction, intendedPosition] using hEating
      simpa [Spec.foodIsInPlayArea, hEatingRaw] using h

theorem foodIsNotOnSnake_step (input : Option PlayerInput) (state : GameState)
    (h : Spec.foodIsNotOnSnake state) :
    Spec.foodIsNotOnSnake (Snake.step input state) := by
  unfold Snake.step
  by_cases hEnded : state.phase ≠ .playing
  · simpa [hEnded] using h
  simp only [ite_eq_right hEnded]
  have hPlaying : state.phase = .playing := by
    simpa using hEnded
  have hFood : state.food ≠ state.snake.position ∧
      state.food ∉ state.snake.body := by
    rcases h with hWon | hFood
    · simp [hPlaying] at hWon
    · exact hFood
  let direction := Snake.directionAfterInput input state.direction
  let intendedPosition := Snake.positionAfterMove Snake.playArea direction state.snake.position
  let body := if intendedPosition = state.food then
      state.snake.position :: state.snake.body
    else if state.snake.body.isEmpty then [] else
      state.snake.position :: state.snake.body.dropLast
  let snake : Spec.Snake := { position := intendedPosition, body := body }
  by_cases hCollision : intendedPosition ∈ state.snake.body
  · rw [ite_eq_left hCollision]
    by_cases hEating : intendedPosition = state.food
    · exact (hFood.2 (hEating ▸ hCollision)).elim
    · right
      have hHead : state.food ≠
          Snake.positionAfterMove Snake.playArea
            (Snake.directionAfterInput input state.direction) state.snake.position := by
        simpa [direction, intendedPosition] using Ne.symm hEating
      have hDropLast : state.food ∉ state.snake.body.dropLast := by
        intro hMem
        exact hFood.2 ((List.dropLast_sublist state.snake.body).subset hMem)
      simp [direction, intendedPosition, hEating, hHead, hDropLast, hFood.1]
  · rw [ite_eq_right hCollision]
    by_cases hEating : intendedPosition = state.food
    · rw [ite_eq_left hEating]
      cases hAvailable :
          Snake.availableFoodPositionForSnake Snake.playArea state.food snake with
      | none =>
        simp [Spec.foodIsNotOnSnake, direction, intendedPosition, hEating]
      | some food =>
        have hSelected := availableFoodPositionForSnake_spec state.food food snake hAvailable
        simpa [Spec.foodIsNotOnSnake, direction, intendedPosition, body, snake,
          hEating, hAvailable, hPlaying] using hSelected.2
    · rw [ite_eq_right hEating]
      have hEatingRaw :
          Snake.positionAfterMove Snake.playArea
              (Snake.directionAfterInput input state.direction) state.snake.position ≠
            state.food := by
        simpa [direction, intendedPosition] using hEating
      simp only [hEatingRaw, ite_false]
      by_cases hFull : Snake.snakeFillsPlayArea Snake.playArea
          { position := Snake.positionAfterMove Snake.playArea
              (Snake.directionAfterInput input state.direction) state.snake.position,
            body := if state.snake.body.isEmpty then [] else
              state.snake.position :: state.snake.body.dropLast } = true
      · rw [ite_eq_left hFull]
        simp [Spec.foodIsNotOnSnake]
      · rw [ite_eq_right hFull]
        right
        have hHead : state.food ≠
            Snake.positionAfterMove Snake.playArea
              (Snake.directionAfterInput input state.direction) state.snake.position := by
          exact Ne.symm hEatingRaw
        have hDropLast : state.food ∉ state.snake.body.dropLast := by
          intro hMem
          exact hFood.2 ((List.dropLast_sublist state.snake.body).subset hMem)
        simp [hHead, hDropLast, hFood.1]

theorem foodMovesWhenEaten :
    Spec.foodMovesWhenEaten Snake.step := by
  intro input state hRunning
  dsimp only
  intro hEaten
  let direction := Snake.directionAfterInput input state.direction
  let intendedPosition := Snake.positionAfterMove Snake.playArea direction state.snake.position
  let body := if intendedPosition = state.food then
      state.snake.position :: state.snake.body
    else if state.snake.body.isEmpty then [] else
      state.snake.position :: state.snake.body.dropLast
  let snake : Spec.Snake := { position := intendedPosition, body := body }
  have hNotEnded : ¬ state.phase ≠ .playing := by
    simpa [Spec.gameIsRunning] using hRunning
  rcases step_some_direction_and_position input state (Snake.step input state)
      hRunning rfl with ⟨hDirection, hPosition⟩
  unfold Spec.foodIsEaten at hEaten
  have hEatingRaw :
      Snake.positionAfterMove Snake.playArea direction state.snake.position = state.food := by
    rw [hDirection] at hPosition
    calc
      Snake.positionAfterMove Snake.playArea direction state.snake.position =
          (Snake.step input state).snake.position := by
            simpa [direction] using hPosition.symm
      _ = state.food := hEaten
  unfold Snake.step
  rw [ite_eq_right hNotEnded]
  have hPlaying : state.phase = .playing := hRunning
  by_cases hCollision : intendedPosition ∈ state.snake.body
  · have hCollisionRaw :
        Snake.positionAfterMove Snake.playArea direction state.snake.position ∈ state.snake.body :=
      by simpa [direction, intendedPosition] using hCollision
    rw [ite_eq_left hCollisionRaw]
    cases hAvailable : Snake.availableFoodPositionForSnake Snake.playArea state.food snake with
    | none =>
      simp [direction, hEatingRaw]
      intro hSame
      exact (differentFoodPosition_ne state.food) hSame
    | some food =>
      have hFood := availableFoodPositionForSnake_spec state.food food snake hAvailable
      simp [direction, hEatingRaw]
      simpa [snake, intendedPosition, hEatingRaw] using hFood.2.1
  · have hCollisionRaw :
        Snake.positionAfterMove Snake.playArea direction state.snake.position ∉ state.snake.body :=
      by simpa [direction, intendedPosition] using hCollision
    rw [ite_eq_right hCollisionRaw]
    cases hAvailable : Snake.availableFoodPositionForSnake Snake.playArea state.food snake with
    | none =>
      simp [direction, hEatingRaw]
    | some food =>
      have hFood := availableFoodPositionForSnake_spec state.food food snake hAvailable
      simp [direction, hPlaying, hEatingRaw]
      simpa [snake, intendedPosition, hEatingRaw] using hFood.2.1

theorem snakeGrowsWhenEating :
    Spec.snakeGrowsWhenEating Snake.step := by
  intro input state hRunning
  dsimp only
  intro hEaten
  unfold Spec.foodIsEaten at hEaten
  rcases step_some_direction_and_position input state (Snake.step input state)
      hRunning rfl with ⟨hDirection, hPosition⟩
  have hEating :
      Snake.positionAfterMove Snake.playArea
          (Snake.directionAfterInput input state.direction) state.snake.position =
        state.food := by
    rw [hDirection] at hPosition
    calc
      Snake.positionAfterMove Snake.playArea
            (Snake.directionAfterInput input state.direction) state.snake.position =
          (Snake.step input state).snake.position := hPosition.symm
      _ = state.food := hEaten
  have hNotEnded : ¬ state.phase ≠ .playing := by
    simpa [Spec.gameIsRunning] using hRunning
  unfold Snake.step
  rw [ite_eq_right hNotEnded]
  by_cases hCollision :
      Snake.positionAfterMove Snake.playArea
          (Snake.directionAfterInput input state.direction) state.snake.position ∈
        state.snake.body
  · rw [ite_eq_left hCollision]
    simp [hEating]
  · rw [ite_eq_right hCollision]
    by_cases hEats :
        Snake.positionAfterMove Snake.playArea
            (Snake.directionAfterInput input state.direction) state.snake.position =
          state.food
    · cases hAvailable :
        Snake.availableFoodPositionForSnake Snake.playArea state.food
          { position := state.food,
            body := state.snake.position :: state.snake.body }
      · simp [hEats, hAvailable]
      · simp [hEats, hAvailable]
    · exact (hEats hEating).elim

theorem foodChangesBothCoordinatesWhenPossible :
    Spec.foodChangesBothCoordinatesWhenPossible Snake.step Snake.playArea := by
  intro input state hRunning
  dsimp only
  intro hEaten hNotWon hPossible
  let direction := Snake.directionAfterInput input state.direction
  let intendedPosition := Snake.positionAfterMove Snake.playArea direction state.snake.position
  let body : List Position := if intendedPosition = state.food then
      state.snake.position :: state.snake.body
    else if state.snake.body.isEmpty then [] else
      state.snake.position :: state.snake.body.dropLast
  let snake : Spec.Snake := { position := intendedPosition, body := body }
  have hNotEnded : ¬ state.phase ≠ .playing := by
    simpa [Spec.gameIsRunning] using hRunning
  rcases step_some_direction_and_position input state (Snake.step input state)
      hRunning rfl with ⟨hDirection, hPosition⟩
  unfold Spec.foodIsEaten at hEaten
  have hEatingRaw :
      Snake.positionAfterMove Snake.playArea direction state.snake.position = state.food := by
    rw [hPosition, hDirection] at hEaten
    simpa [direction] using hEaten
  have hEatingMove :
      Snake.positionAfterMove Snake.playArea
          (Snake.directionAfterInput input state.direction) state.snake.position = state.food := by
    simpa [direction] using hEatingRaw
  unfold Snake.step at hPossible hNotWon ⊢
  rw [ite_eq_right hNotEnded] at hPossible hNotWon ⊢
  by_cases hCollision : intendedPosition ∈ state.snake.body
  · have hCollisionRaw :
        Snake.positionAfterMove Snake.playArea direction state.snake.position ∈ state.snake.body :=
      by simpa [direction, intendedPosition] using hCollision
    rw [ite_eq_left hCollisionRaw] at hPossible hNotWon ⊢
    rw [ite_eq_left hEatingRaw] at hPossible hNotWon ⊢
    cases hAvailable : Snake.availableFoodPositionForSnake Snake.playArea state.food snake with
    | some food =>
      have hPossibleSnake : ∃ candidate,
          Spec.isWithinPlayArea Snake.playArea candidate ∧
            candidate ≠ snake.position ∧ candidate ∉ snake.body ∧
            candidate.x ≠ state.food.x ∧ candidate.y ≠ state.food.y := by
        simpa [direction, intendedPosition, body, snake, hEatingRaw] using hPossible
      have hBoth := availableFoodPosition_changesBoth state.food food snake
        hAvailable hPossibleSnake
      have hSelected :
          (Snake.availableFoodPositionForSnake Snake.playArea state.food snake).getD
              (Snake.differentFoodPosition Snake.playArea state.food) = food := by
        simp [hAvailable]
      have hSelectedRaw :
          (Snake.availableFoodPositionForSnake Snake.playArea state.food
              { position := Snake.positionAfterMove Snake.playArea
                  (Snake.directionAfterInput input state.direction) state.snake.position,
                body := state.snake.position :: state.snake.body }).getD
            (Snake.differentFoodPosition Snake.playArea state.food) = food := by
        simpa [direction, intendedPosition, body, snake, hEatingMove] using hSelected
      have hSelectedAtFood :
          (Snake.availableFoodPositionForSnake Snake.playArea state.food
              { position := state.food,
                body := state.snake.position :: state.snake.body }).getD
            (Snake.differentFoodPosition Snake.playArea state.food) = food := by
        simpa [hEatingMove] using hSelectedRaw
      simpa [hEatingMove, hSelectedAtFood] using hBoth
    | none =>
      have hFull := (availableFoodPosition_none_iff_full state.food snake).mp hAvailable
      have hPossibleSnake : ∃ candidate,
          Spec.isWithinPlayArea Snake.playArea candidate ∧
            candidate ≠ snake.position ∧ candidate ∉ snake.body ∧
            candidate.x ≠ state.food.x ∧ candidate.y ≠ state.food.y := by
        simpa [direction, intendedPosition, body, snake, hEatingRaw] using hPossible
      rcases hPossibleSnake with ⟨candidate, hWithin, hHead, hBody, hx, hy⟩
      rcases hFull candidate hWithin with hHead' | hBody'
      · exact (hHead hHead').elim
      · exact (hBody hBody').elim
  · have hCollisionRaw :
        Snake.positionAfterMove Snake.playArea direction state.snake.position ∉ state.snake.body :=
      by simpa [direction, intendedPosition] using hCollision
    rw [ite_eq_right hCollisionRaw] at hPossible hNotWon ⊢
    rw [ite_eq_left hEatingRaw] at hPossible hNotWon ⊢
    cases hAvailable : Snake.availableFoodPositionForSnake Snake.playArea state.food snake with
    | some food =>
      have hAvailableRaw :
          Snake.availableFoodPositionForSnake Snake.playArea state.food
            { position := state.food,
              body := state.snake.position :: state.snake.body } = some food := by
        simpa [direction, intendedPosition, body, snake, hEatingRaw] using hAvailable
      have hPossibleSnake : ∃ candidate,
          Spec.isWithinPlayArea Snake.playArea candidate ∧
            candidate ≠ snake.position ∧ candidate ∉ snake.body ∧
            candidate.x ≠ state.food.x ∧ candidate.y ≠ state.food.y := by
        simpa [direction, intendedPosition, body, snake, hEatingRaw, hAvailableRaw] using hPossible
      have hBoth := availableFoodPosition_changesBoth state.food food snake
        hAvailable hPossibleSnake
      simpa [direction, intendedPosition, body, snake, hEatingRaw, hAvailable] using hBoth
    | none =>
      have hAvailableRaw :
          Snake.availableFoodPositionForSnake Snake.playArea state.food
            { position := state.food,
              body := state.snake.position :: state.snake.body } = none := by
        simpa [direction, intendedPosition, body, snake, hEatingRaw] using hAvailable
      simp [hEatingMove, hAvailableRaw] at hNotWon

private theorem gameEndsOnSelfCollision :
    Spec.gameEndsOnSelfCollision Snake.step := by
  intro input state hRunning
  dsimp only
  intro hCollision
  have hNotEnded : ¬ state.phase ≠ .playing := by
    simpa [Spec.gameIsRunning] using hRunning
  rcases step_some_direction_and_position input state (Snake.step input state)
      hRunning rfl with ⟨hDirection, hPosition⟩
  have hCollisionRaw :
      Snake.positionAfterMove Snake.playArea
          (Snake.directionAfterInput input state.direction) state.snake.position ∈
        state.snake.body := by
    unfold Spec.snakeCollides at hCollision
    rw [hDirection] at hPosition
    simpa [hPosition] using hCollision
  unfold Snake.step
  rw [ite_eq_right hNotEnded, ite_eq_left hCollisionRaw]

private theorem gameHasNoStepAfterEnd :
    Spec.gameHasNoStepAfterEnd Snake.step := by
  intro input state hEnded
  unfold Snake.step
  rw [ite_eq_left]
  simpa [Spec.gameIsRunning] using hEnded

private theorem gameEndsWhenPlayAreaIsFull :
    Spec.gameEndsWhenPlayAreaIsFull Snake.step Snake.playArea := by
  intro input state hRunning
  dsimp only
  intro hSafe
  let direction := Snake.directionAfterInput input state.direction
  let intendedPosition := Snake.positionAfterMove Snake.playArea direction state.snake.position
  let body : List Position := if intendedPosition = state.food then
      state.snake.position :: state.snake.body
    else if state.snake.body.isEmpty then [] else
      state.snake.position :: state.snake.body.dropLast
  let snake : Spec.Snake := { position := intendedPosition, body := body }
  have hNotEnded : ¬ state.phase ≠ .playing := by
    simpa [Spec.gameIsRunning] using hRunning
  rcases step_some_direction_and_position input state (Snake.step input state)
      hRunning rfl with ⟨hDirection, hPosition⟩
  have hCollision : intendedPosition ∉ state.snake.body := by
    unfold Spec.snakeCollides at hSafe
    rw [hDirection] at hPosition
    simpa [direction, intendedPosition, hPosition] using hSafe
  unfold Snake.step
  rw [ite_eq_right hNotEnded]
  have hCollisionRaw :
      Snake.positionAfterMove Snake.playArea
          (Snake.directionAfterInput input state.direction) state.snake.position ∉
        state.snake.body := by
    simpa [direction, intendedPosition] using hCollision
  rw [ite_eq_right hCollisionRaw]
  by_cases hEating : intendedPosition = state.food
  · have hEatingRaw :
        Snake.positionAfterMove Snake.playArea
            (Snake.directionAfterInput input state.direction) state.snake.position =
          state.food := by
      simpa [direction, intendedPosition] using hEating
    rw [ite_eq_left hEatingRaw]
    cases hAvailableRaw :
        Snake.availableFoodPositionForSnake Snake.playArea state.food
          { position := Snake.positionAfterMove Snake.playArea
              (Snake.directionAfterInput input state.direction) state.snake.position,
            body := state.snake.position :: state.snake.body } with
    | some food =>
      have hAvailable :
          Snake.availableFoodPositionForSnake Snake.playArea state.food snake = some food := by
        simpa [direction, intendedPosition, body, snake, hEating] using hAvailableRaw
      have hAvailableFood :
          Snake.availableFoodPositionForSnake Snake.playArea state.food
              { position := state.food,
                body := state.snake.position :: state.snake.body } = some food := by
        simpa [hEatingRaw] using hAvailableRaw
      have hFood := availableFoodPositionForSnake_spec state.food food snake hAvailable
      have hNotFull : ¬ Spec.boardIsFull Snake.playArea snake := by
        intro hFull
        rcases hFull food hFood.1 with hHead | hBody
        · exact hFood.2.1 hHead
        · exact hFood.2.2 hBody
      have hSnake : snake = { position := state.food, body := state.snake.position :: state.snake.body } := by
        simp [snake, intendedPosition, direction, body, hEating]
      have hPhasePlaying : state.phase = .playing := by
        simpa [Spec.gameIsRunning] using hRunning
      constructor
      · constructor
        · intro hWon
          simp [hEatingRaw, hAvailableFood, hPhasePlaying] at hWon
        · intro hFull
          have hBoard : Spec.boardIsFull Snake.playArea snake := by
            simpa [hEatingRaw, hAvailableFood, hSnake] using hFull
          exact (hNotFull hBoard).elim
      · simp [hEatingRaw, hAvailableFood, hPhasePlaying]
    | none =>
      have hAvailable :
          Snake.availableFoodPositionForSnake Snake.playArea state.food snake = none := by
        simpa [direction, intendedPosition, body, snake, hEating] using hAvailableRaw
      have hAvailableFood :
          Snake.availableFoodPositionForSnake Snake.playArea state.food
              { position := state.food,
                body := state.snake.position :: state.snake.body } = none := by
        simpa [hEatingRaw] using hAvailableRaw
      have hFull := (availableFoodPosition_none_iff_full state.food snake).mp hAvailable
      have hSnake : snake = { position := state.food, body := state.snake.position :: state.snake.body } := by
        simp [snake, intendedPosition, direction, body, hEating]
      rw [hSnake] at hFull
      simp [hEatingRaw, hAvailableFood, hFull]
  · have hEatingRaw :
        Snake.positionAfterMove Snake.playArea
            (Snake.directionAfterInput input state.direction) state.snake.position ≠
          state.food := by
      simpa [direction, intendedPosition] using hEating
    rw [ite_eq_right hEatingRaw]
    simp only [hEatingRaw, ite_false]
    by_cases hFull : Spec.boardIsFull Snake.playArea
        { position := Snake.positionAfterMove Snake.playArea
            (Snake.directionAfterInput input state.direction) state.snake.position,
          body := if state.snake.body = [] then [] else
            state.snake.position :: state.snake.body.dropLast }
    · have hFills : Snake.snakeFillsPlayArea Snake.playArea
          { position := Snake.positionAfterMove Snake.playArea
              (Snake.directionAfterInput input state.direction) state.snake.position,
            body := if state.snake.body = [] then [] else
              state.snake.position :: state.snake.body.dropLast } = true :=
        (snakeFillsPlayArea_iff _).mpr hFull
      simp [hFills, hFull]
    · have hNotFills : Snake.snakeFillsPlayArea Snake.playArea
          { position := Snake.positionAfterMove Snake.playArea
              (Snake.directionAfterInput input state.direction) state.snake.position,
            body := if state.snake.body = [] then [] else
              state.snake.position :: state.snake.body.dropLast } ≠ true := by
        intro hFills
        exact hFull ((snakeFillsPlayArea_iff _).mp hFills)
      simp [hNotFills, hFull]

theorem snakeIsInPlayArea_step (input : Option PlayerInput) (state : GameState)
    (h : Spec.snakeIsInPlayArea Snake.playArea state.snake) :
    Spec.snakeIsInPlayArea Snake.playArea (Snake.step input state).snake := by
  unfold Snake.step
  by_cases hEnded : state.phase ≠ .playing
  · simpa [hEnded] using h
  simp only [ite_eq_right hEnded]
  let direction := Snake.directionAfterInput input state.direction
  let intendedPosition := Snake.positionAfterMove Snake.playArea direction state.snake.position
  let body := if intendedPosition = state.food then state.snake.position :: state.snake.body
    else if state.snake.body.isEmpty then []
    else state.snake.position :: state.snake.body.dropLast
  let snake : Spec.Snake := { position := intendedPosition, body := body }
  by_cases hCollision : intendedPosition ∈ state.snake.body
  · rw [ite_eq_left hCollision]
    by_cases hEating : intendedPosition = state.food
    · rw [ite_eq_left hEating]
      cases hAvailable : Snake.availableFoodPositionForSnake Snake.playArea state.food snake <;>
        simpa [direction, intendedPosition, body, snake, hEating, hAvailable] using
          snakeAfterMove_inPlayArea direction state.snake true h
    · rw [ite_eq_right hEating]
      simpa [direction, intendedPosition, body, snake, hEating] using
        snakeAfterMove_inPlayArea direction state.snake false h
  · rw [ite_eq_right hCollision]
    by_cases hEating : intendedPosition = state.food
    · rw [ite_eq_left hEating]
      cases hAvailable : Snake.availableFoodPositionForSnake Snake.playArea state.food snake <;>
        simpa [direction, intendedPosition, body, snake, hEating, hAvailable] using
          snakeAfterMove_inPlayArea direction state.snake true h
    · rw [ite_eq_right hEating]
      by_cases hFull : Snake.snakeFillsPlayArea Snake.playArea snake = true <;>
        simpa [direction, intendedPosition, body, snake, hEating, hFull] using
          snakeAfterMove_inPlayArea direction state.snake false h

theorem snakeIsConnected_step (input : Option PlayerInput) (state : GameState)
    (h : Spec.snakeIsConnected Snake.playArea state.snake) :
    Spec.snakeIsConnected Snake.playArea (Snake.step input state).snake := by
  unfold Snake.step
  by_cases hEnded : state.phase ≠ .playing
  · simpa [hEnded] using h
  simp only [ite_eq_right hEnded]
  let direction := Snake.directionAfterInput input state.direction
  let intendedPosition := Snake.positionAfterMove Snake.playArea direction state.snake.position
  let body := if intendedPosition = state.food then state.snake.position :: state.snake.body
    else if state.snake.body.isEmpty then []
    else state.snake.position :: state.snake.body.dropLast
  let snake : Spec.Snake := { position := intendedPosition, body := body }
  by_cases hCollision : intendedPosition ∈ state.snake.body
  · rw [ite_eq_left hCollision]
    by_cases hEating : intendedPosition = state.food
    · rw [ite_eq_left hEating]
      cases hAvailable : Snake.availableFoodPositionForSnake Snake.playArea state.food snake <;>
        simpa [direction, intendedPosition, body, snake, hEating, hAvailable] using
          snakeAfterMove_connected direction state.snake true h
    · rw [ite_eq_right hEating]
      simpa [direction, intendedPosition, body, snake, hEating] using
        snakeAfterMove_connected direction state.snake false h
  · rw [ite_eq_right hCollision]
    by_cases hEating : intendedPosition = state.food
    · rw [ite_eq_left hEating]
      cases hAvailable : Snake.availableFoodPositionForSnake Snake.playArea state.food snake <;>
        simpa [direction, intendedPosition, body, snake, hEating, hAvailable] using
          snakeAfterMove_connected direction state.snake true h
    · rw [ite_eq_right hEating]
      by_cases hFull : Snake.snakeFillsPlayArea Snake.playArea snake = true <;>
        simpa [direction, intendedPosition, body, snake, hEating, hFull] using
          snakeAfterMove_connected direction state.snake false h

theorem wonImpliesBoardIsFull_step
    (input : Option PlayerInput) (state : GameState)
    (h : state.phase = .won → Spec.boardIsFull Snake.playArea state.snake) :
    (Snake.step input state).phase = .won →
      Spec.boardIsFull Snake.playArea (Snake.step input state).snake := by
  intro hWon
  by_cases hRunning : Spec.gameIsRunning state
  · have hSafe : ¬ Spec.snakeCollides state.snake
        (Snake.step input state).snake.position := by
      intro hCollision
      have hLost := gameEndsOnSelfCollision input state hRunning hCollision
      simp [hWon] at hLost
    exact (gameEndsWhenPlayAreaIsFull input state hRunning hSafe).1.1 hWon
  · have hSame := gameHasNoStepAfterEnd input state hRunning
    rw [hSame] at hWon ⊢
    exact h hWon

theorem gameStateInvariant_step
    (input : Option PlayerInput) (state : GameState)
    (h : Spec.gameStateInvariant Snake.playArea state) :
    Spec.gameStateInvariant Snake.playArea (Snake.step input state) := by
  rcases h with ⟨hFoodArea, hFoodSnake, hSnakeArea, hWon, hConnected⟩
  exact ⟨foodIsInPlayArea_step input state hFoodArea,
    foodIsNotOnSnake_step input state hFoodSnake,
    snakeIsInPlayArea_step input state hSnakeArea,
    wonImpliesBoardIsFull_step input state hWon,
    snakeIsConnected_step input state hConnected⟩

private theorem gameStepRequirements :
    Spec.gameStepRequirements Snake.step Snake.playArea := by
  exact ⟨movesInDirectionIfNotAtEdge,
    arrowInputSetsDirection,
    wrapsAtEdge,
    foodMovesWhenEaten,
    foodChangesBothCoordinatesWhenPossible,
    snakeGrowsWhenEating,
    gameEndsOnSelfCollision,
    gameEndsWhenPlayAreaIsFull,
    gameHasNoStepAfterEnd⟩

theorem gameRequirements :
    Spec.gameRequirements Snake.initialState Snake.step Snake.playArea := by
  exact ⟨gameStateInvariant_initial, gameStateInvariant_step, gameStepRequirements⟩

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
