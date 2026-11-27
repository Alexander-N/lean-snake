import ProofSupport

/-!
Theorems connecting the concrete Snake functions to the current specification.
-/
namespace Proofs

open Spec
open Classical

private def boardPositions : List Position :=
  (List.range 20).flatMap fun y =>
    (List.range 30).map fun x => { x := x, y := y }

private theorem positionInBoardPositions (position : Position) :
    position ∈ boardPositions ↔
      Spec.isWithinPlayArea Snake.playArea position := by
  cases position with
  | mk x y =>
    constructor
    · simp only [boardPositions, List.mem_flatMap, List.mem_map, List.mem_range]
      rintro ⟨yy, hyy, xx, hxx, hEq⟩
      rcases Position.mk.inj hEq with ⟨hxxEq, hyyEq⟩
      subst xx
      subst yy
      simp [Spec.isWithinPlayArea, Snake.playArea]
      omega
    · intro h
      rcases h with ⟨hLeft, hRight, hTop, hBottom⟩
      simp only [boardPositions, List.mem_flatMap, List.mem_map, List.mem_range]
      refine ⟨y, ?_, x, ?_, rfl⟩ <;>
        simp [Snake.playArea] at * <;> omega

private theorem boardPositionsNodup : boardPositions.Nodup := by
  unfold boardPositions List.Nodup
  rw [List.pairwise_flatMap]
  constructor
  · intro y hy
    rw [List.pairwise_map]
    apply List.Pairwise.imp (R := fun a b => a ≠ b)
    · intro a b hab heq
      apply hab
      simpa using congrArg Position.x heq
    · exact List.nodup_range
  · apply List.Pairwise.imp (R := fun a b => a ≠ b)
    · intro y1 y2 hyNe position1 hPosition1 position2 hPosition2 hEq
      apply hyNe
      simp only [List.mem_map] at hPosition1 hPosition2
      rcases hPosition1 with ⟨x1, hx1, rfl⟩
      rcases hPosition2 with ⟨x2, hx2, rfl⟩
      simpa using congrArg Position.y hEq
    · exact List.nodup_range

private theorem freeFoodPositionsMatchesSpec (snake : Snake) :
    Snake.freeFoodPositions Snake.playArea snake =
      boardPositions.filter fun position =>
        decide (Spec.isFree Snake.playArea snake position) := by
  classical
  unfold Snake.freeFoodPositions boardPositions
  apply List.filter_congr
  intro position hMember
  have hMemBoard : position ∈ boardPositions := by
    simpa [boardPositions, Snake.playArea] using hMember
  have hWithin : Spec.isWithinPlayArea Snake.playArea position :=
    (positionInBoardPositions position).mp hMemBoard
  simp [Snake.isFreeForSnake, Spec.isFree, hWithin]

theorem nextFoodPositionIsPlacedRandomly (snake : Snake) :
    Spec.foodIsPlacedRandomly Snake.playArea snake
      (Snake.nextFoodPosition Snake.playArea snake) := by
  refine ⟨Snake.freeFoodPositions Snake.playArea snake, ?_, ?_, rfl⟩
  · intro position
    change position ∈ Snake.freeFoodPositions Snake.playArea snake ↔
      Spec.isFree Snake.playArea snake position
    rw [freeFoodPositionsMatchesSpec, List.mem_filter]
    constructor
    · rintro ⟨hPosition, hFree⟩
      exact of_decide_eq_true hFree
    · intro hFree
      exact ⟨(positionInBoardPositions position).mpr hFree.1,
        decide_eq_true hFree⟩
  · rw [freeFoodPositionsMatchesSpec]
    exact List.Pairwise.filter _ boardPositionsNodup

theorem initialSnakeHasFreePosition :
    ∃ position, Spec.isFree Snake.playArea Snake.initialSnake position := by
  refine ⟨⟨0, 0⟩, ?_⟩
  simp [Spec.isFree, Spec.isWithinPlayArea, Snake.playArea, Snake.initialSnake]

theorem initialStateInvariant (food : Position)
    (foodFree : Spec.isFree Snake.playArea Snake.initialSnake food) :
    Spec.gameIsRunning (Snake.initialState food) ∧
      Spec.gameStateInvariant Snake.playArea (Snake.initialState food) := by
  constructor
  · rfl
  · refine ⟨foodFree.1, Or.inr ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨fun h => foodFree.2.1 h, foodFree.2.2⟩
    · simp [Spec.snakeIsInPlayArea, Spec.isWithinPlayArea,
        Snake.initialState, Snake.initialSnake, Snake.playArea]
    · intro hWon
      cases hWon
    · simp [Spec.snakeIsConnected, Spec.segmentsAreConnected,
        Snake.initialState, Snake.initialSnake]
    · intro _
      exact ProofSupport.initialSnakeDoesNotOverlap

theorem arrowInputSetsDirection (input : Option PlayerInput) (state : GameState) :
    arrowInputSetsDirection input state
      { state with snake := Snake.moveSnake input state } :=
  ProofSupport.moveSetsDirection input state

private theorem positionAfterMove_moves (direction : Direction) (state : GameState) :
    ¬ Spec.isAtEdge direction Snake.playArea state →
      Spec.movesInDirection direction state
        { state with snake :=
          { state.snake with
            head := Snake.positionAfterMove Snake.playArea direction state.snake.head } } := by
  cases direction
  · intro h
    by_cases hx : state.snake.head.x = Snake.playArea.leftEdge <;>
      simp only [Snake.playArea] at hx <;>
      simp [Snake.positionAfterMove, Snake.playArea, Spec.isAtEdge,
        Spec.movesInDirection, hx] at h ⊢ <;> omega
  · intro h
    by_cases hy : state.snake.head.y = Snake.playArea.topEdge <;>
      simp only [Snake.playArea] at hy <;>
      simp [Snake.positionAfterMove, Snake.playArea, Spec.isAtEdge,
        Spec.movesInDirection, hy] at h ⊢ <;> omega
  · intro h
    by_cases hx : state.snake.head.x = Snake.playArea.rightEdge <;>
      simp only [Snake.playArea] at hx <;>
      simp [Snake.positionAfterMove, Snake.playArea, Spec.isAtEdge,
        Spec.movesInDirection, hx] at h ⊢ <;> omega
  · intro h
    by_cases hy : state.snake.head.y = Snake.playArea.bottomEdge <;>
      simp only [Snake.playArea] at hy <;>
      simp [Snake.positionAfterMove, Snake.playArea, Spec.isAtEdge,
        Spec.movesInDirection, hy] at h ⊢ <;> omega

theorem movesInDirectionIfNotAtEdge (input : Option PlayerInput) (state : GameState) :
    Spec.movesInDirectionIfNotAtEdge Snake.playArea state
      { state with snake := Snake.moveSnake input state } := by
  let moved := Snake.moveSnake input state
  have hDirection : moved.direction = Snake.directionAfterInput input state.snake.direction := by
    simp [moved, Snake.moveSnake]
  intro hNotAtEdge
  have hNotAtEdge' : ¬ Spec.isAtEdge moved.direction Snake.playArea state := hNotAtEdge
  rw [hDirection] at hNotAtEdge'
  have hMove := positionAfterMove_moves moved.direction state hNotAtEdge'
  have hHead : moved.head =
      Snake.positionAfterMove Snake.playArea moved.direction state.snake.head := by
    simp [moved, Snake.moveSnake]
  simpa only [Spec.movesInDirection, moved, hHead] using hMove

private theorem positionAfterMove_wraps (direction : Direction) (state : GameState) :
    Spec.isAtEdge direction Snake.playArea state →
      match direction with
      | .left =>
          (Snake.positionAfterMove Snake.playArea direction state.snake.head).x =
              Snake.playArea.rightEdge ∧
            (Snake.positionAfterMove Snake.playArea direction state.snake.head).y =
              state.snake.head.y
      | .up =>
          (Snake.positionAfterMove Snake.playArea direction state.snake.head).y =
              Snake.playArea.bottomEdge ∧
            (Snake.positionAfterMove Snake.playArea direction state.snake.head).x =
              state.snake.head.x
      | .right =>
          (Snake.positionAfterMove Snake.playArea direction state.snake.head).x =
              Snake.playArea.leftEdge ∧
            (Snake.positionAfterMove Snake.playArea direction state.snake.head).y =
              state.snake.head.y
      | .down =>
          (Snake.positionAfterMove Snake.playArea direction state.snake.head).y =
              Snake.playArea.topEdge ∧
            (Snake.positionAfterMove Snake.playArea direction state.snake.head).x =
              state.snake.head.x := by
  cases direction <;> intro h <;>
    simp_all [Spec.isAtEdge, Snake.positionAfterMove, Snake.playArea]

theorem wrapsAtEdge (input : Option PlayerInput) (state : GameState) :
    Spec.wrapsAtEdge Snake.playArea state
      { state with snake := Snake.moveSnake input state } := by
  let moved := Snake.moveSnake input state
  have hDirection : moved.direction = Snake.directionAfterInput input state.snake.direction := by
    simp [moved, Snake.moveSnake]
  have hHead : moved.head =
      Snake.positionAfterMove Snake.playArea moved.direction state.snake.head := by
    simp [moved, Snake.moveSnake]
  intro hAtEdge
  have hAtEdge' : Spec.isAtEdge moved.direction Snake.playArea state := hAtEdge
  have hWrap := positionAfterMove_wraps moved.direction state hAtEdge'
  cases direction : moved.direction <;>
    simpa [Spec.wrapsAtEdge, moved, direction, hHead] using hWrap

private theorem positionAfterMoveWithin (direction : Direction)
    (position : Position) (h : Spec.isWithinPlayArea Snake.playArea position) :
    Spec.isWithinPlayArea Snake.playArea
      (Snake.positionAfterMove Snake.playArea direction position) := by
  unfold Spec.isWithinPlayArea at h
  simp only [Snake.playArea] at h
  cases direction
  · by_cases edge : position.x = Snake.playArea.leftEdge <;>
      simp only [Snake.playArea] at edge <;>
      simp [Spec.isWithinPlayArea, Snake.positionAfterMove, Snake.playArea, edge] <;> omega
  · by_cases edge : position.y = Snake.playArea.topEdge <;>
      simp only [Snake.playArea] at edge <;>
      simp [Spec.isWithinPlayArea, Snake.positionAfterMove, Snake.playArea, edge] <;> omega
  · by_cases edge : position.x = Snake.playArea.rightEdge <;>
      simp only [Snake.playArea] at edge <;>
      simp [Spec.isWithinPlayArea, Snake.positionAfterMove, Snake.playArea, edge] <;> omega
  · by_cases edge : position.y = Snake.playArea.bottomEdge <;>
      simp only [Snake.playArea] at edge <;>
      simp [Spec.isWithinPlayArea, Snake.positionAfterMove, Snake.playArea, edge] <;> omega

private theorem positionAfterMoveAdjacent (direction : Direction)
    (position : Position) :
    Spec.positionsAreAdjacent Snake.playArea position
      (Snake.positionAfterMove Snake.playArea direction position) := by
  cases direction
  · by_cases edge : position.x = Snake.playArea.leftEdge <;>
      simp only [Snake.playArea] at edge <;>
      simp [Spec.positionsAreAdjacent, Snake.positionAfterMove, Snake.playArea, edge] <;> omega
  · by_cases edge : position.y = Snake.playArea.topEdge <;>
      simp only [Snake.playArea] at edge <;>
      simp [Spec.positionsAreAdjacent, Snake.positionAfterMove, Snake.playArea, edge] <;> omega
  · by_cases edge : position.x = Snake.playArea.rightEdge <;>
      simp only [Snake.playArea] at edge <;>
      simp [Spec.positionsAreAdjacent, Snake.positionAfterMove, Snake.playArea, edge] <;> omega
  · by_cases edge : position.y = Snake.playArea.bottomEdge <;>
      simp only [Snake.playArea] at edge <;>
      simp [Spec.positionsAreAdjacent, Snake.positionAfterMove, Snake.playArea, edge] <;> omega

private theorem segmentsConnectedDropLast
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

private theorem positionsAdjacentSymm (area : PlayArea) (left right : Position)
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

private theorem movedSnakeInPlayArea (direction : Direction) (snake : Snake)
    (eating : Bool) (h : Spec.snakeIsInPlayArea Snake.playArea snake) :
    Spec.snakeIsInPlayArea Snake.playArea
      { head := Snake.positionAfterMove Snake.playArea direction snake.head,
        body := if eating then snake.head :: snake.body
          else if snake.body.isEmpty then [] else snake.head :: snake.body.dropLast,
        direction := direction } := by
  refine ⟨positionAfterMoveWithin direction snake.head h.1, ?_⟩
  intro position member
  by_cases hEating : eating
  · simp only [ite_eq_left hEating, List.mem_cons] at member
    rcases member with rfl | member
    · exact h.1
    · exact h.2 position member
  · simp only [ite_eq_right hEating] at member
    by_cases hEmpty : snake.body.isEmpty
    · simp [hEmpty] at member
    · simp only [ite_eq_right hEmpty, List.mem_cons] at member
      rcases member with rfl | member
      · exact h.1
      · exact h.2 position (List.dropLast_subset snake.body member)

private theorem movedSnakeConnected (direction : Direction) (snake : Snake)
    (eating : Bool) (h : Spec.snakeIsConnected Snake.playArea snake) :
    Spec.snakeIsConnected Snake.playArea
      { head := Snake.positionAfterMove Snake.playArea direction snake.head,
        body := if eating then snake.head :: snake.body
          else if snake.body.isEmpty then [] else snake.head :: snake.body.dropLast,
        direction := direction } := by
  by_cases hEating : eating
  · simp only [ite_eq_left hEating, Spec.snakeIsConnected, Spec.segmentsAreConnected]
    exact ⟨positionsAdjacentSymm Snake.playArea snake.head
      (Snake.positionAfterMove Snake.playArea direction snake.head)
      (positionAfterMoveAdjacent direction snake.head), h⟩
  · simp only [ite_eq_right hEating]
    by_cases hEmpty : snake.body.isEmpty
    · simp [hEmpty, Spec.snakeIsConnected, Spec.segmentsAreConnected]
    · simp only [ite_eq_right hEmpty, Spec.snakeIsConnected, Spec.segmentsAreConnected]
      exact ⟨positionsAdjacentSymm Snake.playArea snake.head
        (Snake.positionAfterMove Snake.playArea direction snake.head)
        (positionAfterMoveAdjacent direction snake.head),
        segmentsConnectedDropLast snake.head snake.body h⟩

private theorem snakeFillsPlayAreaIff (snake : Snake) :
    Snake.snakeFillsPlayArea Snake.playArea snake = true ↔
      Spec.boardIsFull Snake.playArea snake := by
  classical
  have hFree : ∀ position,
      position ∈ Snake.freeFoodPositions Snake.playArea snake ↔
        Spec.isFree Snake.playArea snake position := by
    intro position
    rw [freeFoodPositionsMatchesSpec, List.mem_filter]
    constructor
    · rintro ⟨_, hFree⟩
      exact of_decide_eq_true hFree
    · intro hFree
      exact ⟨(positionInBoardPositions position).mpr hFree.1,
        decide_eq_true hFree⟩
  constructor
  · intro full position hWithin
    by_cases hHead : position = snake.head
    · exact Or.inl hHead
    by_cases hBody : position ∈ snake.body
    · exact Or.inr hBody
    have positionFree : Spec.isFree Snake.playArea snake position :=
      ⟨hWithin, hHead, hBody⟩
    have member := (hFree position).mpr positionFree
    have empty : Snake.freeFoodPositions Snake.playArea snake = [] := by
      simpa [Snake.snakeFillsPlayArea] using full
    rw [empty] at member
    simp at member
  · intro hFull
    unfold Snake.snakeFillsPlayArea
    cases hPositions : Snake.freeFoodPositions Snake.playArea snake with
    | nil => rfl
    | cons position rest =>
      have member : position ∈ Snake.freeFoodPositions Snake.playArea snake := by
        simp [hPositions]
      have hPositionFree := (hFree position).mp member
      exfalso
      rcases hFull position hPositionFree.1 with hHead | hBody
      · exact hPositionFree.2.1 hHead
      · exact hPositionFree.2.2 hBody

private theorem movedSnakeShape (input : Option PlayerInput) (state : GameState) :
    Snake.moveSnake input state =
      { head := Snake.positionAfterMove Snake.playArea
          (Snake.directionAfterInput input state.snake.direction) state.snake.head,
        body := if Snake.positionAfterMove Snake.playArea
            (Snake.directionAfterInput input state.snake.direction) state.snake.head = state.food
          then state.snake.head :: state.snake.body
          else if state.snake.body.isEmpty then []
          else state.snake.head :: state.snake.body.dropLast,
        direction := Snake.directionAfterInput input state.snake.direction } := by
  simp [Snake.moveSnake]

private theorem movedSnakeInvariants (input : Option PlayerInput) (state : GameState)
    (inArea : Spec.snakeIsInPlayArea Snake.playArea state.snake)
    (connected : Spec.snakeIsConnected Snake.playArea state.snake) :
    Spec.snakeIsInPlayArea Snake.playArea (Snake.moveSnake input state) ∧
      Spec.snakeIsConnected Snake.playArea (Snake.moveSnake input state) := by
  let direction := Snake.directionAfterInput input state.snake.direction
  let head := Snake.positionAfterMove Snake.playArea direction state.snake.head
  let eating := decide (head = state.food)
  let shape : Snake.moveSnake input state =
      { head := head,
        body := if eating then state.snake.head :: state.snake.body
          else if state.snake.body.isEmpty then [] else
            state.snake.head :: state.snake.body.dropLast,
        direction := direction } := by
    rw [movedSnakeShape]
    simp [direction, head, eating]
  have inArea' := movedSnakeInPlayArea direction state.snake eating inArea
  have connected' := movedSnakeConnected direction state.snake eating connected
  exact ⟨by simpa [shape] using inArea', by simpa [shape] using connected'⟩

private theorem noFreePositionImpliesBoardFull (snake : Snake)
    (noFree : ∀ position, ¬ Spec.isFree Snake.playArea snake position) :
    Spec.boardIsFull Snake.playArea snake := by
  intro position within
  by_cases head : position = snake.head
  · exact Or.inl head
  by_cases body : position ∈ snake.body
  · exact Or.inr body
  exact False.elim (noFree position ⟨within, head, body⟩)

private theorem freePositionImpliesNotFull (snake : Snake) (position : Position)
    (free : Spec.isFree Snake.playArea snake position) :
    Snake.snakeFillsPlayArea Snake.playArea snake ≠ true := by
  intro full
  have boardFull := snakeFillsPlayAreaIff snake |>.mp full
  rcases boardFull position free.1 with head | body
  · exact free.2.1 head
  · exact free.2.2 body

private theorem gameStateInvariantAfterStep (input : Option PlayerInput)
    (state : GameState) (nextFood : Option Position)
    (invariant : Spec.gameStateInvariant Snake.playArea state)
    (running : Spec.gameIsRunning state)
    (choice : Spec.foodIsEaten state
        { state with snake := Snake.moveSnake input state } →
      Spec.foodChoiceIsValid Snake.playArea (Snake.moveSnake input state) nextFood) :
    Spec.gameStateInvariant Snake.playArea
      (Snake.updateGame state (Snake.moveSnake input state) nextFood) := by
  rcases invariant with ⟨foodArea, foodNotSnake, snakeArea, wonFull, connected, unique⟩
  rcases foodNotSnake with foodWon | ⟨foodNotHead, foodNotBody⟩
  · have : state.phase = .won := by
      exact foodWon
    rw [running] at this
    cases this
  have phasePlaying : state.phase = .playing := running
  let moved := Snake.moveSnake input state
  have movedProperties := movedSnakeInvariants input state snakeArea connected
  have movedArea : Spec.snakeIsInPlayArea Snake.playArea moved := movedProperties.1
  have movedConnected : Spec.snakeIsConnected Snake.playArea moved := movedProperties.2
  have headEq : moved.head =
      Snake.positionAfterMove Snake.playArea
        (Snake.directionAfterInput input state.snake.direction) state.snake.head := by
    simp [moved, Snake.moveSnake]
  have eating : moved.head = state.food ↔
      Snake.positionAfterMove Snake.playArea
        (Snake.directionAfterInput input state.snake.direction) state.snake.head = state.food := by
    rw [headEq]
  have bodyWhenEating : moved.head = state.food →
      moved.body = state.snake.head :: state.snake.body := by
    intro hEat
    rw [headEq] at hEat
    change (Snake.moveSnake input state).body = _
    rw [movedSnakeShape]
    simp [hEat]
  have bodyWhenNotEating : moved.head ≠ state.food →
      moved.body =
        if state.snake.body.isEmpty then [] else
          state.snake.head :: state.snake.body.dropLast := by
    intro hNotEat
    rw [headEq] at hNotEat
    change (Snake.moveSnake input state).body = _
    rw [movedSnakeShape]
    simp [hNotEat]
  have validFood : moved.head = state.food →
      Spec.foodChoiceIsValid Snake.playArea moved nextFood := by
    intro hEat
    apply choice
    simpa [Spec.foodIsEaten] using hEat
  have collisionNotEating : moved.head ∈ moved.body →
      moved.head ≠ state.food := by
    intro collision eating
    have grown := bodyWhenEating eating
    rw [grown] at collision
    rcases List.mem_cons.mp collision with head | body
    · exact foodNotHead (eating.symm.trans head)
    · exact foodNotBody (eating ▸ body)
  have uniqueState : Spec.snakeDoesNotOverlapItself state.snake := by
    apply unique
    rw [phasePlaying]
    decide
  have movedUniqueBody : moved.body.Nodup :=
    ProofSupport.moveSnakeBodyDoesNotOverlap input state uniqueState
  have notEatingFree : moved.head ≠ state.food →
      Spec.isFree Snake.playArea moved state.food := by
    intro notEat
    refine ⟨foodArea, notEat.symm, ?_⟩
    intro member
    rw [bodyWhenNotEating notEat] at member
    cases body : state.snake.body with
    | nil => simp [body] at member
    | cons first rest =>
      simp [body] at member
      rcases member with head | tail
      · exact foodNotHead head
      · have tail' : state.food ∈ state.snake.body.dropLast := by
          simpa [body] using tail
        exact foodNotBody ((List.dropLast_subset state.snake.body) tail')
  have absentChoiceFull : moved.head = state.food → nextFood = none →
      Spec.boardIsFull Snake.playArea moved := by
    intro eats absent
    have choiceValid := choice (by simpa [Spec.foodIsEaten] using eats)
    rw [absent] at choiceValid
    exact noFreePositionImpliesBoardFull moved choiceValid
  -- The remaining proof handles collision, eating, and ordinary movement separately.
  by_cases collision : moved.head ∈ moved.body
  · have notEat : moved.head ≠ state.food := collisionNotEating collision
    have bodyEq := bodyWhenNotEating notEat
    have result :
        Snake.updateGame state moved nextFood =
          { state with snake := moved, phase := .lost } := by
      simp [Snake.updateGame, phasePlaying, collision]
    rw [result]
    simp only [Spec.gameStateInvariant, Spec.foodIsInPlayArea, Spec.foodIsNotOnSnake,
      Spec.snakeIsInPlayArea, Spec.snakeIsConnected]
    refine ⟨foodArea, Or.inr ?_, movedArea, ?_, movedConnected, ?_⟩
    · exact ⟨(fun h => notEat h.symm), by
        rw [bodyEq]
        intro member
        cases body : state.snake.body with
        | nil => simp [body] at member
        | cons first rest =>
          simp [body] at member
          rcases member with head | tail
          · exact foodNotHead head
          · have tail' : state.food ∈ state.snake.body.dropLast := by
              simpa [body] using tail
            exact foodNotBody ((List.dropLast_subset state.snake.body) tail')⟩
    · intro won
      cases won
    · intro notLost
      simp at notLost
  · by_cases eats : moved.head = state.food
    · have grown := bodyWhenEating eats
      have foodChoiceValid := validFood eats
      have collisionFood : ¬ state.food ∈ moved.body := by
        simpa [eats] using collision
      cases nextFood with
      | none =>
        have boardFull := absentChoiceFull eats rfl
        have result :
            Snake.updateGame state moved none =
              { state with snake := moved, phase := .won } := by
          simp [Snake.updateGame, phasePlaying, collisionFood, eats]
        rw [result]
        simp only [Spec.gameStateInvariant, Spec.foodIsInPlayArea, Spec.foodIsNotOnSnake,
          Spec.snakeIsInPlayArea, Spec.snakeIsConnected]
        refine ⟨foodArea, ?_, movedArea, ?_, movedConnected, ?_⟩
        · simp
        · intro _
          exact boardFull
        · intro _
          exact List.nodup_cons.mpr ⟨collision, movedUniqueBody⟩
      | some replacement =>
        have replacementFree : Spec.isFree Snake.playArea moved replacement := by
          simpa [Spec.foodChoiceIsValid] using foodChoiceValid
        have result :
            Snake.updateGame state moved (some replacement) =
              { state with snake := moved, food := replacement } := by
          simp [Snake.updateGame, phasePlaying, collisionFood, eats]
        rw [result]
        simp only [Spec.gameStateInvariant, Spec.foodIsInPlayArea, Spec.foodIsNotOnSnake,
          Spec.snakeIsInPlayArea, Spec.snakeIsConnected]
        refine ⟨replacementFree.1, Or.inr ?_, movedArea, ?_, movedConnected, ?_⟩
        · exact ⟨fun h => replacementFree.2.1 h, replacementFree.2.2⟩
        · intro won
          have impossible : GamePhase.playing = GamePhase.won := by
            simp [phasePlaying] at won
          cases impossible
        · intro _
          exact List.nodup_cons.mpr ⟨collision, movedUniqueBody⟩
    · have foodFree := notEatingFree eats
      have notFull := freePositionImpliesNotFull moved state.food foodFree
      have result :
          Snake.updateGame state moved nextFood =
            { state with snake := moved, phase := .playing } := by
        simp [Snake.updateGame, phasePlaying, collision, eats,
          notFull]
      rw [result]
      simp only [Spec.gameStateInvariant, Spec.foodIsInPlayArea, Spec.foodIsNotOnSnake,
        Spec.snakeIsInPlayArea, Spec.snakeIsConnected]
      refine ⟨foodArea, Or.inr ?_, movedArea, ?_, movedConnected, ?_⟩
      · exact ⟨(fun h => eats h.symm), by
          rw [bodyWhenNotEating eats]
          intro member
          cases body : state.snake.body with
          | nil => simp [body] at member
          | cons first rest =>
            simp [body] at member
            rcases member with head | tail
            · exact foodNotHead head
            · have tail' : state.food ∈ state.snake.body.dropLast := by
                simpa [body] using tail
              exact foodNotBody ((List.dropLast_subset state.snake.body) tail')⟩
      · intro won
        cases won
      · intro _
        exact List.nodup_cons.mpr ⟨collision, movedUniqueBody⟩

private theorem gameWonAfterStep (input : Option PlayerInput) (state : GameState)
    (nextFood : Option Position)
    (invariant : Spec.gameStateInvariant Snake.playArea state)
    (running : Spec.gameIsRunning state)
    (choice : Spec.foodIsEaten state
        { state with snake := Snake.moveSnake input state } →
      Spec.foodChoiceIsValid Snake.playArea (Snake.moveSnake input state) nextFood) :
    Spec.gameIsWonWhenPlayAreaIsFull Snake.playArea state
      (Snake.updateGame state (Snake.moveSnake input state) nextFood) := by
  rcases invariant with ⟨foodArea, foodNotSnake, _, _, _, _⟩
  rcases foodNotSnake with foodWon | ⟨foodNotHead, foodNotBody⟩
  · change state.phase = .playing at running
    rw [foodWon] at running
    cases running
  let moved := Snake.moveSnake input state
  have phasePlaying : state.phase = .playing := running
  have headEq : moved.head =
      Snake.positionAfterMove Snake.playArea
        (Snake.directionAfterInput input state.snake.direction) state.snake.head := by
    simp [moved, Snake.moveSnake]
  have bodyWhenEating : moved.head = state.food →
      moved.body = state.snake.head :: state.snake.body := by
    intro eats
    have eats' :
        Snake.positionAfterMove Snake.playArea
          (Snake.directionAfterInput input state.snake.direction) state.snake.head =
            state.food := by
      simpa [moved, Snake.moveSnake] using eats
    change (Snake.moveSnake input state).body = _
    rw [movedSnakeShape]
    simp [eats']
  have bodyWhenNotEating : moved.head ≠ state.food →
      moved.body =
        if state.snake.body.isEmpty then [] else
          state.snake.head :: state.snake.body.dropLast := by
    intro notEating
    have notEating' :
        Snake.positionAfterMove Snake.playArea
          (Snake.directionAfterInput input state.snake.direction) state.snake.head ≠
            state.food := by
      simpa [moved, Snake.moveSnake] using notEating
    change (Snake.moveSnake input state).body = _
    rw [movedSnakeShape]
    simp [notEating']
  have collisionNotEating : moved.head ∈ moved.body →
      moved.head ≠ state.food := by
    intro collision eats
    have grown := bodyWhenEating eats
    rw [grown] at collision
    simp only [List.mem_cons] at collision
    rcases collision with head | body
    ·     exact foodNotHead (eats.symm.trans head)
    · exact foodNotBody (by simpa [eats] using body)
  have noCollisionFull (eats : moved.head = state.food)
      (absent : nextFood = none) :
      Spec.boardIsFull Snake.playArea moved := by
    have valid := choice (by simpa [Spec.foodIsEaten] using eats)
    rw [absent] at valid
    exact noFreePositionImpliesBoardFull moved valid
  by_cases collision : moved.head ∈ moved.body
  · have notEating := collisionNotEating collision
    have result :
        Snake.updateGame state moved nextFood =
          { state with snake := moved, phase := .lost } := by
      simp [Snake.updateGame, phasePlaying, collision]
    change Spec.gameIsWonWhenPlayAreaIsFull Snake.playArea state
      (Snake.updateGame state moved nextFood)
    rw [result]
    simp [Spec.gameIsWonWhenPlayAreaIsFull, Spec.snakeCollides, collision]
  · by_cases eats : moved.head = state.food
    · cases nextFood with
      | none =>
        have boardFull := noCollisionFull eats rfl
        have result :
            Snake.updateGame state moved none =
              { state with snake := moved, phase := .won } := by
          have collisionFood : ¬ state.food ∈ moved.body := by
            simpa [eats] using collision
          simp [Snake.updateGame, phasePlaying, collisionFood, eats]
        change Spec.gameIsWonWhenPlayAreaIsFull Snake.playArea state
          (Snake.updateGame state moved none)
        rw [result]
        simp [Spec.gameIsWonWhenPlayAreaIsFull, Spec.snakeCollides,
          boardFull, collision]
      | some replacement =>
        have foodChoiceValid := choice (by simpa [Spec.foodIsEaten] using eats)
        have replacementFree : Spec.isFree Snake.playArea moved replacement := by
          simpa [Spec.foodChoiceIsValid] using foodChoiceValid
        have notFull := freePositionImpliesNotFull moved replacement replacementFree
        have notBoardFull : ¬ Spec.boardIsFull Snake.playArea moved := by
          intro full
          exact notFull ((snakeFillsPlayAreaIff moved).mpr full)
        have result :
            Snake.updateGame state moved (some replacement) =
              { state with snake := moved, food := replacement } := by
          have collisionFood : ¬ state.food ∈ moved.body := by
            simpa [eats] using collision
          simp [Snake.updateGame, phasePlaying, collisionFood, eats]
        change Spec.gameIsWonWhenPlayAreaIsFull Snake.playArea state
          (Snake.updateGame state moved (some replacement))
        rw [result]
        simp [Spec.gameIsWonWhenPlayAreaIsFull, Spec.snakeCollides,
          phasePlaying, notBoardFull, collision]
    · have foodFree : Spec.isFree Snake.playArea moved state.food := by
        refine ⟨?_, ?_, ?_⟩
        · exact foodArea
        · exact fun h => eats h.symm
        · rw [bodyWhenNotEating eats]
          intro member
          cases body : state.snake.body with
          | nil => simp [body] at member
          | cons first rest =>
            simp [body] at member
            rcases member with head | tail
            · exact foodNotHead head
            · have tail' : state.food ∈ state.snake.body.dropLast := by
                simpa [body] using tail
              exact foodNotBody ((List.dropLast_subset state.snake.body) tail')
      have notFull := freePositionImpliesNotFull moved state.food foodFree
      have notBoardFull : ¬ Spec.boardIsFull Snake.playArea moved := by
        intro full
        exact notFull ((snakeFillsPlayAreaIff moved).mpr full)
      have result :
          Snake.updateGame state moved nextFood =
            { state with snake := moved, phase := .playing } := by
        simp [Snake.updateGame, phasePlaying, collision, eats, notFull]
      change Spec.gameIsWonWhenPlayAreaIsFull Snake.playArea state
        (Snake.updateGame state moved nextFood)
      rw [result]
      simp [Spec.gameIsWonWhenPlayAreaIsFull, Spec.snakeCollides,
        notBoardFull, collision]

private theorem foodMovesAfterStep (input : Option PlayerInput) (state : GameState)
    (nextFood : Option Position)
    (invariant : Spec.gameStateInvariant Snake.playArea state)
    (running : Spec.gameIsRunning state)
    (choice : Spec.foodIsEaten state
        { state with snake := Snake.moveSnake input state } →
      Spec.foodChoiceIsValid Snake.playArea (Snake.moveSnake input state) nextFood) :
    Spec.foodMovesToNextPosition nextFood state
      (Snake.updateGame state (Snake.moveSnake input state) nextFood) := by
  rcases invariant with ⟨_, foodNotSnake, _, _, _, _⟩
  rcases foodNotSnake with foodWon | ⟨foodNotHead, foodNotBody⟩
  · change state.phase = .playing at running
    rw [foodWon] at running
    cases running
  let moved := Snake.moveSnake input state
  have phasePlaying : state.phase = .playing := running
  have bodyWhenEating : moved.head = state.food →
      moved.body = state.snake.head :: state.snake.body := by
    intro eats
    have eats' :
        Snake.positionAfterMove Snake.playArea
          (Snake.directionAfterInput input state.snake.direction) state.snake.head =
            state.food := by
      simpa [moved, Snake.moveSnake] using eats
    change (Snake.moveSnake input state).body = _
    rw [movedSnakeShape]
    simp [eats']
  have collisionNotEating : moved.head ∈ moved.body →
      moved.head ≠ state.food := by
    intro collision eats
    have grown := bodyWhenEating eats
    rw [grown] at collision
    simp only [List.mem_cons] at collision
    rcases collision with head | body
    · exact foodNotHead (eats.symm.trans head)
    · exact foodNotBody (by simpa [eats] using body)
  by_cases collision : moved.head ∈ moved.body
  · have notEating := collisionNotEating collision
    have result :
        Snake.updateGame state moved nextFood =
          { state with snake := moved, phase := .lost } := by
      simp [Snake.updateGame, phasePlaying, collision]
    change Spec.foodMovesToNextPosition nextFood state
      (Snake.updateGame state moved nextFood)
    rw [result]
    simp [Spec.foodMovesToNextPosition, Spec.foodIsEaten, notEating]
  · by_cases eats : moved.head = state.food
    · cases nextFood with
      | none =>
        have collisionFood : ¬ state.food ∈ moved.body := by
          simpa [eats] using collision
        have result :
            Snake.updateGame state moved none =
              { state with snake := moved, phase := .won } := by
          simp [Snake.updateGame, phasePlaying, collisionFood, eats]
        change Spec.foodMovesToNextPosition none state
          (Snake.updateGame state moved none)
        rw [result]
        simp [Spec.foodMovesToNextPosition, Spec.foodIsEaten, eats]
      | some replacement =>
        have collisionFood : ¬ state.food ∈ moved.body := by
          simpa [eats] using collision
        have result :
            Snake.updateGame state moved (some replacement) =
              { state with snake := moved, food := replacement } := by
          simp [Snake.updateGame, phasePlaying, collisionFood, eats]
        change Spec.foodMovesToNextPosition (some replacement) state
          (Snake.updateGame state moved (some replacement))
        rw [result]
        simp [Spec.foodMovesToNextPosition, Spec.foodIsEaten, phasePlaying, eats]
    · change Spec.foodMovesToNextPosition nextFood state
        (Snake.updateGame state moved nextFood)
      simp [Spec.foodMovesToNextPosition, Spec.foodIsEaten, Snake.updateGame,
        phasePlaying, collision, eats]

theorem initialFoodUsesChosenPosition :
    initialFoodUsesChosenPosition Snake.initialState := by
  intro position
  rfl

theorem gameHasNoStepAfterEnd :
    gameHasNoStepAfterEnd Snake.updateGame := by
  intro nextMove nextFood state hEnded
  unfold gameIsRunning at hEnded
  simp [Snake.updateGame, hEnded]

theorem gameEndsOnSelfCollision (state : GameState) (snake : Snake)
    (food : Option Position) (running : gameIsRunning state) :
    Spec.gameEndsOnSelfCollision state (Snake.updateGame state snake food) :=
  ProofSupport.gameEndsOnSelfCollision state snake food running

theorem movePreservesNonOverlap (input : Option PlayerInput) (state : GameState)
    (food : Option Position) (running : gameIsRunning state)
    (unique : snakeDoesNotOverlapItself state.snake)
    (notLost : (Snake.updateGame state (Snake.moveSnake input state) food).phase ≠ .lost) :
    snakeDoesNotOverlapItself
      (Snake.updateGame state (Snake.moveSnake input state) food).snake :=
  ProofSupport.movePreservesNonOverlap input state food running unique notLost

theorem snakeGrowsWhenEating (input : Option PlayerInput) (state : GameState) :
    Spec.snakeGrowsWhenEating state
      { state with snake := Snake.moveSnake input state } := by
  unfold Spec.snakeGrowsWhenEating Spec.foodIsEaten
  intro eating
  simp only [Snake.moveSnake] at eating ⊢
  simp [eating]

theorem snakeBodyMoves (input : Option PlayerInput) (state : GameState) :
    Spec.snakeBodyMoves state
      { state with snake := Snake.moveSnake input state } := by
  unfold Spec.snakeBodyMoves Spec.foodIsEaten
  intro notEating
  simp only [Snake.moveSnake] at notEating ⊢
  simp [notEating]

theorem stepWithRandomFoodUsesMovedSnake (move : MoveSnake) (update : UpdateGame)
    (nextFoodPosition : Snake → BaseIO (Option Position))
    (input : Option PlayerInput) (state : GameState)
    (running : state.phase = .playing)
    (eating : (move input state).head = state.food) :
    GameFlow.stepWithRandomFood move update nextFoodPosition input state =
      (do
        let food ← nextFoodPosition (move input state)
        pure (update state (move input state) food)) :=
  ProofSupport.stepWithRandomFoodUsesMovedSnake move update nextFoodPosition
    input state running eating

theorem stepWithRandomFoodDoesNotSelectWithoutEating (move : MoveSnake)
    (update : UpdateGame) (nextFoodPosition : Snake → BaseIO (Option Position))
    (input : Option PlayerInput) (state : GameState)
    (running : state.phase = .playing)
    (notEating : (move input state).head ≠ state.food) :
    GameFlow.stepWithRandomFood move update nextFoodPosition input state =
      pure (update state (move input state) none) := by
  simp [GameFlow.stepWithRandomFood, running, notEating]

theorem stepWithRandomFoodDoesNotStepAfterEnd (move : MoveSnake)
    (update : UpdateGame) (nextFoodPosition : Snake → BaseIO (Option Position))
    (input : Option PlayerInput) (state : GameState)
    (ended : state.phase ≠ .playing) :
    GameFlow.stepWithRandomFood move update nextFoodPosition input state = pure state := by
  simp [GameFlow.stepWithRandomFood, ended]

theorem invariantOnReachableStates (move : MoveSnake) (update : UpdateGame)
    (area : PlayArea) (initialState : GameState)
    (initial : gameStateInvariant area initialState)
    (requirements : gameStepRequirements move update area) :
    ProofSupport.alwaysOnReachableStates move update area initialState
      (gameStateInvariant area) :=
  ProofSupport.invariantOnReachableStates move update area initialState initial requirements

theorem gameStepRequirements :
    Spec.gameStepRequirements Snake.moveSnake Snake.updateGame Snake.playArea := by
  refine ⟨Proofs.gameHasNoStepAfterEnd, ?_⟩
  intro input state invariant running
  change state.phase = .playing at running
  let moved := Snake.moveSnake input state
  let movedState := { state with snake := moved }
  have originalInvariant := invariant
  rcases invariant with ⟨_, _, snakeArea, _, connected, _⟩
  have movedProperties := movedSnakeInvariants input state snakeArea connected
  refine ⟨Proofs.movesInDirectionIfNotAtEdge input state,
    Proofs.arrowInputSetsDirection input state, Proofs.wrapsAtEdge input state,
    Proofs.snakeGrowsWhenEating input state, Proofs.snakeBodyMoves input state, ?_⟩
  intro nextFood choice
  let nextState := Snake.updateGame state moved nextFood
  have snakeEq : nextState.snake = moved := by
    change (Snake.updateGame state moved nextFood).snake = moved
    by_cases collision : moved.head ∈ moved.body
    · simp [Snake.updateGame, running, collision]
    · simp only [Snake.updateGame, running, collision, ↓reduceIte]
      by_cases eats : moved.head = state.food
      · cases nextFood <;> simp [eats]
      · simp [eats]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [nextState, moved] using snakeEq
  · exact foodMovesAfterStep input state nextFood originalInvariant running choice
  · exact Proofs.gameEndsOnSelfCollision state moved nextFood running
  · exact gameWonAfterStep input state nextFood originalInvariant running choice
  · exact gameStateInvariantAfterStep input state nextFood originalInvariant running choice

theorem gameRequirements :
    Spec.gameRequirements Snake.initialSnake Snake.initialState Snake.moveSnake
      Snake.updateGame Snake.playArea (Snake.nextFoodPosition Snake.playArea) := by
  refine ⟨?_, initialSnakeHasFreePosition, initialFoodUsesChosenPosition,
    ?_, ?_, gameStepRequirements, ?_⟩
  · simp [Spec.playAreaIsValid, Snake.playArea]
  · intro position
    rfl
  · intro position foodFree
    exact initialStateInvariant position foodFree
  · intro snake
    exact nextFoodPositionIsPlacedRandomly snake

end Proofs
