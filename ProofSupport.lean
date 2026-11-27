import GameFlow
import Snake

namespace ProofSupport

open Spec

theorem moveSetsDirection (input : Option PlayerInput) (state : GameState) :
    arrowInputSetsDirection input state { state with snake := Snake.moveSnake input state } := by
  cases input with
  | none =>
    cases direction : state.snake.direction <;>
      simp [arrowInputSetsDirection, Snake.moveSnake, Snake.directionAfterInput,
        oppositeDirection, direction]
  | some key =>
    cases key <;> cases direction : state.snake.direction <;>
      simp [arrowInputSetsDirection, Snake.moveSnake, Snake.directionAfterInput,
        oppositeDirection, direction]

theorem gameEndsOnSelfCollision (state : GameState) (snake : Snake)
    (food : Option Position) (running : gameIsRunning state) :
    Spec.gameEndsOnSelfCollision state (Snake.updateGame state snake food) := by
  have playing : state.phase = .playing := running
  simp only [Spec.gameEndsOnSelfCollision, Spec.snakeCollides, Snake.updateGame,
    playing, ne_eq, not_true_eq_false, ↓reduceIte]
  split
  · simp_all
  · rename_i safe
    split
    · cases food <;> simp_all
    · split <;> simp_all

theorem initialSnakeDoesNotOverlap :
    snakeDoesNotOverlapItself Snake.initialSnake := by
  simp [snakeDoesNotOverlapItself, Snake.initialSnake]

theorem moveSnakeBodyDoesNotOverlap (input : Option PlayerInput) (state : GameState)
    (unique : snakeDoesNotOverlapItself state.snake) :
    (Snake.moveSnake input state).body.Nodup := by
  have original : (state.snake.head :: state.snake.body).Nodup := unique
  have headFree := (List.nodup_cons.mp original).1
  have bodyUnique := (List.nodup_cons.mp original).2
  simp only [Snake.moveSnake]
  split
  · exact original
  · split
    · exact List.nodup_nil
    · apply List.nodup_cons.mpr
      constructor
      · intro member
        exact headFree ((List.dropLast_sublist state.snake.body).subset member)
      · exact bodyUnique.sublist (List.dropLast_sublist state.snake.body)

theorem movePreservesNonOverlap (input : Option PlayerInput) (state : GameState)
    (food : Option Position) (running : gameIsRunning state)
    (unique : snakeDoesNotOverlapItself state.snake)
    (notLost : (Snake.updateGame state (Snake.moveSnake input state) food).phase ≠ .lost) :
    snakeDoesNotOverlapItself
      (Snake.updateGame state (Snake.moveSnake input state) food).snake := by
  have noCollision : ¬ snakeCollides (Snake.moveSnake input state)
      (Snake.moveSnake input state).head := by
    intro collision
    apply notLost
    have playing : state.phase = .playing := running
    have collision' : (Snake.moveSnake input state).head ∈
        (Snake.moveSnake input state).body := collision
    simp [Snake.updateGame, playing, collision']
  have bodyUnique := moveSnakeBodyDoesNotOverlap input state unique
  have playing : state.phase = .playing := running
  have sameSnake :
      (Snake.updateGame state (Snake.moveSnake input state) food).snake =
        Snake.moveSnake input state := by
    simp only [Snake.updateGame, playing, ne_eq, not_true_eq_false, ↓reduceIte]
    split
    · rfl
    · split
      · cases food <;> rfl
      · rfl
  rw [sameSnake]
  exact List.nodup_cons.mpr ⟨noCollision, bodyUnique⟩

theorem stepWithRandomFoodUsesMovedSnake (move : MoveSnake) (update : UpdateGame)
    (nextFoodPosition : Snake → BaseIO (Option Position))
    (input : Option PlayerInput) (state : GameState)
    (running : state.phase = .playing)
    (eating : (move input state).head = state.food) :
    GameFlow.stepWithRandomFood move update nextFoodPosition input state =
      (do
        let food ← nextFoodPosition (move input state)
        pure (update state (move input state) food)) := by
  simp [GameFlow.stepWithRandomFood, running, eating]

/-- Reachability covers every valid outcome of random food selection. -/
inductive Reachable (move : MoveSnake) (update : UpdateGame) (area : PlayArea)
    (initialState : GameState) : GameState → Prop where
  | initial : Reachable move update area initialState initialState
  | next {state : GameState} (input : Option PlayerInput) (nextFood : Option Position)
      (reachable : Reachable move update area initialState state)
      (valid : gameIsRunning state →
        (move input state).head = state.food →
          foodChoiceIsValid area (move input state) nextFood) :
      Reachable move update area initialState
        (update state (move input state) nextFood)

def alwaysOnReachableStates (move : MoveSnake) (update : UpdateGame) (area : PlayArea)
    (initialState : GameState) (property : GameState → Prop) : Prop :=
  ∀ state, Reachable move update area initialState state → property state

theorem invariantOnReachableStates (move : MoveSnake) (update : UpdateGame) (area : PlayArea)
    (initialState : GameState)
    (initial : gameStateInvariant area initialState)
    (requirements : gameStepRequirements move update area) :
    alwaysOnReachableStates move update area initialState (gameStateInvariant area) := by
  obtain ⟨ended, steps⟩ := requirements
  intro state reachable
  induction reachable with
  | initial => exact initial
  | @next state input nextFood reachable valid ih =>
    by_cases running : gameIsRunning state
    · obtain ⟨_, _, _, _, _, finishes⟩ := steps input state ih running
      obtain ⟨_, _, _, _, invariant⟩ :=
        finishes nextFood (valid running)
      exact invariant
    · rw [ended (move input state) nextFood state running]
      exact ih

end ProofSupport
