import Spec

namespace GameFlow

open Spec

def initialStateWithRandomFood (initialSnake : Snake)
    (makeInitialState : Position → GameState)
    (nextFoodPosition : Snake → BaseIO (Option Position)) :
    BaseIO (Option GameState) := do
  let food ← nextFoodPosition initialSnake
  pure (food.map makeInitialState)

def stepWithRandomFood (move : MoveSnake) (update : UpdateGame)
    (nextFoodPosition : Snake → BaseIO (Option Position))
    (input : Option PlayerInput) (state : GameState) : BaseIO GameState := do
  if state.phase = .playing then
    let moved := move input state
    if moved.head = state.food then
      let food ← nextFoodPosition moved
      pure (update state moved food)
    else
      pure (update state moved none)
  else
    pure state

end GameFlow
