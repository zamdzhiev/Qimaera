import Data.Vect

export
data Graph : Nat -> Type where
  Empty     : Graph 0
  AddVertex : Graph n -> Vect n Bool -> Graph (S n)

singletonGraph : Graph 1
singletonGraph = AddVertex Empty []

-- neighbourhood : (vertex : Fin (S n)) -> (g : Graph (S n)) -> (v ** ((isInjective n v) = True))

-- edges : Graph n -> List (Nat, Nat, prf1, prf2, prf3)
