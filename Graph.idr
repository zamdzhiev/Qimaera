module Graph

import Data.Vect
import Lemmas

public export
data Graph : Nat -> Type where
  Empty     : Graph 0
  AddVertex : Graph n -> Vect n Bool -> Graph (S n)

export
singletonGraph : Graph 1
singletonGraph = AddVertex Empty []

public export
Cut : Nat -> Type
Cut n = Vect n Bool

||| Compute the size of a cut of a graph
||| TODO : not actually implemented
export
sizeCut : Graph n -> Cut n -> Nat
sizeCut g c = 0

||| Find the best cut of a graph from a list of cuts
||| currently not optimal
export
bestCut : {n : Nat} -> Graph n -> Vect k (Cut n) -> Cut n
bestCut graph [] = replicate n True
bestCut graph (cut::cuts) =
  let best = bestCut graph cuts
      size = sizeCut graph cut
  in  if (sizeCut graph best > size) then best else cut
