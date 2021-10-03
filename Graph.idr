module Graph

import Data.Vect
import Lemmas

%default total

||| 'Graph n' is the type of undirected graphs with no parallel edges and no self-loops with 'n' vertices.
public export
data Graph : Nat -> Type where
  Empty     : Graph 0
  AddVertex : Graph n -> Vect n Bool -> Graph (S n)

||| The complete graph on 'n' vertices.
export
completeGraph : (n : Nat) -> Graph n
completeGraph 0 = Empty
completeGraph (S k) = AddVertex (completeGraph k) (replicate k True)

||| The graph with one vetex. Same as 'completeGraph 1'.
export
singletonGraph : Graph 1
singletonGraph = AddVertex Empty []

||| A convenient representation of a graph cut.
public export
Cut : Nat -> Type
Cut n = Vect n Bool

||| Compute the size of a cut of a graph.
||| TODO : not actually implemented
export
sizeCut : Graph n -> Cut n -> Nat
sizeCut g c = 0

||| Find the best cut of a graph from a list of cuts.
||| currently not optimal
export
bestCut : {n : Nat} -> Graph n -> Vect k (Cut n) -> Cut n
bestCut graph [] = replicate n True
bestCut graph (cut::cuts) =
  let best = bestCut graph cuts
      size = sizeCut graph cut
  in  if (sizeCut graph best > size) then best else cut
