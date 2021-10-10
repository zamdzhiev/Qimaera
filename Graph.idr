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

|||Helper function fot sizeCut
|||
|||color  -- Color of the current vertex
|||cut    -- Colors of the other vertices
|||edges  -- Vect of edges between the current vertex and the others
|||output -- Number of edges between the current vertex and the other vertices of a different color
sizeCut' : (color : Bool) -> (cut : Vect n Bool) -> (edges : Vect n Bool) -> Nat
sizeCut' _ [] [] = 0
sizeCut' True (False :: cut) (True :: edges) = S (sizeCut' True cut edges)
sizeCut' False (True :: cut) (True :: edges) = S (sizeCut' False cut edges)
sizeCut' color (_::cut) (_::edges) = sizeCut' color cut edges

||| Compute the size of a cut of a graph.
|||
||| graph  -- The input graph of the problem
||| cut    -- The given cut
||| output -- The size of the cut
export
sizeCut : (graph : Graph n) -> (cut : Cut n) -> Nat
sizeCut Empty [] = 0
sizeCut (AddVertex graph edges) cuts = 
  let x = last cuts
      cut = init cuts
  in sizeCut' x cut edges + sizeCut graph cut


||| Find the best cut of a graph from a list of cuts.
||| 
||| n      -- The size of the input graph of the problem
||| graph  -- The input graph of the problem
||| cuts   -- Vector of all observed cuts
||| output -- The best cut and its size
export
bestCut : {n : Nat} -> (graph : Graph n) -> (cuts : Vect k (Cut n)) -> (Cut n, Nat)
bestCut graph [] = (replicate n True, 0)
bestCut graph (cut::cuts) = 
  let (best, size) = bestCut graph cuts
      s = sizeCut graph cut
  in if s > size then (cut, s) else (best,size)


