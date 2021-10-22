module Graph

import Data.Vect
import Lemmas

%default total

||| 'Graph n' is the type of undirected graphs with no parallel edges and no self-loops with 'n' vertices.
||| Vertex '0' corresponds to the innermost AddVertex call in the graph expression.
||| Vertex '1' corresponds to the penultimate AddVertex call in the graph expression.
||| ...
||| Vertex 'n-1' corresponds to the outermost AddVertex call in the graph expression.
||| The second argument of AddVertex is a Vect of Bools, where the 'i'-th entry indicates whether
|||   the current vertex should be connected to the 'i'-th vertex of the graph.
public export
data Graph : Nat -> Type where
  Empty     : Graph 0
  AddVertex : Graph n -> Vect n Bool -> Graph (S n)

||| The complete graph on 'n' vertices.
export
completeGraph : (n : Nat) -> Graph n
completeGraph 0 = Empty
completeGraph (S k) = AddVertex (completeGraph k) (replicate k True)

||| The graph with one vertex. Same as 'completeGraph 1'.
export
singletonGraph : Graph 1
singletonGraph = AddVertex Empty []

||| A convenient representation of a graph cut.
||| The 'i'-th entry indicates the color of the 'i'-th vertex in the cut.
public export
Cut : Nat -> Type
Cut n = Vect n Bool

||| Helper function fot sizeCut
|||
||| color  -- Color of the current vertex
||| cut    -- Colors of the other vertices
||| edges  -- Vect of edges between the current vertex and the others
||| output -- Number of edges between the current vertex and the other vertices of a different color
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
sizeCut (AddVertex graph edges) cut = 
  let x = last cut
      smaller_cut = init cut
  in sizeCut' x smaller_cut edges + sizeCut graph smaller_cut


||| Find the best cut of a graph among a vector of cuts (or the trivial cut if the vector is []).
||| 
||| n      -- The size of the input graph of the problem
||| graph  -- The input graph of the problem
||| cuts   -- Vector of cuts
||| output -- The best cut from the vector and its size
export
bestCut : {n : Nat} -> (graph : Graph n) -> (cuts : Vect k (Cut n)) -> (Cut n, Nat)
bestCut graph [] = (replicate n True, 0)
bestCut graph (cut::cuts) = 
  let (best, size) = bestCut graph cuts
      s = sizeCut graph cut
  in if s >= size then (cut, s) else (best,size)


