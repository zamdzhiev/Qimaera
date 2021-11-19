module QAOA

import Data.Nat
import Data.Vect
import Graph
import Lemmas
import Unitary
import Control.Linear.LIO
import QStateT
import Injection
import LinearTypes
import Complex
import System.Random
import QuantumOp
import RandomUtilities

%default total

||| Vanilla QAOA : we use QAOA with a vanilla optimisation procedure to solve MAXCUT.


-------------------------QUANTUM CIRCUITS----------------------

||| The unitary operator induced by the mixing hamiltonian.
||| n    -- the arity of the operator
||| beta -- the rotation angle parameter
mixingUnitary : (n : Nat) -> (beta : Double) -> Unitary n
mixingUnitary n beta = tensorn n (RxGate beta)

||| Helper function for costUnitary
||| m              -- number of vertices of the input subgraph
||| n              -- number of remaining edges between current vertex and the rest
||| prf            -- proof witness that the number of vertices does not exceed the arity of the operator
||| gamma          -- the rotation parameter
||| edges          -- vector of edges that the current vertex is connected to
||| currentUnitary -- the currently constructed unitary operator
||| output         -- the final unitary operator
costUnitary' : {n : Nat} -> {m : Nat} -> {auto prf : n < m = True} -> 
               (gamma : Double) -> (edges : Vect n Bool) -> (currentUnitary : Unitary m) -> Unitary m
costUnitary' _ [] currentUnitary = currentUnitary
costUnitary' {n = S k} gamma (False :: xs) currentUnitary =
  let proof1 = lemmaLTSuccLT k m 
  in costUnitary' gamma xs currentUnitary
costUnitary' {n = S k} gamma (True  :: xs) currentUnitary =
  let proof1 = lemmaCompLT0 m (S k)
      proof2 = lemmaLTSuccLT k m
      cx     = CNOT 0 (S k) (IdGate {n = m})
      rzcx   = P gamma (S k) cx
      rest   = costUnitary' gamma xs currentUnitary
  in rest . cx . rzcx

||| The unitary operator induced by the cost hamiltonian.
||| n      -- the number of vertices of the input graph
||| graph  -- the input graph
||| gamma  -- rotation parameter
||| output -- the resulting unitary operator
costUnitary : {n : Nat} -> (graph: Graph n) -> (gamma : Double) -> Unitary n
costUnitary Empty _ = IdGate
costUnitary (AddVertex graph edges) gamma = 
  let circuit = (IdGate {n = 1}) # (costUnitary graph gamma)
      proof1 = lemmaLTSucc n
  in costUnitary' gamma edges circuit

||| The iterated cost and mixing unitaries for QAOA_p
||| n       -- the number of vertices of the graph
||| p       -- the "p" parameter of QAOA_p, i.e., the number of iterations of the mixing and cost unitaries
||| betas   -- list of rotation parameters for the mixing hamiltonians
||| gammas  -- list of rotation parameters for the cost hamilitonians
||| graph   -- the input graph
||| output  -- the overall unitary operator of QAOA_p
QAOA_Unitary' : {n : Nat} ->
               (betas : Vect p Double) -> (gammas : Vect p Double) -> 
               (graph: Graph n) ->
               Unitary n
QAOA_Unitary' [] [] g = IdGate
QAOA_Unitary' (beta :: betas) (gamma :: gammas) g = 
  let circuit = QAOA_Unitary' betas gammas g 
  in circuit . mixingUnitary n beta . costUnitary g gamma

||| The overall unitary operator for QAOA_p
||| n       -- the number of vertices of the graph
||| p       -- the "p" parameter of QAOA_p, i.e., the number of iterations of the mixing and cost unitaries
||| betas   -- list of rotation parameters for the mixing hamiltonians
||| gammas  -- list of rotation parameters for the cost hamilitonians
||| graph   -- the input graph
||| output  -- the overall unitary operator of QAOA_p
export
QAOA_Unitary : {n : Nat} ->
               (betas : Vect p Double) -> (gammas : Vect p Double) -> 
               (graph: Graph n) ->
               Unitary n
QAOA_Unitary betas gammas graph = (QAOA_Unitary' betas gammas graph) . (tensorn n HGate)


-------------------------CLASSICAL PART------------------------

||| The (probabilistic) classical optimisation procedure for QAOA.
||| IO output allows us to use probabilistic optimisation procedures.
||| Given all previously observed information, determine new rotation angles for the next QAOA run. 
||| Remark: we randomly generate the next rotation angles for simplicity.
|||
||| k             -- number of previous iterations of the algorithm
||| p             -- "p" parameter for QAOA_p
||| n             -- number of vertices of the input graph
||| graph         -- the input graph
||| previous_info -- previously used parameters and previously observed cuts from QAOA runs
||| IO output     -- new rotation angles for the next run of QAOA
classicalOptimisation : {p : Nat} ->
                       (graph : Graph n) ->
                       (previous_info : Vect k (Vect p Double, Vect p Double, Cut n)) -> 
                       IO (Vect p Double, Vect p Double)
classicalOptimisation g ys = do
  betas <- randomVect p
  gammas <- randomVect p
  pure (betas,gammas)


-----------------------------QAOA------------------------------

||| Helper function for QAOA
||| 
||| n      -- number of vertices of the input graph
||| p      -- the "p" parameter of QAOA_p
||| k      -- number of times we sample (the number of times we execute QAOA_p)
||| graph  -- input graph of the problem
||| output -- all observed cuts and all rotation angles from all the runs of QAOA
QAOA' : QuantumOp t =>
        {n : Nat} ->
        (k : Nat) -> (p : Nat) -> (graph : Graph n) ->
        IO (Vect k (Vect p Double, Vect p Double, Cut n))
QAOA' 0 p graph = pure []
QAOA' (S k) p graph = do
  previous_info <- QAOA' {t} k p graph 
  (betas, gammas) <- classicalOptimisation graph previous_info
  let circuit = QAOA_Unitary betas gammas graph
  cut <- run (do
              qs <- newQubits {t} n
              qs <- applyUnitary qs circuit 
              measureAll qs
              )
  pure $ (betas, gammas, cut) :: previous_info

||| QAOA for the MAXCUT problem. Given an input graph, return the best observed cut after some number of iterations.
||| 
||| n      -- number of vertices of the input graph
||| p      -- the "p" parameter of QAOA_p
||| k      -- number of times we sample (the number of times we execute QAOA_p)
||| graph  -- input graph of the problem
||| output -- best observed cut from the execution of the algorithm
export
QAOA : QuantumOp t =>
       {n : Nat} ->
       (k : Nat) -> (p : Nat) -> Graph n ->
       IO (Cut n)
QAOA k p graph = do
  res <- QAOA' {t} k p graph
  let cuts = map (\(_, _, cut) => cut) res
  let (cut,size) = bestCut graph cuts
  pure cut
