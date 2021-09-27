module VanillaQAOA

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
import QuantumState
--import Graph


%default total

||| Vanilla QAOA : returns random numbers instead of classical optimisation




-------------------------QUANTUM CIRCUITS----------------------

mixingHamiltonian : (n : Nat) -> (beta : Double) -> Unitary n
mixingHamiltonian n beta = tensorn n (RxGate beta)

costHamiltonian' : {n : Nat} -> {m : Nat} -> {auto prf : n < m = True} -> 
                   Double -> Vect n Bool -> Unitary m -> Unitary m
costHamiltonian' _ [] u = u
costHamiltonian' {n = S k} gamma (False :: xs) u = 
  let p1 = lemmaLTSuccLT k m 
  in costHamiltonian' gamma xs u
costHamiltonian' {n = S k} gamma (True  :: xs) u = 
  let p1 = lemmaCompLT0 m (S k)
      p2 = lemmaLTSuccLT k m
      c = CNOT 0 (S k) (IdGate {n = m})
      rz = P gamma (S k) c
      h = costHamiltonian' gamma xs u
  in h @@ c @@ rz

costHamiltonian : {n : Nat} -> Graph n -> (gamma : Double) -> Unitary n
costHamiltonian Empty _ = IdGate
costHamiltonian (AddVertex g xs) gamma = 
  let circuit = (IdGate {n = 1}) `tensor` (costHamiltonian g gamma)
      p1 = lemmaLTSucc n
  in costHamiltonian' gamma xs circuit


prepareState : {n : Nat} ->
               (betas : Vect p Double) -> (gammas : Vect p Double) -> 
               Graph n ->
               Unitary n
prepareState [] [] g = IdGate
prepareState (beta :: betas) (gamma :: gammas) g = 
  let circuit = prepareState betas gammas g 
  in circuit @@ mixingHamiltonian n beta @@ costHamiltonian g gamma



-------------------------CLASSICAL PART------------------------

||| generate a vector of random doubles
randomVect : (n : Nat) -> IO (Vect n Double)
randomVect 0 = pure []
randomVect (S k)  = do
  r <- randomRIO (0,2*pi)
  v <- randomVect k
  pure (r :: v)


randomBoolVect : (n : Nat) -> IO (Vect n Bool)
randomBoolVect 0 = pure []
randomBoolVect (S k) = do
  r <- randomRIO (0,1)
  v <- randomBoolVect k
  if r > 0.5 then pure (True :: v)
             else pure (False :: v)

|||pretendClassicalWork :
|||    k : Nat -> number of previous iterations of the algorithm
|||    Vect n Bool : results from the quantum measurements
|||    Graph n : the graph of the problem
|||    Vect k (Vect n Bool, Vect p Double, Vect p Double, Vect n Bool) :
|||           Vect n Bool : results from previous quantum iterations
|||           Vect p Double : previous beta vectors
|||           Vect p Double : previous gamma vectors
|||           Vect n Bool : cuts obtained by previous iterations
|||   IO output : Vect (S k) (Vect p Double, Vect p Double, Vect n Bool)
|||           Same vectors as before, but including all the results from this iteration + best cut until now
pretendClassicalWork : {p : Nat} -> {n : Nat} -> 
                       Vect n Bool -> Graph n ->
                       Vect k (Vect n Bool, Vect p Double, Vect p Double, Vect n Bool) -> 
                       IO (Vect (S k) (Vect n Bool, Vect p Double, Vect p Double, Vect n Bool))
pretendClassicalWork xs g ys = do
  betas <- randomVect p
  gammas <- randomVect p
  cuts <- randomBoolVect n
  pure ((xs,betas,gammas,xs)::ys)


-----------------------------QAOA------------------------------
|||QAOA' :
|||  k : number of iterations of th algorithm
|||  p : depth of the circuits
|||  graph : graph of the problem
|||  output : result of the classical optimization at each iteration
QAOA' : QuantumState t =>
        {n : Nat} ->
        (k : Nat) -> (p : Nat) -> (graph : Graph n) ->
        IO (Vect (S k) (Vect n Bool, Vect p Double, Vect p Double, Vect n Bool))
QAOA' 0 p graph = pretendClassicalWork (replicate n False) graph [] 
QAOA' (S k) p graph = do
  res @ ((_, betas, gammas, _) :: _) <- QAOA' {t} k p graph 
  let circuit = prepareState betas gammas graph
  xs <- run (do
            q <- newQubits {t} n
            q <- applyUnitary q circuit 
            measureAll q
            )
  pretendClassicalWork xs graph res


export
QAOA : QuantumState t =>
       {n : Nat} ->
       (k : Nat) -> (p : Nat) -> Graph n ->
       IO (Vect n Bool)
QAOA k p graph = do
  res <- QAOA' {t} k p graph
  randomBoolVect n

