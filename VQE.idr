module VQE

import Data.Nat
import Data.Vect
import Unitary
import LIO
import QStateT
import Injection
import LinearTypes
import Complex
import Random
import QuantumState

%default total

--Exemple of code where quantum and classical information interact
--VQE : find an upper bound for the lowest eigenvalue of a Hamiltonian operator
--Here we did not write the classical part, we only return some random numbers


----------QUANTUM PART : CIRCUIT------------------

Ry : Double -> Unitary 1
Ry p = SAdjGate @@ HGate @@ (P (-p) 0 (HGate @@ SGate))

Rz : Double -> Unitary 1
Rz p = PGate p 

export
linearEntanglement : (n : Nat) -> Unitary n
linearEntanglement 0 = IdGate
linearEntanglement 1 = IdGate
linearEntanglement (S (S n)) = 
  let circ = IdGate {n = 1} # linearEntanglement (S n)
  in circ @@ (CNOT 0 1 IdGate)

tensorPhases : (n : Nat) -> Vect n Double -> Unitary n
tensorPhases 0 _ = IdGate
tensorPhases (S k) (x :: xs) = Rz x # (tensorPhases k xs)

tensorRy : (n : Nat) -> Vect n Double -> Unitary n
tensorRy 0 _ = IdGate
tensorRy (S k) (x :: xs) = Ry x # (tensorRy k xs)

|||Building the ansatz
||| parameters : number of qubits, number of repetitions of the pattern, vectors of parameters for the Ry rotations, vector of parameters for the Rz rotations
export
ansatz : (nbQubits : Nat) -> (depth : Nat) -> 
         Vect (S depth) (Vect nbQubits Double) -> 
         Vect (S depth) (Vect nbQubits Double) ->
         Unitary nbQubits
ansatz 0 _ _ _ = IdGate
ansatz (S n) 0 [v] [w] = tensorPhases (S n) w @@ tensorRy (S n) v
ansatz (S n) (S r) (v :: vs) (w :: ws) = 
  let circ1 = ansatz (S n) r vs ws 
  in circ1 @@ linearEntanglement (S n) @@ tensorPhases (S n) w @@ tensorRy (S n) v


-------------IMAGINARY CLASSICAL OPTIMIZATION PART------------

--generate a vector of random doubles
randomVect : (n : Nat) -> IO (Vect n Double)
randomVect 0 = pure []
randomVect (S k)  = do
  r <- randomRIO (0,2*pi)
  v <- randomVect k
  pure (r :: v)

--pretend to compute the lowest eigenvalue given the results of the quantum operations
pretendComputeEnergy : Vect n Bool -> IO Double
pretendComputeEnergy vs = randomRIO (0,1024)

--pretend to compute the parameters for the quantum circuit by classical optimisation using the results of the measurements
pretendClassicalWork : (nbQubits : Nat) -> (depth : Nat) ->
                       (resultAnsatz : Vect nbQubits Bool) -> 
                       (hamiltonian : Vect (power 2 nbQubits) (Vect (power 2 nbQubits) (Complex Double))) -> 
                       IO (Vect (S depth) (Vect nbQubits Double), Vect (S depth) (Vect nbQubits Double))
pretendClassicalWork n 0 v m = do
  a <- randomVect n
  b <- randomVect n
  pure ([a],[b])
pretendClassicalWork n (S k) v m = do
  a <- randomVect n
  b <- randomVect n
  (c,d) <- pretendClassicalWork n k v m
  pure (a::c,b::d)


-------------------PUTTING QUANTUM AND CLASSICAL PARTS TOGETHER : SIMULATIONS------------------

VQE' : {t : Nat -> Type} -> QuantumState t =>
       (n : Nat) -> (hamiltonian : Vect (power 2 n) (Vect (power 2 n) (Complex Double))) -> (nbIter : Nat) -> (depth : Nat) ->
       IO (Vect n Bool)
VQE' n _ 0 depth = pure (replicate n False)
VQE' n m (S k) depth = do
  v <- VQE' {t=t} n m k depth
  (xs,ys) <- pretendClassicalWork n depth v m
  run (do
    let c = ansatz n depth xs ys
    q <- newQubits {t=t} n
    q <- applyUnitary q c
    measureAll q)
  
export
VQE : {t : Nat -> Type} -> QuantumState t =>
      (n : Nat) -> (hamiltonian : Vect (power 2 n) (Vect (power 2 n) (Complex Double))) -> (nbIter : Nat) -> (depth : Nat) ->
      IO Double
VQE n m k d = do
  res <- VQE' {t=t} n m k d
  pretendComputeEnergy res


export
main : IO ()
main = do
  putStrLn "\nSmall test VQE"
  w <- VQE {t = SimulatedState} 3 (replicate 8 (replicate 8 0)) 2 1
  putStrLn (show w)
  putStrLn "\nprinting another ansatz:"
  draw (ansatz 2 2 [[1,2],[9,10],[17,18]] [[5,6],[13,14],[21,22]])
