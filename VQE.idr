module VQE

import Data.Nat
import Data.Vect
import Unitary
import Control.Linear.LIO
import QStateT
import Injection
import LinearTypes
import Complex
import System.Random
import QuantumState

%default total

--Exemple of code where quantum and classical information interact
--VQE : find an upper bound for the lowest eigenvalue of a Hamiltonian operator
--Here we did not write the classical part, we only return some random numbers


---------------------- HAMILTONIAN -----------------------------
||| The Hamiltonian type
|||
||| Complex matrix of size 2^n * 2^n
public export
Hamiltonian : Nat -> Type
Hamiltonian n = Vect (power 2 n) (Vect (power 2 n) (Complex Double))

||| Type for the matrices of rotation angles
|||
||| Matrix of size (n+1) * m
public export
RotationAnglesMatrix : Nat -> Nat -> Type
RotationAnglesMatrix n m = Vect (S n) (Vect m Double)

----------QUANTUM PART : CIRCUIT------------------

||| Unitary operator used for linear entanglement
|||
||| n -- The arity of the operator
export
linearEntanglement : (n : Nat) -> Unitary n
linearEntanglement 0 = IdGate
linearEntanglement 1 = IdGate
linearEntanglement (S (S n)) = 
  let circ = IdGate {n = 1} # linearEntanglement (S n)
  in circ @@ (CNOT 0 1 IdGate)

||| Unitary operator, tensor product of phase gates
|||
||| n      -- The arity of the operator
||| phases -- The vector of phases
tensorPhases : (n : Nat) -> (phases : Vect n Double) -> Unitary n
tensorPhases 0 _ = IdGate
tensorPhases (S n) (phase :: phases) = RzGate phase # (tensorPhases n phases)

||| Unitary operator, tensor product of Ry gates
|||
||| n      -- The arity of the operator
||| phases -- The vector of phases for the Ry gates
tensorRy : (n : Nat) -> (phases : Vect n Double) -> Unitary n
tensorRy 0 _ = IdGate
tensorRy (S k) (phase :: phases) = RyGate phase # (tensorRy k phases)

||| The overall unitary operator for VQE, the ansatz
|||
||| n        -- The arity of the operator
||| depth    -- The depth of the ansatz, ie the number of repetitions of the pattern
||| phasesRy -- The vector of phases for all the Ry rotations
||| phasesRz -- The vector of phases for all the phase gates
||| output   -- The overall unitary operator for VQE, the ansatz
export
ansatz : (n : Nat) -> (depth : Nat) -> 
         (phasesRy : RotationAnglesMatrix depth n) -> 
         (phasesRz : RotationAnglesMatrix depth n) ->
         Unitary n
ansatz 0 _ _ _ = IdGate
ansatz (S n) 0 [phaseRy] [phaseRz] = tensorPhases (S n) phaseRz @@ tensorRy (S n) phaseRy
ansatz (S n) (S d) (phaseRy :: phasesRy) (phaseRz :: phasesRz) = 
  let circ1 = ansatz (S n) d phasesRy phasesRz 
  in circ1 @@ linearEntanglement (S n) @@ tensorPhases (S n) phaseRz @@ tensorRy (S n) phaseRy


-------------IMAGINARY CLASSICAL OPTIMIZATION PART------------

||| Generate a vector of random doubles
randomVect : (n : Nat) -> IO (Vect n Double)
randomVect 0 = pure []
randomVect (S k)  = do
  r <- randomRIO (0,2*pi)
  v <- randomVect k
  pure (r :: v)

||| Generate a matrix of size (n+1) * m of random Double
randomMatrix : (n : Nat) -> (m : Nat) -> IO (RotationAnglesMatrix n m)
randomMatrix 0 m = do
  xs <- randomVect m
  pure [xs]
randomMatrix (S n) m = do
  xs <- randomVect m
  ys <- randomMatrix n m
  pure (xs :: ys) 

||| The (probabilistic) classical optimisation procedure for VQE.
||| IO output allows us to use probabilistic optimisation procedures.
||| Given all previously observed information, determine new rotation angles for the next VQE run (while still remembering the previous info).
||| Remark: we randomly generate the next rotation angles for simplicity.
|||
||| k             -- number of previous iterations of the algorithm
||| n             -- arity of the ansatz circuit
||| depth         -- depth of the ansatz circuit
||| measurements  -- result of the last measurements
||| hamiltonian   -- the input Hamiltonian of the problem
||| previous_info -- previously used parameters and previously computed energies for the hamiltonian
||| output        -- new rotation angles for VQE and computed energy of the hamiltonian + all the previous information
classicalOptimisation : {n : Nat} -> (depth : Nat) ->
                        (measurements : Vect n Bool) ->
                        (hamiltonian : Hamiltonian n) ->
                        (previousInfo : Vect k (RotationAnglesMatrix depth n, RotationAnglesMatrix depth n, Double)) ->
                        IO (Vect (S k) (RotationAnglesMatrix depth n, RotationAnglesMatrix depth n, Double))
classicalOptimisation depth ms h prevs = do
  energy <- randomRIO(0,1024)
  phasesRy <- randomMatrix depth n
  phasesRz <- randomMatrix depth n
  pure ((phasesRy, phasesRz, energy)::prevs)


-------------------PUTTING QUANTUM AND CLASSICAL PARTS TOGETHER : SIMULATIONS------------------
||| Helper function for VQE
|||
||| n           -- The arity of the ansatz
||| hamiltonian -- The input Hamiltonian of the problem
||| k           -- Number of times we sample (the number of times we execute VQE)
||| depth       -- Depth of the ansatz
||| output      -- result of the classical optimization after all iterations
VQE' : QuantumState t =>
       (n : Nat) -> (hamiltonian : Hamiltonian n) -> (k : Nat) -> (depth : Nat) ->
       IO (Vect (S k) (RotationAnglesMatrix depth n, RotationAnglesMatrix depth n, Double))
VQE' n hamiltonian 0 depth = classicalOptimisation depth (replicate n False) hamiltonian []
VQE' n hamiltonian (S k) depth = do
  res @ ((phasesRy, phasesRz, _) :: _) <- VQE' {t} n hamiltonian k depth 
  let circuit = ansatz n depth phasesRy phasesRz
  meas <- run (do
               qs <- newQubits {t} n
               qs <- applyUnitary qs circuit 
               measureAll qs
               )
  classicalOptimisation depth meas hamiltonian res



||| VQE algorith. Given an input hamiltonian, return the ground state energy of this hamiltonian
||| 
||| n           -- The arity of the ansatz
||| hamiltonian -- the input Hamiltonian of the problem
||| k           -- number of times we sample (the number of times we execute VQE)
||| depth       -- Depth of the ansatz
||| output      -- Ground state energy of the Hamiltonian
export
VQE : QuantumState t =>
      (n : Nat) -> (hamiltonian : Hamiltonian n) -> (k : Nat) -> (depth : Nat) ->
      IO Double
VQE n hamiltonian k depth = do
  res @ ((_,_,energy) :: _) <- VQE' {t=t} n hamiltonian k depth
  pure energy
