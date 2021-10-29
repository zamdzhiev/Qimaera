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
import RandomUtilities

%default total

-- Example of code where quantum and classical information interact
-- VQE : find an upper bound for the lowest eigenvalue of a Hamiltonian operator
-- Here we did not write the classical part, we only return some random numbers

-- TODO : DOCUMENTATION + CODE


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
  in circ . (CNOT 0 1 IdGate)

||| Unitary operator, tensor product of phase gates
|||
||| n      -- The arity of the operator
||| phases -- The vector of phases
tensorRzs : {n : Nat} -> (phases : Vect n Double) -> Unitary n
tensorRzs phases = tensorMapSimple (map (\phase => RzGate phase) phases)

||| Unitary operator, tensor product of Ry gates
|||
||| n      -- The arity of the operator
||| phases -- The vector of phases for the Ry gates
tensorRys : {n : Nat} -> (phases : Vect n Double) -> Unitary n
tensorRys phases = tensorMapSimple (map (\phase => RyGate phase) phases)


||| The overall unitary operator for VQE, the ansatz
|||
||| n        -- The arity of the operator
||| depth    -- The depth of the ansatz, i.e. the number of repetitions of the pattern
||| phasesRy -- The vector of phases for all the Ry rotations
||| phasesRz -- The vector of phases for all the phase gates
||| output   -- The overall unitary operator for VQE, the ansatz
export
ansatz : (n : Nat) -> (depth : Nat) -> 
         (phasesRy : RotationAnglesMatrix depth n) -> 
         (phasesRz : RotationAnglesMatrix depth n) ->
         Unitary n
ansatz n 0 [phaseRy] [phaseRz] = tensorRzs phaseRz . tensorRys phaseRy
ansatz n (S d) (phaseRy :: phasesRy) (phaseRz :: phasesRz) = 
  let circ1 = ansatz n d phasesRy phasesRz 
  in circ1 . linearEntanglement n . tensorRzs phaseRz . tensorRys phaseRy


-------------CLASSICAL OPTIMIZATION PART------------


data PauliAtomic : Type where
  PauliI : PauliAtomic
  PauliX : PauliAtomic
  PauliY : PauliAtomic
  PauliZ : PauliAtomic

||| n -- number of qubits
PauliBasis : Nat -> Type
PauliBasis n = Vect n PauliAtomic

||| H = a_1P_1 + a_2P_2 + ... + a_kP_k
Hamiltonian : Nat -> Type
Hamiltonian n = List (Double, PauliBasis n)

encodingUnitary : {n : Nat} -> PauliBasis n -> Unitary (S n)
encodingUnitary [] = IdGate
encodingUnitary (PauliI :: xs) = ?qweasd --(encodingUnitary xs) `tensor` IdGate {n=1}
encodingUnitary (PauliX :: xs) = ?qewasddqweqwe -- CNOT n 0 (H n ((encodingUnitary xs) `tensor` IdGate {n=1}))
encodingUnitary (PauliY :: xs) = ?qweasdwe_3
encodingUnitary (PauliZ :: xs) = ?qweasdwe_4

||| Generate a matrix of size (n+1) * m of random Double
export
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
||| Given all previously observed information, determine new rotation angles for the next VQE run.
||| Remark: we randomly generate the next rotation angles for simplicity.
|||
||| k             -- number of previous iterations of the algorithm
||| n             -- arity of the ansatz circuit
||| depth         -- depth of the ansatz circuit
||| cost_function -- function that computes the cost of inputs
||| previous_info -- previously used parameters and measurement outcomes
||| output        -- new rotation angles for the next run of VQE 
classicalOptimisation : {n : Nat} -> (depth : Nat) ->
                        (h : Hamiltonian n) ->
                        (previous_info : Vect k (RotationAnglesMatrix depth n, RotationAnglesMatrix depth n, Double)) ->
                        IO (RotationAnglesMatrix depth n, RotationAnglesMatrix depth n)
classicalOptimisation depth h previos_info = do
  phasesRy <- randomMatrix depth n
  phasesRz <- randomMatrix depth n
  pure (phasesRy, phasesRz)



-------------------PUTTING QUANTUM AND CLASSICAL PARTS TOGETHER : SIMULATIONS------------------

computeEnergyPauli : QuantumState t => (n : Nat) -> (p : PauliBasis n) -> (nSamples : Nat) -> (circuit : Unitary n) -> IO Double
computeEnergyPauli n p 0 circuit = pure 0
computeEnergyPauli n p (S nSamples) circuit = do
  let encodingCircuit = encodingUnitary p
  (b :: _) <- run (do
               qs <- newQubits {t} (S n)
               qs <- applyUnitary qs ( (IdGate {n=1}) `tensor` circuit)
               qs <- applyUnitary qs encodingCircuit
               measureAll qs
               )
  rest <- computeEnergyPauli {t} n p nSamples circuit
  if (not b) then pure $ 1 + rest else pure $ rest - 1


computeEnergy : QuantumState t => (n : Nat) -> (h : Hamiltonian n) -> (nSamples : Nat) -> Unitary n -> IO Double
computeEnergy n [] nSamples circuit = pure 0
computeEnergy n ((r, p) :: hs) nSamples circuit = do
  res1 <- computeEnergy {t} n hs nSamples circuit
  res2 <- computeEnergyPauli {t} n p nSamples circuit
  pure $ res1 + r*res2/(cast nSamples)

VQE': QuantumState t =>
       (n : Nat) -> (h : Hamiltonian n) -> (nSamples : Nat) -> (k : Nat) -> (depth : Nat) ->
       IO (Vect k (RotationAnglesMatrix depth n, RotationAnglesMatrix depth n, Double))
VQE' n h nSamples 0 depth = pure []
VQE' n h nSamples (S k) depth = do
  previous_info <- VQE' {t} n h nSamples k depth 
  (phasesRy, phasesRz) <- classicalOptimisation depth h previous_info
  let circuit = ansatz n depth phasesRy phasesRz
  energy <- computeEnergy {t} n h nSamples circuit
  pure $ (phasesRy, phasesRz, energy) :: previous_info

export
VQE : QuantumState t =>
      (n : Nat) -> (h : Hamiltonian n) -> (nSamples : Nat) -> (k : Nat) -> (depth : Nat) ->
      IO Double
VQE n h nSamples k depth = do
  observed_info <- VQE' {t=t} n h nSamples (S k) depth
  let energies = map (\(_, _, r) => r) observed_info
  pure $ foldl min (head energies) energies



-------------------PUTTING QUANTUM AND CLASSICAL PARTS TOGETHER : SIMULATIONS------------------
{-
||| Helper function for VQE
|||
||| n             -- the arity of the ansatz
||| cost_function -- function that computes the cost of inputs
||| k             -- number of times we sample (the number of times we execute VQE)
||| depth         -- depth of the ansatz
||| output        -- all of the observed information from all the runs of VQE
VQE' : QuantumState t =>
       (n : Nat) -> (cost_function : Vect n Bool -> Double) -> (k : Nat) -> (depth : Nat) ->
       IO (Vect k (RotationAnglesMatrix depth n, RotationAnglesMatrix depth n, Vect n Bool))
VQE' n cost_function 0 depth = pure []
VQE' n cost_function (S k) depth = do
  previous_info <- VQE' {t} n cost_function k depth 
  (phasesRy, phasesRz) <- classicalOptimisation depth cost_function previous_info
  let circuit = ansatz n depth phasesRy phasesRz
  meas <- run (do
               qs <- newQubits {t} n
               qs <- applyUnitary qs circuit 
               measureAll qs
               )
  pure $ (phasesRy, phasesRz, meas) :: previous_info



||| VQE algorithm. Given an input cost function, return the best output
||| 
||| n             -- The arity of the ansatz
||| cost_function -- function that computes the cost of inputs
||| k+1           -- number of times we sample (the number of times we execute VQE)
||| depth         -- Depth of the ansatz
||| output        -- Ground state energy of the Hamiltonian

export
VQE : QuantumState t =>
      (n : Nat) -> (cost_function : Vect n Bool -> Double) -> (k : Nat) -> (depth : Nat) ->
      IO Double
VQE n cost_function k depth = do
  observed_info <- VQE' {t=t} n cost_function (S k) depth
  let measurement_outcomes = map (\(_, _, measurement) => measurement) observed_info
  let costs = map cost_function measurement_outcomes
  pure $ foldl min (head costs) costs
-}
