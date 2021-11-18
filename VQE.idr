module VQE

import Data.Nat
import Data.Vect
import Unitary
import Control.Linear.LIO
import Lemmas
import QStateT
import Injection
import LinearTypes
import Complex
import System.Random
import QuantumState
import RandomUtilities

%default total

-- Example of code where quantum and classical information interact
-- The VQE (Variational Quantum Eigensolver) algorithm finds the lowest eigenvalue for an Hamiltonian operator
-- More precisely, we suppose that the eigenstate corresponding to the lowest eigenvalue is given by some ansatz
-- that depends on some parameters, and we optimize the value of the parameters, to find the eigenvalue.


-- The next lines of code explain how the ansatz is given in general. The ansatz has some depth p, and all parameters
-- the ansatz is depending on are given by two matrices of angles, represented by the RotationAnglesMatrix type.


||| Type for the matrices of rotation angles
|||
||| Matrix of size (n+1) * m
public export
RotationAnglesMatrix : Nat -> Nat -> Type
RotationAnglesMatrix n m = Vect (S n) (Vect m Double)

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




------------- THE HAMILTONIAN -------------------------------------------------------

-- The ansatz gives us some vector |psi>, that depends on some parameters
-- We want to find the minimum value of <psi|H|psi> over all possible parameters
-- To do that, we need a way to compute <psi|H|psi>.

-- This is easy if H is an tensor product of Pauli Matrices. In this case, one can build a circuit U_H
-- such that, if we build the circuit U_H|psi> and measure the first qubit, then
-- <psi|H|psi> is equal to x - y where x (resp.y) is the probability of measuring 0 (resp. 1)


-- More generally, if H is a sum of tensor product of Pauli Matrices, say H = a_1 H_1 + ... a_k H_k
-- then one can obtain <psi|H|psi> by computing separately each <psi|H_i|psi> using the previous idea

-- As a consequence, for all intent and purposes here, we suppose that Hamiltonians are given by linear combinations of
-- tensor product of Pauli Matrices.
-- This is represented by the type Hamiltonian below, that is a list of pairs (coefficient, tensor product of pauli matrix)

||| Data type for the the Pauli matrices X,Y,Z and Identity
public export
data PauliAtomic : Type where
  PauliI : PauliAtomic
  PauliX : PauliAtomic
  PauliY : PauliAtomic
  PauliZ : PauliAtomic

||| Tensor product of n Pauli matrices represented as a vector
||| n -- number of qubits
public export
PauliBasis : Nat -> Type
PauliBasis n = Vect n PauliAtomic

||| Decomposition of Hamiltonian as sum of Pauli matrices
||| Hamiltonian = a_1P_1 + a_2P_2 + ... + a_kP_k
||| n -- number of qubits
public export
Hamiltonian : Nat -> Type
Hamiltonian n = List (Double, PauliBasis n)

-- Now the next lines of code  explain how to obtain the  value of <psi|H|psi>, first for a tensor product of Pauli matrices, then more generally.

-- First here is the definition of U_H, the unitary s.t. measuring U_H|psi> makes us able to compute <psi|H|psi>:

--------------------- COMPUTE THE ENERGY ------------------------------

-- The value of the energy <psi|H|psi> can be computed by applying a unitary operator U_H to |psi> and mesuring the first qubit
-- Here the operator U_H uses one more  qubits than H. It is possible to use the exact same number of qubits, but the code is easier this way.


||| With a tensor product of Pauli matrices, compute the corresponding unitary operator U_H
|||
||| n      -- number of qubits
||| h      -- vector that represents the tensor product of Pauli matrices
||| output -- U_h
encodingUnitary : {n : Nat} -> (h : PauliBasis n) -> Unitary (S n)
encodingUnitary [] = IdGate
encodingUnitary {n = S k} (PauliI :: xs) = rewrite sym $ lemmaplusOneRight k in (encodingUnitary xs) # IdGate {n=1}
encodingUnitary {n = S k} (PauliX :: xs) = 
  let p1 = lemmakLTSk k
  in rewrite sym $ lemmaplusOneRight k in CNOT (S k) 0 (H (S k) ((encodingUnitary xs) # IdGate {n=1}))
encodingUnitary {n = S k} (PauliY :: xs) =
  let p1 = lemmakLTSk k 
  in rewrite sym $ lemmaplusOneRight k in CNOT (S k) 0 (H (S k) (S (S k) ((encodingUnitary xs) # IdGate {n=1})))
encodingUnitary {n = S k} (PauliZ :: xs) = 
  let p1 = lemmakLTSk k
  in rewrite sym $ lemmaplusOneRight k in CNOT (S k) 0 ((encodingUnitary xs) # IdGate {n=1})


-- the next function computes <psi|H|psi>, for H a tensor product of Pauli Matrices
-- This is the function that needs to run the quantum circuit
-- As explained above, to obtain <psi|H|psi>, we produce a circuit for U_H|psi> and then measure the first qubit
-- The value of <psi|H|psi> is then equal to the probability of measuring 0 minus the probability of measuring 1
-- the following code runs the whole experiment nSamples times,
-- and records the number of time we measure 0 and the number of times we measure 1 and returns the difference between the two quantities
-- if nSamples is big enough, then <psi|H|psi> is therefore well approximated by the result of this function divided by the number of samples.


||| Computes an approximation of <psi|H|psi> when H is a tensor product of Pauli Matrices
||| More precisely, <psi|H|psi> is equal to the result of this function divided by nSamples
|||
||| n        -- number of qubits
||| p        -- tensor product of Pauli matrices
||| nSamples -- the number of time we sample
||| circuit  -- the state |psi>
||| output   -- computed energy
computeEnergyPauli : QuantumState t => (n : Nat) -> (p : PauliBasis n) -> (nSamples : Nat) -> (circuit : Unitary n) -> IO Double
computeEnergyPauli n p 0 circuit = pure 0
computeEnergyPauli n p (S nSamples) circuit = do
  let encodingCircuit = encodingUnitary p
  (b :: _) <- run (do
               qs <- newQubits {t} (S n)
               qs <- applyUnitary qs ( (IdGate {n=1}) # circuit)
               qs <- applyUnitary qs encodingCircuit
               measureAll qs
               )
  rest <- computeEnergyPauli {t} n p nSamples circuit
  if (not b) then pure $ 1 + rest else pure $ rest - 1


-- the next function computes <psi|H|psi> for a general hamiltonian H, expressed as a linear combination of tensor product of Pauli Matrices
-- we just have to call the function computeEnergyPauli for each element inside the linear combination:

||| Compute an approximation of <psi|H|psi> for a general Hamiltonian H
|||
||| n        -- number of qubits
||| h        -- the hamiltonian of the problem
||| nSamples -- the number of time we sample for each component of H
||| circuit  -- the state |psi>
||| output   -- computed energy
computeEnergy : QuantumState t => (n : Nat) -> (h : Hamiltonian n) -> (nSamples : Nat) -> (circuit : Unitary n) -> IO Double
computeEnergy n [] nSamples circuit = pure 0
computeEnergy n ((r, p) :: hs) nSamples circuit = do
  res1 <- computeEnergy {t} n hs nSamples circuit
  res2 <- computeEnergyPauli {t} n p nSamples circuit
  pure $ res1 + r*res2/(cast nSamples)



--------------------- CLASSICAL OPTIMISATION ------------------------


--- The energy that is compute by the function computeEnergy is fed to the function classicalOptimisation before
--- That will produces  new parameters for the ansatz to try, based on the value of <psi|H|psi> on all previous runs


--- This function should use general optimisation techniques, like for instance the Nelder-Mead method
--- For simplicity, we opted instead for a function that returns random parameters


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
||| We ask for the function to be able to return also parameters for the very first ansatz (that is, the function
||| will be called for the first time with an empty vector of previous information)
||| Remark: we randomly generate the next rotation angles for simplicity.
|||
||| k             -- number of previous iterations of the algorithm
||| n             -- arity of the ansatz circuit
||| depth         -- depth of the ansatz circuit
||| h             -- hamiltonian of the problem
||| previous_info -- previously used parameters and measurement outcomes
||| output        -- new rotation angles for the next run of VQE 
classicalOptimisation : {n : Nat} -> (depth : Nat) ->
                        (h : Hamiltonian n) ->
                        (previous_info : Vect k (RotationAnglesMatrix depth n, RotationAnglesMatrix depth n, Double)) ->
                        IO (RotationAnglesMatrix depth n, RotationAnglesMatrix depth n)
classicalOptimisation depth h previous_info = do
  phasesRy <- randomMatrix depth n
  phasesRz <- randomMatrix depth n
  pure (phasesRy, phasesRz)




-----------------------PUTTING QUANTUM AND CLASSICAL PARTS TOGETHER -------------------------

-- We now put everything together
-- This function will run the whole process k times, computing <psi|H|psi> at each step, and calling the classical optimiser to obtain
-- the next value of |psi> to test


||| Helper function for VQE
||| n        -- number of qubits
||| h        -- the hamiltonian of the problem
||| nSamples -- number of times we sample to compute <psi|H|psi>
||| k        -- number of iterations of the algorithm
||| depth    -- depth of the ansatz circuit
||| output   -- all observed information : rotation angles and computed energies
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



--- The VQE algorithm just calls the previous function, and returns the minimum value of <psi|H|psi> that was observed
--- Note that, in practice, if the classical Optimiser does their job correctly, the minimum value of <psi|H|psi>
--- is very likely to be obtained in the last iteration. As we use a random function instead of an optimiser, this is
--- not true, so we take the minimum among all runs.

||| VQE algorithm
||| n        -- number of qubits
||| h        -- the hamiltonian of the problem
||| nSamples -- number of times we sample to compute <psi|H|psi>
||| k        -- number of iterations of the algorithm
||| depth    -- depth of the ansatz circuit
||| output   -- the lowest computed energy
export
VQE : QuantumState t =>
      (n : Nat) -> (h : Hamiltonian n) -> (nSamples : Nat) -> (k : Nat) -> (depth : Nat) ->
      IO Double
VQE n h nSamples k depth = do
  observed_info <- VQE' {t=t} n h nSamples (S k) depth
  let energies = map (\(_, _, r) => r) observed_info
  pure $ foldl min (head energies) energies




