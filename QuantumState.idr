module QuantumState

import Data.Vect
import Data.Nat
import Decidable.Equality
import System.File
import Injection
import Matrix
import Complex
import Random
import Lemmas
import QStateT
import LIO
import LinearTypes
import Unitary

||| The Qubit type is used to identify individual qubits. The Nat argument is
||| used to uniquely identify a qubit. This type does *not* carry any quantum
||| state information. The constructor MkQubit is *private* in order to prevent
||| pattern matching by users of the library.
export
data Qubit : Type where
  MkQubit : (n : Nat) -> Qubit


||| The QuantumState interface is used to abstract over the representation of a
||| quantum state. It is parameterised by the number of qubits it contains.
export
interface QuantumState (t : Nat -> Type) where

  ||| Prepare 'p' new qubits in state |00...0>
  newQubits : (p : Nat) -> QStateT (t n) (t (n+p)) (LVect p Qubit)

  ||| Prepare a single new qubit in state |0>
  newQubit : QStateT (t n) (t (n+1)) Qubit
  newQubit = do
    [q] <- newQubits 1
    pure q

  ||| Apply a unitary circuit to the qubits specified by the LVect argument
  applyUnitary : {n : Nat} -> {i : Nat} ->
                 (1 _ : LVect i Qubit) -> Unitary i -> QStateT (t n) (t n) (LVect i Qubit)


  ||| Apply the Hadamard gate to a single qubit
  applyH : {n : Nat} -> (1 _ : Qubit) -> QStateT (t n) (t n) Qubit
  applyH q = do
    [q1] <- applyUnitary {n} {i = 1} [q] HGate 
    pure q1

  ||| Apply a P gate to a single qubit
  applyP : {n : Nat} -> Double -> (1 _ : Qubit) -> QStateT (t n) (t n) Qubit
  applyP p q = do
    [q1] <- applyUnitary {n} {i = 1} [q] (PGate p)
    pure q1

  ||| Apply the CNOT gate to a pair of qubits
  applyCNOT : {n : Nat} -> (1 _ : Qubit) -> (1 _ : Qubit) -> QStateT (t n) (t n) (LPair Qubit Qubit)
  applyCNOT q1 q2 = do
    [q1,q2] <- applyUnitary {n} {i = 2} [q1,q2] CNOTGate
    pure (q1 # q2)

  ||| Measure some qubits in a quantum state
  public export
  measure : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> QStateT (t (i + n)) (t n) (Vect i Bool)

  ||| Measure only one qubit
  measureQubit : {n : Nat} -> (1 _ : Qubit) -> QStateT (t (S n)) (t n) Bool
  measureQubit q = do
    [b] <- measure [q]
    pure b

  ||| Same as measure, but with an initial state of n + i instead of i + n qubits to help with theorem proving in some cases
  -- public export
  -- measure2 : {n : Nat} -> {i : Nat} -> (LVect i Qubit) -> QStateT (t (n + i)) (t n) (Vect i Bool)
  -- measure2 v = rewrite plusCommutative n i in measure v

  ||| Measure all qubits in a quantum state
  ||| Because of a bug in Idris2, we use the implementation below.
  ||| However, the implementation commented out is preferable if the bug gets fixed.
  public export
  measureAll : {n : Nat} -> (1 _ : LVect n Qubit) -> QStateT (t n) (t 0) (Vect n Bool)
  measureAll [] = pure []
  measureAll (q :: qs) = do
                            b <- measureQubit q
                            bs <- measureAll qs
                            pure (b `consLin` bs)
  --measureAll qs = rewrite sym $ plusZeroRightNeutral n in measure qs
                          



  ||| Execute a quantum operation : start and finish with trivial quantum state
  ||| (0 qubits) and measure 'n' qubits in the process
  run : QStateT (t 0) (t 0) (Vect n Bool) -> IO (Vect n Bool)





----- IMPLEMENTATION OF QUANTUMSTATE: LINEAR-ALGEBRAIC SIMULATION -----------


||| SimulatedState : linear-algebraic vector representation of the quantum state, vector of indices of the qubits, counter
export
data SimulatedState : Nat -> Type where
  MkSimulatedState : {n : Nat} -> Matrix (power 2 n) 1 -> Vect n Qubit -> Nat -> SimulatedState n

public export
QuantumOp : Nat -> Nat -> Type -> Type
QuantumOp n m t = QStateT (SimulatedState n) (SimulatedState m) t






------ SIMULATE CIRCUITS : AUXILIARY (PRIVATE) FUNCTIONS ------


|||Find an element in a list : used to find the wire of a qubit
private
listIndex' : {n : Nat} -> Vect n Qubit -> Qubit -> Nat
listIndex' [] _ = 0
listIndex' (MkQubit x :: xs) (MkQubit k) = if x == k then 0 else S (listIndex' xs (MkQubit k))

private
listIndex : (1 _ : SimulatedState n) -> (1 _ : Qubit) -> LFstPair (LPair (SimulatedState n) Qubit) Nat
listIndex (MkSimulatedState qs v counter) (MkQubit k) = (MkSimulatedState qs v counter # MkQubit k) # (listIndex' v (MkQubit k))

private 
listIndices : (1 _ : SimulatedState n) -> (1 _ : LVect i Qubit) -> LFstPair (LPair (SimulatedState n) (LVect i Qubit)) (Vect i Nat)
listIndices qs [] = (qs # []) # []
listIndices qs (x :: xs) = 
  let (qs' # x') # y = listIndex qs x
      (qs2 # xs') # ys = listIndices qs' xs
  in (qs2 # (x' :: xs')) # (y :: ys)

|||Remove an element at a given index in the vector
private 
removeElem : {n : Nat} -> Vect (S n) Qubit -> Nat -> Vect n Qubit
removeElem (x :: xs) 0 = xs
removeElem (x :: xs) (S k) = case xs of
                                  [] => []
                                  y :: ys => x :: removeElem xs k


|||add the indices of the new qubits to the vector in the SimulatedState
private 
newQubitsPointers : (p : Nat) -> (counter : Nat) -> LFstPair (LVect p Qubit) (Vect p Qubit)
newQubitsPointers 0 _ = ([] # [])
newQubitsPointers (S p) counter = 
  let (q # v) = newQubitsPointers p (S counter)
  in (MkQubit counter :: q) #  (MkQubit counter :: v)

|||Auxiliary function for applying a circuit to some qubits
private
applyUnitary' : {n : Nat} -> {i : Nat} ->
                (1 _ : LVect i Qubit) -> Unitary i -> (1 _ : SimulatedState n) -> R (LPair (SimulatedState n) (LVect i Qubit))
applyUnitary' v u q = 
  let (qs # v') # ind = listIndices q v 
      qs2 = applyCirc ind u qs
  in pure1 (qs2 # v') where
    applyCirc : Vect i Nat -> Unitary i -> (1 _ : SimulatedState n) -> SimulatedState n
    applyCirc v IdGate qst = qst
    applyCirc v (H j g) st = 
      let k = index j v 
          h = simpleTensor matrixH n k
          MkSimulatedState qst q counter = applyCirc v g st
      in MkSimulatedState (h `matrixMult` qst) q counter
    applyCirc v (P p j g) st = 
      let k = index j v
          ph = simpleTensor (matrixP p) n k
          MkSimulatedState qst q counter = applyCirc v g st
      in MkSimulatedState (ph `matrixMult` qst) q counter
    applyCirc v (CNOT c t g) st = 
      let kc = index c v
          kt = index t v
          cn =  tensorCNOT n kc kt
          MkSimulatedState qst q counter = applyCirc v g st
      in MkSimulatedState (cn `matrixMult` qst) q counter


|||Auxiliary function for measurements
private
measure' : {n : Nat} -> (i : Nat) ->
           (1 _ : SimulatedState (S n)) ->
           R (LFstPair (SimulatedState n) Bool)
measure' {n} i (MkSimulatedState v w counter) = do
  let projector0 = simpleTensor matrixKet0Bra0 (S n) i
  let projection0 = projector0 `matrixMult` v
  let norm20 = normState2 projection0
  let projector1 = simpleTensor matrixKet1Bra1 (S n) i
  let projection1 = projector1 `matrixMult` v
  let norm21 = normState2 projection1
  let newQubits = removeElem w i
  randnb <- liftIO1 randomIO
  if randnb < norm20
     then do
       let proj = multScalarMatrix (inv (sqrt norm20) :+ 0) projection0
       pure1 (MkSimulatedState (projectState {n} proj i False) newQubits counter # False)
     else do
       let proj = multScalarMatrix (inv (sqrt norm21) :+ 0) projection1
       pure1 (MkSimulatedState (projectState {n} proj i True) newQubits counter # True)

|||Auxiliary function for measurements
private
measureQubits' : {n : Nat} -> {i : Nat} ->
                 (1 _ : LVect i Qubit) ->
                 (1 _ : SimulatedState (i + n)) -> R (LPair (SimulatedState n) (Vect i Bool))
measureQubits' [] qs = pure1 (qs # [])
measureQubits' (x :: xs) qs = do
  let (qs' # (MkQubit k)) # y = listIndex qs x
  (s # b) <- measure' y qs'
  (s1 # bs) <- measureQubits' xs s
  case bs of 
       [] => pure1 (s1 # [b])
       (b' :: bs') => pure1 (s1 # (b :: b' :: bs'))

------- SIMULATE CIRCUITS : OPERATIONS ON QUANTUM STATES ------


----------ADD NEW QUBITS TO QUNTUM STATES

||| Add new qubits to a Quantum State
export
newQubitsSimulated : (p : Nat) -> QuantumOp n (n+p) (LVect p Qubit)
newQubitsSimulated p = MkQST (newQubits' p) where
  newQubits' : (q : Nat) -> (1 _ : SimulatedState m) -> R (LPair (SimulatedState (m + q)) (LVect q Qubit))
  newQubits' q (MkSimulatedState qs v counter) =
    let s' = toTensorBasis (ket0 q)
        (qubits # v') = newQubitsPointers q counter
    in pure1 (MkSimulatedState (tensorProductVect qs s') (v ++ v') (counter + q) # qubits)


-------------APPLY CIRCUITS TO QUANTUM STATES


||| Apply a circuit to a SimulatedState
export
applyUnitarySimulated : {n : Nat} -> {i : Nat} ->
               (1 _ : LVect i Qubit) -> Unitary i -> QuantumOp n n (LVect i Qubit)
applyUnitarySimulated q u = MkQST (applyUnitary' q u)

------------MEASURE QUBITS

||| Measure some qubits in a quantum state
export
measureSimulated : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> QuantumOp (i + n) n (Vect i Bool)
measureSimulated v = MkQST (measureQubits' v)

||| Run all simulations : start with 0 qubit and measure all qubits at the end (end with 0 qubit)
export
runSimulated : QuantumOp 0 0 (Vect n Bool) -> IO (Vect n Bool)
runSimulated s = LIO.run (do
  ((MkSimulatedState st w c) # v) <- runQStateT (MkSimulatedState [[1]] [] 0) s
  case v of 
       [] => pure []
       (x :: xs) => pure (x :: xs))
 

export
QuantumState SimulatedState where
  newQubits    = newQubitsSimulated
  applyUnitary = applyUnitarySimulated
  measure      = measureSimulated
  run          = runSimulated
