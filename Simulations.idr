module Simulations

import Data.Vect
import Data.Nat
import Decidable.Equality
import System.File
import Injection
import Matrix
import Complex
import Random
import Lemmas
import StateLT
import LIO
import LinearTypes
import Unitary

----- SIMULATE CIRCUITS : QUANTUM STATES AND QUBITS -----------

|||The Qubit type holds an index
export
data Qubit : Type where
  MkQubit : (n : Nat) -> Qubit


|||QuantumState : vector representation of the quantum state, vector of indices of the qubits, counter
export
data QuantumState : Nat -> Type where
  MkQuantumState : {n : Nat} -> Matrix (power 2 n) 1 -> Vect n Qubit -> Nat -> QuantumState n

public export
QuantumOp : Nat -> Nat -> Type -> Type
QuantumOp n m t = QStateT (QuantumState n) (QuantumState m) t


------------SIMULATE CIRCUITS : MATRIX OPERATIONS--------------

private
matrixH : Matrix 2 2
matrixH = [[(1/(sqrt 2)) :+ 0, (1/(sqrt 2)) :+ 0], [(1/(sqrt 2)) :+ 0 , (-1/(sqrt 2)) :+ 0]]

private
matrixP : Double -> Matrix 2 2
matrixP p = [[1 , 0] , [0, cis p]]

private
matrixCNOT : Matrix 4 4
matrixCNOT = [[1,0,0,0] , [0,1,0,0] , [0,0,0,1] , [0,0,1,0]]

private
matrixX : Matrix 2 2
matrixX = [[0,1] , [1,0]]

private
matrixKet0Bra0 : Matrix 2 2
matrixKet0Bra0 = [[1,0] , [0,0]]

private
matrixKet1Bra1 : Matrix 2 2
matrixKet1Bra1 = [[0,0] , [0,1]]

private
simpleTensor : Matrix 2 2 -> (n : Nat) -> Nat -> Matrix (power 2 n) (power 2 n)
simpleTensor _ 0 _ = [[1]]
simpleTensor m (S n) 0 = m `tensorProduct` (simpleTensor m n (S n))
simpleTensor m (S n) (S k) = (matrixId 2) `tensorProduct` (simpleTensor m n k)

private
tensorCnotAux : (n : Nat) -> (control : Nat) -> (target : Nat) -> Matrix (power 2 n) (power 2 n)
tensorCnotAux 0 _ _ = [[1]]
tensorCnotAux (S n) 0 0 = (matrixId 2) `tensorProduct` (tensorCnotAux n (S n) (S n)) --should not be happening
tensorCnotAux (S n) 0 (S m) = matrixKet1Bra1 `tensorProduct` (tensorCnotAux n (S n) m)
tensorCnotAux (S n) (S k) 0 = matrixX `tensorProduct` (tensorCnotAux n k (S n))
tensorCnotAux (S n) (S k) (S m) = (matrixId 2) `tensorProduct` (tensorCnotAux n k m)

private
tensorCNOT : (n : Nat) -> (control : Nat) -> (target : Nat) -> Matrix (power 2 n) (power 2 n)
tensorCNOT nbQbits control target = (simpleTensor matrixKet0Bra0 nbQbits control) `addMatrix` (tensorCnotAux nbQbits control target)

private
tensorProductVect : Matrix (power 2 n) 1 -> Matrix (power 2 p) 1 -> Matrix (power 2 (n + p)) 1
tensorProductVect xs ys =
  rewrite multPowerPowerPlus 2 n p
  in tensorProduct xs ys

private
normState2 : Matrix n 1 -> Double
normState2 [] = 0
normState2 ([x] :: xs) = let m = magnitude x in m * m + normState2 xs


private
toTensorBasis : Matrix n 2 -> Matrix (power 2 n) 1
toTensorBasis [] = [[1]]
toTensorBasis ([x,y] :: xs) = tensorProduct [[x] , [y]] (toTensorBasis xs)

private
ket0 : (n : Nat) -> Matrix n 2
ket0 0 = []
ket0 (S k) = [1 , 0] :: ket0 k

private
inv : Double -> Double
inv x = if x == 0 then 0 else 1/x

private
projectState : {n : Nat} -> Matrix (power 2 (S n)) 1 -> (i : Nat) -> 
               Bool -> Matrix (power 2 n) 1
projectState v 0 b =
  let (v1, v2) = splitAt (power 2 n) v in
      case b of
           True => rewrite sym $ powPlusMultZeroRightNeutral n in v2
           False => v1
projectState {n = 0} _ (S k) _ = [[1]]
projectState {n = S m} v (S k) b =
  let (v1, v2) = splitAt (power 2 (S m)) v
      v1' = projectState {n = m} v1 k b
      v2' = projectState {n = m} (powPlusZeroRightNeutral v2) k b
  in rewrite plusZeroRightNeutral (power 2 m) in v1' ++ v2'




------ SIMULATE CIRCUITS : AUXILIARY (PRIVATE) FUNCTIONS ------


|||Find an element in a list : used to find the wire of a qubit
private
listIndex' : {n : Nat} -> Vect n Qubit -> Qubit -> Nat
listIndex' [] _ = 0
listIndex' (MkQubit x :: xs) (MkQubit k) = if x == k then 0 else S (listIndex' xs (MkQubit k))

private
listIndex : (1 _ : QuantumState n) -> (1 _ : Qubit) -> LFstPair (LPair (QuantumState n) Qubit) Nat
listIndex (MkQuantumState qs v counter) (MkQubit k) = (MkQuantumState qs v counter # MkQubit k) # (listIndex' v (MkQubit k))

private 
listIndices : (1 _ : QuantumState n) -> (1 _ : LVect i Qubit) -> LFstPair (LPair (QuantumState n) (LVect i Qubit)) (Vect i Nat)
listIndices qs [] = (qs # []) # []
listIndices qs (x :: xs) = 
  let (qs' # x') # y = listIndex qs x
      (qs2 # xs') # ys = listIndices qs' xs
  in (qs2 # x' :: xs') # (y :: ys)

|||Remove an element at a given index in the vector
private 
removeElem : {n : Nat} -> Vect (S n) Qubit -> Nat -> Vect n Qubit
removeElem (x :: xs) 0 = xs
removeElem (x :: xs) (S k) = case xs of
                                  [] => []
                                  y :: ys => x :: removeElem xs k


|||add the indices of the new qubits to the vector in the QuantumState
private 
newQubitsPointers : (p : Nat) -> (counter : Nat) -> LFstPair (LVect p Qubit) (Vect p Qubit)
newQubitsPointers 0 _ = ([] # [])
newQubitsPointers (S p) counter = 
  let (q # v) = newQubitsPointers p (S counter)
  in (MkQubit counter :: q) #  (MkQubit counter :: v)

|||Auxiliary function for applying a circuit to some qubits
private
applyCircuit' : {n : Nat} -> {i : Nat} ->
                (1 _ : LVect i Qubit) -> Unitary i -> (1 _ : QuantumState n) -> R (LPair (QuantumState n) (LVect i Qubit))
applyCircuit' v u q = 
  let (qs # v') # ind = listIndices q v 
      qs2 = applyCirc ind u qs
  in pure1 (qs2 # v') where
    applyCirc : Vect i Nat -> Unitary i -> (1 _ : QuantumState n) -> QuantumState n
    applyCirc v IdGate qst = qst
    applyCirc v (H j g) st = 
      let k = index j v 
          h = simpleTensor matrixH n k
          MkQuantumState qst q counter = applyCirc v g st
      in MkQuantumState (h `matrixMult` qst) q counter
    applyCirc v (P p j g) st = 
      let k = index j v
          ph = simpleTensor (matrixP p) n k
          MkQuantumState qst q counter = applyCirc v g st
      in MkQuantumState (ph `matrixMult` qst) q counter
    applyCirc v (CNOT c t g) st = 
      let kc = index c v
          kt = index t v
          cn =  tensorCNOT n kc kt
          MkQuantumState qst q counter = applyCirc v g st
      in MkQuantumState (cn `matrixMult` qst) q counter


|||Auxiliary function for measurements
private
measure' : {n : Nat} -> (i : Nat) ->
           (1 _ : QuantumState (S n)) ->
           R (LFstPair (QuantumState n) Bool)
measure' {n} i (MkQuantumState v w counter) = do
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
       pure1 (MkQuantumState (projectState {n} proj i False) newQubits counter # False)
     else do
       let proj = multScalarMatrix (inv (sqrt norm21) :+ 0) projection1
       pure1 (MkQuantumState (projectState {n} proj i True) newQubits counter # True)

|||Auxiliary function for measurements
private
measureQubits' : {n : Nat} -> {i : Nat} ->
                 (1 _ : LVect i Qubit) ->
                 (1 _ : QuantumState (i + n)) -> R (LPair (QuantumState n) (Vect i Bool))
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

|||Add new qubits to a Quantum State
export
newQubits : (p : Nat) -> QuantumOp n (n+p) (LVect p Qubit)
newQubits p = MkQST (newQubits' p) where
  newQubits' : (q : Nat) -> (1 _ : QuantumState m) -> R (LPair (QuantumState (m + q)) (LVect q Qubit))
  newQubits' q (MkQuantumState qs v counter) =
    let s' = toTensorBasis (ket0 q)
        (qubits # v') = newQubitsPointers q counter
    in pure1 (MkQuantumState (tensorProductVect qs s') (v ++ v') (counter + q) # qubits)

|||Add only one new qubit to a quantum state
export
newQubit : QuantumOp n (n+1) Qubit
newQubit = do
  [q] <- newQubits 1
  pure q



-------------APPLY CIRCUITS TO QUANTUM STATES


|||Apply a circuit to a QuantumState
export
applyCircuit : {n : Nat} -> {i : Nat} ->
               (1 _ : LVect i Qubit) -> Unitary i -> QuantumOp n n (LVect i Qubit)
applyCircuit q u = MkQST (applyCircuit' q u)


export
applyH : {n : Nat} -> (1 _ : Qubit) -> QuantumOp n n Qubit
applyH q = do
  [q1] <- applyCircuit {n} {i = 1} [q] HGate 
  pure q1

export
applyP : {n : Nat} -> Double -> (1 _ : Qubit) -> QuantumOp n n Qubit
applyP p q = do
  [q1] <- applyCircuit {n} {i = 1} [q] (PGate p)
  pure q1

export
applyCNOT : {n : Nat} -> (1 _ : Qubit) -> Qubit -> QuantumOp n n (LPair Qubit Qubit)
applyCNOT q1 q2 = do
  [q1,q2] <- applyCircuit {n} {i = 2} [q1,q2] CNOTGate
  pure (q1 # q2)

------------MEASURE QUBITS

|||Measure some qubits in a quantum state
export
measure : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> QuantumOp (i + n) n (Vect i Bool)
measure v = MkQST (measureQubits' v)


|||Same as measure, but with an initial state of n + i instead of i + n qubits to avoid theorem proving in some cases
export
measure2 : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> QuantumOp (n + i) n (Vect i Bool)
measure2 v = rewrite plusCommutative n i in
          let res = measure v
          in res

|||Measure only one qubit
export
measureQubit : {n : Nat} -> (1 _ : Qubit) -> QuantumOp (S n) n Bool
measureQubit q = do
  [b] <- measure [q]
  pure b


-------------RUN

|||Run all simulations : start with 0 qubit and measure all qubits at the end (end with 0 qubit)
public export
run : QuantumOp 0 0 (Vect n Bool) -> IO (Vect n Bool)
run s = LIO.run (do
  ((MkQuantumState st w c) # v) <- runQStateT (MkQuantumState [[1]] [] 0) s
  case v of 
       [] => pure []
       (x :: xs) => pure (x :: xs))
 


