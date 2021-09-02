module Grover

import Data.Nat
import Data.Vect
import Decidable.Equality
import Unitary
import Injection
import LinearTypes
import Lemmas
import Control.Linear.LIO
import QStateT
import AlterningBitsOracle
import QuantumState

%default total

|||GROVER'S ALGORITHM
|||1. Start with |0> ¤ n
|||2. Apply H ¤ n
|||3. Grover iteration
|||   3.1 : Apply oracle
|||   3.2 : Apply H ¤ n
|||   3.3 : Amplification
|||   3.4 : Apply H ¤ n


------------- AMPLIFICATION-------------

public export total
amplification : (n : Nat) -> Unitary n
amplification 0 = IdGate
amplification 1 = IdGate
amplification (S k) = 
  let x = tensorn (S k) (X 0 IdGate)
      h1 = H k {prf = lemmaLTSucc k} x
      c = bigControlledCNOT (S k) @@ h1
      h2 = H k {prf = lemmaLTSucc k} c
  in x @@ h2 

---------------GROVER ITERATION--------------

public export total
groverIteration : (n : Nat) -> {p : Nat} -> (oracle : Unitary (n + p)) -> Unitary (n + p)
groverIteration n oracle = 
  let h = tensorn n (H 0 IdGate) 
  in (h # IdGate) @@ (amplification n # IdGate) @@ (h # IdGate) @@ oracle

public export total
repeatGroverIteration : (k : Nat) -> (n : Nat) -> {p : Nat} -> (oracle : Unitary (n + p)) -> Unitary (n + p)
repeatGroverIteration 0 n _ = IdGate
repeatGroverIteration (S k) n oracle = (groverIteration n oracle) @@ (repeatGroverIteration k n oracle)

----------------GROVER'S ALGORITHM------------------

xhAncilla : (p : Nat) -> Unitary p
xhAncilla 0 = IdGate
xhAncilla (S p) = let xh = (H 0 IdGate) @@ (X 0 IdGate) in rewrite sym $ lemmaplusOneRight p in IdGate # xh

hxAncilla : (p : Nat) -> Unitary p
hxAncilla 0 = IdGate 
hxAncilla (S p) = let xh = (X 0 IdGate) @@ (H 0 IdGate) in rewrite sym $ lemmaplusOneRight p in IdGate # xh

public export total
grover' : (n : Nat) -> {p : Nat} -> (oracle : Unitary (n + p)) -> (nbIter : Nat) -> Unitary (n + p)
grover' n oracle nbIter = 
  let h = (tensorn n (H 0 IdGate)) # xhAncilla p
  in (IdGate # hxAncilla p) @@ (repeatGroverIteration nbIter n oracle) @@ h
  

public export total
grover : QuantumState t =>
         (n : Nat) -> {p : Nat} -> (oracle : Unitary (n + p)) -> (nbIter : Nat) -> IO (Vect n Bool)
grover n oracle nbIter = do
    let circuit = grover' n oracle nbIter
    w <- run (do
                 q <- newQubits {t=t} (n + p)
                 q <- applyUnitary q circuit
                 v <- measureAll q
                 pure v
                 )
    pure (take n w)


--------------------------SMALL TEST---------------------------

--Example with the alternating bits oracle

public export
testGrover : IO (Vect 4 Bool)
testGrover = 
  grover {t = SimulatedState} 4 {p = 1} (solve 2) 1


