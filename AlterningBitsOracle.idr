module AlterningBitsOracle

import Data.Nat
import Unitary
import Lemmas


%default total

|||Alternating bits oracle : checks if the input alternates, i-e does not have a pair of adjacent qubits in stae 00 or 11


lemmaFlip : (i : Nat) -> (k : Nat) -> (p : S (S i) < k = True) -> i < k = True
lemmaFlip 0 k p = lemmaCompLT0 k 2 
lemmaFlip (S i) (S k) p = lemmaFlip i k p

lemmaSolve : (n : Nat) -> n < S (S n) = True
lemmaSolve 0 = Refl
lemmaSolve (S k) = lemmaSolve k

flip : (n : Nat) -> (i : Nat) -> {auto prf : i < S (S n) = True} -> Unitary (S (S n))
flip n 0 = X 0 IdGate
flip n 1 = X 1 IdGate
flip n (S (S i)) = X (S (S i)) (flip n i {prf = lemmaFlip i (S (S n)) prf})


export 
solve : (n : Nat) -> Unitary ((S (S n)) + 1)
solve n = 
  let circ1 = (flip n (S n) {prf = lemmaLTSucc n}) # IdGate {n=1}
      circ2 = flip n n {prf = lemmaSolve n} # IdGate {n = 1}
      circ1' = circ1 @@ multipleQubitControlledNOT ((S (S n)) + 1) @@ circ1
      circ2' = circ2 @@ multipleQubitControlledNOT ((S (S n)) + 1) @@ circ2
  in circ1' @@ circ2'
