module QFT

import Data.Nat
import Data.Vect
import Decidable.Equality
import Unitary
import Injection
import Lemmas

%default total

|||Quantum circuit for the Quantum Fourier Transform

--CONTROLLED PHASE GATES FOR THE QFT

Rm : Nat -> Unitary 1
Rm m = let m' = cast m in PGate (2 * pi / (pow 2 m'))

cRm : Nat -> Unitary 2
cRm m = controlled (Rm m)

--A FEW LEMMAS FOR THE QFT

kLTSucc1 : (k : Nat) -> k < (k + 1) = True
kLTSucc1 0 = Refl
kLTSucc1 (S k) = kLTSucc1 k

lemmaInj1 : (k : Nat) -> isInjective (S (k + 1)) [S k, 0] = True
lemmaInj1 k = 
  let p1 = kLTSucc1 k
  in lemmaAnd (lemmaAnd p1 Refl) Refl


--QFT

export
recursivePattern : (n : Nat) -> Unitary n
recursivePattern 0 = IdGate
recursivePattern 1 = HGate
recursivePattern (S (S k)) = 
  let t1 = (recursivePattern (S k)) # IdGate
  in rewrite sym $ lemmaplusOneRight k in apply (cRm (S k)) t1 [S k, 0] {prf = lemmaInj1 k}

export
qft : (n : Nat) -> Unitary n
qft Z = IdGate
qft (S k) = 
  let g = recursivePattern (S k)
      h = (IdGate {n = 1}) # (qft k)
  in h . g
