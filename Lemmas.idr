module Lemmas

import Data.Nat
import Data.Vect
import Decidable.Equality
import Injection
import Complex

%default total

export
lemmaplusOneRight : (n : Nat) -> n + 1 = S n
lemmaplusOneRight n = rewrite plusCommutative n 1 in Refl

export
lemmaPlusSRight : (n : Nat) -> (k : Nat) -> plus n (S k) = S (plus n k)
lemmaPlusSRight Z     k = Refl
lemmaPlusSRight (S p) k = rewrite lemmaPlusSRight p k in Refl

--LEMMAS ABOUT &&

export
lemmaAndLeft : {a : Bool} -> {b : Bool} -> (a && b = True) -> (a = True)
lemmaAndLeft {a = True} {b} p =  Refl
lemmaAndLeft {a = False} {b} p impossible

export
lemmaAndRight : {a : Bool} -> {b : Bool} -> (a && b = True) -> (b = True)
lemmaAndRight {a} {b = True} p = Refl
lemmaAndRight {a = True} {b = False} p impossible
lemmaAndRight {a = False} {b = False} p impossible

export
lemmaAnd : {a : Bool} -> {b : Bool} -> (a = True) -> (b = True) -> (a && b = True)
lemmaAnd {a = True} {b = True} p1 p2 = Refl





--LEMMAS ABOUT <, >, =, /=, <=, >= : TRANSITIVITY
export
lemmaTransLTELT : (i : Nat) -> (n : Nat) -> (p : Nat) -> (i <= n) = True -> (n < p) = True -> (i < p) = True
lemmaTransLTELT 0 0 (S k) _ _ = Refl
lemmaTransLTELT 0 (S k) (S j) _ _ = Refl
lemmaTransLTELT (S k) (S n) (S p) prf1 prf2 = rewrite lemmaTransLTELT k n p prf1 prf2 in Refl

export
lemmaTransLTLTE : (i : Nat) -> (n : Nat) -> (p : Nat) -> (i < n) = True -> (n <= p) = True -> (i < p) = True
lemmaTransLTLTE 0 (S n) (S k) prf prf1 = Refl
lemmaTransLTLTE (S k) (S n) (S p) prf prf1 = rewrite lemmaTransLTLTE k n p prf prf1 in Refl

export
lemmaTransitivity : (i : Nat) -> (n : Nat) -> (p : Nat) -> (i < n) = True -> (n < p) = True -> (i < p) = True
lemmaTransitivity 0 (S k) (S m) prf prf1 = Refl
lemmaTransitivity (S k) (S m) (S l) prf prf1 = lemmaTransitivity k m l prf prf1








--BASIC LEMMAS ABOUT <, >, =, /=, <=, >=

export
lemmaLTERefl : (n : Nat) -> (n <= n) = True
lemmaLTERefl 0 = Refl
lemmaLTERefl (S k) = lemmaLTERefl k

export
lemmaSymDiff : {x : Nat} -> {y : Nat} -> (x /= y) = True -> (y /= x) = True
lemmaSymDiff {x = 0} {y = (S m)} _ = Refl
lemmaSymDiff {x = (S k)} {y = 0} _ = Refl
lemmaSymDiff {x = (S k)} {y = (S j)} prf = lemmaSymDiff {x = k} {y = j} prf

export
lemma0LTSucc : (k : Nat) -> 0 < S k = True
lemma0LTSucc k = Refl

export
lemma1LTESucc : (k : Nat) -> 1 <= S k = True
lemma1LTESucc 0 = Refl
lemma1LTESucc (S k) = Refl

export
lemmaLTEAddR : (n : Nat) -> (p : Nat) -> n <= (n + p) = True
lemmaLTEAddR Z 0 = Refl
lemmaLTEAddR Z (S k) = Refl
lemmaLTEAddR (S n) p = lemmaLTEAddR n p

export
lemmaLTEAddL : (n : Nat) -> (p : Nat) -> p <= (n + p) = True
lemmaLTEAddL n p = rewrite plusCommutative n p in lemmaLTEAddR p n


export
lemmaDiffSuccPlus : (k : Nat) -> (p : Nat) -> (k /= S (p + k)) = True
lemmaDiffSuccPlus 0 p = Refl
lemmaDiffSuccPlus (S k) j = rewrite sym $ plusSuccRightSucc j k in lemmaDiffSuccPlus k j

export
lemmaLTSuccPlus : (k : Nat) -> (p : Nat) -> (k < S (k + p)) = True
lemmaLTSuccPlus 0 p = Refl
lemmaLTSuccPlus (S k) j = lemmaLTSuccPlus k j

export
lemmaLTSucc : (k : Nat) -> (k < S k) = True
lemmaLTSucc 0 = Refl
lemmaLTSucc (S k) = lemmaLTSucc k

export
lemmakLTSk : (k : Nat) -> (S k) < S (k + 1) = True
lemmakLTSk k = rewrite lemmaplusOneRight k in lemmaLTSucc k

export
lemmaLTSuccLT : (k : Nat) -> (n : Nat) -> (S k) < n = True -> k < n = True
lemmaLTSuccLT k 0 prf impossible
lemmaLTSuccLT 0 (S j) prf = Refl
lemmaLTSuccLT (S k) (S j) prf = lemmaLTSuccLT k j prf

export
lemmaLTESuccLT : (k : Nat) -> (n : Nat) -> (S k) <= n = True -> k < n = True
lemmaLTESuccLT k 0 prf impossible
lemmaLTESuccLT 0 (S j) prf = Refl
lemmaLTESuccLT (S k) (S j) prf = lemmaLTESuccLT k j prf


export
lemmaLTESuccLTE : (k : Nat) -> (n : Nat) -> (S k) <= n = True -> k <= n = True
lemmaLTESuccLTE k 0 prf impossible
lemmaLTESuccLTE 0 (S j) prf = Refl
lemmaLTESuccLTE (S k) (S j) prf = lemmaLTESuccLTE k j prf

export 
lemmaSuccsLT : (k : Nat) -> (n : Nat) -> (S k) < (S n) = True -> k < n = True
lemmaSuccsLT k n prf = prf

export
lemmaCompLT0 : (n : Nat) -> (j : Nat) -> {auto prf : j < n = True} -> 0 < n = True
lemmaCompLT0 n 0 {prf} = prf
lemmaCompLT0 (S p) (S k) = Refl




--LEMMAS USED BY THE APPLY FUNCTION
export
indexInjectiveVect : (j : Nat) -> (n : Nat) -> (v : Vect i Nat) ->
                     {prf : isInjective n v = True} -> {prf1 : j < i = True} ->
                     (index j v < n) = True
indexInjectiveVect Z n (x :: xs) {prf} = lemmaAndLeft (lemmaAndLeft prf)
indexInjectiveVect (S k) n (x :: xs) {prf} =
      indexInjectiveVect k n xs {prf = lemmaAnd (lemmaAndRight (lemmaAndLeft prf)) (lemmaAndRight (lemmaAndRight prf))}


export
different' : (x : Nat) -> (m : Nat) -> (xs : Vect i Nat) ->
             {prf1 : m < i = True} -> {prf2 : isDifferent x xs = True} ->
             (x /= index m xs) = True
different' x 0 (y :: xs) = lemmaAndLeft prf2
different' x (S k) (y :: xs) =
  different' x k xs {prf1} {prf2 = lemmaAndRight prf2}

private
different'' : (x : Nat) -> (m : Nat) -> (xs : Vect i Nat) ->
             {prf1 : m < i = True} -> {prf2 : isDifferent x xs = True} ->
             (index m xs /= x) = True
different'' x m xs = lemmaSymDiff (different' x m xs {prf1} {prf2})


export
differentIndexInjectiveVect : (c : Nat) -> (t : Nat) -> (n : Nat) -> {prf1 : (c /= t) = True} ->
                              (v : Vect i Nat) -> {prf2 : isInjective n v = True} ->
                              {prf3 : c < i = True} -> {prf4 : t < i = True} ->
                              (index c v /= index t v) = True
differentIndexInjectiveVect 0 (S m) n (x :: xs) =
      different' x m xs {prf1 = prf4} {prf2 = lemmaAndLeft (lemmaAndRight prf2)}
differentIndexInjectiveVect (S k) 0 n (x :: xs) =
      different'' x k xs {prf1 = prf3} {prf2 = lemmaAndLeft (lemmaAndRight prf2)}
differentIndexInjectiveVect (S k) (S j) n (x :: xs) =
  let p2 = lemmaAnd (lemmaAndRight (lemmaAndLeft prf2)) (lemmaAndRight (lemmaAndRight prf2)) in
  differentIndexInjectiveVect k j n {prf1} xs {prf2 = p2} {prf3} {prf4}







--LEMMAS USED BY THE CONTROLLED FUNCTION

export
lemmaControlledInj : (n : Nat) -> (j : Nat) -> {auto prf : j < n = True} -> isInjective (S n) [0, S j] = True
lemmaControlledInj 0 0 impossible
lemmaControlledInj 0 (S k) {prf} = prf
lemmaControlledInj (S k) 0 = Refl
lemmaControlledInj (S p) (S k) {prf} = lemmaControlledInj p k {prf} 

export
lemmaControlledInj2 : (n : Nat) -> (c : Nat) -> (t : Nat) ->
                      {auto prf1 : (c < n) = True} -> {auto prf2 : (t < n) = True} -> {auto prf3 : (c /= t) = True} ->
                      isInjective (S n) [0, S c, S t] = True
lemmaControlledInj2 0 0 t impossible
lemmaControlledInj2 0 (S k) t {prf1} = prf1
lemmaControlledInj2 (S k) 0 0 {prf3} = prf3
lemmaControlledInj2 (S k) 0 (S j) = lemmaAnd (lemmaAnd prf2 Refl) Refl
lemmaControlledInj2 (S k) (S j) 0 = lemmaAnd (lemmaAnd prf1 Refl) Refl
lemmaControlledInj2 (S k) (S j) (S i) = lemmaControlledInj2 k j i {prf1} {prf2} {prf3}






--LEMMAS USED BY THE TENSOR FUNCTION
export
isDiffRangeVect : (k : Nat) -> (length : Nat) -> (p : Nat) -> isDifferent k (rangeVect (S (p + k)) length) = True
isDiffRangeVect k 0 _ = Refl
isDiffRangeVect k (S j) p = 
  lemmaAnd (lemmaDiffSuccPlus k p) (isDiffRangeVect k j (S p))

export
allDiffRangeVect : (startIndex : Nat) -> (length : Nat) -> allDifferent (rangeVect startIndex length) = True
allDiffRangeVect startIndex 0 = Refl
allDiffRangeVect startIndex (S k) = 
  let p1 = isDiffRangeVect startIndex k 0
  in lemmaAnd p1 (allDiffRangeVect (S startIndex) k)

export
allSmallerRangeVect : (startIndex : Nat) -> (length : Nat) -> allSmaller (rangeVect startIndex length) (startIndex + length) = True
allSmallerRangeVect startIndex 0 = Refl
allSmallerRangeVect startIndex (S k) = 
  rewrite sym $ plusSuccRightSucc startIndex k in 
          lemmaAnd (lemmaLTSuccPlus startIndex k) (allSmallerRangeVect (S startIndex) k) 

export
allSmallerPlus : (n : Nat) -> (p : Nat) -> (v : Vect k Nat) -> allSmaller v n = True -> allSmaller v (n + p) = True
allSmallerPlus n p [] prf = Refl
allSmallerPlus n p (x :: xs) prf = 
  let p1 = lemmaAndLeft prf
      p2 = lemmaTransLTLTE x n (n + p) p1 (lemmaLTEAddR n p)
      p3 = lemmaAndRight prf
  in lemmaAnd p2 (allSmallerPlus n p xs p3)

