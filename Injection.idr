module Injection

import Data.Vect
import Data.Nat

%default total

|||Is a Nat different from all the Nats in a vector?
public export
isDifferent : Nat -> Vect n Nat -> Bool
isDifferent n [] = True
isDifferent n (x :: xs) = (n /= x) && isDifferent n xs

|||Are all the elements of a Nat vector different?
public export
allDifferent : Vect n Nat -> Bool
allDifferent [] = True
allDifferent (x :: xs) = isDifferent x xs && allDifferent xs

|||Are all the elements in a vector smaller than a given Nat?
public export 
allSmaller : Vect n Nat -> Nat -> Bool
allSmaller [] m = True
allSmaller (x :: xs) m = (x < m) && allSmaller xs m

public export
isInjective : Nat -> Vect n Nat -> Bool
isInjective m v = allSmaller v m && allDifferent v

|||Returns the element at index k in a vector
public export
index : (k : Nat) -> Vect n Nat -> {auto prf : (k < n) = True} -> Nat
index Z     (x::_)  = x
index (S k) (_::xs) = index k xs

|||Returns the vector [1,2,...,n]
public export
rangeVect : (startIndex : Nat) -> (length : Nat) -> Vect length Nat
rangeVect k Z = []
rangeVect k (S i) = k :: rangeVect (S k) i
