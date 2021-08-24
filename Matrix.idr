module Matrix

import Data.Vect
import Data.Nat
import Complex
import Lemmas

%default total

public export
Matrix : Nat -> Nat ->  Type
Matrix n m = Vect n (Vect m (Complex Double))

public export
Vector : Nat -> Type
Vector n = Vect n (Complex Double)


private
idRow : (n : Nat) -> Nat -> Vector n
idRow 0 _ = []
idRow (S k) 0 = 1 :: idRow k (S k)
idRow (S k) (S p) = 0 :: idRow k p

export
matrixId : (n : Nat) -> Matrix n n
matrixId n = matrixId' n 0 n where
  matrixId' : (k : Nat) -> (p : Nat) -> (n : Nat) -> Matrix k n
  matrixId' 0 p n = []
  matrixId' (S k) p n = (idRow n p) :: matrixId' k (S p) n

export
addVector : Vector n -> Vector n -> Vector n
addVector [] [] = []
addVector (x::xs) (y::ys) = (x+y) :: (addVector xs ys)

export
addMatrix : Matrix n m -> Matrix n m -> Matrix n m
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = (addVector x y) :: (addMatrix xs ys)

private
vectProduct : Vector n -> Vector n -> Complex Double
vectProduct [] [] = 0
vectProduct (x :: xs) (y :: ys) = x * y + vectProduct xs ys

private
makeCol : Vector n -> Matrix n 1
makeCol [] = []
makeCol (x :: xs) = [x] :: makeCol xs

private
addCol : Vector n -> Matrix n p -> Matrix n (S p)
addCol [] [] = []
addCol (x :: xs) (v :: vs) = (x :: v) :: addCol xs vs

export
transposeMatrix : {n : Nat} -> {p : Nat} ->  Matrix n p -> Matrix p n
transposeMatrix [] = replicate _ []
transposeMatrix (x :: xs) = addCol x (transposeMatrix xs)

export
multVectMatrix : {n : Nat} -> {p : Nat} ->  Vector n -> Matrix n p -> Vector p
multVectMatrix v m =
  let mt = transposeMatrix m in multVectMatrix' v mt where
    multVectMatrix' : Vector l -> Matrix k l -> Vector k
    multVectMatrix' v [] = []
    multVectMatrix' v (x :: xs) = (vectProduct v x) :: multVectMatrix' v xs

export
matrixMult : {n : Nat} -> {m : Nat} -> {p : Nat} -> Matrix n m -> Matrix m p -> Matrix n p
matrixMult [] ys = []
matrixMult (x :: xs) ys = (multVectMatrix x ys) :: matrixMult xs ys

export
multScalarVect : Complex Double -> Vector n -> Vector n
multScalarVect _ [] = []
multScalarVect x (y :: ys) = (x * y) :: multScalarVect x ys

export
multScalarMatrix : Complex Double -> Matrix n m -> Matrix n m
multScalarMatrix _ [] = []
multScalarMatrix x (y :: ys) = multScalarVect x y :: multScalarMatrix x ys

private
concatRows : Matrix n p -> Matrix n q -> Matrix n (p + q)
concatRows [] [] = []
concatRows (x :: xs) (y :: ys) = (x ++ y) :: (concatRows xs ys)

private
concatCols : Matrix n p -> Matrix m p -> Matrix (n + m) p
concatCols v w = v ++ w

private
tensorProduct' : Vector (S n) -> Matrix p r -> Matrix p ((S n) * r)
tensorProduct' [x] m = rewrite multZeroLeftZero r in rewrite plusZeroRightNeutral r in multScalarMatrix x m
tensorProduct' (x :: y :: ys) m = (multScalarMatrix x m) `concatRows` (tensorProduct' (y :: ys) m)

export
tensorProduct : Matrix n (S m) -> Matrix p r -> Matrix (n * p) ((S m) * r)
tensorProduct [] _ = []
tensorProduct [v] xs = rewrite multZeroLeftZero p in rewrite plusZeroRightNeutral p in tensorProduct' v xs
tensorProduct (v :: w :: vs) xs = (tensorProduct' v xs) `concatCols` (tensorProduct (assert_smaller (v::w::vs) (w :: vs)) xs)

export
printComplex : Complex Double -> String
printComplex (x :+ y) =
  if y == 0 then show x
            else if x == 0 then show y ++ "i"
                 else show x ++ " + " ++ show y ++ "i"

export
printVector : Vector n -> String
printVector v = "[" ++ printVector' v ++ "]" where
  printVector' : Vector m -> String
  printVector' [] = ""
  printVector' [x] = printComplex x
  printVector' (x :: xs) = printComplex x ++ " , " ++  printVector' xs

export
printMatrix : Matrix n m -> String
printMatrix v = "[ " ++ printMat' v where
  printMat' : Matrix p q -> String
  printMat' [] = ""
  printMat' [x] = printVector x ++ " ]"
  printMat' (x :: xs) = printVector x ++ "\n  " ++ printMat' xs


------------ Lemmas about matrices ---------------------------------------

export
powPlusMultZeroRightNeutral : (n : Nat) -> plus (power 2 n) (mult 0 (power 2 n)) = power 2 n
powPlusMultZeroRightNeutral n = rewrite plusZeroRightNeutral (power 2 n) in Refl

export
multPowerPowerPlus : (base, exp, exp' : Nat) ->
                     power base (exp + exp') = (power base exp) * (power base exp')
multPowerPowerPlus base Z       exp' = 
    rewrite plusZeroRightNeutral (power base exp') in Refl
multPowerPowerPlus base (S exp) exp' =
  rewrite multPowerPowerPlus base exp exp' in
    rewrite sym $ multAssociative base (power base exp) (power base exp') in
       Refl


export
powPlusZeroRightNeutral : {m : Nat} -> Matrix (plus (plus (power 2 m) (plus (power 2 m) 0)) 0) 1 -> Matrix (plus (power 2 m) (plus (power 2 m) 0)) 1
powPlusZeroRightNeutral mat = rewrite sym $ plusZeroRightNeutral (plus (power 2 m) (plus (power 2 m) 0)) in mat





------------ LINEAR-ALGEBRAIC SIMULATION: MATRIX OPERATIONS ---------------



export
matrixH : Matrix 2 2
matrixH = [[(1/(sqrt 2)) :+ 0, (1/(sqrt 2)) :+ 0], [(1/(sqrt 2)) :+ 0 , (-1/(sqrt 2)) :+ 0]]

export
matrixP : Double -> Matrix 2 2
matrixP p = [[1 , 0] , [0, cis p]]

export
matrixCNOT : Matrix 4 4
matrixCNOT = [[1,0,0,0] , [0,1,0,0] , [0,0,0,1] , [0,0,1,0]]

export
matrixX : Matrix 2 2
matrixX = [[0,1] , [1,0]]

export
matrixKet0Bra0 : Matrix 2 2
matrixKet0Bra0 = [[1,0] , [0,0]]

export
matrixKet1Bra1 : Matrix 2 2
matrixKet1Bra1 = [[0,0] , [0,1]]

export
simpleTensor : Matrix 2 2 -> (n : Nat) -> Nat -> Matrix (power 2 n) (power 2 n)
simpleTensor _ 0 _ = [[1]]
simpleTensor m (S n) 0 = m `tensorProduct` (simpleTensor m n (S n))
simpleTensor m (S n) (S k) = (matrixId 2) `tensorProduct` (simpleTensor m n k)

export
tensorCnotAux : (n : Nat) -> (control : Nat) -> (target : Nat) -> Matrix (power 2 n) (power 2 n)
tensorCnotAux 0 _ _ = [[1]]
tensorCnotAux (S n) 0 0 = (matrixId 2) `tensorProduct` (tensorCnotAux n (S n) (S n)) --should not be happening
tensorCnotAux (S n) 0 (S m) = matrixKet1Bra1 `tensorProduct` (tensorCnotAux n (S n) m)
tensorCnotAux (S n) (S k) 0 = matrixX `tensorProduct` (tensorCnotAux n k (S n))
tensorCnotAux (S n) (S k) (S m) = (matrixId 2) `tensorProduct` (tensorCnotAux n k m)

export
tensorCNOT : (n : Nat) -> (control : Nat) -> (target : Nat) -> Matrix (power 2 n) (power 2 n)
tensorCNOT nbQbits control target = (simpleTensor matrixKet0Bra0 nbQbits control) `addMatrix` (tensorCnotAux nbQbits control target)

export
tensorProductVect : Matrix (power 2 n) 1 -> Matrix (power 2 p) 1 -> Matrix (power 2 (n + p)) 1
tensorProductVect xs ys =
  rewrite multPowerPowerPlus 2 n p
  in tensorProduct xs ys

export
normState2 : Matrix n 1 -> Double
normState2 [] = 0
normState2 ([x] :: xs) = let m = magnitude x in m * m + normState2 xs


export
toTensorBasis : Matrix n 2 -> Matrix (power 2 n) 1
toTensorBasis [] = [[1]]
toTensorBasis ([x,y] :: xs) = tensorProduct [[x] , [y]] (toTensorBasis xs)

export
ket0 : (n : Nat) -> Matrix n 2
ket0 0 = []
ket0 (S k) = [1 , 0] :: ket0 k

export
inv : Double -> Double
inv x = if x == 0 then 0 else 1/x

export
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
