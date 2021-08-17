module Matrix

import Data.Vect
import Data.Nat
import Complex

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


