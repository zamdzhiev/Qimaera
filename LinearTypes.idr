module LinearTypes 

import Data.Vect

infixr 10 ::
infix 5 #

%default total

public export
data LFstPair : Type -> Type -> Type where
  (#) : (1 _ : a) -> b -> LFstPair a b


public export
data LVect : Nat -> Type ->  Type where
  Nil : LVect Z a
  (::) : (1 _ : a) -> (1 _ : LVect k a) -> LVect (S k) a

public export
Show a => Show (LVect n a) where
  show v = "[" ++ show' v ++ "]" where
    show' :  LVect k a -> String
    show' Nil = ""
    show' [x] = show x
    show' (x :: xs) = show x ++ " , " ++ show' xs 

public export
(Show a, Show b) => Show (LPair a b) where
  show ( a # b ) = "( " ++ show a ++ " # " ++ show b ++ " )"

public export
(Show a, Show b) => Show (LFstPair a b) where
  show ( a # b ) = "( " ++ show a ++ " # " ++ show b ++ " )"

public export
(++) : (1 xs : LVect m a) -> (1 ys : LVect n a) -> LVect (m + n) a
(++) []      ys = ys
(++) (x::xs) ys = x :: (xs ++ ys)

public export
splitAt : {n : Nat} -> (i : Nat) -> (1 xs : LVect (i+n) a) -> LPair (LVect i a) (LVect n a)
splitAt 0 xs            = [] # xs
splitAt (S k) (x :: xs) = let ys # zs = LinearTypes.splitAt k xs in
                              (x :: ys) # zs

||| diff n i = n - i
public export
diff : Nat -> Nat -> Nat
diff Z     n = Z
diff (S k) n = S (diff k n)

export
lemmaDiffZero : (n : Nat) -> diff n 0 = n
lemmaDiffZero 0 = Refl
lemmaDiffZero (S k) = rewrite lemmaDiffZero k in Refl

||| TODO: below function is needed for applyUnitary implementation.
||| But the Idris2 "rewrite linearity" bug prevents us from implementing it.
-- public export
-- splitFancy : {n : Nat} -> (i : Nat) -> {auto prf : (i < n) = True} -> (1 xs : LVect n a) -> LPair (LVect i a) (LVect (diff n i) a)
-- splitFancy 0 xs = rewrite lemmaDiffZero n in [] # xs
-- splitFancy (S k) xs = ?splitFancy_rhs_2

public export
consLin : (1 _ : Bool) -> (1 _ : Vect n Bool) -> Vect (S n) Bool
consLin False [] = [False]
consLin False (x :: xs) = False :: x :: xs
consLin True [] = [True]
consLin True (x :: xs) = True :: x :: xs

public export
toVect : (1 _ : LVect n Bool) -> Vect n Bool
toVect [] = []
toVect (x :: xs) = x `consLin` (toVect xs)
