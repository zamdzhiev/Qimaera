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
consLin : (1 _ : Bool) -> (1 _ : Vect n Bool) -> Vect (S n) Bool
consLin False [] = [False]
consLin False (x :: xs) = (False :: (x `consLin` xs))
consLin True [] = [True]
consLin True (x :: xs) = (True :: (x `consLin` xs))

public export
convert : (1 _ : LVect n Bool) -> Vect n Bool
convert [] = []
convert (x :: xs) = x `consLin` (convert xs)
