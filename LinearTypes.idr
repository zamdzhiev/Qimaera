module LinearTypes 


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
(++) : (1 xs : LVect m elem) -> (1 ys : LVect n elem) -> LVect (m + n) elem
(++) []      ys = ys
(++) (x::xs) ys = x :: (xs ++ ys)


