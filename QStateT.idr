module QStateT

import Control.Monad.State
import LinearTypes
import LIO

%default total

public export
R : Type -> Type
R = L IO {use = Linear}


--Inspired by the indexed state monad in Haskell, and for linear types
public export
data QStateT : (initialType : Type) -> (finalType : Type) -> (returnType : Type) -> Type where
  MkQST : (1 _ : (1 _ : initialType) -> R (LPair finalType returnType)) -> QStateT initialType finalType returnType


||| Unwrap and apply a StateLT monad computation.
public export
runQStateT : (1 _ : initialType) -> (1 _ : QStateT initialType finalType returnType) -> R (LPair finalType returnType)
runQStateT i (MkQST f) = f i


public export
pure : (1 _ : a) -> QStateT t t a
pure x = MkQST (\st => pure1 (st # x))


public export
(>>=) : (1 _ : QStateT i m a) -> (1 _ : ((1 _ : a) -> QStateT m o b)) -> QStateT i o b
v >>= f = MkQST $ \i => do 
                         (a # m) <- runQStateT i v
                         runQStateT a (f m)


public export
modify : ((1 _ : i) -> o) -> QStateT i o ()
modify f = MkQST $ \i => pure1 (f i # ())


