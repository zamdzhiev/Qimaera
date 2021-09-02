module CoinToss

import Data.Vect
import QStateT
import QuantumState

||| A quantum state transformer which realises a fair coin toss in the obvious way:
||| first create a new qubit in state |0>
||| then apply a hadamard gate to it, thereby preparing state |+>
||| and finally measure the qubit and return this as the result
coinT : QuantumState t => QStateT (t 0) (t 0) (Vect 1 Bool)
coinT = do
  q <- newQubit
  q <- applyH q
  b <- measureQubit q
  pure (if b then [True] else [False])

||| A fair coin toss (as an IO effect) via quantum resources.
export
coin : QuantumState t => IO Bool
coin = do
  [b] <- run (coinT {t = t})
  pure b
