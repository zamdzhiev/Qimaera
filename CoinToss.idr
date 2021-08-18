module CoinToss

import Data.Vect
import Data.List
import QStateT
import Simulations

||| A quantum state transformer which realises a fair coin toss in the obvious way:
||| first create a new qubit in state |0>
||| then apply a hadamard gate to it, thereby preparing state |+>
||| and finally measure the qubit and return this as the result
coinT : {t : Nat -> Type} -> QuantumState t => QStateT (t 0) (t 0) (Vect 1 Bool)
coinT = do
  q <- newQubit
  q <- applyH q
  b <- measureQubit q
  pure (if b then [True] else [False])

||| A fair coin toss (as an IO effect) via quantum resources.
coin : {t : Nat -> Type} -> QuantumState t => IO Bool
coin = do
  [b] <- run (coinT {t = t})
  pure b

-- Perform 1000 fair coin tosses and count the number of heads
-- (via simulating the quantum dynamics).
main : IO ()
main = do
  let f = coin {t = SimulatedState}
  s <- sequence (Data.List.replicate 1000 f)
  let heads = filter (== True) s
  putStrLn $ "Number of heads: " ++ (show (length heads))
