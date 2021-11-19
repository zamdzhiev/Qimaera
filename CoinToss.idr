module CoinToss

import Data.Vect
import QStateT
import QuantumOp
import LinearTypes

||| A fair coin toss (as an IO effect) via quantum resources.
|||
||| first create a new qubit in state |0>
||| then apply a hadamard gate to it, thereby preparing state |+>
||| and finally measure the qubit and return this as the result
export
coin : QuantumOp t => IO Bool
coin = do
  [b] <- run (do
           q <- newQubit {t = t}
           q <- applyH q
           r <- measure [q]
           pure r
         )
  pure b

testCoin : IO Bool
testCoin = coin {t = SimulatedOp}
