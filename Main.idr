module Main

import Data.Nat
import Data.Vect
import Data.List
import LinearTypes
import Control.Linear.LIO
import Unitary
import QStateT
import Teleportation
import System.Random
import Injection
import QFT
import Grover
import AlterningBitsOracle
import VQE
import Complex
import QuantumState
import CoinToss

%default total
testDepth : Unitary 3
testDepth = 
--  CNOT 0 1 (CNOT 2 1 (H 1 (CNOT 0 2 IdGate)))
--  H 2 (H 1 (H 0 (H 1 IdGate)))
  CNOT 1 2 (CNOT 0 2 (CNOT 0 1 (H 1 (P 0.5 1 (H 1 IdGate)))))





testBreak : QuantumOp 0 0 (Vect 6 Bool)
testBreak  = do
  [q1,q2,q3,q4] <- newQubits 4
  [b3] <- measure [q3]
  [q5,q6] <- newQubits 2
  [q4,q2,q5] <- applyUnitary [q4,q2,q5] (X 0 IdGate)
  [b1,b4,b2] <- measure [q1,q4,q2]
  [b5,b6] <- measure [q5,q6]
  pure ([b1,b2,b3,b4,b5,b6])


testG : (nbIter : Nat) -> IO (Vect 3 Nat)
testG 0 = pure [0,0,0]
testG (S k) = do
  [a,b,c] <- testG k
  v <- testGrover
  case v of
       [True,False,True,False] => pure [S a,b,c]
       [False,True,False,True] => pure [a,S b,c]
       _ => pure [a,b,S c]
  
testCH : IO (Vect 2 Bool)
testCH = run (
  do 
    [q0,q1] <- newQubits {t = SimulatedState} 2
    [q0] <- applyUnitary [q0] XGate
    [q0,q1] <- applyUnitary [q0,q1] controlledH
    measure [q0,q1])


-- Perform 1000 fair coin tosses and count the number of heads
-- (via simulating the quantum dynamics).
testCoins : IO ()
testCoins = do
  let f = coin {t = SimulatedState}
  s <- sequence (Data.List.replicate 1000 f)
  let heads = filter (== True) s
  putStrLn $ "Number of heads: " ++ (show (length heads))


export
testVQE : IO ()
testVQE = do
  putStrLn "\nSmall test VQE"
  w <- VQE {t = SimulatedState} 3 (replicate 8 (replicate 8 0)) 2 1
  putStrLn (show w)
  putStrLn "\nprinting another ansatz:"
  draw (ansatz 2 2 [[1,2],[9,10],[17,18]] [[5,6],[13,14],[21,22]])

||| Call the drawTeleportation function (using the SimulatedState implementation)
||| then execute the runTeleportation function 1000 times and report on the
||| observed measurement results on the third qubit
||| (which is in state |+> at the end of the teleportation protocol).
export
testTeleport : IO ()
testTeleport = do
  drawTeleportation {t = SimulatedState}
  l <- sequence (Data.List.replicate 1000 (runTeleportation {t = SimulatedState}))
  let nbT = length $ filter (\x => (last x) == True) l
  putStrLn "\n\nFor 1000 measurements"
  putStrLn ("Number of True measurements : " ++ show nbT) 

export
main : IO ()
main = do
--  testVQE
--  putStrLn (show (depth testDepth))
--  testCoins
--  drawTeleportation
--  testTeleport
--  putStrLn "\n\n\nQuantum Fourier Transform for n = 3"
  draw (qft 3)
--  putStrLn "\nSmall test Grover"
--  v <- testGrover
--  putStrLn (show v)
--  putStrLn "\nSmall test VQE"
--  w <- VQE 3 (replicate 8 (replicate 8 0)) 2 1
--  putStrLn (show w)
--  draw (solve 2)
--  draw (ansatz 4 2 [[1,2,3,4],[9,10,11,12],[17,18,19,20]] [[5,6,7,8],[13,14,15,16],[21,22,23,24]])
--  [b1,b2] <- testCH
--  putStrLn (show (b1,b2))
  pure ()

