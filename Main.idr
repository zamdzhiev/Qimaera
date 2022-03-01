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
import QuantumOp
import CoinToss
import QAOA
import Graph
import Examples
import RUS

-- %default total
  

||| Perform 1000 fair coin tosses and count the number of heads
||| (via simulating the quantum dynamics).
testCoins : IO ()
testCoins = do
  let f = coin {t = SimulatedOp}
  s <- sequence (Data.List.replicate 1000 f)
  let heads = filter (== True) s
  putStrLn $ "Number of heads: " ++ (show (length heads))


||| Test graph for the QAOA problem
export
graph1 : Graph 5
graph1 = AddVertex (AddVertex (AddVertex (AddVertex (AddVertex Empty []) [True]) [True, True]) [False, True, False]) [False, False, True, True]

||| Execute QAOA with 100 samples on the previous graph to solve the MAXCUT problem
export
testQAOA : IO (Cut 5)
testQAOA = do
  QAOA {t = SimulatedOp} 100 1 graph1


||| Small test for the VQE algorithm
export
testVQE : IO Double
testVQE = do
  putStrLn "Test VQE"
  let hamiltonian = [(2, [PauliX, PauliY]),(3,[PauliZ, PauliI])]
  VQE {t = SimulatedOp} 2 hamiltonian 5 10 5


export
main : IO ()
main = do

  -- Execute the example file and draw the circuit examples
  drawExamples

  -- Draw the Quantum Fourier Transform for n = 3
--  putStrLn "\n\n\nQuantum Fourier Transform for n = 3"
--  draw (qft 3)


  -- Execute the coin toss example
  putStrLn "\nTest coin toss by performing 1000 coin tosses."
  testCoins

  -- Repeat until success
  putStrLn "\nTest 'Repeat Until Success'. Probability to measure '1' is 2/3 for this example."
  testMultipleRUS 10000

  -- VQE
--  putStrLn "\nSmall test with VQE"
--  r <- testVQE
--  putStrLn $ "result from VQE : " ++ show r

  -- QAOA
  putStrLn "\nSmall test with QAOA"
  cut <- testQAOA
  putStrLn $ "result from QAOA : " ++ show cut

  pure ()


  


