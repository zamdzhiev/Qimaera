module OperationExamples

import Data.Nat
import Data.Vect
import Unitary
import LIO
import StateLT
import Injection
import LinearTypes
import Simulations

quantum_operation : QuantumOp 0 1 Qubit
quantum_operation = do
  q <- newQubit 
  [q] <- applyCircuit [q] HGate
  pure q


quantum_operation2 : (1 _ : Qubit) -> QuantumOp 1 1 Qubit
quantum_operation2 q = do
  [r] <- applyCircuit [q] HGate
  pure r
