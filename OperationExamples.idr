module OperationExamples

import Data.Nat
import Data.Vect
import Unitary
import LIO
import QStateT
import Injection
import LinearTypes
import QuantumState

quantum_operation : QuantumOp 0 1 Qubit
quantum_operation = do
  q <- newQubit 
  [q] <- applyUnitary [q] HGate
  pure q


quantum_operation2 : (1 _ : Qubit) -> QuantumOp 1 1 Qubit
quantum_operation2 q = do
  [r] <- applyUnitary [q] HGate
  pure r
