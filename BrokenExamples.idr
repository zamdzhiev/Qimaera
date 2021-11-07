module BrokenExamples

import Data.Nat
import Data.Vect
import Data.List
import LinearTypes
import Control.Linear.LIO
import Unitary
import QStateT
import System.Random
import Injection
import Complex
import QuantumState
import Examples

-------------------------------------- Impossible Unitaries ---------------------------------------

brokenH : Unitary 3
--brokenH = H 4 toffoli

--Error: While processing right hand side of brokenH. Can't find an implementation for == (compare 4 3) LT = True.



brokenCNOT : Unitary 2
--brokenCNOT = CNOT 1 1 IdGate

--Error: While processing right hand side of brokenCNOT. Can't find an implementation for not (== 1 1) = True.



brokenApply1 : Unitary 3
--brokenApply1 = apply toBellBasis toffoli [1,4]

--Error: While processing right hand side of brokenApply1. Can't find an implementation for allSmaller [1, 4] 3 && Delay (allDifferent [1, 4]) = True.



brokenApply2 : Unitary 3
--brokenApply2 = apply toffoli IdGate [1,2,1]

--Error: While processing right hand side of brokenApply2. Can't find an implementation for allSmaller [1, 2, 1] 3 && Delay (allDifferent [1, 2,1]) = True.


--------------------------------- BROKEN QUANTUM STATE OPERATIONS ---------------------------------

brokenOp1 : QuantumOp 0 0 (Vect 4 Bool)
{-brokenOp1  = do
  [q1,q2,q3,q4] <- newQubits 4
  [b3] <- measure [q3]
  [r4,r3,r1] <- applyUnitary [q4,q3,q1] (X 0 IdGate) --trying to reuse q3
  [b1,b4,b2] <- measure [r1,r4,q2]
  pure ([b1,b2,b3,b4])
  -}
--Error: While processing right hand side of brokenOp1. q3 is not accessible in this context.

brokenOp2 : QuantumOp 0 0 (Vect 4 Bool)
{-brokenOp2  = do
  [q1,q2,q3,q4] <- newQubits 4
  [b3] <- measure [q3]
  [r4,r2,r1] <- applyUnitary [q4,q2,q1] (X 0 IdGate) 
  [b1,b4,b2] <- measure [r1,r4,q2] --trying to reuse the name q2
  pure ([b1,b2,b3,b4])
  -}
--Error: While processing right hand side of brokenOp2. q2 is not accessible in this context.

