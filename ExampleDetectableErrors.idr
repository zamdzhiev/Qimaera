module ExampleDetectableErrors

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
import QuantumOp
import Examples

-------------------------------------- Impossible Unitaries ---------------------------------------
-- In this example, we try to apply a Hadamard gate on a non-existing wire (index 4 on a gate of size 3)

brokenH : Unitary 3
--brokenH = H 4 toffoli

-- Error: While processing right hand side of brokenH. Can't find an implementation for == (compare 4 3) LT = True.




-- In this example, we try to apply the control and the target of a CNOT on the same wire

brokenCNOT : Unitary 2
--brokenCNOT = CNOT 1 1 IdGate

-- Error: While processing right hand side of brokenCNOT. Can't find an implementation for not (== 1 1) = True.




-- In this example, we try to apply a circuit on a non existing wire (index 4 on a gate of size 3)

brokenApply1 : Unitary 3
--brokenApply1 = apply toBellBasis toffoli [1,4]

-- Error: While processing right hand side of brokenApply1. Can't find an implementation for allSmaller [1, 4] 3 && Delay (allDifferent [1, 4]) = True.




-- In this example, we try to apply a circuit twice on the same wire

brokenApply2 : Unitary 3
--brokenApply2 = apply toffoli IdGate [1,2,1]

-- Error: While processing right hand side of brokenApply2. Can't find an implementation for allSmaller [1, 2, 1] 3 && Delay (allDifferent [1, 2,1]) = True.


--------------------------------- BROKEN QUANTUM STATE OPERATIONS ---------------------------------

-- In this example, wew try to reuse a qubit that has be measured

brokenOp1 : IO (Vect 4 Bool)
{-brokenOp1  = 
  run (do
      [q1,q2,q3,q4] <- newQubits {t = SimulatedOp} 4
      [b3] <- measure [q3]
      [r4,r3,r1] <- applyUnitary [q4,q3,q1] (X 0 IdGate) --trying to reuse q3
      [b1,b4,b2] <- measure [r1,r4,q2]
      pure ([b1,b2,b3,b4])
      )
      -} 
-- Error: While processing right hand side of brokenOp1. q3 is not accessible in this context.



-- In this example, we try to copy a qubit

brokenOp2 : IO (Vect 5 Bool)
{-brokenOp2 = 
  run (do
      [q1,q2,q3,q4] <- newQubits {t = SimulatedOp} 4
      [b3] <- measure [q3]
      [q4,q1,q5] <- applyUnitary [q4,q1,q4] (X 0 IdGate) --trying to copy q4
      [b1,b2,b5] <- measure [q1,q2,q5]
      pure [b1,b2,b3,b5,b5]
      )
      -}
--Error : While processing right hand side of brokenOp2. There are 2 uses of linear name q4. 



-- In this example, we try to reuse a pointer to an old state of a qubit (the state of the qubit has been modified)

brokenOp3 : IO (Vect 4 Bool)
{-brokenOp3  = 
  run (do
      [q1,q2,q3,q4] <- newQubits {t = SimulatedOp} 4
      [b3] <- measure [q3]
      [r4,r2,r1] <- applyUnitary [q4,q2,q1] (X 0 IdGate) 
      [b1,b4,b2] <- measure [r1,r4,q2] --trying to reuse the name q2
      pure ([b1,b2,b3,b4])
      )
      -}
--Error: While processing right hand side of brokenOp2. q2 is not accessible in this context.

