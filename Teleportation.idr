module Teleportation

import Data.Nat
import Data.List
import Data.Vect
import Unitary
import Control.Linear.LIO
import QStateT
import Injection
import LinearTypes
import QuantumOp
import Examples

%default total

||| Example : Teleportation protocol

||| The unitary circuit that we have to apply to the initial state.
export
telep1 : Unitary 3
telep1 = H 0 (CNOT 0 1 (apply toBellBasis IdGate [1,2]))

||| The unitary correction that has to be applied after performing the measurement in the Bell basis.
||| The two Bool arguments indicate the measurement results.
export
unitary_correction : Bool -> Bool -> Unitary 1
unitary_correction b1 b2 = (if b2 then XGate else IdGate) . (if b1 then ZGate else IdGate)

||| The Quantum Teleportation Protocol as a state transformer.
export
teleportation : QuantumOp t =>
                (1 _ : Qubit) -> QStateT (t 1) (t 1) Qubit
teleportation q0 = do
  [q1, q2] <- newQubits 2
  [q0,q1,q2] <- applyUnitary [q0,q1,q2] telep1
  [b1, b2] <- measure [q0,q1]
  [q] <- applyUnitary [q2] (unitary_correction b1 b2) 
  pure q
  
||| Run the teleportation protocol two times on specific input states
export
exampleTeleportation : QuantumOp t => IO (Vect 2 Bool)
exampleTeleportation = 
      run (do
        q <- newQubit {t = t}
        q <- applyH q
        q <- teleportation q
        [b1] <- measure [q]
        -- Second teleportation run
        q <- newQubit {t = t}
        [q] <- applyUnitary [q] XGate
        q <- teleportation q
        [b2] <- measure [q]
        pure [b1,b2]
      )
