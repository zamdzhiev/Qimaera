module Teleportation

import Data.Nat
import Data.List
import Data.Vect
import Unitary
import Control.Linear.LIO
import QStateT
import Injection
import LinearTypes
import QuantumState

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
unitary_correction b1 b2 = (if b2 then XGate else IdGate) `compose` (if b1 then ZGate else IdGate)

||| The Quantum Teleportation Protocol as a state transformer.
export
teleportation : QuantumState t =>
                (1 _ : Qubit) -> QStateT (t 1) (t 1) (LFstPair Qubit (Vect 2 Bool))
teleportation q0 = do
  [q1, q2] <- newQubits 2
  [q0,q1,q2] <- applyUnitary [q0,q1,q2] telep1
  [b1, b2] <- measure [q0,q1]
  [q] <- applyUnitary [q2] (unitary_correction b1 b2) 
  pure (q # [b1, b2])
  
||| Run the teleportation protocol where the qubit to be teleported is in state |+>.
export
runTeleportation : QuantumState t => IO (Vect 3 Bool)
runTeleportation = 
      run (do
        q <- newQubit {t = t}
        q <- applyH q
        (q # [b1, b2]) <- teleportation q
        [b3] <- measure [q]
        pure [b1,b2,b3]
      )

||| Print some useful information on the screen obtained by executing runTeleportation.
export
drawTeleportation : QuantumState t => IO ()
drawTeleportation = do
  [b1, b2, b3] <- runTeleportation {t = t}
  putStrLn "Teleportation Protocol\n\n"
  putStrLn "First circuit:"
  draw telep1
  putStrLn "Measurement results on first two qubits:"
  putStrLn (show (b1, b2))
  putStrLn "\nUnitary corrections:"
  draw (unitary_correction b1 b2)
  putStrLn "Result of measurement on the last qubit:"
  putStrLn (show b3)

