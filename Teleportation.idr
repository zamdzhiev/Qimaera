module Teleportation

import Data.Nat
import Data.Vect
import Unitary
import LIO
import StateLT
import Injection
import LinearTypes
import Simulations

%default total

|||Example : Teleportation protocol

export
telep1 : Unitary 3
telep1 = H 0 (CNOT 0 1 (apply toBellBasis IdGate [1,2]))

export
unitary_correction : Bool -> Bool -> Unitary 1
unitary_correction b1 b2 = (if b2 then XGate else IdGate) `compose` (if b1 then ZGate else IdGate)



export
teleportation : (1 _ : Qubit) -> QuantumOp 1 1 (LFstPair Qubit (Vect 2 Bool))
teleportation q0 = do
  [q1, q2] <- newQubits 2
  [q0,q1,q2] <- applyCircuit [q0,q1,q2] telep1
  [b1, b2] <- measure [q0,q1]
  [q] <- applyCircuit [q2] (unitary_correction b1 b2) 
  pure (q # [b1, b2])
  



export
runTeleportation : IO (Vect 3 Bool)
runTeleportation = 
      run (do
         q <- newQubit
         [q] <- applyCircuit [q] HGate
         (q # [b1, b2]) <- teleportation q
         [b3] <- measure [q]
         pure [b1,b2,b3])



--test with a qubit in state H |0>
export
drawTeleportation : IO ()
drawTeleportation = do
  [b1, b2, b3] <- runTeleportation
  putStrLn "Teleportation Protocol\n\n"
  putStrLn "First circuit"
  draw telep1
  putStrLn "Measurements"
  putStrLn (show (b1, b2))
  putStrLn "\nUnitary corrections"
  draw (unitary_correction b1 b2)
  putStrLn "Measure last qubit"
  putStrLn (show b3)

export
run1000Teleportation : IO ()
run1000Teleportation = do
  (nbT, nbF) <- run1000Telep' 1000 
  putStrLn "\n\nFor 1000 measurements"
  putStrLn ("Number of True measurements : " ++ show nbT) 
  putStrLn ("Number of False measurements : " ++ show nbF) where
  run1000Telep' : Nat -> IO (Nat, Nat)
  run1000Telep' 0 = pure (0,0)
  run1000Telep' (S k) = do
    [b1, b2, b3] <- runTeleportation
    (nbT, nbF) <- run1000Telep' k
    if b3 then pure (S nbT, nbF) else pure (nbT, S nbF)

