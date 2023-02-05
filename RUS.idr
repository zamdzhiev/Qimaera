module RUS

import Data.Vect
import QStateT
import QuantumOp
import LinearTypes
import Unitary
import Data.List

||| Problem: Given an input qubit |q> and a single-qubit unitary operation U,
|||          return the state U|q>. The "Repeat Until Success" approach solves
|||          this problem in the following way:
|||
||| 1. Prepare a new qubit in state |0>
||| 2. Apply some two-qubit unitary operation U' (depends on U)
||| 3. Measure the auxiliary qubit
||| 4. With (high) probability the result is now U|q> and then stop.
||| 5. With (low) probability the result is state E|q>, where E is some other unitary operator
|||    (depending on U), so we uncompute the error by applying E^dagger and we go back to step 1.
||| For more information, see https://arxiv.org/abs/1311.1074

export
RUS : QuantumOp t => (1 _ : Qubit) -> (u' : Unitary 2) -> (e : Unitary 1) -> QStateT (t 1) (t 1) Qubit
RUS q u' e = do
  q' <- newQubit
  [q',q] <- applyUnitary [q',q] u'
  b <- measureQubit q'
  if b then do
         [q] <- applyUnitary [q] (adjoint e)
         RUS q u' e
       else pure q 

||| Figure 8 of https://arxiv.org/abs/1311.1074
example_u' : Unitary 2
example_u' = H 0 $ T 0 $ CNOT 0 1 $ H 0 $ CNOT 0 1 $ T 0 $ H 0 IdGate

export
runRUS : QuantumOp t => IO Bool
runRUS = do
  [b] <- run (do
              q <- newQubit {t = t}
              q <- RUS q example_u' IdGate
              measure [q]
         )
  pure b

export
testRUS : IO Bool
testRUS = runRUS {t = SimulatedOp}

export
testMultipleRUS : Nat -> IO ()
testMultipleRUS n = do
  let f = testRUS
  s <- sequence (Data.List.replicate n f)
  let heads = filter (== True) s
  putStrLn $ "Number of '1' outcomes: " ++ (show (length heads)) ++ " out of " ++ (show n) ++ " measurements."
