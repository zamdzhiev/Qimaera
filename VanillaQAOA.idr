module VanillaQAOA

import Data.Nat
import Data.Vect
import Lemmas
import Unitary
import Control.Linear.LIO
import QStateT
import Injection
import LinearTypes
import Complex
import System.Random
import QuantumState

%default total

|||Vanilla QAOA : returns random numbers instead of classical optimisation

---------------CONSTRAINTS ON THE LIST OF EDGES----------------
public export
edgeDifferent : (Nat, Nat) -> List (Nat, Nat) -> Bool
edgeDifferent (x,y) [] = True
edgeDifferent (x,y) ((x1,y1) :: xs) = 
  (x/=x1 || y/=y1) && (x/=y1 || y/=x1) && edgeDifferent (x,y) xs

public export
edgesAllDifferent : List (Nat,Nat) -> Bool
edgesAllDifferent [] = True
edgesAllDifferent (x :: xs) = edgeDifferent x xs && edgesAllDifferent xs

public export
isCorrectListOfEdges : (n : Nat) -> List (Nat, Nat) -> Bool
isCorrectListOfEdges _ [] = True
isCorrectListOfEdges n ((x,y) :: xs) = 
  x /= y && x < n && y < n && isCorrectListOfEdges n xs


-------------------------QUANTUM CIRCUITS----------------------

mixingHamiltonian : (n : Nat) -> (beta : Double) -> Unitary n
mixingHamiltonian n beta = tensorn n (RxGate beta)


costHamiltonian : (n : Nat) -> (edges : List (Nat, Nat)) -> (gamma : Double) -> 
                  {auto prf : isCorrectListOfEdges n edges = True} -> 
                  Unitary n
costHamiltonian n [] _ = IdGate
costHamiltonian n ((x, y) :: xs) gamma {prf} = 
  let p1 = lemmaAndLeft (lemmaAndRight prf)
      p2 = lemmaAndLeft (lemmaAndRight (lemmaAndRight prf))
      p3 = lemmaAndLeft prf
      p4 = lemmaAndRight (lemmaAndRight (lemmaAndRight prf))
      c = CNOT x y {prf1 = p1} {prf2 = p2} {prf3 = p3} IdGate
      rz = P gamma y {prf = p2} c
      h = costHamiltonian n xs gamma {prf = p4}
  in h @@ c @@ rz

prepareState : (n : Nat) -> 
               (beta : Double) -> (gamma : Double) -> 
               (edges : List (Nat, Nat)) ->
               {auto prf : isCorrectListOfEdges n edges = True} ->
               Unitary n
prepareState n beta gamma edges = 
  mixingHamiltonian n beta @@ costHamiltonian n edges gamma @@ tensorn n HGate


-------------------------CLASSICAL PART------------------------

pretendClassicalWork : Vect n Bool -> IO (Double, Double)
pretendClassicalWork v = do
  a <- randomRIO (0,2 * pi)
  b <- randomRIO (0,2 * pi)
  pure (a,b)

-----------------------------QAOA------------------------------
export
QAOA : QuantumState t =>
       (nbIter : Nat) -> (n : Nat) -> (edges : List (Nat, Nat)) ->
       {auto prf : isCorrectListOfEdges n edges = True} ->
       {auto prf1 : edgesAllDifferent edges = True} ->
       IO (Vect n Bool)
QAOA 0 n _ = pure (replicate n False)
QAOA (S k) n edges = do
  xs <- QAOA {t} k n edges
  (beta, gamma) <- pretendClassicalWork xs
  putStrLn ("beta = " ++ (show beta) ++ " , gamma = " ++ (show gamma))
  let circuit = prepareState n beta gamma edges
  putStrLn "QAOA circuit : "
  draw circuit
  ys <- run (do
            q <- newQubits {t} n
            q <- applyUnitary q circuit
            measureAll q)
  putStrLn "Results from measurements : "
  putStrLn (show ys)
  pure ys


