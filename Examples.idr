module Examples

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


------------------------ Example of circuits built with unitary contructors -----------------------

||| Put two qubits initally in state |00> in the Bell state
public export
toBellBasis : Unitary 2
toBellBasis = CNOT 0 1 (H 0 IdGate)

||| Draw the circuit toBellBasis using draw function
export
drawToBellBasis : IO ()
drawToBellBasis = do
  putStrLn "\nDrawing ToBellBasis: \nCNOT 0 1 (H 0 IdGate)"
  draw toBellBasis


constructorsExample : Unitary 3
constructorsExample = H 1 (P (pi/2) 2 (CNOT 2 0 IdGate))

drawConstructorsExample : IO ()
drawConstructorsExample = do
  putStrLn "An example of circuit built with H, P and CNOT constructors :"
  putStrLn " H 1 (P (pi/2) 2 (CNOT 2 0 IdGate))"
  draw constructorsExample


---------------------------------- Examples using composition -------------------------------------

compose_example1 : Unitary 1
compose_example1 = TGate . HGate

compose_example2 : Unitary 2
compose_example2 = (H 1 IdGate) . (P pi 0 IdGate) . toBellBasis

drawComposeExamples : IO ()
drawComposeExamples = do
  putStrLn "Examples using composition"
  putStrLn "Example 1 : TGate . HGate"
  draw compose_example1
  putStrLn "Example 2 : (H 1 IdGate) . (P pi 0 IdGate) . toBellBasis"
  draw compose_example2

------------------------------------ Examples using tensor product --------------------------------

||| Example using the # operator for tensor product
tensorExample1 : Unitary 4
tensorExample1 = HGate # PGate pi # CNOTGate

||| Example using tensorn function :
|||Make n tensor products of the same unitary of size 1
tensornExample : Unitary 3
tensornExample = tensorn 3 HGate

||| Example using tensorMapSimple function
||| Tensor product of a Vector of single-qubit Unitary operators
tensorMapSimpleExample : Unitary 3
tensorMapSimpleExample = tensorMapSimple [HGate, PGate pi, HGate]

||| Example using tensorMap function
||| ||| Tensor product of a Vector of Unitary operators
tensorMapExample : Unitary 6
tensorMapExample = tensorMap [CNOTGate, toBellBasis, CNOTGate]

drawTensorExamples : IO ()
drawTensorExamples = do
  putStrLn "Examples using tensor product"
  putStrLn "Example 1 : HGate # PGate pi # CNOTGate"
  draw tensorExample1
  putStrLn "Example 2 : tensorn 3 HGate"
  draw tensornExample
  putStrLn "Example 3 : tensorMapSimple [HGate, PGate pi, HGate]"
  draw tensorMapSimpleExample
  putStrLn "Example 4 : tensorMap [CNOTGate, toBellBasis, CNOTGate]"
  draw tensorMapExample


||| Another version of toBellBasis using composition and tensor product
toBellBasis2 : Unitary 2
toBellBasis2 = CNOTGate . (HGate # IdGate)

drawToBellBasis2 : IO ()
drawToBellBasis2 = do
  putStrLn "\nAnother possibility for toBellBasis: \nCNOTGate . (HGate # IdGate)"
  draw toBellBasis2

---------------------------------------- Examples using adjoint -----------------------------------

adjoint_example1 : Unitary 2
adjoint_example1 = adjoint toBellBasis

adjoint_example2 : Unitary 3
adjoint_example2 = adjoint toffoli

drawAdjointExamples : IO ()
drawAdjointExamples = do
  putStrLn "Examples using adjoint"
  putStrLn "Example 1 : adjoint toBellBasis"
  draw adjoint_example1
  putStrLn "Example 2 : adjoint toffoli"
  draw adjoint_example2


||| Draw an example of circuit using tensor, compose and adjoint
export
exampleComposeTensor1 : IO ()
exampleComposeTensor1 = do
  putStrLn "\nAn example of usage of compose, tensor and adjoint: \n(adjoint toBellBasis # IdGate) . (TGate # toBellBasis)"
  let circuit = (adjoint toBellBasis # IdGate) . (TGate # toBellBasis)
  draw circuit


---------------------------------------- Examples using apply -------------------------------------

U : Unitary 3
U = HGate # IdGate {n = 1} # (PGate pi)

apply_example1 : Unitary 3
apply_example1 = apply toBellBasis U [0,1]

apply_example2 : Unitary 3
apply_example2 = apply toBellBasis U [0,2]

apply_example3 : Unitary 3
apply_example3 = apply toBellBasis U [2,0]

apply_example4 : Unitary 3
apply_example4 = apply toBellBasis U [2,1]

apply_example5 : Unitary 3
apply_example5 = apply toffoli IdGate [2,0,1]

drawApplyExamples : IO ()
drawApplyExamples = do
  putStrLn "\nApply Examples \nU = HGate # IdGate {n = 1} # (PGate pi)\n"
  putStrLn "Example 1 : apply toBellBasis U [0,1]"
  draw apply_example1
  putStrLn "Example 2 : apply toBellBasis U [0,2]"
  draw apply_example2
  putStrLn "Example 3 : apply toBellBasis U [2,0]"
  draw apply_example3
  putStrLn "Example 4 : apply toBellBasis U [2,1]"
  draw apply_example4
  putStrLn "Example 5 : apply toffoli [2,0,1]"
  draw apply_example5

-------------------------------------- Example using controlled -----------------------------------

controlled_example1 : Unitary 2
controlled_example1 = controlled TGate

||| Example using multipleQubitControlledNOT
||| Makes a multiple qubit CNOT gate : control on the first n qubits, target on the last
multipleQubitsCNOTExample : Unitary 4
multipleQubitsCNOTExample = multipleQubitControlledNOT 4

--------------------------------- Examples of parametrized circuits -------------------------------

parametrized_example1 : Bool -> Unitary 1
parametrized_example1 b = if b then HGate else PGate pi

parametrized_example2 : Bool -> Bool -> Double -> Unitary 2
parametrized_example2 b1 b2 p = CNOTGate . (if b1 then H 0 IdGate else IdGate) . (if b2 then IdGate else P p 1 IdGate)

drawParamExamples : IO ()
drawParamExamples = do
  putStrLn "Examples of circuits parametrized by classical data"
  putStrLn "Example 1 : for b : bool , if b then HGate else PGate pi"
  putStrLn "For b = True : "
  draw (parametrized_example1 True)
  putStrLn "For b = False : "
  draw (parametrized_example1 False)
  putStrLn "Example 2 : for b1, b2 : Bool and p : Double , CNOTGate . (if b1 then H 0 IdGate else IdGate) . (if b2 then IdGate else P p 1 IdGate)"
  putStrLn "For b1 = True, b2 = False, p = pi/2"
  draw (parametrized_example2 True False (pi/2))


------------------------------------ Example of depth computation ---------------------------------
||| Compute the depth of a circuit


depthExample1 : Unitary 3
depthExample1 = CNOT 0 1 $ CNOT 2 1 $ H 1 $ CNOT 0 2 IdGate 

depthExample2 : Unitary 3
depthExample2 = H 2 $ H 1 $ H 0 $ H 1 IdGate

depthExample3 : Unitary 3
depthExample3 = CNOT 1 2 $ CNOT 0 2 $ CNOT 0 1 $ H 1 $ P pi 1 $ H 1 IdGate

drawDepthExamples : IO ()
drawDepthExamples = do
  putStrLn "Examples of depth computation"
  putStrLn "The depth of the following circuit"
  draw depthExample1
  putStrLn  ("is " ++ show (depth depthExample1))
  putStrLn "The depth of the following circuit"
  draw depthExample2
  putStrLn $ "is " ++ show (depth depthExample2)
  putStrLn "The depth of the following circuit"
  draw depthExample3
  putStrLn $ "is " ++ show (depth depthExample3)


----------------------------------- Examples of quantum operations --------------------------------

||| QuantumOp n m t : 
||| Simulation of a quantum operation from a quantum state with n qubits to a quantum state of m qubits. 
||| The user is returned a value of type t


||| Create a new qubit and apply a H gate
quantum_operation : QuantumOp 0 1 Qubit
quantum_operation = do
  q <- newQubit
  applyH q
  

||| Apply the toBellBasis to 2 input qubits in a quantum state with 3 qubits
||| Return the linear pair of the 2 qubit pointers
quantum_operation2 : (1 _ : Qubit) -> (1 _ : Qubit) -> QuantumOp 3 3 (LPair Qubit Qubit)
quantum_operation2 q1 q2 = do
  [r1, r2] <- applyUnitary [q1, q2] toBellBasis
  pure (r1 # r2)

||| Apply a H gate to a qubit in a quantum state with 2 qubits and measure it
quantum_operation3 : (1 _ : Qubit) -> QuantumOp 2 1 Bool
quantum_operation3 q = do
  q <- applyH q
  measureQubit q

||| Sequencing quantum operations using run
||| 
quantum_operation4 : QuantumState t => IO (Vect 3 Bool)
quantum_operation4 = 
  run (do
      [q1,q2] <- newQubits {t=t} 2
      [q1,q2] <- applyUnitary [q1,q2] toBellBasis
      q3 <- newQubit
      [q1,q3,q2] <- applyUnitary [q1,q3,q2] toffoli
      [b2] <- measure [q2]
      (q3 # q1) <- applyCNOT q3 q1 
      [b1,b3] <- measure [q1,q3]
      pure [b1,b2,b3]
      )

------------------------------------ Draw all example circuits ------------------------------------

export
drawExamples : IO ()
drawExamples = do
  drawToBellBasis
  drawConstructorsExample
  drawComposeExamples
  drawTensorExamples
  drawToBellBasis2
  drawAdjointExamples
  exampleComposeTensor1
  drawApplyExamples
  drawParamExamples
  drawDepthExamples
