module Unitary

import Data.Vect
import Data.Nat
import System.File
import Injection
import Lemmas

infixr 9 @@
infixr 10 #

%default total


------------------------QUANTUM CIRCUITS-----------------------

public export
data Unitary : Nat -> Type where
  IdGate : Unitary n
  H      : (j : Nat) -> {auto prf : (j < n) = True} -> Unitary n -> Unitary n
  P      : (p : Double) -> (j : Nat) -> {auto prf : (j < n) = True} -> Unitary n -> Unitary n
  CNOT   : (c : Nat) -> (t : Nat) -> 
            {auto prf1 : (c < n) = True} -> {auto prf2 : (t < n) = True} -> {auto prf3 : (c /= t) = True} -> 
            Unitary n -> Unitary n


-- P p = [[1,0],[0,e^ip]]

-------------------------------APPLY---------------------------
|||Apply a smaller circuit of size i to a bigger one of size n
|||The vector of wires on which we apply the circuit must follow some constraints:
|||All the indices must be smaller than n, and they must be all different
public export
apply : {i : Nat} -> {n : Nat} -> 
        Unitary i -> Unitary n -> 
        (v : Vect i Nat) -> 
        {auto prf : (isInjective n v) = True} -> 
        Unitary n
apply IdGate g2 _ = g2
apply (H j g1) g2 v = 
  let prf1 = indexInjectiveVect j n v {prf} 
  in H (index j v) {prf = prf1} (apply g1 g2 v)
apply (P p j g1) g2 v = 
  let prf1 = indexInjectiveVect j n v {prf}
  in P p (index j v) {prf = prf1} (apply g1 g2 v)
apply {i} {n} (CNOT c t {prf1} {prf2} {prf3} g1) g2 v = 
  let prf4 = indexInjectiveVect c n v {prf = prf}
      prf5 = indexInjectiveVect t n v {prf = prf}
      prf6 = differentIndexInjectiveVect c t n {prf1 = prf3} v {prf2 = prf} {prf3 = prf1} {prf4 = prf2}
  in CNOT (index c v) (index t v) {prf1 = prf4} {prf2 = prf5} {prf3 = prf6} (apply g1 g2 v)

---------------------------COMPOSE-----------------------------
|||Compose 2 circuits of the same size
public export
compose : Unitary n -> Unitary n -> Unitary n
compose IdGate g1 = g1
compose (H j g1) g2 = H j (compose g1 g2)
compose (P p j g1) g2 = P p j (compose g1 g2)
compose (CNOT c t g1) g2 = CNOT c t (compose g1 g2)

public export
(@@) : Unitary n -> Unitary n -> Unitary n
(@@) = compose

public export
(.) : Unitary n -> Unitary n -> Unitary n
(.) = compose

---------------------------ADJOINT-----------------------------
|||Find the adjoint of a circuit
public export
adjoint : Unitary n -> Unitary n
adjoint IdGate = IdGate
adjoint (H j g) = compose (adjoint g) (H j IdGate)
adjoint (P p j g) = compose (adjoint g) (P (-p) j IdGate)
adjoint (CNOT c t g) = compose (adjoint g) (CNOT c t IdGate)


---------------------TENSOR PRODUCT----------------------------
|||Make the tensor product of two circuits
public export
tensor : {n : Nat} -> {p : Nat} -> Unitary n -> Unitary p -> Unitary (n + p)
tensor g1 g2 = 
  let p1 = (allSmallerRangeVect 0 n)
      p2 = lemmaAnd (allSmallerRangeVect n p) (allDiffRangeVect n p)
      p3 = allSmallerPlus n p (rangeVect 0 n) p1 
      p4 = lemmaAnd p3 (allDiffRangeVect 0 n)
      g' = apply {i=n} {n = n+p} g1 (IdGate {n = n+p}) (rangeVect 0 n) {prf = p4}
  in apply {i = p} {n = n + p} g2 g' (rangeVect n p) {prf = p2}

public export
(#) : {n : Nat} -> {p : Nat} -> Unitary n -> Unitary p -> Unitary (n + p)
(#) = tensor

----------------------CLASSICAL GATES--------------------------
public export
HGate : Unitary 1
HGate = H 0 IdGate

public export
PGate : Double -> Unitary 1
PGate r = P r 0 IdGate

public export
CNOTGate : Unitary 2
CNOTGate = CNOT 0 1 IdGate

public export
T : (j : Nat) -> {auto prf : (j < n) = True} -> Unitary n -> Unitary n
T j g = P (pi/4) j {prf} g

public export
TGate : Unitary 1
TGate = T 0 IdGate

public export
TAdj : (j : Nat) -> {auto prf : (j < n) = True} -> Unitary n -> Unitary n
TAdj j g = P (-pi/4) j {prf} g

public export
TAdjGate : Unitary 1
TAdjGate = TAdj 0 IdGate

public export
S : (j : Nat) -> {auto prf : (j < n) = True} -> Unitary n -> Unitary n
S j g = P (pi/2) j {prf} g

public export
SGate : Unitary 1
SGate = S 0 IdGate

public export
SAdj : (j : Nat) -> {auto prf : (j < n) = True} -> Unitary n -> Unitary n
SAdj j g = P (-pi/2) j {prf} g

public export
SAdjGate : Unitary 1
SAdjGate = SAdj 0 IdGate

public export
Z : (j : Nat) -> {auto prf : (j < n) = True} -> Unitary n -> Unitary n
Z j g = P pi j {prf} g

public export
ZGate : Unitary 1
ZGate = Z 0 IdGate

public export
X : (j : Nat) -> {auto prf : (j < n) = True} -> Unitary n -> Unitary n
X j g = H j (Z j (H j g))

public export
XGate : Unitary 1
XGate = X 0 IdGate

public export
RxGate : Double -> Unitary 1
RxGate p = HGate @@ PGate p @@ HGate

public export
RyGate : Double -> Unitary 1
RyGate p = SAdjGate @@ HGate @@ PGate (-p) @@ HGate @@ SGate

public export
RzGate : Double -> Unitary 1
RzGate p = PGate p 

||| Put two qubits initally in state |00> in the Bell state
public export
toBellBasis : Unitary 2
toBellBasis = CNOT 0 1 (H 0 IdGate)

---------------------CONTROLLED VERSIONS-----------------------
|||Toffoli gate
public export
toffoli : Unitary 3
toffoli = 
  let g1 = CNOT 1 2 (H 2 IdGate)
      g2 = CNOT 0 2 (TAdj 2 g1)
      g3 = CNOT 1 2 (T 2 g2)
      g4 = CNOT 0 2 (TAdj 2 g3)
      g5 = CNOT 0 1 (T 1 (H 2 (T 2 g4)))
  in CNOT 0 1 (T 0 (TAdj 1 g5))

|||Controlled Hadamard gate
public export
controlledH : Unitary 2
controlledH =
  let h1 = (IdGate {n=1}) # (SAdjGate @@ HGate @@ TGate @@ HGate @@ SGate)
      h2 = (IdGate {n=1}) # (SAdjGate @@ HGate @@ TAdjGate @@ HGate @@ SGate)
  in h1 @@ CNOTGate @@ h2

|||Controlled phase gate
public export
controlledP : Double -> Unitary 2
controlledP p = 
  let p1 = CNOT 0 1 (P (p/2) 1 IdGate)
  in CNOT 0 1 (P (-p/2) 1 p1)

|||Make the controlled version of a gate
public export
controlled : {n : Nat} -> Unitary n -> Unitary (S n)
controlled IdGate = IdGate
controlled (H j g) = 
  let p = lemmaControlledInj n j 
  in apply {i = 2} {n = S n} controlledH (controlled g) [0, S j] {prf = p}
controlled (P p j g) = 
  let p1 = lemmaControlledInj n j
  in apply {i = 2} {n = S n} (controlledP p) (controlled g) [0, S j] {prf = p1}
controlled (CNOT c t g) = 
  let p = lemmaControlledInj2 n c t
  in apply {i = 3} {n = S n} toffoli (controlled g) [0, S c, S t] {prf = p}



------------SOME USEFUL FUNCTIONS FOR CREATING GATES-----------

|||Make n tensor products of the same unitary of size 1
public export
tensorn : (n : Nat) -> Unitary 1 -> Unitary n
tensorn 0 _ = IdGate
tensorn (S k) g = g # (tensorn k g)

|||Controls on the n-1 first qubits, target on the last
public export
bigControlledCNOT : (n : Nat) -> Unitary n
bigControlledCNOT 0 = IdGate
bigControlledCNOT 1 = IdGate
bigControlledCNOT 2 = CNOT 0 1 IdGate
bigControlledCNOT (S k) = controlled (bigControlledCNOT k)

---------------------------------------------------------------
--count the total number of atomic gates in a unitary circuit
export
gateCount : Unitary n -> Nat
gateCount IdGate = 0
gateCount (H j x) = S (gateCount x)
gateCount (P p j x) = S (gateCount x)
gateCount (CNOT c t x) = S (gateCount x)

--count the number of H gates in a unitary circuit
export
Hcount : Unitary n -> Nat
Hcount IdGate = 0
Hcount (H j x) = S (Hcount x)
Hcount (P p j x) = Hcount x
Hcount (CNOT c t x) = Hcount x

--count the number of P gates in a unitary circuit
export
Pcount : Unitary n -> Nat
Pcount IdGate = 0
Pcount (H j x) = Pcount x
Pcount (P p j x) = S (Pcount x)
Pcount (CNOT c t x) = Pcount x


--count the number of CNOT gates in a unitary circuit
export
CNOTcount : Unitary n -> Nat
CNOTcount IdGate = 0
CNOTcount (H j x) = CNOTcount x
CNOTcount (P p j x) = CNOTcount x
CNOTcount (CNOT c t x) = S (CNOTcount x)

----------------------------DEPTH------------------------------
|||Compute the depth of  circuit

addDepth : Nat -> (j : Nat) -> Vect n Nat -> {auto prf : j < n = True} -> Vect n Nat
addDepth j 0 (x :: xs) = j :: xs
addDepth j (S k) (x :: xs) = x :: addDepth j k xs

findValue : (j : Nat) -> Vect n Nat -> {auto prf : j < n = True} -> Nat
findValue 0 (x::xs) = x
findValue (S k) (x::xs) = findValue k xs

max : Vect n Nat -> Nat
max v = max' 0 v where
  max' : Nat -> Vect k Nat -> Nat
  max' k [] = k
  max' k (x::xs) = if x > k then max' x xs else max' k xs

depth' : {n : Nat} -> Unitary n -> Vect n Nat
depth' IdGate = replicate n 0
depth' (H j x) =
  let v = depth' x 
      k = findValue j v
  in addDepth (S k) j v
depth' (P p j x) = 
  let v = depth' x
      k = findValue j v
  in addDepth (S k) j v
depth' (CNOT c t x) = 
  let v = depth' x 
      k = findValue c v
      m = findValue t v
  in if k < m then
              let w = addDepth (S m) c v
              in addDepth (S m) t w
     else
              let w = addDepth (S k) c v
              in addDepth (S k) t w

export
depth : {n : Nat} -> Unitary n -> Nat
depth g = 
  let v = depth' g 
  in max v

----------------------------SHOW-------------------------------
|||For printing the phase gate (used for show, export to Qiskit and draw in the terminal)
|||printPhase : phase -> precision -> string for pi -> String
private
printPhase : Double -> Double -> String -> String
printPhase x epsilon s =
  if x >= pi - epsilon && x <= pi + epsilon then s
  else if x >= pi/2 - epsilon && x <= pi/2 + epsilon then s ++ "/2"
  else if x >= pi/3 - epsilon && x <= pi/3 + epsilon then s ++ "/3"
  else if x >= pi/4 - epsilon && x <= pi/4 + epsilon then s ++ "/4"
  else if x >= pi/6 - epsilon && x <= pi/6 + epsilon then s ++ "/6"
  else if x >= pi/8 - epsilon && x <= pi/8 + epsilon then s ++ "/8"
  else if x >= -pi - epsilon && x <= -pi + epsilon then "-" ++ s
  else if x >= -pi/2 - epsilon && x <= -pi/2 + epsilon then "-" ++ s ++ "/2"
  else if x >= -pi/3 - epsilon && x <= -pi/3 + epsilon then "-" ++ s ++ "/3"
  else if x >= -pi/4 - epsilon && x <= -pi/4 + epsilon then "-" ++ s ++ "/4"
  else if x >= -pi/6 - epsilon && x <= -pi/6 + epsilon then "-" ++ s ++ "/6"
  else if x >= -pi/8 - epsilon && x <= -pi/8 + epsilon then "-" ++ s ++ "/8"
  else show x

public export
Show (Unitary n) where
  show IdGate = ""
  show (H j x) = "(H " ++ show j ++ ") " ++ show x 
  show (P p j x) = "(P " ++ printPhase p 0.001 "π" ++ " " ++ show j ++ ") " ++ show x
  show (CNOT c t x) = "(CNOT " ++ show c ++ " " ++ show t ++ ") " ++ show x



-----------------DRAW CIRCUITS IN THE TERMINAL-----------------

private
newWireQVect : (n : Nat) -> Vect n String
newWireQVect Z = []
newWireQVect (S k) = "" :: newWireQVect k

private
addSymbol : Nat -> Bool -> (String, String) -> Vect n String -> Vect n String
addSymbol _ _ _ [] = []
addSymbol 0 False (s1, s2) (x :: xs) = (x ++ s1) :: addSymbol 0 True  (s1, s2) xs
addSymbol 0 True  (s1, s2) (x :: xs) = (x ++ s2) :: addSymbol 0 True  (s1, s2) xs
addSymbol (S k) _ (s1, s2) (x :: xs) = (x ++ s2) :: addSymbol k False (s1, s2) xs

private
addSymbolCNOT : (Nat, Nat) -> Bool -> Bool -> Vect n String -> Vect n String
addSymbolCNOT _ _ _ [] = []
addSymbolCNOT (0,0)    False b (x :: xs) = (x ++ "- • -") :: addSymbolCNOT (0, 0) True b xs
addSymbolCNOT (0, S k) False b (x :: xs) = (x ++ "- • -") :: addSymbolCNOT (0, k) True b xs
addSymbolCNOT (0, 0)   b False (x :: xs) = (x ++ "- Θ -") :: addSymbolCNOT (0, 0) b True xs
addSymbolCNOT (S k, 0) b False (x :: xs) = (x ++ "- Θ -") :: addSymbolCNOT (k, 0) b True xs
addSymbolCNOT (0, 0) True True (x :: xs) = (x ++ "-----") :: addSymbolCNOT (0, 0) True True xs
addSymbolCNOT (S j, S k) _ _   (x :: xs) = (x ++ "-----") :: addSymbolCNOT (j, k) False False xs
addSymbolCNOT (0, S k) True _  (x :: xs) = (x ++ "--|--") :: addSymbolCNOT (0, k) True False xs
addSymbolCNOT (S k, 0) _ True  (x :: xs) = (x ++ "--|--") :: addSymbolCNOT (k, 0) False True xs

private
drawWirePhase : Nat -> String
drawWirePhase 0 = ""
drawWirePhase (S n) = "-" ++ drawWirePhase n

private
drawGate : {n : Nat} -> Unitary n -> Vect n String
drawGate {n} IdGate = newWireQVect n
drawGate (H i g) = addSymbol i False ("- H -", "-----") (drawGate g)
drawGate (P p i g) =
  let epsilon = 0.001 in
  if pi/4 - epsilon <= p && pi/4 + epsilon >= p
    then addSymbol i False ("- T -", "-----") (drawGate g)
  else if -pi/4 - epsilon <= p && -pi/4 + epsilon >= p
    then addSymbol i False ("- T+ -", "------") (drawGate g)
  else if pi/2 - epsilon <= p && pi/2 + epsilon >= p
    then addSymbol i False ("- S -", "-----") (drawGate g)
  else if -pi/2 - epsilon <= p && -pi/2 + epsilon >= p
    then addSymbol i False ("- S+ -", "------") (drawGate g)
  else if pi - epsilon <= p && pi + epsilon >= p
    then addSymbol i False ("- Z -", "-----") (drawGate g)
  else let s = printPhase p epsilon "π"
  in addSymbol i False ("- P(" ++ s ++ ") -", drawWirePhase (length s + 7)) (drawGate g)
drawGate (CNOT i j g) = addSymbolCNOT (i,j) False False (drawGate g)


private
drawVect : Vect n String -> String
drawVect [] = ""
drawVect (x :: xs) = x ++ "\n" ++ drawVect xs

|||Draw a circuit in the terminal
public export
draw : {n : Nat} ->  Unitary n -> IO ()
draw g =
  let vs1 = drawGate {n} g in
  let s = drawVect vs1 in
  putStrLn s



--------------------------EXPORT TO QISKIT---------------------

private
unitarytoQiskit : Unitary n -> String
unitarytoQiskit IdGate = ""
unitarytoQiskit (H i g) = unitarytoQiskit g ++  "qc.h(qr[" ++ show i ++ "])\n"
unitarytoQiskit (P p i g) = unitarytoQiskit g ++ "qc.p(" ++ printPhase p 0.001 "np.pi" ++ ", qr[" ++ show i ++ "])\n" 
unitarytoQiskit (CNOT c t g) = unitarytoQiskit g ++ "qc.cx(qr[" ++ show c ++ "], qr[" ++ show t ++ "])\n" 


private
toQiskit : {n : Nat} -> Unitary n -> String
toQiskit g =
  let s = unitarytoQiskit g in
  ("import numpy as np\n" ++
  "from qiskit import QuantumCircuit\n" ++
  "from qiskit import QuantumRegister\n" ++
  "qr = QuantumRegister(" ++ show n ++ ")\n" ++
  "qc = QuantumCircuit(qr)\n\n" ++ s ++
  "\nqc.draw('mpl')")

|||Export a circuit to Qiskit code
public export
exportToQiskit : {n : Nat} -> String -> Unitary n -> IO ()
exportToQiskit str g =
  let s = toQiskit g in
      do
        a <- writeFile str s
        case a of
             Left e1 => putStrLn "Error when writing file"
             Right io1 => pure ()





