module OptimiseUnitary

import Data.Vect
import Data.Nat
import Unitary



simplify : Unitary n -> Unitary n -> (Unitary n, Bool)
simplify IdGate _ = (IdGate, False)
simplify _ IdGate = (IdGate, False)
simplify (H j x) (H k y) = 
  if j == k then (y,True)
  else let (g,b) = simplify (H j x) y in (H k g, b)
simplify (H j x) (P p k y) = 
  if j == k then (P p k y, False)
  else let (g,b) = simplify (H j x) y in (P p k g, b)
simplify (H j x) (CNOT c t y) = 
  if j == c || j == t then (CNOT c t y, False)
  else let (g,b) = simplify (H j x) y in (CNOT c t g, b)
simplify (P p j x) (H k y) = 
  if j == k then (H k y, False)
  else let (g,b) = simplify (P p j x) y in (H k g, b)
simplify (P p j x) (P p1 k y) = 
  if j == k then (P (p + p1) k y, True)
  else let (g,b) = simplify (P p j x) y in (P p1 k g, b)
simplify (P p j x) (CNOT c t y) = 
  if j == c || j == t then (CNOT c t y, False)
  else let (g,b) = simplify (P p j x) y in (CNOT c t g, b)
simplify (CNOT c t x) (H j y) = 
  if j == c || j == t then (H j y, False)
  else let (g,b) = simplify (CNOT c t x) y in (H j g, b)
simplify (CNOT c t x) (P p j y) = 
  if j == c || j == t then (P p j y, False)
  else let (g,b) = simplify (CNOT c t x) y in (P p j g, b)
simplify (CNOT c t x) (CNOT c1 t1 y) = 
  if c == c1 && t == t1 then (y, True)
  else if c == c1 || t == t1 || c == t1 || t == c1 
          then (CNOT c1 t1 y, False)
       else let (g,b) = simplify (CNOT c t x) y in (CNOT c1 t1 g, b)


optimise' : Unitary n -> (Unitary n, Bool)
optimise' IdGate = (IdGate, False)
optimise' (H j x) = 
  let (g, b) = simplify (H j x) x 
      (g1, b1) = optimise' g
  in if b then (g1, True)
     else (H j g1, b1)
optimise' (P p j x) = 
  let (g, b) = simplify (P p j x) x
      (g1, b1) = optimise' g
  in if b then (g1, True)
     else (P p j g1, b1)
optimise' (CNOT c t x) = 
  let (g, b) = simplify (CNOT c t x) x
      (g1, b1) = optimise' g
  in if b then (g1, True)
     else (CNOT c t g1, b1)

export
optimise : Unitary n -> Unitary n
optimise g = 
  let (g1, b1) = optimise' g
  in if b1 then optimise g1
           else g1
