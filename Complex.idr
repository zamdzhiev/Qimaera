{-
  https://github.com/idris-lang/Idris-dev/blob/master/libs/base/Data/Complex.idr
  (c) 2012 Copyright Mekeor Melire
-}


module Complex

--%access public export

------------------------------ Rectangular form

infix 6 :+
public export
data Complex a = (:+) a a

public export
realPart : Complex a -> a
realPart (r:+i) = r

public export
imagPart : Complex a -> a
imagPart (r:+i) = i

public export
implementation Eq a => Eq (Complex a) where
    (==) a b = realPart a == realPart b && imagPart a == imagPart b

public export
implementation Show a => Show (Complex a) where
    showPrec d (r :+ i) = showParens (d >= plus_i) $ showPrec plus_i r ++ " :+ " ++ showPrec plus_i i
      where plus_i : Prec
            plus_i = User 6


-- when we have a type class 'Fractional' (which contains Double),
-- we can do:
{-
implementation Fractional a => Fractional (Complex a) where
    (/) (a:+b) (c:+d) = let
                          real = (a*c+b*d)/(c*c+d*d)
                          imag = (b*c-a*d)/(c*c+d*d)
                        in
                          (real:+imag)
-}



------------------------------ Polarform
public export
mkPolar : Double -> Double -> Complex Double
mkPolar radius angle = radius * cos angle :+ radius * sin angle

public export
cis : Double -> Complex Double
cis angle = cos angle :+ sin angle

public export
magnitude : Complex Double -> Double
magnitude (r:+i) = sqrt (r*r+i*i)

public export
atan2 : Double -> Double -> Double
atan2 y x = 2 * atan (y / (sqrt (y*y+x*x) + x))

public export
phase : Complex Double -> Double
phase (x:+y) = atan2 y x


------------------------------ Conjugate
public export
conjugate : Neg a => Complex a -> Complex a
conjugate (r:+i) = (r :+ (0-i))

public export
implementation Functor Complex where
    map f (r :+ i) = f r :+ f i

-- We can't do "implementation Num a => Num (Complex a)" because
-- we need "abs" which needs "magnitude" which needs "sqrt" which needs Double
public export
implementation Num (Complex Double) where
    (+) (a:+b) (c:+d) = ((a+c):+(b+d))
    (*) (a:+b) (c:+d) = ((a*c-b*d):+(b*c+a*d))
    fromInteger x = (fromInteger x:+0)

{-public export
implementation Neg (Complex Double) where
    negate = map negate
    (-) (a:+b) (c:+d) = ((a-c):+(b-d))
    abs (a:+b) = (magnitude (a:+b):+0)
-}
