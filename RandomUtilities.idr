module RandomUtilities

import System.Random
import Data.Vect

||| Generate a vector of random doubles
export
randomVect : (n : Nat) -> IO (Vect n Double)
randomVect 0 = pure []
randomVect (S k)  = do
  r <- randomRIO (0,2*pi)
  v <- randomVect k
  pure (r :: v)
