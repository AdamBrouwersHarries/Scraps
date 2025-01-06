module Extensions.LNat

import Data.Linear.Interface
import Data.Linear.Notation
import Data.Linear.LNat

-- Comparisons between linear nats
infix 5 <@

public export
(<@) : LNat -@ LNat -@ Bool
(<@) Zero Zero = False
(<@) Zero (Succ y) = y `seq` True
(<@) (Succ x) Zero = x `seq` False
(<@) (Succ x) (Succ y) = x <@ y

public export
fromNat : Nat -> LNat
fromNat 0 = Zero
fromNat (S k) = Succ (fromNat k)

public export
Num LNat where
    (+) Zero y = y
    (+) (Succ x) y = Succ (x + y)

    (*) Zero y = y
    (*) (Succ x) y = y + (x * y)

    fromInteger i = fromNat $ integerToNat i

public export
lnatToInteger : LNat -> Integer
lnatToInteger Zero = 0
lnatToInteger (Succ x) = 1 + lnatToInteger x

prim__integerToLNat : Integer -> LNat
prim__integerToLNat i
  = if intToBool (prim__lte_Integer 0 i)
      then believe_me i
      else Zero

public export
integerToLNat : Integer -> LNat
integerToLNat 0 = Zero -- Force evaluation and hence caching of x at compile time
integerToLNat x
  = if intToBool (prim__lte_Integer x 0)
       then Zero
       else Succ (assert_total (integerToLNat (prim__sub_Integer x 1)))


public export
Show LNat where
    show n = show (the Integer (lnatToInteger n))