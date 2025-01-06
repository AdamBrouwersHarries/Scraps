module Linear.Reproduction

import Data.Linear.Interface
import Data.Linear.Notation
import Data.Linear.LNat
import Data.Linear.LEither
import Data.Linear.LMaybe
import Data.Linear.LVect

-- Some useful things defined for LNats

-- Comparisons between linear nats
infix 5 <@

public export
(<@) : LNat -@ LNat -@ Bool
(<@) Zero Zero = False
(<@) Zero (Succ y) = y `seq` True
(<@) (Succ x) Zero = x `seq` False
(<@) (Succ x) (Succ y) = x <@ y

-- Conversion from Nat to LNat
public export
fromNat : Nat -> LNat
fromNat 0 = Zero
fromNat (S k) = Succ (fromNat k)

-- Numeric interface
public export
Num LNat where
    (+) Zero y = y
    (+) (Succ x) y = Succ (x + y)

    (*) Zero y = y
    (*) (Succ x) y = y + (x * y)

    fromInteger i = fromNat $ integerToNat i

-- To/from integers ease of use
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
integerToLNat 0 = Zero
integerToLNat x
  = if intToBool (prim__lte_Integer x 0)
       then Zero
       else Succ (assert_total (integerToLNat (prim__sub_Integer x 1)))

-- Make it easier to print an LNat
public export
Show LNat where
    show n = show (the Integer (lnatToInteger n))

-- Proofs about comparisons (`LTE`s) between LNats
-- This is copied almost verbatim from the equivalent implementation on Nat
public export
data LTE  : (1 n : LNat) -> (1 m : LNat) -> Type where
  LTEZero : LTE Zero    right
  LTESucc : LTE left right -> LTE (Succ left) (Succ right)

export
succNotLTEzero : Not (LTE (Succ m) Zero)
succNotLTEzero LTEZero impossible

export
fromLteSucc : LTE (Succ m) (Succ n) -> LTE m n
fromLteSucc (LTESucc x) = x

export
lteSuccRight : LTE n m -> LTE n (Succ m)
lteSuccRight LTEZero     = LTEZero
lteSuccRight (LTESucc x) = LTESucc (lteSuccRight x)

export
lteSuccLeft : LTE (Succ n) m -> LTE n m
lteSuccLeft (LTESucc x) = lteSuccRight x

-- Dependent pair of linear and linear
infix 1 ##
public export
record DPairLL (t : Type) (f : t -> Type) where
  constructor (##)
  1 fst : t
  1 snd : f fst

-- Decide if m is less than N. We could use `isLTE` here, but as we want this to be linear, we would "forget" the inputs.
-- Instead we return a copy of each input, produced during the recursion, along with proofs that they are the same values
-- as the input arguments. This is clunky, but is necessary as linear dependent pairs do not (currently) capture the input
-- syntactically, which means that Idris2 will "forget" that it's the same as the argument.
public export
isLTELin : (1 m : LNat) -> (1 n : LNat) -> DPairLL LNat (\x => DPairLL LNat (\y => (Dec $ LTE x y, x === m, y === n)))
isLTELin Zero n = Zero ## (n ## (Yes LTEZero, Refl, Refl))
isLTELin (Succ x) Zero = (Succ x) ## (Zero ## (No succNotLTEzero, Refl, Refl))
isLTELin (Succ x) (Succ z) = case isLTELin x z of
                                  (x ## (y ## (Yes prf, Refl, Refl))) => (Succ x ## (Succ y ## (Yes (LTESucc prf), Refl, Refl)))
                                  (x ## (y ## (No contra, Refl, Refl))) => (Succ x ## (Succ y ## (No (contra . fromLteSucc), Refl, Refl)))

-- A sorted vector data type. We require than any element we "push" to the vector be strictly smaller than any element
-- that is already in the list. This is achieved by indexing the type with the size of the smallest element, and then
-- providing a proof that the new element is is smaller than the indexing size.
-- We also make this type linear, which makes it easier to build in linear environments later.
data LSortedVect : Nat -> LNat -> Type where
    Nil : (1 e : LNat) -> LSortedVect 1 e
    Cons : (1 e : LNat) -> (1 es : LSortedVect n o) -> (0 prf : LTE e o) -> LSortedVect (S n) e

-- Hints for interactive editing, names that would be good for lsortedvect types.
%name LSortedVect xs, ys, zs, ws, es, ms

-- Print!
Show (LSortedVect l m) where
    show sv = "[" ++ printSortedVect sv where
        printSortedVect : LSortedVect n e -> String
        printSortedVect ([] e) = (show e) ++ "]"
        printSortedVect (Cons e es prf) = (show e) ++ "," ++ printSortedVect es

-- Print!
Show (DPairLL LNat (\m => LSortedVect l m)) where
    show (_ ## snd) = show snd

-- This is an adaptation of the Nat library's proof `notLTEImpliesGT`, but to avoid going through the `GT` interface.
-- We can do this, because `GT` is eventually defined through an inversion of `LT` (`GT left right = LT right left`),
-- which is itself defined through: `LT left right = LTE (Succ left) right`. Putting it all together gets us:
-- `GT left right = LTE (Succ right) left`
notLTEImpliesFlipLTESucc : {a, b : LNat} -> Not (a `LTE` b) -> ((Succ b) `LTE` a)
notLTEImpliesFlipLTESucc {a = Zero} not_z_lte_b = absurd $ not_z_lte_b LTEZero
notLTEImpliesFlipLTESucc {a = Succ a} {b = Zero} notLTE = LTESucc LTEZero
notLTEImpliesFlipLTESucc {a = Succ a} {b = Succ k} notLTE = LTESucc (notLTEImpliesFlipLTESucc (notLTE . LTESucc))

-- Given a proof of Not (n <= m), produce a proof of m <= n. This seems counterintuitive, but is correct.
flipOrdContra : {n, m : LNat} -> Not (LTE n m) -> LTE m n
flipOrdContra f = lteSuccLeft $ notLTEImpliesFlipLTESucc f

-- Insert a new element into a sorted Vector.
-- Returns back a vector one element longer, with either the smallest element being `x`, or remaining unchanged.
insert : (1 x : LNat) -> (1 xs : LSortedVect l m) -> LEither (LSortedVect (S l) x) (LSortedVect (S l) m)
insert x ([] m) = case isLTELin x m of
                       (x ## (m ## (Yes prf, Refl, Refl))) => Left $ Cons x (Nil m) prf
                       (x ## (m ## (No contra, Refl, Refl))) => Right $ Cons m (Nil x) (flipOrdContra contra)
insert x (Cons m ms p) = case isLTELin x m of
                                (x ## (m ## ((Yes prf), (Refl, Refl)))) => Left $ Cons x (Cons m ms p) prf
                                (x ## (m ## ((No contra), (Refl, Refl)))) => case insert x ms of
                                                                                  (Left ms') => Right (Cons m ms' (flipOrdContra contra))
                                                                                  (Right ms') => Right (Cons m ms' p)

-- Insertion sort a vector, transforming it into a sorted vector!
isort : (xs : LVect (S n) LNat) -> DPairLL LNat (\m =>LSortedVect (S n) m)
isort (x :: []) = (x ## Nil x)
isort (x :: (y :: xs)) = let (m' ## sv) = isort (y :: xs) in
    case insert x sv of
        (Left z) => x ## z
        (Right z) => m' ## z

-- Example
sortedVector = isort [41, 2, 6, 3, 7, 3, 9, 11, 13, 29]