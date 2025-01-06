module Linear.LSortedVect

import Data.Linear.Interface
import Data.Linear.Notation
import Data.Linear.LNat
import Data.Linear.LEither
import Data.Linear.LMaybe

import Extensions.LNat
import Data.Nat

-- import Linear.LTE
import Linear.LinLTE

-- data LSortedVect : Nat -> LNat -> Type where
--     Nil : (e : LNat) -@ LSortedVect 1 e
--     Cons : (e : LNat) -@ LSortedVect n o -@ (prf : LTE e o) -> LSortedVect (S n) e

data LSortedVect : Nat -> LNat -> Type where
    Nil : (1 e : LNat) -> LSortedVect 1 e
    Cons : (1 e : LNat) -> (1 es : LSortedVect n o) -> (0 prf : LTE e o) -> LSortedVect (S n) e

mkLSVector : (1 e : LNat) -> LSortedVect 1 e
mkLSVector e1 = Nil e1

consLSVector : (1 e : LNat) -> (1 es : LSortedVect n o) -> (prf : LTE e o) -> LSortedVect (S n) e
consLSVector e es prf = Cons e es prf

-- Hints for interactive editing
%name LSortedVect xs, ys, zs, ws, es

Show (LSortedVect l m) where
    show sv = "[" ++ printSortedVect sv where
        printSortedVect : LSortedVect n e -> String
        printSortedVect ([] e) = (show e) ++ "]"
        printSortedVect (Cons e es prf) = (show e) ++ "," ++ printSortedVect es


-- Given a proof of Not (n <= m), produce a proof of m <= n
flipOrdContra : {n, m : LNat} -> Not (Linear.LinLTE.LTE n m) -> Linear.LinLTE.LTE m n
flipOrdContra f = lteSuccLeft $ Linear.LinLTE.notLTEImpliesGT f

-- Given a linear sorted vector, turn it into a dependent linear type, without duplicating the minimal element
-- toDPairLL : (1 lsv : LSortedVect n x) -> DPairLL LNat (\x => LSortedVect n x)
-- toDPairLL ([] x) = x ## ([] x)
-- toDPairLL (Cons x es prf) = ?hjklasdf_1

-- Insert a new element into a sorted Vector.
-- Returns back a vector one element longer, with either the smallest element being `x`, or remaining unchanged.
insert : (1 x : LNat) -> (1 xs : LSortedVect l m) -> LEither (LSortedVect (S l) x) (LSortedVect (S l) m)
insert x ([] m) = case Linear.LinLTE.isLinLTE x m of
                       (x ## (m ## (Yes prf))) => Left $ Cons x (Nil m) prf
                       (x ## (m ## (No contra))) => Right $ Cons m (Nil x) (flipOrdContra contra)
insert x (Cons m es prf) = ?asdfasdfkljh
-- case Linear.LinLTE.isLinLTE x m of
                                -- case_val => ?insert_rhs_1

-- insert : (1 x : LNat) -> (1 xs : LSortedVect l m) -> LEither (LSortedVect (S l) x) (LSortedVect (S l) m)
-- insert x ([] m) = let (x' # x'') = pair $ duplicate x in
--                   let (m' # m'') = pair $ duplicate m in
--                   case Linear.LTE.isLTE x' m' of
--                     (Yes prf) => Left (Cons x'' (Nil m'') prf)
--                     (No contra) => Right (Cons m (Nil x'') (flipOrdContra contra))
-- insert x (Cons m ms p) = ?helpme2
    -- case isLTE x m of
    --                         (Yes prf) => Left (Cons x (Cons m ms p) prf)
    --                         (No contra) => case insert x ms of
    --                                             (Left ms') => Right (Cons m ms' (flipOrdContra contra))
    --                                             (Right ms') => Right (Cons m ms' p)

-- -- merge together two sorted lists, maintaining the sorting property
-- merge : (xs : SortedVect l1 m1) -> (ys : SortedVect l2 m2) -> Either (SortedVect (l1 + l2) m1) (SortedVect (l1 + l2) m2)
-- merge ([] x) ys = insert x ys
-- merge (Cons x xs' p) ys = case merge xs' ys of
--                               -- We've maintained that xs is still smallest, so we can manually re-add x
--                               (Left ys') => Left (Cons x ys' p)
--                               -- Otherwise, we need to try and insert x into the resulting vector
--                               (Right ys') => insert x ys'

-- lfind : {l : Nat} -> (needle : Nat) -> (haystack : SortedVect l m) -> Maybe Nat
-- lfind needle ([] x) = if needle == x then Just 0 else Nothing
-- lfind needle (Cons x xs p) = case compare needle x of
--                                  LT => Nothing
--                                  EQ => Just l
--                                  GT => lfind needle xs >>= (Just . S)

-- -- Sorted vectors have a minimum length of 1, so we need to always sort an array of length at least 1
-- insertionSort : (xs : Vect (S n) Nat) -> (m ** SortedVect (S n) m)
-- -- Impossible to have an empty list of size S n
-- insertionSort [] impossible
-- -- However, a list of size 1 is size S Z
-- insertionSort (x :: []) = (x ** (Nil x))
-- -- As we need to recurse, we must ensure that this is of at least size 2, as xs might be []
-- insertionSort (x :: (x' :: xs)) = let (m ** sxs) = insertionSort (x' :: xs) in
--     case insert x sxs of
--          (Left sxs') => (x ** sxs')
--          (Right sxs') => (m ** sxs')
