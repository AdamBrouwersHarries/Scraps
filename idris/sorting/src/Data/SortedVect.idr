module Data.SortedVect

import Data.Vect
import Data.Nat

public export
data SortedVect : (n : Nat) -> (e : Nat) -> Type where
    Nil : (e : Nat) -> SortedVect 1 e
    Cons : (e : Nat) -> (es : SortedVect n o) -> (prf : LTE e o) -> SortedVect (S n) e

-- Hints for interactive editing
%name SortedVect xs, ys, zs, ws, es


public export
Show (SortedVect l m) where
    show sv = "[" ++ printSortedVect sv where
        printSortedVect : SortedVect n e -> String
        printSortedVect ([] e) = (show e) ++ "]"
        printSortedVect (Cons e es prf) = (show e) ++ "," ++ printSortedVect es


-- Given a proof of Not (n <= m), produce a proof of m <= n
public export
flipOrdContra : {n, m : Nat} -> Not (LTE n m) -> LTE m n
flipOrdContra f = lteSuccLeft $ notLTEImpliesGT f

-- Insert a new element into a sorted Vector.
-- Returns back a vector one element longer, with either the smallest element being `x`, or remaining unchanged.
public export
insert : (x : Nat) -> (xs : SortedVect l m) -> Either (SortedVect (S l) x) (SortedVect (S l) m)
insert x ([] m) = case isLTE x m of
                    (Yes prf) => Left (Cons x (Nil m) prf)
                    (No contra) => Right (Cons m (Nil x) (flipOrdContra contra))
insert x (Cons m ms p) = case isLTE x m of
                            (Yes prf) => Left (Cons x (Cons m ms p) prf)
                            (No contra) => case insert x ms of
                                                (Left ms') => Right (Cons m ms' (flipOrdContra contra))
                                                (Right ms') => Right (Cons m ms' p)

-- merge together two sorted lists, maintaining the sorting property
public export
merge : (xs : SortedVect l1 m1) -> (ys : SortedVect l2 m2) -> Either (SortedVect (l1 + l2) m1) (SortedVect (l1 + l2) m2)
merge ([] x) ys = insert x ys
merge (Cons x xs' p) ys = case merge xs' ys of
                              -- We've maintained that xs is still smallest, so we can manually re-add x
                              (Left ys') => Left (Cons x ys' p)
                              -- Otherwise, we need to try and insert x into the resulting vector
                              (Right ys') => insert x ys'

public export
lfind : {l : Nat} -> (needle : Nat) -> (haystack : SortedVect l m) -> Maybe Nat
lfind needle ([] x) = if needle == x then Just 0 else Nothing
lfind needle (Cons x xs p) = case compare needle x of
                                 LT => Nothing
                                 EQ => Just l
                                 GT => lfind needle xs >>= (Just . S)

-- Sorted vectors have a minimum length of 1, so we need to always sort an array of length at least 1
public export
insertionSort : (xs : Vect (S n) Nat) -> (m ** SortedVect (S n) m)
-- Impossible to have an empty list of size S n
insertionSort [] impossible
-- However, a list of size 1 is size S Z
insertionSort (x :: []) = (x ** (Nil x))
-- As we need to recurse, we must ensure that this is of at least size 2, as xs might be []
insertionSort (x :: (x' :: xs)) = let (m ** sxs) = insertionSort (x' :: xs) in
    case insert x sxs of
         (Left sxs') => (x ** sxs')
         (Right sxs') => (m ** sxs')
