import Data.Nat
import Data.Vect

%default total

-- Partition a vector, according to a pivot, and provide a proof that the
-- lengths of the resulting vectors sum to the same length as the original input vector.
partition : (Ord a) => (pivot : a) -> Vect n a -> (l ** (h ** (Vect l a, Vect h a, l + h = n)))
partition pivot [] = (0 ** (0 ** ([], ([], Refl))))
partition pivot (x :: xs) = let (l ** (h ** (ls, (hs, prf)))) = partition pivot xs in
    case x < pivot of
        True => ((S l) ** (h ** ((x :: ls), (hs, rewrite prf in Refl))))
        False => (l ** ((S h) ** (ls, ((x :: hs), rewrite sym $ plusSuccRightSucc l h in rewrite prf in Refl))))

-- Proof that a successor in the RHS of a plus "floats" to the top of the plus
plusFloatsS : (l : Nat) -> (h : Nat) -> plus l (1 + h) = S (plus l h)
plusFloatsS 0 h = Refl
plusFloatsS (S k) h = let rec = plusFloatsS k h in rewrite rec in Refl

-- Simple quicksort on vectors.
qs : (Ord a) => {n : _ } -> Vect n a -> Vect n a
qs [] = []
qs (x :: xs) = let (l ** (h ** (ls, (hs, prf)))) = partition x xs in
    let sls = qs (assert_smaller (x::xs) ls)
        shs = qs (assert_smaller (x::xs) hs) in
    rewrite sym prf in
    rewrite sym (plusFloatsS l h) in
    ((sls) ++ [x] ++ shs)


example = qs ([0, 5, 3, 4, 1, 2])

insert : (Ord a) => a -> Vect n a -> Vect (S n) a
insert x [] = [x]
insert x (y :: xs) = if x < y then
    x :: (y :: xs)
    else
    y :: (insert x xs)

-- Inefficient insertion sort.
inss : (Ord a) => {n : _} -> Vect n a -> Vect n a
inss [] = []
inss (x :: xs) = let sxs = inss xs in
    insert x sxs

example2 = inss ([0, 5, 3, 4, 1, 2])

-- insertL : (Ord a) => (1 x : a) -> (1 _ : Vect n a) -> Vect (S n) a
-- insertL x [] = (assert_linear (::) x) Nil
-- insertL x (y :: xs) = if (assert_linear (<) x) y then
--     x :: (y :: xs)
--     else
--     y :: (insertL x xs)

-- -- Inefficient insertion sort.
-- inssL : (Ord a) => {n : _} -> (1 v : Vect n a) -> Vect n a
-- inssL [] = []
-- inssL (x :: xs) = let sxs = inssL xs in
--     insertL x sxs

-- example3 = inssL ([0, 5, 3, 4, 1, 2])
