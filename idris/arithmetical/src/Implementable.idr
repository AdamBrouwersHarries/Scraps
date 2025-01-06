import Data.Vect
import Decidable.Equality
import Data.Either

succCong : (prf : k = j) -> (S k) = (S j)
succCong Refl = Refl

total my_take : Nat -> List a -> List a
my_take 0 _ = []
my_take (S k) [] = []
my_take (S k) (x::xs) = x :: (my_take k xs)

repeat : (n : Nat) -> a -> Vect n a
repeat 0 x = []
repeat (S k) x = x :: repeat k x

total list_length_add : (xs, ys : List a) -> (length (xs ++ ys) = length xs + length ys)
list_length_add [] ys = Refl
list_length_add (x :: xs) ys = rewrite list_length_add xs ys in Refl

lla : (xs, ys : List a) -> (length (xs ++ ys) = length xs + length ys)
lla [] ys = Refl
lla (x :: xs) ys = succCong (lla xs ys)

total map_preserves_length : (f : (a -> b)) -> (xs : List a) -> (length xs = length (map f xs))
map_preserves_length f [] = Refl
map_preserves_length f (x :: xs) = rewrite map_preserves_length f xs in Refl

mpl : (f : (a -> b)) -> (xs : List a) -> (length xs = length (map f xs))
mpl f [] = Refl
mpl f (x :: xs) = succCong (mpl f xs)

z_not_succ : 0 = S k -> Void
z_not_succ Refl impossible

succ_not_z : S k = 0 -> Void
succ_not_z Refl impossible

succDiffers : (k = j -> Void) -> S k = S j -> Void
succDiffers contra Refl = contra Refl

total dec_eq_nat : (a : Nat) -> (b : Nat) -> Dec (a = b)
dec_eq_nat 0 0 = Yes (Refl)
dec_eq_nat 0 (S k) = No z_not_succ
dec_eq_nat (S k) 0 = No succ_not_z
dec_eq_nat (S k) (S j) = case dec_eq_nat k j of
                              (Yes prf) => Yes (succCong prf)
                              (No contra) => No (succDiffers contra)


succNotZero : (prf : (S k) === Z) -> Void
succNotZero Refl impossible

-- Proof of the fact that list contains an element
data Contains : a -> List a -> Type where
  Here : (x : a) -> (xs : List a) -> Contains x (x :: xs)
  There : (x : a) -> Contains y xs -> Contains y (x :: xs)

here_it_is2 : {x : a} -> {y : a} -> {xs : List a} -> (x = y) -> (Contains y xs) -> (Contains x xs)
here_it_is2 prf z = replace {p = ((flip Contains) xs)} (sym prf) z

here_it_is : {x : a} -> {y : a} -> {xs : List a} -> (x = y) -> Dec (Contains y xs) -> Dec (Contains x xs)
here_it_is prf z = rewrite prf in z

total
prepend_preserves_contains : {x : a} -> {y : a} -> {xs : List a} -> (Contains x xs) -> (Contains x (y :: xs))
prepend_preserves_contains (Here x ys) = There y (Here x ys)
prepend_preserves_contains (There z w) = There y (prepend_preserves_contains w)

total
rprepend_preserves_contains : {x : a} -> {y : a} -> {xs : List a} -> Not (x = y) -> (Contains x (y :: xs)) -> (Contains x xs)
rprepend_preserves_contains f (Here x xs) = void $ f Refl
rprepend_preserves_contains f (There y w) = w

total
prepend_preserves_missing : Not (x = y) -> Not (Contains x xs) -> Not (Contains x (y :: xs))
prepend_preserves_missing f g (Here _ _) = case xs of { [] => f Refl ; v :: xs => f Refl }
prepend_preserves_missing f g (There _ y) = g y

total
rprepend_preserves_missing : {x: a} -> {y: a} -> {xs: List a} -> Not (x = y) -> Not (Contains x (y :: xs)) -> Not (Contains x xs)
rprepend_preserves_missing p g z = g $ prepend_preserves_contains z

total
-- rprepend_is_missing : {x : a} -> {y : a} -> (xs : List a) -> Not (x = y) -> Not (Contains x (y :: xs)) = Not (Contains x xs)
-- rprepend_is_missing [] f = neq_contains_is_impossible f = empty_contains_is_impossible
-- rprepend_is_missing (z :: xs) f = ?rprepend_is_missing_rhs_1

total
empty_contains_is_impossible : {x : a} -> Contains x [] -> Void
empty_contains_is_impossible (Here z xs) impossible
empty_contains_is_impossible (There z w) impossible

total
neq_contains_is_impossible : {x : a} -> {y : a} -> Not (x = y) -> Contains x [y] -> Void
neq_contains_is_impossible f (Here x []) = f Refl
neq_contains_is_impossible f (There y w) = empty_contains_is_impossible w


-- Check that list contains an element and return a proof
total list_contains : DecEq a => (x : a) -> (xs : List a) -> Dec (Contains x xs)
-- Base case: If we reach the end of this list, without finding it, the list does not contain x
list_contains x [] = No (empty_contains_is_impossible)
-- Recursive case: Check to see if this element is the element we are looking for
list_contains x (y :: xs) = case decEq x y of
                                 -- If it is, provide a proof that it is in this list
                                 (Yes prf) => let here = Yes (Here y xs) in here_it_is prf here
                                 -- Otherwise, recurse down into the list
                                 (No contra) => case list_contains x xs of
                                                     (Yes prf) => Yes (prepend_preserves_contains prf)
                                                     (No f) => No (prepend_preserves_missing contra f)

total
precat_preserves_contains : {x : a} -> {xs : List a} -> (Contains x xs) -> (ys : List a) -> Contains x (ys ++ xs)
precat_preserves_contains y [] = y
precat_preserves_contains y (z :: ys) = let rec = precat_preserves_contains y ys in prepend_preserves_contains rec

total
postcat_preserves_contains : {x : a} -> {xs : List a} -> (Contains x xs) -> (ys : List a)-> Contains x (xs ++ ys)
postcat_preserves_contains (Here x []) ys = Here x ys
postcat_preserves_contains (Here x (y :: zs)) ys = Here x (y :: (zs ++ ys))
postcat_preserves_contains (There y z) ys = There y (postcat_preserves_contains z ys)

total
concat_preserves_contains : {x : a} -> {xs : List a} -> {ys : List a} -> Either (Contains x xs) (Contains x ys) -> Contains x (xs ++ ys)
concat_preserves_contains (Left xcont) = postcat_preserves_contains xcont ys
concat_preserves_contains (Right ycont) = precat_preserves_contains ycont xs

total
dconcat_preserves_contains : DecEq a =>
    {x: a} ->                           -- Element we're looking for
    {xs : List a} ->                    -- First list
    {ys : List a} ->                    -- Second list
    (Either                             -- The element is either in:
        (Contains x xs)               -- The first list
        (Contains x ys)) ->           -- Or the second list
        Dec (Contains x (xs++ys))       -- So if we're concatenating them, it should be in the result!
dconcat_preserves_contains (Left xprf) = Yes $ postcat_preserves_contains xprf ys
dconcat_preserves_contains (Right yprf) = Yes $ precat_preserves_contains yprf xs

total
concat_preserves_missing : DecEq a => (x : a) -> (xs : List a) -> (ys : List a) -> Not (Contains x xs) -> Not (Contains x ys) -> Not (Contains x (xs ++ ys))
concat_preserves_missing x [] ys nixs niys nier = niys nier
concat_preserves_missing x (z :: xs) ys nixs niys nier = case (decEq x z) of
    -- If the head is the same, we have a contradiction!
    (Yes prf) => nixs $ rewrite prf in (Here z xs)
    -- Otherwise, recurse
    (No contra) => concat_preserves_missing x xs ys (rprepend_preserves_missing contra nixs) niys (rprepend_preserves_contains contra nier)


total

postcat_eq : (xs : List a) -> xs = (xs ++ [])
postcat_eq [] = Refl
postcat_eq (x :: xs) = let rec = sym $ postcat_eq xs in
    rewrite rec in Refl

total
rconcat_preserves_contains : DecEq a => (x : a) -> (xs : List a) -> (ys : List a) -> Contains x (xs ++ ys) -> Either (Contains x xs) (Contains x ys)
-- case 1, xs empty, therefore it's in ys
rconcat_preserves_contains x [] ys y = Right y
-- case 2, ys empty, therefore it's in xs
rconcat_preserves_contains x xs [] y = Left (rewrite postcat_eq xs in y)
-- case 3, recurse down xs. Start by checking the head
rconcat_preserves_contains x (z :: xs) ys y = case (decEq x z) of
    -- If found, simply give it back
    (Yes prf) => Left $ rewrite sym prf in Here x xs
    -- If not, recurse
    (No contra) => case rconcat_preserves_contains x xs ys (rprepend_preserves_contains contra y) of
        -- Rebuild if in xs
        (Left cxxs) => Left (There z cxxs)
        -- Otherwise return
        (Right w) => Right w


-- here_it_is2 : {x : a} -> {y : a} -> {xs : List a} -> (x = y) -> (Contains y xs) -> (Contains x xs)
-- here_it_is2 prf z = replace {p = ((flip Contains) xs)} (sym prf) z

total
not_in_head_therefore_not_equal : DecEq a => (x : a) -> (z : a) -> (xs: List a) -> Not (Contains x (z :: xs)) -> Not (x = z)
not_in_head_therefore_not_equal x z xs f prf = f $ replace {p = ((flip Contains) (z :: xs))} (sym prf) (Here z xs)

total
rprepend_in_preserves_missing : DecEq a => (x : a) -> (z : a) -> (xs : List a) -> (ys : List a) -> Not (Contains x (xs ++ (z :: ys))) -> Not(Contains x (xs ++ ys))
rprepend_in_preserves_missing x z [] ys f y = let neq = not_in_head_therefore_not_equal x z ys f in
    case (decEq x z) of
         (Yes prf) => neq prf
         (No contra) => f $ prepend_preserves_contains y
rprepend_in_preserves_missing x z (w :: xs) ys f y = let neq = not_in_head_therefore_not_equal x w (xs ++ (z :: ys)) f in
    case (decEq x w) of
         (Yes prf) => neq prf
         (No contra) => rprepend_in_preserves_missing x z xs ys (rprepend_preserves_missing neq f) (rprepend_preserves_contains neq y)


total
rpostcat_preserves_missing  : DecEq a => (x : a) -> (xs : List a) -> (ys : List a) -> Not (Contains x (xs ++ ys)) -> Not (Contains x xs)
rpostcat_preserves_missing x xs [] f y = let f' = rewrite postcat_eq xs in f in f' y
rpostcat_preserves_missing x xs (z :: ys) f y = rpostcat_preserves_missing x xs ys (rprepend_in_preserves_missing x z xs ys f) y

total
contra_contains : DecEq a => {x : a} -> {xs : List a} -> Not (Contains x (x :: xs)) -> Void
contra_contains f = f $ Here x xs

total
rprecat_preserves_missing : DecEq a => (x: a) -> (xs: List a) -> (ys: List a) -> Not (Contains x (ys ++ xs)) -> Not (Contains x xs)
-- Empty ys, must be in xs. Use contradiction
rprecat_preserves_missing x xs [] f prf_x_in_xs = f prf_x_in_xs
-- Empty xs, must by in ys. Use emptyness to prove.
rprecat_preserves_missing x [] ys f prf_x_in_xs = empty_contains_is_impossible prf_x_in_xs
-- Otherwise, recurse down ys
rprecat_preserves_missing x xs (y :: ys) f prf_x_in_xs = case (decEq x y) of
                                                    -- If the head of y is x, then we have a simple contradiction!
                                                    (Yes prf) => let neq = not_in_head_therefore_not_equal x y (ys ++ xs) f in neq prf
                                                    -- Otherwise, recurse down
                                                    (No contra) => rprecat_preserves_missing x xs ys (rprepend_preserves_missing contra f) prf_x_in_xs

total
rconcat_preserves_missing : DecEq a => (x : a) -> (xs : List a) -> (ys : List a) ->
    -- Given a proof that the concatenation does not contain x
    Not (Contains x (xs ++ ys)) ->
    -- Produce a pair of proofs that neither x nor y contain x
    (Not (Contains x xs), Not(Contains x ys))
rconcat_preserves_missing x xs ys f = (rpostcat_preserves_missing x xs ys f, rprecat_preserves_missing x ys xs f)