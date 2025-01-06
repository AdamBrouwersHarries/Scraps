
import Data.Nat
%default total

-- A slightly weird version of binary numbers.
-- We have the LSB as the /outermost/ constructor.
-- This avoids having to pass carry bits "up" the recursion.
-- The "printout" is backwards, but what can you do.
data Bin : Type where
    Z : Bin
    O : Bin -> Bin
    I : Bin -> Bin

Show Bin where
    show Z = ""
    show (O x) = show x ++ "0"
    show (I x) = show x ++ "1"

inc : Bin -> Bin
inc Z = I Z
inc (O x) = I x
inc (I x) = O (inc x)

fromNat : Nat -> Bin
fromNat 0 = Z
fromNat (S k) = inc (fromNat k)

width : Bin -> Nat
width Z = 0
width (O x) = S (width x)
width (I x) = S (width x)

toNatPwr : Bin -> (p : Nat) -> Nat
toNatPwr Z p = 0
toNatPwr (O x) p = toNatPwr x (2 * p)
toNatPwr (I x) p = p + (toNatPwr x (2 * p))

toNat : Bin -> Nat
toNat Z = 0
toNat (O x) = toNat x
toNat (I x) = (power 2 (width x)) + (toNat x)

five = (I (O (I Z)))
incFive = show $ inc five
fiveFromNat = show $ fromNat 5
natFromFive = show $ toNat five

incIsS : (n : Nat) -> inc (fromNat n) = fromNat (S n)
incIsS 0 = Refl
incIsS (S k) = Refl

-- composeIsIdentity : (n : Nat) -> (toNat $ fromNat n) = n
-- composeIsIdentity 0 = Refl
-- composeIsIdentity (S k) = let rec = composeIsIdentity k in ?something

    -- rewrite incIsS k in

-- add : Bin -> Bin -> Bin
-- add Z y = y
-- add (O x) Z = O x
-- add (O x) (O y) = O (add x y)
-- add (O x) (I y) = I (add x y)
-- add (I x) Z = I x
-- add (I x) (O y) = I (add x y)
-- add (I x) (I y) = O (inc $ add x y)

add : Bin -> Bin -> Bin
add Z y = y
add (O x) y = ?add_rhs_1
add (I x) y = ?add_rhs_2

fivePlusFive = show $ five `add` five
ten = show $ fromNat 10

addAssoc : (n : Bin) -> (m : Bin) -> (p : Bin) -> ((n `add` m) `add` p) = (n `add` (m `add` p))
