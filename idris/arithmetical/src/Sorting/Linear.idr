import Builtin
import Data.Linear.Notation
import Data.Linear.Interface
import Data.Linear.LList
import Data.Linear.LVect
import Data.Linear.LNat

%default total

data SList : a -> Type where
    Z : SList a
    C : (x : a) -> (l : SList a) -> SList a

-- Sorted vector, indexed by the maximal element
-- data SVect : Ord a => Nat -> a -> (m : a) -> Type where
--     Nil : SVect @{ordImpl} 0 a m
--     (::) : (e : a) ->


-- Comparisons between linear nats
infix 5 <@
(<@) : LNat -@ LNat -@ Bool
(<@) Zero Zero = False
(<@) Zero (Succ y) = y `seq` True
(<@) (Succ x) Zero = x `seq` False
(<@) (Succ x) (Succ y) = x <@ y


-- Insertion with sized vectors
linsert : LNat -@ LVect n LNat -@ LVect (S n) LNat
linsert x [] = [x]
linsert x (y :: xs) = let (x' # x'') = pair $ duplicate x in
    let (y' # y'') = pair $ duplicate y in
        if x' <@ y' then
            x'' :: y'' :: xs
        else
            y'' :: (linsert x'' xs)

linss : {n : _} -> LVect n LNat -> LVect n LNat
linss [] = []
linss (x :: xs) = let sxs = linss xs in
    linsert x sxs


fromNat : Nat -> LNat
fromNat 0 = Zero
fromNat (S k) = Succ (fromNat k)

Num LNat where
    (+) Zero y = y
    (+) (Succ x) y = Succ (x + y)

    (*) Zero y = y
    (*) (Succ x) y = y + (x * y)

    fromInteger i = fromNat $ integerToNat i

lnatToInteger : LNat -> Integer
lnatToInteger Zero = 0
lnatToInteger (Succ x) = 1 + lnatToInteger x

Show LNat where
    show n = show (the Integer (lnatToInteger n))

printRest : (Show a) => LVect n a -> String
printRest [] = "]"
printRest (x :: xs) = "," ++ (show x) ++ (printRest xs)

printLVect : (Show a) => LVect n a -> String
printLVect [] = "[]"
printLVect (x :: xs) = "[" ++ (show x) ++ printRest xs where


Show a => Show (LVect n a) where
    show lv = printLVect lv

vins : LVect 7 LNat
vins = linsert 10 [2, 3, 9, 12, 34, 50]

-- lsorted : LVect 10 LNat
lsorted = show $ linss [4,7,3,1,2,5,6,8,9,0]