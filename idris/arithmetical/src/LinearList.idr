import Builtin
import Data.Vect

data LList : a -> Type where
    Z : LList a
    C : (1 x : a) -> (1 l : LList a) -> LList a

-- 1 llmap : (f : a -> b) -> (1 x : LList a) -> LList b
-- llmap f Z = Z
-- llmap f (C x l) = l

llmap : (f : (1 _ : a) -> b) -> (1 l : LList a) -> LList b
llmap f Z = Z
llmap f (C x l) = C (f x) (llmap f l)


lconsume : (1 l : LList a) -> LList a
lconsume Z = Z
lconsume (C x l) = C x (lconsume l)

okay : LList Nat
okay = C 0 (C 1 (C 2 (C 3 Z)))

data LVect : Nat -> Type -> Type where
    LNil : LVect 0 e
    LCons : (1 x : e) -> (1 v : LVect n e) -> LVect (S n) e

Show e => Show (LVect len e) where
    show xs = "[" ++ show' xs ++ "]" where
        show' : forall n . LVect n e -> String
        show' LNil        = ""
        show' (LCons x LNil) = show x
        show' (LCons x xs)  = show x ++ ", " ++ show' xs



map : {a, b: Type} -> (f : a -> b) -> (LVect n a) -> LVect n b
map f LNil = LNil
map f (LCons x v) = LCons (f x) (map f v)


-- Compare v and o, return the result as well as copies of v and o
compareLImpl : (Ord a) => (v : a) -> (o : a) -> (Bool, (a, a))
compareLImpl v o = (v < o, v, o)

-- A pseudo-linear implementation of "compare", where we retain a copy of the arguments, and send them back again
compareL : (Ord a) => (1 v : a) -> (1 o : a) -> (Bool, (LPair a a))
compareL v o = let (b, (v', o')) = assert_linear ((assert_linear compareLImpl) v) o in
    (b, v' # o')

linsert : (Ord a) => (1 v : a) -> LVect n a -> LVect (S n) a
linsert v LNil = LCons v LNil
linsert v (LCons x xs) =  let (b, (v' # x')) = compareL v x in
    if b then
        LCons v' (LCons x' xs)
    else
        LCons x' (linsert v' xs)

okayv : LVect 4 Int
okayv = LCons 0 (LCons 1 (LCons 3 (LCons 5 LNil)))

okayvins = linsert 4 okayv

txt : String
txt = show okayvins