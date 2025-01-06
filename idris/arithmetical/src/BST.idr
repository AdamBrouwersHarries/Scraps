import Decidable.Equality
import Data.Fin
import Control.Ord

%default total

data BTree : (v : Nat) -> Type where
    -- A leaf. Strictly empty.
    L : BTree v
    -- A branch/root node in the tree.
    Br : (l : BTree vl) -> (LTE vl v) -> (r : BTree vr) -> (GT vr v) -> BTree v

%hint
eqImpliesLTE : (n : Nat) -> LTE n n
eqImpliesLTE 0 = LTEZero
eqImpliesLTE (S k) = LTESucc (eqImpliesLTE k)

fresh : (n : Nat) -> BTree n
fresh n = Br L (eqImpliesLTE n) (L {v = S(n)}) (LTESucc (eqImpliesLTE n))

-- -- Insert a value to a btree.
insert : {n : Nat} -> (m : Nat) -> (t : BTree n) -> (BTree n)
insert m L = case isLTE m n of
                  (Yes prf) => Br (L {v = m}) prf (L {v = S(n)}) (LTESucc (eqImpliesLTE n))
                  (No contra) => Br L (eqImpliesLTE n) (L {v = m}) (notLTEImpliesGT contra)
insert m (Br l x r y) = case isLTE m n of
                             (Yes prf) => Br (insert {n} m l) ?insert_rhs_2 r y
                             (No contra) => ?insert_rhs_3



-- data BTree : Ord t => (v : t) -> Type where
--     L : BTree @{ordImpl} v
--     Br : (l : BTree vl) -> (LTE vl v) -> (r : BTree vr) -> (GTE vr v) -> BTree @{ordImpl} v

-- empty : Ord a => (v : a) -> BTree @{ordImpl} v
-- empty v = L

-- fresh : Ord a => (v : a) -> BTree @{ordImpl} v
-- fresh v = let left = empty v
--               right = empty v in Br left ()
-- insert : (Ord a) => (x : a) -> {s : a} -> (BTree @{ordImpl} s) -> (BTree @{ordImpl} s)
-- insert x L = Br ?hoele ?hole1 ?holeeee ?hole2
-- insert x (Br l y r z) = ?insert_rhs_1



-- insert x (L v) = if (x < v) then
--     -- Insert to the right
--     Br :
-- case (x < v) of
--                       False => ?insert_rhs_2
--                       True => ?insert_rhs_3
-- insert x (Br l y r z) = ?insert_rhs_1

-- data CallTree : (a : Type) -> Show a => Type where
--     L : CallTree a @{showImpl}
--     Call :  (f : a) -> (calls : List a) -> CallTree a @{showImpl}

-- printCallTree : (Show a) => CallTree a -> String