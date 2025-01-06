import Data.Nat

%default total

--- Balanced AVL trees, with the height kept in the type
--- Derifed from the haskell implementation at : https://hackage.haskell.org/package/AvlTree-4.2/docs/Data-Tree-AVL.html
--- Comments kept for record keeping

-- A balanced binary tree, with invariants encoded in the type
data AVL : a -> (n : Nat) -> Type where
    -- Leaves always have height zero
    E : AVL e 0
    -- Right tree height > left tree height. BF = -1
    N : {n : _} -> (l : AVL a n) -> (e : a) -> (r : AVL a (S n)) -> AVL a (S (S n))
    -- Right tree height = left tree height. Branch factor = 0
    Z : {n : _} -> (l : AVL a n) -> (e : a) -> (r : AVL a n) -> AVL a (S n)
    -- Right tree height < left tree height. BF = +1
    P : {n : _} -> (l : AVL a (S n)) -> (e : a) -> (r : AVL a n) -> AVL a (S (S n))

empty : AVL a 0
empty = E

isEmpty : AVL a n -> Bool
isEmpty E = True
isEmpty _ = False

singleton : a -> AVL a 1
singleton v = Z E v E

data OneOf : (n : Nat) -> (k : Type) -> Type where
    DN : (AVL a (S (S n))) -> OneOf n k
    DZ : (AVL a (S n)) -> OneOf n k
    DP : (AVL a (S (S n))) -> OneOf n k

mutual

    insert' : Ord a => {n : _} -> a -> AVL a n -> OneOf n (AVL a n)


    insert : Ord a => {n : _} -> a -> AVL a n -> OneOf n (AVL a n)
    insert v t = put v t

    put : Ord a => {n : _} -> (v : a) -> AVL a n -> OneOf n (AVL a n)
    put v E = DZ (Z E v E)
    put v (N l e r) = putN v l e r
    put v (Z l e r) = ?put_rhs_2
    put v (P l e r) = ?put_rhs_3

    --- LEVEL 1

    -- Push into an "N" subtree
    putN : Ord a => {n : _ } -> (v : a) -> (l : AVL a n) -> (e : a) -> (r : AVL a (S n)) -> OneOf n (AVL a n)
    putN v l e r = case compare v e of
        LT => putNL v l e r
        EQ => ?hasdf -- DN (N l e r)
        GT => ?homeleo_2

    -- Push into a "Z" subtree
    putZ : Ord a => {n, m : _ } -> (v : a) -> (l : AVL a n) -> (e : a) -> (r : AVL a m) -> OneOf n (AVL a n)
    putZ v l e r = ?putZ_rhs

    -- Push into a "P" subtree
    putP : Ord a => {n, m : _ } -> (v : a) -> (l : AVL a n) -> (e : a) -> (r : AVL a m) -> OneOf n (AVL a n)
    putP v l e r = ?putP_rhs

    --- LEVEL 2

    -- Push into the Left subtree of an "N" node
    putNL : Ord a => {n : _} -> (v : a) -> (l : AVL a n) -> (e : a) -> (r : AVL a (S n)) -> OneOf n (AVL a n)
    -- putNL v E e r = (2 ** Z (Z E v E) e r)
    -- putNL v (N ll le lr) e r = let (nh ** l') = putN v ll le lr in (?homese ** N l' e ?helpme)
    -- putNL v (Z l y z) e r = ?putNL_rhs_2
    -- putNL v (P l y z) e r = ?putNL_rhs_3

--  putNL  E           a r = Z (Z    E  e0 E ) a r       -- L subtree empty, H:0->1, parent BF:-1-> 0
--  putNL (N ll le lr) a r = let l' = putN ll le lr      -- L subtree BF<>0, H:h->h, parent BF:-1->-1
--                           in l' `seq` N l' a r
--  putNL (P ll le lr) a r = let l' = putP ll le lr      -- L subtree BF<>0, H:h->h, parent BF:-1->-1
--                           in l' `seq` N l' a r
--  putNL (Z ll le lr) a r = let l' = putZ ll le lr      -- L subtree BF= 0, so need to look for changes
--                           in case l' of
--                           E       -> error "push: Bug0" -- impossible
--                           Z _ _ _ -> N l' a r         -- L subtree BF:0-> 0, H:h->h  , parent BF:-1->-1
--                           _       -> Z l' a r         -- L subtree BF:0->+/-1, H:h->h+1, parent BF:-1-> 0