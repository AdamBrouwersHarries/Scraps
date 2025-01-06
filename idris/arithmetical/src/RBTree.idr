import Data.Nat

%default total

data Colour = Red | Black

not : Colour -> Colour
not Red = Black
not Black = Red

%hint
notnot : (c : Colour) -> c = (not $ not c)
notnot Red = Refl
notnot Black = Refl

--
data RBTree : (a : Type) -> Colour -> Type where
    L : (c : Colour) -> RBTree a c
    Br : {c : _} ->  (l : RBTree a c) -> (e : a) -> (r : RBTree a c) -> RBTree a (not c)

flip : RBTree a c -> RBTree a (not c)
flip (L c) = L (not c)
flip (Br l e r) = Br (flip r) e (flip r)

-- make the root of a tree the colour "nc" (new colour)
make : (nc : Colour) -> RBTree a c -> RBTree a nc
make nc (L _) = L nc
make nc (Br l e r) = rewrite notnot nc in Br (make (not nc) l) e (make (not nc) r)

makeBlack : RBTree a c -> RBTree a Black
makeBlack = make Black

makeRed : RBTree a c -> RBTree a Red
makeRed = make Red


member : (Ord a) => a -> RBTree a c -> Bool
member x (L c) = False
member x (Br l e r) = case compare x e of
                           LT => member x l
                           EQ => True
                           GT => member x r


ins : (Ord a) => {c : _} -> a -> (t : RBTree a c) -> (d ** RBTree a d)
ins x (L _) = (Red ** Br (L Black) x (L Black))
ins x (Br l e r) = case compare x e of
                        LT => let (ncl ** newl) = ins x l in
                            case (ncl, c) of
                                (Black, Red) => ?hole_3 -- Needs rotation!
                                (Red, Black) => ?hole_4 -- Needs rotation!
                                (_, _) => (not ncl ** Br newl e r)

                        -- Br (ins x l) e r
                        EQ => ?ins_rhs_3
                        GT => ?ins_rhs_4


insert : (Ord a) => a -> (t : RBTree a c) -> (RBTree a Black)
insert x t = ?insert_rhs

-- insert :: (Ord a) => a -> Tree a -> Tree a
-- insert x s = makeBlack $ ins s
--   where ins E  = T R E x E
--         ins (T color a y b)
--           | x < y  = balance color (ins a) y b
--           | x == y = T color a y b
--           | x > y  = balance color a y (ins b)
--         makeBlack (T _ a y b) = T B a y b

balance : (Ord a) => (colour : Colour) -> RBTree a cl -> (x : a) -> RBTree a cr -> (RBTree a Red)
balance Black (Br (Br a x b) y c) z d = ?whatthe --Br (Br a x b) y (Br c z d)
balance colour y x z = ?balance_rhs_0


-- balance :: Color -> Tree a -> a -> Tree a -> Tree a
-- balance B (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
-- balance B (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
-- balance B a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
-- balance B a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
-- balance color a x b = T color a x b

-- data Color = R | B deriving Show

-- data Tree a = E | T Color (Tree a) a (Tree a) deriving Show