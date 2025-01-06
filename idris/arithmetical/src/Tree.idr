import Decidable.Equality
import Data.Fin

%default total

data Tree : a -> Type where
    L : Tree a
    Br : (l : Tree a) -> (x : a) -> (r : Tree a) -> Tree a


-- Proof of the fact that list contains an element
-- data Contains : a -> List a -> Type where
--   Here : (x : a) -> (xs : List a) -> Contains x (x :: xs)
--   There : (x : a) -> Contains y xs -> Contains y (x :: xs)

data TElem : a -> Tree a -> Type where
    -- A proof that x is at the root of the tree
    Here : (x : a) -> (l : Tree a) -> (r : Tree a) -> TElem x (Br l x r)
    -- A proof that x is in the left hand branch of the tree
    Left : (x : a) -> (TElem x l) -> TElem x (Br l y r)
    -- A proof that x is in the right hand branch of the tree
    Right : (x : a) -> (TElem x r) -> TElem x (Br l y r)

leafDoesNotContain : TElem x L -> Void
leafDoesNotContain (Here y l r) impossible
leafDoesNotContain (Left y z) impossible
leafDoesNotContain (Right y z) impossible

branchPreservesMissing : Not (x = y) -> Not (TElem x l) -> Not (TElem x r) -> Not (TElem x (Br l y r))
branchPreservesMissing c l r (Here x l' r') = c Refl
branchPreservesMissing c l r (Left x w) = l w
branchPreservesMissing c l r (Right x w) = r w


isElem : DecEq a => (x : a) -> (t : Tree a) -> Dec (TElem x t)
-- Not in a leaf? Not in the tree.
isElem x L = No (leafDoesNotContain)
-- Search a value in the branch
isElem x (Br l y r) = case (decEq x y) of
                           -- If equal, return that!
                           (Yes prf) => Yes (rewrite (sym prf) in (Here x l r))
                           -- Otherwise, search the branches, starting with the left
                           (No contra) => case (isElem x l) of
                                               (Yes prf) => Yes (Left x prf)
                                               -- If we don't find it, search the right
                                               (No f) => case (isElem x r) of
                                                              (Yes prf) => Yes (Right x prf)
                                                              -- And if it's not there either, witness a proof that if it's not in either, it's not in the tree
                                                              (No g) => No (branchPreservesMissing contra f g)


-- Map a function across a tree
mapT : (f : a -> b) -> (Tree a) -> (Tree b)
mapT f L = L
mapT f (Br l x r) = let l' = mapT f l
                        r' = mapT f r in Br l' (f x) r'

-- An in-order traversal across a tree
inOrderTravT : (f : a -> b) -> (g : b -> b -> b) -> b -> (Tree a) -> b
inOrderTravT f g z L = z
inOrderTravT f g z (Br l x r) = let left = inOrderTravT f g z l
                                    right = inOrderTravT f g z r
                                    c = f x in (left `g` c) `g` right

flatTraverse : Tree a -> List a
flatTraverse t = inOrderTravT (\x => [x]) (++) [] t

flattenTree : Tree a -> List a
flattenTree L = []
flattenTree (Br l x r) = ((flattenTree l) ++ [x]) ++ (flattenTree r)

flatTraverseIsFlatten : (t : Tree a) -> (flatTraverse t) = (flattenTree t)
flatTraverseIsFlatten L = Refl
flatTraverseIsFlatten (Br l x r) = let ftL = flatTraverseIsFlatten l
                                       ftR = flatTraverseIsFlatten r in
                                       rewrite ftL in
                                       rewrite ftR in Refl

exampleTree : Tree Nat
exampleTree = (Br (Br (Br L 0 L) 1 (Br L 2 (Br L 3 L))) 4 (Br (Br L 5 L) 6 (Br L 7 (Br L 8 (Br L 9 L)))))

flatFt : List Nat
flatFt = flattenTree exampleTree

flatTt : List Nat
flatTt = flatTraverse exampleTree

ixExists = isElem 6 exampleTree

notExists = isElem 100 exampleTree

-- Proof that map functions across a tree compose
map_composes : Eq a => (t: Tree a) -> (f : a -> b) -> (g : b -> c) -> (mapT g (mapT f t)) = (mapT (g . f) t)
map_composes L f g = Refl
map_composes (Br l x r) f g = let map_composes_l = map_composes l f g
                                  map_composes_r = map_composes r f g in
                            rewrite map_composes_l in
                            rewrite map_composes_r in Refl