import Data.Nat

%default total

-- Find the absolute difference between two natural numbers
delta : Nat -> Nat -> Nat
delta 0 0 = 0
delta 0 (S k) = (S k)
delta (S k) 0 = (S k)
delta (S k) (S j) = delta k j

-- A balanced binary tree, with invariants kept in the tree
data AVLTree : (n : Nat) -> a -> Type where
    -- Leaves have height zero
    L : AVLTree 0 a
    -- Branches maintain that the height difference is less than or equal to 1
    Br : {m, n : _} -> (v : a) -> (l : AVLTree n a) -> (r : AVLTree m a) -> (LTE (delta n m) 1) -> AVLTree (S (maximum n m)) a

data UnbalancedTree : a -> Type where
    Lu : UnbalancedTree a
    Bru : (v : a) -> (l : UnbalancedTree a) -> (r : UnbalancedTree a) -> UnbalancedTree v

-- k + 2 !<= 1
%hint
succNotLTEOne : Not (LTE (S (S k)) 1)
succNotLTEOne (LTESucc LTEZero) impossible
succNotLTEOne (LTESucc (LTESucc x)) impossible

-- delta n n <= 1
%hint
deltaNLTEOne : (n : Nat) -> LTE (delta n n) 1
deltaNLTEOne 0 = LTEZero
deltaNLTEOne (S k) = deltaNLTEOne k

-- Find the delta, showing if it's less than or equal to 1
deltaLTE : (n : Nat) -> (m : Nat) -> Dec (LTE (delta n m) 1)
deltaLTE 0 0 = Yes LTEZero
deltaLTE 0 (S 0) = Yes (LTESucc LTEZero)
deltaLTE 0 (S (S k)) = No (succNotLTEOne)
deltaLTE (S 0) 0 = Yes (LTESucc LTEZero)
deltaLTE (S (S k)) 0 = No (succNotLTEOne)
deltaLTE (S k) (S j) = deltaLTE k j




hi : {n : Nat} -> AVLTree n a -> Nat
hi t = n

hihi : {n : Nat} -> AVLTree n a -> (p ** AVLTree p a)
hihi t = (n ** t)

mutual
    -- Rotate the tree left. The right branch must be at least a branch node
    leftRotate : Ord a => {lh, rh : _ } -> (c : a) -> (l : AVLTree lh a) -> (r : AVLTree (S rh) a) -> (newHeight ** AVLTree newHeight a)
    leftRotate c l L impossible
    leftRotate c l (Br v rl rr prf) = let (lheight ** newLeft) = balance c l rl
                                          (rheight ** newRight) = hihi rr in
        case deltaLTE lheight rheight of
            (Yes prf) => (S (maximum lheight rheight) ** Br v newLeft newRight prf)
            (No contra) => balance v newLeft newRight


    -- Fixup a tree, given two subtress (left, right) and a value
    balance : Ord a => {lh, rh : _} -> (v : a) -> (l : AVLTree lh a) -> (r : AVLTree rh a) -> (h ** AVLTree h a)
    -- Look to see what the delta is between the subtrees
    balance v l r = case deltaLTE lh rh of
                    -- If the delta <= 1, then we can use the subtrees as-is
                    (Yes prf) => ((S (maximum lh rh)) ** Br v l r prf)
                    (No contra) => if lh < rh then
                        leftRotate v l r
                        else
                        ?hollesome



insert : Ord a => (x : a) -> (AVLTree n a) -> (h ** AVLTree h a)
insert x L = (1 ** Br x L L LTEZero)
insert x (Br v l r p) = if x <= v then
        let (height ** newLeft) = insert x l in
        ((S (maximum height (hi r))) ** Br v newLeft r ?newProof)
    else
    ?insertIntoRight
