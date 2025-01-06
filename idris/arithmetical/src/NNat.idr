-- Natural numbers, now with negatives!
%default total


-- data Sign = Pos | Neg

-- data NegNat : Sign -> Type where
--     Z : NegNat p
--     S : NegNat Pos -> NegNat Pos
--     P : NegNat Neg -> NegNat Neg


-- NNat : Type
-- NNat = (p : Sign ** NegNat p)

-- extract : {p : Sign} -> NegNat p -> NNat
-- extract n = (p ** n)

-- plus : (NegNat p) -> (NegNat q) -> (s ** (NegNat s))
-- plus Z Z = (Pos ** Z)
-- plus Z (S x) = (Pos ** (S x))
-- plus Z (P x) = (Neg ** (P x))
-- plus (S x) Z = (Pos ** (S x))
-- plus (S x) (S y) = let (p ** n) = plus x y in
--     (Pos ** (S (S x)))
-- plus (S x) (P y) = plus x y
-- plus (P x) Z = (Neg ** (P x))
-- plus (P x) (S y) = plus x y
-- plus (P x) (P y) = let (p ** n)  plus x y in
--     (Neg ** (P (P x)))

-- dec : NNat -> NNat
-- dec ((Pos ** Z)) = (Pos ** Z)
-- dec ((Pos ** (S x))) = (Pos ** x)
-- dec ((Neg ** Z)) = (Pos ** Z)
-- dec ((Neg ** (P x))) = (Neg ** x)


-- plus (Pos ** Z) (Pos ** Z) = (Pos ** Z)
-- plus (Pos ** Z) (Neg ** Z) = (Pos ** Z)
-- plus (Pos ** Z) (Neg ** (P r)) = (Neg ** (P r))
-- plus (Pos ** Z) (Pos ** (S x)) = (Pos ** (S x))
-- plus (Pos ** (S l)) (Pos ** Z) = (Pos ** (S l))
-- plus (Pos ** (S l)) (Neg ** Z) = (Pos ** (S l))
-- plus (Pos ** (S l)) (Pos ** (S r)) = ?another
-- --case plus (Pos ** l) (Pos ** r) of
--   --  ?hole => ?rhole
--     -- (Pos ** (S (S n)))
-- plus (Pos ** (S l)) (Neg ** (P r)) = plus (Pos ** l) (Neg ** r)

-- -- Negative LHS
-- plus (Neg ** Z) (Pos ** Z) = (Neg ** Z)
-- plus (Neg ** Z) (Neg ** Z) = (Neg ** Z)
-- plus (Neg ** Z) (Pos ** (S r)) = (Pos ** (S r))
-- plus (Neg ** Z) (Neg ** (P r)) = (Neg ** (P r))
-- plus (Neg ** (P l)) (Pos ** Z) = (Neg ** (P l))
-- plus (Neg ** (P l)) (Neg ** Z) = (Neg ** (P l))
-- plus (Neg ** (P l)) (Pos ** (S r)) = plus (Neg ** l) (Pos ** r)
-- plus (Neg ** (P l)) (Neg ** (P r)) =  ?holesome -- let (Neg ** n) = plus (Neg ** l) (Neg ** r) in
    -- (Neg ** (P (P n)))

-- vec : (n : Nat ** Vect n Int)
-- vec = (2 ** [3, 4])

-- flip : NSign -> NSign
-- flip Pos = Neg
-- flip Neg = Pos



-- plus : (l : NNat p) -> (r : NNat q) -> (r ** NNat r)
-- plus Z Z = (?sa ** Z)
-- plus Z r@(S x) = r
-- plus Z (N x) = ?plus_rhs_5
-- plus (S x) r = ?plus_rhs_1
-- plus (N x) r = ?plus_rhs_2


-- NNat : Type
-- NNat = (Nat, Nat)

-- zero : NNat
-- zero = (0, 0)

-- S : NNat -> NNat
-- S (0, 0) = (1, 0)
-- S (0, (S k)) = (0, 0)
-- S ((S k), 0) = ((S (S k)), 0)
-- S ((S k), (S j)) = ((S k), j)

-- N : NNat -> NNat
-- N (0, 0) = (0, 1)
-- N (0, (S k)) = (0, (S (S k)))
-- N ((S k), 0) = (0, 0)
-- N ((S k), (S j)) = (k, (S j))

-- plus : NNat -> NNat -> NNat

-- data NNat : Type where
--     Z : NNat
--     S : NNat -> NNat
--     P : NNat -> NNat

-- plus : NNat -> NNat -> NNat
-- plus Z Z = ?plus_rhs_3
-- plus Z (S x) = ?plus_rhs_4
-- plus Z (P x) = ?plus_rhs_5
-- plus (S x) y = ?plus_rhs_1
-- plus (P x) y = ?plus_rhs_2



-- weird_nat : NNat P
-- weird_nat = Sc (Sb (Z))


-- plus : (pl : PN ** NNat pl) -> (pr : PN ** NNat pr) -> (pq : PN ** NNat pq)
-- plus ((pl ** Z)) ((pr ** Z)) = (P ** Z)
-- plus ((pl ** Z)) ((P ** (Sc x))) = (P ** (Sc x))
-- plus ((pl ** Z)) ((N ** (Sb x))) = (N ** (Sb x))
-- plus ((P ** (Sc x))) ((pr ** Z)) = (P ** (Sc x))
-- plus ((P ** (Sc x))) ((P ** (Sc y))) = let (p ** n) = plus (P ** x) (P ** y) in
--     (p ** (Sc (Sc x)))
-- plus ((P ** (Sc x))) ((N ** (Sb y))) = ?plus_rhs_7
-- plus ((N ** (Sb x))) ((pr ** Z)) = (N ** (Sb x))
-- plus ((N ** (Sb x))) ((P ** (Sc y))) = ?plus_rhs_9
-- plus ((N ** (Sb x))) ((N ** (Sb y))) = ?plus_rhs_10


-- Base case(s)
-- plus ((Ze ** Z)) ((Ze ** Z)) = (Ze ** Z)
-- plus ((Ze ** Z)) r = r
-- plus l ((Ze ** Z)) = l

-- -- Not matching, which are just stripped
-- plus ((P ** (Sc x))) ((N ** (Sb y))) = plus (P ** x) (N ** y)
-- plus ((N ** (Sb x))) ((P ** (Sc y))) = plus (N ** x) (P ** y)

-- -- matching, where we need to pattern match on a recursion
-- plus ((P ** (Sc x))) ((P ** (Sc y))) = let (P ** n) = (plus (P ** x) (P ** y)) in
--     (P ** (Sc (Sc n)))
-- plus ((N ** (Sb x))) ((N ** (Sb y))) = let (N ** n) = (plus (N ** x) (N ** y)) in
--     (N ** (Sb (Sb n)))

-- Base case(s)
-- plus Z Z = (Ze ** Z)
-- plus Z r = (pr ** r)
-- plus l Z = (pl ** l)
-- -- "Compatible" NNats
-- plus (Sc x) (Sc y) = plus x (Sc (Sc y))
-- plus (Sb x) (Sb y) = plus x (Sb (Sb y))
-- -- "Incompatible" NNats
-- plus (Sc x) (Sb y) = plus x y
-- plus (Sb x) (Sc y) = plus x y

-- plusZeroLeftNeutral : {p : PN} -> (right : NNat p) -> (Z `plus` right) = (p ** right)
-- plusZeroLeftNeutral Z = Refl
-- plusZeroLeftNeutral (Sc x) = Refl
-- plusZeroLeftNeutral (Sb x) = Refl

-- plusZeroRightNeutral : {p : PN} -> (left : NNat p) -> (left `plus` Z) = (p ** left)
-- plusZeroRightNeutral Z = Refl
-- plusZeroRightNeutral (Sc x) = Refl
-- plusZeroRightNeutral (Sb x) = Refl

-- plusAssoc : (left : NNat lp) -> (mid : NNat mp) -> (right : NNat rp) -> (left `plus` (mid `plus` right)) = ((left `plus` mid) `plus` right)



-- data NNat : Type where
--     Z : NNat
--     S : NNat -> NNat
--     N : NNat -> NNat

-- normalise_stack : (n : NNat) -> (stack : NNat) -> NNat
-- -- If both are zero, then that's our trivial answer
-- normalise_stack Z Z = Z
-- -- Once we have finished "consuming" our input, we can reverse the stack as our output
-- normalise_stack Z (S x) = S (normalise_stack Z x)
-- normalise_stack Z (N x) = N (normalise_stack Z x)
-- -- eliminate negations of successors
-- normalise_stack (N y) (S x) = normalise_stack y x
-- normalise_stack (S y) (N x) = normalise_stack y x
-- -- continue as normal
-- normalise_stack (S x) Z = normalise_stack x (S Z)
-- normalise_stack (N x) Z = normalise_stack x (N Z)
-- normalise_stack (S y) (S x) = normalise_stack y (S (S x))
-- normalise_stack (N y) (N x) = normalise_stack y (N (N x))

-- normalise : (n : NNat) -> NNat
-- normalise n = normalise_stack n Z


-- normLemma1 : (x : NNat) -> normalise_stack x (S Z) = S x
-- normLemma1 Z = Refl
-- normLemma1 (S x) = rewrite ?something in  normLemma1 x
-- normLemma1 (N x) = ?normLemma1_rhs_2


-- plus : (x : NNat) -> (y : NNat) -> NNat
-- plus Z y = normalise y
-- plus (S x) y = normalise $ S (plus x y)
-- plus (N x) y = normalise $ N (plus x y)

-- test1 : normalise (S (S (N (S (S (N (N Z))))))) = S Z
-- test1 = Refl

-- plusZeroLeftNeutral : (right : NNat) -> (Z `plus` right) = right
-- plusZeroLeftNeutral Z = Refl
-- plusZeroLeftNeutral (S x) = ?hsdfsd_1
-- plusZeroLeftNeutral (N x) = ?hsdfsd_2

-- plusZeroRightNeutral : (left : NNat) -> normalise (left `plus` Z) = normalise left
-- plusZeroRightNeutral Z = Refl
-- plusZeroRightNeutral (S x) =

-- ?plusZeroRightNeutral_rhs_1
-- plusZeroRightNeutral (N x) = ?plusZeroRightNeutral_rhs_2
