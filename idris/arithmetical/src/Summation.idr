import Decidable.Equality
import Data.Fin
import Data.Vect

%default total



-- Proof of the fact that list contains an element
-- data Contains : a -> List a -> Type where
--   Here : (x : a) -> (xs : List a) -> Contains x (x :: xs)
--   There : (x : a) -> Contains y xs -> Contains y (x :: xs)

fin_implies_lte : (n : Nat) -> (f : Fin n) -> LTE (finToNat f) n
fin_implies_lte (S k) FZ = LTEZero
fin_implies_lte (S k) (FS x) = LTESucc (fin_implies_lte k x)

weaken_pair : (n ** Fin n) -> (LTE n m) -> (m ** Fin m)
weaken_pair ((fst ** snd)) LTEZero = (fst ** snd)
weaken_pair p (LTESucc x) = weaken_pair p x

data SRange : (upper : Nat) -> (lower : Fin upper) -> Type where
    MkSRange : (upper : Nat) -> (lower : Fin upper) -> SRange upper lower


extend_sigma : SRange u l -> (u' : Nat) -> (p: LTE u u') -> SRange u' (weakenLTE l p)
extend_sigma (MkSRange u l) u' p = MkSRange u' (weakenLTE l p)

bounded_implies_LTE : {m : Nat} -> (f : Fin m) -> (n : Nat) -> (n = finToNat f) -> LTE n m
bounded_implies_LTE FZ 0 prf = LTEZero
bounded_implies_LTE f (S k) prf = rewrite prf in (fin_implies_lte m f)

abuttments_concatenate : (lower : SRange ltop lbot) ->    -- A lower range
    (upper : SRange utop ubot) ->                      -- an "upper" range
    (prf: (ltop = finToNat ubot)) ->                   -- a proof that the top of the "lower" range touches the bottom of the "upper" range
    SRange utop (weakenLTE lbot (bounded_implies_LTE ubot ltop prf)) -- A range that goes from lower bottom to upper top
abuttments_concatenate (MkSRange ltop lbot) (MkSRange utop ubot) prf = extend_sigma (MkSRange ltop lbot) utop (bounded_implies_LTE ubot ltop prf)

data PSRange : (lower : Nat) -> (upper : Nat) -> (LTE lower upper) -> Type where
    MkPSRange : (lower : Nat) -> (upper : Nat) -> (prf: LTE lower upper) -> PSRange lower upper prf

psrange_concat : (low: Nat) -> (mid: Nat) -> (hi: Nat) -> (lprf : LTE low mid) -> (rprf : LTE mid hi) -> (lhs : PSRange low mid lprf) -> (rhs: PSRange mid hi rprf) -> PSRange low hi (transitive lprf rprf)
psrange_concat low mid hi lprf rprf lhs rhs = MkPSRange low hi (transitive lprf rprf)

psrange_concat2 : {low: Nat} -> {mid: Nat} -> {hi: Nat} -> {lprf : LTE low mid} -> {rprf : LTE mid hi} -> (lhs : PSRange low mid lprf) -> (rhs: PSRange mid hi rprf) -> PSRange low hi (transitive lprf rprf)
psrange_concat2 lhs rhs = MkPSRange low hi (transitive lprf rprf)

eval_psrange : (r : PSRange low high lprf) -> Vect (high `minus` low) Nat
eval_psrange (MkPSRange low high lprf) = count_up_with low (high `minus` low) where
    count_up_with : (counter : Nat) -> (n : Nat) -> Vect n Nat
    count_up_with counter 0 = Nil
    count_up_with counter (S k) = counter :: (count_up_with (S counter) k)


succ_plus : (k : Nat) -> (high : Nat) -> S (plus k (minus high (S k))) = minus high 0
succ_plus 0 high = ?succ_plus_rhs_0
succ_plus (S k) high = ?succ_plus_rhs_1

succCong : (prf : k = j) -> (S k) = (S j)
succCong Refl = Refl

n_succ : (n : Nat) -> (p : GT 0 n) -> n = S (minus n 1)
n_succ 0 LTEZero impossible
n_succ 0 (LTESucc x) impossible
n_succ (S 0) p = Refl
n_succ (S k) p = rewrite minusZeroRight k in Refl



both_succ : (n : Nat) -> (k: Nat) -> (p : LTE (S k) n) -> (minus (S n) k = S (minus n k)) -> (minus n k = S (minus n (S k)))
-- both_succ (S right) 0 (LTESucc x) prf = rewrite minusZeroRight right in Refl
-- both_succ (S right) (S k) (LTESucc x) prf = both_succ right k x prf


minus_succ_right : (n : Nat) -> (k : Nat) -> (p : LTE k n) -> minus (S n) k = S (minus (S n) (S k))
minus_succ_right n 0 p = rewrite minusZeroRight n in Refl
minus_succ_right n (S k) p = both_succ n k p $ minus_succ_right n k (lteSuccLeft p)


minus_succ_left : (n : Nat) -> (k : Nat) -> (p : LTE k (S n)) -> minus (S n) k = S (minus n k)
minus_succ_left n 0 p = rewrite minusZeroRight n in Refl
minus_succ_left n (S k) p = let rec = minus_succ_left n k (lteSuccLeft p) in ?holesome

minus_plus_other : (m : Nat) -> (k : Nat) -> (o: Nat) -> plus (minus m k) o = minus (m `plus` o) k
minus_plus_other m k 0 = rewrite plusZeroRightNeutral (minus m k) in
    rewrite plusZeroRightNeutral m in Refl
minus_plus_other m k (S j) = let rec = minus_plus_other m k j in
    rewrite sym $ plusSuccRightSucc (minus m k) j in
    rewrite sym $ plusSuccRightSucc m j in ?holeasd

-- plus_succ_right : (m : Nat) -> (n : Nat) -> plus m (S n) = S (plus m n)


rearrange : (m : Nat) -> (n : Nat) -> (l : Nat) -> (h : Nat) -> (p1: LTE m l) -> (p2 : LTE h n) -> (p3 : LTE m n) -> (p4 : LTE h l) -> (m `minus` l) `plus` (h `minus` n) = (m `minus` n) `plus` (h `minus` l)
rearrange m 0 0 h p1 p2 p3 p4 = Refl
rearrange m 0 (S k) h p1 p2 p3 p4 = rewrite minusZeroRight h in
    rewrite minusZeroRight m in ?rearrange_rhs_3
rearrange m (S k) l h p1 p2 p3 p4 = ?rearrange_rhs_1



-- (m - l) + (h - m) = (h - l)
eliminate_middle : (low : Nat) -> (mid : Nat) -> (high : Nat) -> (lp : LTE low mid) -> (rp : LTE mid high) -> plus (minus mid low) (minus high mid) = minus high low
eliminate_middle 0 mid high lp rp = rewrite minusZeroRight mid in
    rewrite minusZeroRight high in
    rewrite plusCommutative mid (minus high mid) in
    rewrite plusMinusLte mid high rp in Refl
eliminate_middle (S k) mid high lp rp = let rec = eliminate_middle k mid high (lteSuccLeft lp) rp in ?hsadfd


-- concat_errr : {low : Nat} -> {mid: Nat} -> {high : Nat} -> {lp : LTE low mid} -> {rp : LTE mid high} -> (l : PSRange low mid lp) -> (r : PSRange mid high rp) -> (eval_psrange l ++ eval_psrange r) = (eval_psrange (psrange_concat2 l r))





-- abuttments_concatenate (MkSRange 0 lbot) (MkSRange utop ubot) prf = MkSRange utop (weakenLTE lbot (bounded_implies_LTE ubot 0 prf))
-- -- abuttments_concatenate (MkSRange (S lk) lbot) (MkSRange (S uk) FZ) prf =
-- abuttments_concatenate (MkSRange (S lk) lbot) (MkSRange (S uk) (FS x)) prf = MkSRange (S uk) (weakenLTE lbot (LTESucc (fin_implies_lte uk x)))

-- data SumRange :


-- data SumRange : (a : Nat ** Fin a) -> Type where
--     SRange : (upper : Nat) -> (lower : Fin upper) -> SumRange (upper ** lower)




-- extend_fin : (n : Nat) -> (m : Nat) -> (p : LTE n m) -> (Fin n) -> (Fin m)
-- extend_fin 0 0 p x = x
-- extend_fin 0 (S k) p x = FZ
-- extend_fin (S k) m p FZ = ?holers
-- extend_fin (S k) m p (FS x) = ?holesom_1



-- merge_pairs : (lUpper : Nat) -> (lLower : Fin lUpper) -> (lUpper ** Fin n) -> (m ** (lower: Fin m)) -> (LTE n m) -> (n = (finToNat lower)) -> (m ** Fin m)




-- concat_range :
--     (upperL = (finToNat lowerU)) ->                -- A proof that the ranges match, i.e. that they abutt
--     (lower_range : SumRange (upperL ** lowerL)) -> (upper_range : SumRange (upperU ** lowerU)) -> SumRange (newUpper ** (newLower))
-- concat_range prf (SRange upperL lowerL) (SRange upperU lowerU) = ?concat_range_rhs_1



-- IndexTy : Type
-- IndexTy = Nat

-- ValueTy : Type
-- ValueTy = Double

-- data Summation : IndexTy -> IndexTy -> (IndexTy -> ValueTy) -> Type where
--     Sum : (lower: IndexTy) -> (upper: IndexTy) -> (lower < upper) -> (fn : (IndexTy -> ValueTy)) -> Summation lower upper fn

-- eval : (Summation l u fn) -> ValueTy
-- eval s = eval_acc s 0 where
--     eval_acc : (Summation l' u' p' fn') -> (acc : ValueTy) -> ValueTy
--     eval_acc (Sum l' u' p' fn') acc = case ( l' == u') of
--                                     False => eval_acc (Sum (S l') u' fn') (acc + (fn' l'))
--                                     True => acc

-- seq_is_equal : (l1 : IndexTy) -> (u1 : IndexTy) -> (u2 : IndexTy) -> (fn : (IndexTy->ValueTy)) ->
--     (s1 : Summation l1 u1 fn) -> (s2 : Summation u1 u2 fn) ->
--     (c1 : Summation l1 u2 fn) ->
--     ((eval s1) + (eval s2)) = (eval c1)
-- seq_is_equal 0 u1 u2 fn s1 s2 c1 = ?seq_is_equal_rhs_0
-- seq_is_equal (S k) u1 u2 fn s1 s2 c1 = ?seq_is_equal_rhs_1
