module Linear.LTE
-- LTE and associated proofs for Linear Natural numbers.
import Extensions.LNat

import Control.Relation
import Control.Order

import Data.Linear.Interface
import Data.Linear.Notation
import Data.Linear.LNat

%default total

public export
data LTE  : (1 n : LNat) -> (1 m : LNat) -> Type where
  LTEZero : LTE Zero    right
  LTESucc : LTE left right -> LTE (Succ left) (Succ right)

public export
GTE : LNat -> LNat -> Type
GTE left right = LTE right left

public export
LT : LNat -> LNat -> Type
LT left right = LTE (Succ left) right

namespace LT

  ||| LT is defined in terms of LTE which makes it annoying to use.
  ||| This convenient view of allows us to avoid having to constantly
  ||| perform nested matches to obtain another LT subproof instead of
  ||| an LTE one.
  public export
  data View : LT m n -> Type where
    LTZero : View (LTESucc LTEZero)
    LTSucc : (lt : m `LT` n) -> View (LTESucc lt)

  ||| Deconstruct an LT proof into either a base case or a further *LT*
  export
  view : (lt : LT m n) -> View lt
  view (LTESucc LTEZero) = LTZero
  view (LTESucc lt@(LTESucc _)) = LTSucc lt

  ||| A convenient alias for trivial LT proofs
  export
  ltZero : Zero `LT` Succ m
  ltZero = LTESucc LTEZero

public export
GT : LNat -> LNat -> Type
GT left right = LT right left

export
succNotLTEzero : Not (LTE (Succ m) Zero)
succNotLTEzero LTEZero impossible

export
fromLteSucc : LTE (Succ m) (Succ n) -> LTE m n
fromLteSucc (LTESucc x) = x

export
succNotLTEpred : {x : LNat} -> Not $ LTE (Succ x) x
succNotLTEpred {x =   Zero} prf = succNotLTEzero prf
succNotLTEpred {x = Succ _} prf = succNotLTEpred $ fromLteSucc prf

public export
isLTE : (1 m : LNat) -> (1 n : LNat) -> Dec (LTE m n)
isLTE Zero n = consume n `seq` Yes LTEZero
isLTE (Succ k) Zero = consume k `seq` No succNotLTEzero
isLTE (Succ k) (Succ j)
    = case isLTE k j of
           No contra => No (contra . fromLteSucc)
           Yes prf => Yes (LTESucc prf)

public export
isGTE : (m, n : LNat) -> Dec (GTE m n)
isGTE m n = isLTE n m

public export
isLT : (m, n : LNat) -> Dec (LT m n)
isLT m n = isLTE (Succ m) n

public export
isGT : (m, n : LNat) -> Dec (GT m n)
isGT m n = isLT n m

lteRecallLeft : LTE m n -> (m' : LNat ** m = m')
lteRecallLeft LTEZero = (Zero ** Refl)
lteRecallLeft (LTESucc x) with (lteRecallLeft x)
  lteRecallLeft (LTESucc x) | (left ** Refl) = (Succ left ** Refl)

irrelevantLte : {m : LNat} -> (0 prf : LTE m n) -> LTE m n
irrelevantLte {m = Zero} LTEZero = LTEZero
irrelevantLte {m = (Succ k)} (LTESucc x) = LTESucc (irrelevantLte x)

lteRecall : LTE m n -> {p : LNat -> LNat} -> (0 prf : LTE (p m) q) -> LTE (p m) q
lteRecall {m} x prf with (lteRecallLeft x)
  lteRecall {m = m} x prf | (m ** Refl) = irrelevantLte prf

ltRecall : LT m n -> {p : LNat -> LNat} -> (0 prf : LT (p m) q) -> LT (p m) q
ltRecall {m} x prf with (lteRecallLeft x)
  ltRecall {m = m} x prf | (Succ m ** Refl) = irrelevantLte prf

export
lteSuccRight : LTE n m -> LTE n (Succ m)
lteSuccRight LTEZero     = LTEZero
lteSuccRight (LTESucc x) = LTESucc (lteSuccRight x)

export
lteSuccLeft : LTE (Succ n) m -> LTE n m
lteSuccLeft (LTESucc x) = lteSuccRight x

export
lteAddRight : (n : LNat) -> LTE n (n + m)
lteAddRight Zero = LTEZero
lteAddRight (Succ k) {m} = LTESucc (lteAddRight {m} k)

export
notLTEImpliesGT : {a, b : LNat} -> Not (a `LTE` b) -> a `GT` b
notLTEImpliesGT {a = Zero  }           not_z_lte_b    = absurd $ not_z_lte_b LTEZero
notLTEImpliesGT {a = Succ a} {b = Zero  } notLTE = LTESucc LTEZero
notLTEImpliesGT {a = Succ a} {b = Succ k} notLTE = LTESucc (notLTEImpliesGT (notLTE . LTESucc))

-- export
-- LTEImpliesNotGT : a `LTE` b -> Not (a `GT` b)
-- LTEImpliesNotGT LTEZero q = absurd q
-- LTEImpliesNotGT (LTESucc p) (LTESucc q) = LTEImpliesNotGT p q

-- export
-- notLTImpliesGTE : {a, b : _} -> Not (LT a b) -> GTE a b
-- notLTImpliesGTE notLT = fromLteSucc $ notLTEImpliesGT notLT

-- export
-- LTImpliesNotGTE : a `LT` b -> Not (a `GTE` b)
-- LTImpliesNotGTE p q = LTEImpliesNotGT q p

public export
lte : LNat -> LNat -> Bool
lte Zero        right     = True
lte left     Zero         = False
lte (Succ left) (Succ right) = lte left right

public export
gte : LNat -> LNat -> Bool
gte left right = lte right left

public export
lt : LNat -> LNat -> Bool
lt left right = lte (Succ left) right

public export
gt : LNat -> LNat -> Bool
gt left right = lt right left

export
lteReflectsLTE : (k : LNat) -> (n : LNat) -> lte k n === True -> k `LTE` n
lteReflectsLTE (Succ k)  0    _ impossible
lteReflectsLTE 0      0    _   = LTEZero
lteReflectsLTE 0     (Succ k) _   = LTEZero
lteReflectsLTE (Succ k) (Succ j) prf = LTESucc (lteReflectsLTE k j prf)

export
gteReflectsGTE : (k : LNat) -> (n : LNat) -> gte k n === True -> k `GTE` n
gteReflectsGTE k n prf = lteReflectsLTE n k prf

export
ltReflectsLT : (k : LNat) -> (n : LNat) -> lt k n === True -> k `LT` n
ltReflectsLT k n prf = lteReflectsLTE (Succ k) n prf

-- public export
-- ltOpReflectsLT : (m,n : LNat) -> So (m < n) -> LT m n
-- ltOpReflectsLT 0     (Succ k) prf = LTESucc LTEZero
-- ltOpReflectsLT (Succ k) (Succ j) prf = LTESucc (ltOpReflectsLT k j prf)
-- ltOpReflectsLT (Succ k) 0     prf impossible
-- ltOpReflectsLT 0 0         prf impossible

export
gtReflectsGT : (k : LNat) -> (n : LNat) -> gt k n === True -> k `GT` n
gtReflectsGT k n prf = ltReflectsLT n k prf