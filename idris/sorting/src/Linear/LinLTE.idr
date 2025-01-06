module Linear.LinLTE
-- LTE and associated proofs for Linear Natural numbers.
import Extensions.LNat

import Control.Relation
import Control.Order

import Data.Linear.Interface
import Data.Linear.Notation
import Data.Linear.LNat
import Data.Linear.LVect

import Data.Singleton


%default total


-- LTE etc copied from the Nat implementation
public export
data LTE  : (1 n : LNat) -> (1 m : LNat) -> Type where
  LTEZero : LTE Zero    right
  LTESucc : LTE left right -> LTE (Succ left) (Succ right)

public export
GTE : LNat -@ LNat -@ Type
GTE left right = LTE right left

public export
LT : LNat -@ LNat -@ Type
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
GT : LNat -@ LNat -@ Type
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
isLTEBool : (1 m : LNat) -> (1 n : LNat) -> Bool
isLTEBool m n = case isLTE m n of
                     (Yes prf) => True
                     (No contra) => False

public export
isLT : (1 m : LNat) -> (1 n : LNat) -> Dec (LT m n)
isLT m n = isLTE (Succ m) n

public export
isGT :  (1 m : LNat) -> (1 n : LNat) -> Dec (GT m n)
isGT m n = isLT n m


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

infix 1 ##

-- Dependent pair of linear and linear
public export
record DPairLL (t : Type) (f : t -> Type) where
  constructor (##)
  1 fst : t
  1 snd : f fst

public export
isLinLTE : (1 m : LNat) -> (1 n : LNat) -> DPairLL LNat (\x => DPairLL LNat (\y => Dec $ LTE x y))
isLinLTE Zero n = Zero ## (n ## Yes LTEZero)
isLinLTE (Succ x) Zero = (Succ x) ## (Zero ## No succNotLTEzero)
isLinLTE (Succ x) (Succ z) = case isLinLTE x z of
                                  (x ## (y ## (Yes prf))) => (Succ x ## (Succ y ## Yes (LTESucc prf)))
                                  (x ## (y ## (No contra))) => (Succ x ## (Succ y ## No (contra . fromLteSucc)))
