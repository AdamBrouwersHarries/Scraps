import Data.Nat

-- lemma:  {0 n, r, x, b : Nat} -> (0 _ : LTE x n) -> (0 _ : n + r = b) -> ((n `minus` x) + (r + x) = b)
--   lemma1 ltenx invariant =
--     let foo = cong (+ x) invariant -- add x to both sides???
--     in ?help

lemma : {n, r, x, b : Nat} -> (LTE x n) -> (n + r = b) -> ((n `minus` x) + (r + x)) = b
lemma {x = 0} y prf = rewrite minusZeroRight n in
                      rewrite plusZeroRightNeutral r in prf
lemma {x = (S k)} y prf = let rec = lemma {x = k} (lteSuccLeft y) prf in
    ?lemma_rhs_1