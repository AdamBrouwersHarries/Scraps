module Arithmetical
import Data.Vect

%default total

succCong : (prf : k = j) -> (S k) = (S j)
succCong Refl = Refl

plu : Nat -> Nat -> Nat
plu Z m = m
plu (S k) m = S (plu k m)

four_eq : 4 = 4
four_eq = Refl

twoplutwo_eq_four : 2 + 2 = 4
twoplutwo_eq_four = Refl

plu_reduces_Z : (m : Nat) -> plu Z m = m
plu_reduces_Z m = Refl

plu_reduces_Sk : (k, m : Nat) -> plu (S k) m = S (plu k m)
plu_reduces_Sk k m = Refl

vect_eq_length : (xs : Vect n a) -> (ys : Vect m a) -> (xs = ys) -> n = m
vect_eq_length xs xs Refl = Refl

plu_commutes_Z : (m : Nat) -> m = plu m 0
plu_commutes_Z {m = 0} = Refl
plu_commutes_Z {m = (S k)} = let rec = plu_commutes_Z {m=k} in
    rewrite sym rec in Refl

pcZ : (m : Nat) -> m = plu m 0
pcZ 0 = Refl
pcZ (S k) = succCong (pcZ k)


plu_commutes_S : (k : Nat) -> (m : Nat) -> S (plu m k) = plu m (S k)
plu_commutes_S k 0 = Refl
plu_commutes_S k (S j) = rewrite plu_commutes_S k j in Refl

pcS : (k : Nat) -> (m : Nat) -> S (plu m k) = plu m (S k)
pcS k 0 = Refl
pcS k (S j) = succCong (pcS k j)


total
plu_commutes : (n, m : Nat) -> plu n m = plu m n
plu_commutes 0 m = plu_commutes_Z m
plu_commutes (S k) m = rewrite plu_commutes k m in plu_commutes_S k m

pluc : (n, m : Nat) -> plu n m = plu m n
pluc 0 m = pcZ m
pluc (S k) m = rewrite pluc k m in pcS k m


plu_assoc : (n, m, p : Nat) -> plu n (plu m p) = plu (plu n m) p
plu_assoc 0 m p = Refl
plu_assoc (S k) m p = rewrite plu_assoc k m p in Refl

pluReducesR : (n: Nat) -> plu n Z = n
pluReducesR 0 = Refl
pluReducesR (S k) = rewrite pluReducesR k in Refl

plurR : (n: Nat) -> plu n Z = n
plurR 0 = Refl
plurR (S k) =  succCong $ plurR k


plurR2 : (n: Nat) -> plu n Z = n
plurR2 0 = Refl
plurR2 (S k) = succCong $ plurR2 k


---

my_nat_ind : (P : Nat -> Type) -> -- Property on natural numbers
             (P Z) ->             -- Property on zero, i.e. base case
             ((k : Nat) -> P k -> P (S k)) -> -- Induction principle
             (x : Nat) ->         -- For all x
             P x
my_nat_ind p p_Z f 0 = p_Z
my_nat_ind p p_Z f (S k) = f k (my_nat_ind p p_Z f k)

inductive_plus : Nat -> Nat -> Nat
inductive_plus n m
    = my_nat_ind (\x => Nat)
                 m
                 (\k, k_rec => S k_rec)
                 n

--- exercises from learn-idris.net

total zero_plus : (n : Nat) -> n + 0 = n
zero_plus 0 = Refl
zero_plus (S k) = rewrite zero_plus k in Refl

total plus_assoc : (a, b, c : Nat) -> (a + b) + c = a + (b + c)
plus_assoc 0 b c = Refl
plus_assoc (S k) b c = rewrite plus_assoc k b c in Refl


plus_comm_RHS : (right : Nat) -> right = plus right 0
plus_comm_RHS 0 = Refl
plus_comm_RHS (S k) = let rec = plus_comm_RHS {right = k} in
    rewrite sym rec in Refl

pcrr2 : (right : Nat) -> S right = plus right 1
pcrr2 0 = Refl
pcrr2 (S k) = rewrite pcrr2 k in Refl

jobbie : (k : Nat) -> (right : Nat) -> S (plus right (S k)) = plus right (S (S k))
jobbie k 0 = Refl
jobbie k (S j) = rewrite jobbie k j in Refl

plus_comm_RHS2 : (k : Nat) -> (right : Nat) -> S (plus k right) = plus right (S k)
plus_comm_RHS2 0 right = pcrr2 right
plus_comm_RHS2 (S k) right = rewrite plus_comm_RHS2 k right in jobbie k right


total plus_comm : (left : Nat) -> (right : Nat) -> left + right = right + left
plus_comm 0 right = plus_comm_RHS right
plus_comm (S k) right = plus_comm_RHS2 k right