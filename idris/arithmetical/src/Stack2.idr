-- data Discrim = V | F (Nat -> Nat) | B

-- data Stack : Discrim -> Nat -> Type where
--     Bot : Stack B 0
--     PushVal : a -> (Stack d n) -> Stack V (S n)
--     PushFn : (f : Nat -> Nat) -> (Stack d n -> (e: Discrim ** Stack e (f n))) -> (Stack d n) -> Stack (F f) (S n)

mutual
    data RecStack : (a : Type) -> Nat -> Type where
        Bot : RecStack
