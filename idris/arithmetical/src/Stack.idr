-- %default total

data Tye = V Type | F (List Tye) Tye

Sig : Type
Sig = List Tye

data Stack : Sig -> Type where
    Bot : Stack []                   -- The bottom of the stack is an empty list of discriminants

    PushVal : {t : Type} -> (a : t)  -- Push a value of type t
              -> (Stack d)           -- Onto a stack containing d other values
              -> Stack ((V t) :: d)  -- Resulting in a stack with a value on top.

    PushFn : {ty : Sig} -> {r : Tye} -- Given a type signature, of ty input, and r output, push a function
            -> (fn : {other : Sig} ->    -- That takes an implicit stack `other`
                  Stack (ty ++ other)    -- and transforms `ty` values at the `other` stack into
                -> Stack (r :: other)    -- a value `r`, which it then pushes to the top of stack `other`
                )
            -> (Stack ds)                -- And a stack of ds other values
            -> Stack ((F ty r) :: ds)    -- Resulting in a stack with a function on top of a stack of other values.



-- Helper method for push
pushVal : {t : Type} -> (a : t) -> Stack d -> Stack ((V t) :: d)
pushVal x y = PushVal x y

-- Helper method for push
pushFn : {ty : Sig} -> {r : Tye} -> ({d : Sig} -> Stack (ty ++ d) -> Stack (r :: d)) -> Stack ds -> Stack ((F ty r) :: ds)
pushFn f = PushFn f

-- Call a function at the top of the stack
-- `Rest` is the set of values in the stack that are not involved with the function call
call : {rest :Sig}
    -- Require that our stack has a function at the top, followed by discriminants the same as the signature input.
    -> Stack ((F f r) :: (f ++ rest))
    -- Our output is a new stack, with the result at the top.
    -> (Stack (r :: rest))
call (PushFn g y) = g y

-- Given a stack with two `Nat` numbers at the top, produce a stack with one `Nat` at the top
add : Stack (([V Nat, V Nat]) ++ other) -> Stack (V Nat :: other)
add (PushVal x (PushVal y st)) = PushVal (x + y) st
add (PushVal x z) = case z of (PushVal y st) => PushVal (x + y) st

BinFn : Type
BinFn = {other : Sig} -> Stack (([V Nat, V Nat]) ++ other) -> Stack (V Nat :: other)

pushBinFn : BinFn -> (Stack ds) -> Stack ((F [V Nat, V Nat] (V Nat)) :: ds)
pushBinFn f st = pushFn f {ty = [V Nat, V Nat]} st

simpleStack = call (pushFn add {ty = [V Nat, V Nat]} $ pushVal 1 $ pushVal 1 Bot)

cmplxStack = pushBinFn add $ pushBinFn add $ pushVal 1 $ pushVal 1 $ pushVal 2 Bot
