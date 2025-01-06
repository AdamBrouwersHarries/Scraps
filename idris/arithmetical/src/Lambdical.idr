module Lambdical

Id : Type
Id = String

data Term : Type where
    Var : Id -> Term
    Abs : Id -> Term -> Term
    App : Term -> Term -> Term
    Zero : Term
    Successor : Term -> Term
    Case : Term -> Term -> Id -> Term -> Term
    Fixpoint : Id -> Term -> Term

infix 5 `Abs`
infix 5 `Fixpoint`
infixl 7 `App`
infix 8 `Successor`
infix 9 `Var`

two : Term
two = Successor (Successor Zero)

plus : Term
plus = Fixpoint "+"
    (Abs "m"
        (Abs "n" (Case
                (Var "m")
                (Var "n")
                "m"
                (Successor ((Var "+" ) `App` (Var "m") `App` (Var "n"))))))

