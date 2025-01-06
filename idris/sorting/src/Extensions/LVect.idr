module Extensions.LVect

import Data.Linear.Notation
import Data.Linear.LVect

printRest : (Show a) => LVect n a -> String
printRest [] = "]"
printRest (x :: xs) = "," ++ (show x) ++ (printRest xs)

printLVect : (Show a) => LVect n a -> String
printLVect [] = "[]"
printLVect (x :: xs) = "[" ++ (show x) ++ printRest xs where


Show a => Show (LVect n a) where
    show lv = printLVect lv

