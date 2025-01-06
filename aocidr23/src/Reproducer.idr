module Reproducer
import Data.String.Parser

-- %default total

%inline
myName : Applicative m => ParseT m String
myName = (string "myName") <?> "The text did not contain myName!"

multipleNames : Monad m => Applicative m => Alternative (ParseT m) => ParseT m (List String)
multipleNames = some (string "myName")

test = parse (some $ string ("myName")) "myMame"

main : IO ()
main = do
    putStrLn "This is the main function"
    names <- parseT (some (string "myName")) "myNamemyNamemyName"
    putStrLn "Found names:"
    putStrLn (show names)