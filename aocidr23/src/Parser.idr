module Parser
import Data.String.Parser

-- %default total

adam : Applicative m => ParseT m String
adam = (string "adam") <?> "The text did not contain adam!"

adamOrBecca : (Applicative m, Alternative (ParseT m)) => ParseT m String
adamOrBecca = ((string "adam") <|> (string "becca")) <?> "The text did not contain adam or becca!"

names = ["adam","becca","emmy"]

anyName : Applicative m => Alternative (ParseT m) => ParseT m String
anyName = (choiceMap string names) <?> "The text did not contain any of the names in the list"

multipleNames : Monad m => Applicative m => Alternative (ParseT m) => ParseT m (List String)
multipleNames = (some (string "adam"))

test = parse adam "adamadamadam"
test2 = parse adamOrBecca "becca"
test3 = parse adamOrBecca "adam"
test4 = parse adamOrBecca "emmy"

test5 = parse anyName "adam"

test6 = parse anyName "becca"

test7 = parse anyName "emmy"

test8 = parse anyName "john"

test9 = parse multipleNames "ad"



test19 : IO ()
test19 = do
    putStrLn "Running part one"
    res <- parseT multipleNames "ad"
    putStrLn $ (show res)