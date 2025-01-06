module Day1
import Util
import System.File
import Data.String
import Control.Monad.Error.Either

-- For now, just use single characters
data ParsedPair : a -> Type where
    Neither : ParsedPair a
    First : a -> ParsedPair a
    Both : a -> a -> ParsedPair a

(Eq a) => Eq (ParsedPair a) where
    Neither == Neither = True
    (First i) == (First j) = i == j
    (Both i j) == (Both i' j') = (i == i') && (j == j')
    _ == _ = False

(Show a) => Show (ParsedPair a) where
    show Neither = "Neither"
    show (First i) = "First " ++ (show i)
    show (Both i j) = "Both " ++ (show i) ++ ", " ++ (show j)

push : a -> ParsedPair a -> ParsedPair a
push i Neither = First i
push j (First i) = Both i j
push j' (Both i j) = Both i j'



total
parsePair : String -> ParsedPair Int
parsePair str = foldl matchPush Neither (unpack str) where
    matchPush : ParsedPair Int -> Char -> ParsedPair Int
    matchPush pi c = case isDigit c of
        False => pi
        True => case parsePositive {a = Int} $ singleton c of
            Just i => push i pi
            Nothing => pi

total
testParsePair : AOC ()
testParsePair = let t = test "parsePair" parsePair in
    do
        t "abc1cdfg5fd" (Both 1 5)
        t "14sdfgsdfglaf" (Both 1 4)
        t "safgsdfgsdfkgjh" (Neither)
        t "1345643574567456" (Both 1 6)
        t "asdfadsfkljh1sdfgsdfg" (First 1)

parseLine : String -> AOC Int
parseLine str = do
    let pair = parsePair str
    case pair of
        (Both x y) => pure $ (x * 10) + y
        (First i) => pure $ (i * 10) + i
        fail => throwE $ FailedToParseLineD1 str (show fail)

parseFile : String -> AOC Int
parseFile contents = let ls = lines contents in
    foldlM (\acc, line => (parseLine line) <&> (+ acc)) 0 ls

public export day1 : AOC ()
day1 = do
    -- run some tests first
    putStrLn "running tests"
    testParsePair
    -- load the data
    dat <- loadFile "data/day1.txt"
    i <- parseFile dat
    putStrLn $ "Got value: " ++ (show i)
    putStrLn "successfully run"
    pure ()
