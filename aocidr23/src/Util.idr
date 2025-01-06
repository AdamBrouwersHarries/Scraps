module Util
import Control.Monad.Error.Either
import System.File

public export
data Err =
    FailedToLoadFile String |
    TestFailed String String |
    FailedToParseLineD1 String String

public export
AOC : Type -> Type
AOC t = EitherT Err IO t

public export
loadFile : String -> AOC String
loadFile f = do
    contents <- readFile f
    case contents of
        Right c => right c
        Left _ => throwE $ FailedToLoadFile f

public export
test : (Eq t, Show u) => (name: String) -> (u -> t) -> (input : u) -> (gold : t) -> AOC ()
test name f input gold = do
    let v = f input
    if v == gold then
        pure ()
        else
        throwE $ TestFailed name (show input)

handler : Err -> AOC ()
handler (FailedToLoadFile str) = putStrLn $ "Failed to load file " ++ str
handler (TestFailed name input) = putStrLn $ "Test failed " ++ name ++ " with input " ++ input
handler (FailedToParseLineD1 input parseres) = putStrLn $ "Failed to parse line " ++ input ++ " into " ++ parseres

public export
runDay : AOC () -> IO ()
runDay f = do
    _ <- runEitherT $ catchE f handler
    pure ()