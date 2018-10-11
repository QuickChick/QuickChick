{-# LANGUAGE FlexibleContexts #-}

import System.Directory
import System.FilePath
import System.IO

import Control.Monad

import Text.ParserCombinators.Parsec

import Debug.Trace

{-- File structure

 QuickChecking ...
 Extracted ML file ...
 Compile command ...
 success (maybe)
 discard (maybe)
 fail (maybe)
 +++ Passed
 time
 inputs/outputs

-}

data TestData = MkData { successes :: !Int
                       , discards  :: !Int
                       , failures  :: !Int
                       , time      :: !Double
                       , total     :: !Int
                       } deriving (Eq, Ord, Show)

numberP :: GenParser Char st (String, Int)
numberP = do
  x <- read <$> many1 digit
  spaces
  char ':'
  spaces
  s <- string "true" <|> string "\"()\"" <|> string "false"
  return (s,x)

timeP :: GenParser Char st Double
timeP = do
  s <- many1 (noneOf "u")
  return $ read s

updateTriple :: (Int,Int,Int) -> String -> Int -> (Int, Int, Int)
updateTriple (s,d,f) "true"   x = (x,d,f)
updateTriple (s,d,f) "\"()\"" x = (s,x,f)
updateTriple (s,d,f) "false"  x = (s,d,x)

stats :: String -> [String] -> (Int, Int, Int) -> (Int, Int, Int)
stats fn [] acc = acc
stats fn (l : ls) acc = 
  case parse numberP fn l of
    Right (s,x) -> stats fn ls (updateTriple acc s x)
    Left  _     -> acc

parseOutput :: String -> String -> TestData
parseOutput fn contents =
  -- Drop three first lines
  let _ : _ : _ : rest = lines contents
  -- Parse the next three lines for data (always at least 3)
      (s,d,f) = stats fn (take 3 rest) (0,0,0)
      (_ : timeLine : _) = reverse rest
  in case parse timeP fn timeLine of
       Right t -> MkData s d f t 1000000
       Left  _ -> error "Parse failed"

main = do
  -- Get all files in the current dir
  allFiles <- getDirectoryContents "."
  -- Filter the ones that are output files (.out)
  let outputs = filter ((== ".out") . takeExtension) allFiles
  -- Iterate through each file
  forM_ outputs $ \f -> do
    handle   <- openFile f ReadMode
    contents <- hGetContents handle
    putStrLn $ f ++ ":\n" ++ show (parseOutput f contents)
  putStrLn $ show outputs
