{-# LANGUAGE FlexibleContexts #-}

import System.Directory
import System.FilePath
import System.IO

import Control.Monad
import Control.Arrow (second)

import Text.ParserCombinators.Parsec

import Data.List
import Data.Either

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

data Mode = Naive | Medium | Smart
  deriving (Eq, Ord, Show)

smode "naive"  = Naive
smode "medium" = Medium
smode "smart"  = Smart


data TestData = MkData { mode      :: !Mode
                       , mutant    :: !Int
                       , successes :: !Int
                       , discards  :: !Int
                       , failures  :: !Int
                       , time      :: !Double
                       , total     :: !Int
                       } deriving (Eq, Ord, Show)

fileNameP :: GenParser Char st (Mode, Int)
fileNameP = do
  string "rand_SSNI_"
  m <- smode <$> (string "naive" <|> string "medium" <|> string "smart")
  char '_'
  xs <- many1 digit
  let x = read xs :: Int
  return (m, x)

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

right (Right x) = x

parseOutput :: String -> String -> TestData
parseOutput fn contents =
  -- Drop three first lines
  let _ : _ : _ : rest = lines contents
  -- Parse the next three lines for data (always at least 3)
      (s,d,f) = stats fn (take 3 rest) (0,0,0)
      (_ : timeLine : _) = reverse rest
      (m,id) = right $ parse fileNameP fn fn
      t = right $ parse timeP fn timeLine
  in MkData m id s d f t 1000000

main = do
  -- Get all files in the current dir
  allFiles <- getDirectoryContents "."
  -- Filter the ones that are output files (.out)
  let outputs = filter ((== ".out") . takeExtension) allFiles
  -- Iterate through each file
  parsedData <- forM outputs $ \f -> do
    handle   <- openFile f ReadMode
    contents <- hGetContents handle
    return (parseOutput f contents)
  let sorted = sort parsedData
  let (naive,(medium,smart)) = second (splitAt 20) (splitAt 20 sorted)
  putStrLn $ show (naive, medium, smart)
