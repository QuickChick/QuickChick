{-# LANGUAGE FlexibleContexts #-}

import System.Directory
import System.FilePath
import System.IO

import Control.Monad
import Control.Arrow (second)

import Text.ParserCombinators.Parsec

import Data.List
import Data.Either
import Data.Char

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
                       , execs     :: !Int
                       , unique    :: !Int
                       , crashes   :: !Int
                       , time      :: !Double
                       } deriving (Eq, Ord, Show)

fileNameP :: GenParser Char st (Mode, Int)
fileNameP = do
  string "fuzz_SSNI_"
  m <- smode <$> (string "naive" <|> string "medium" <|> string "smart")
  char '_'
  xs <- many1 digit
  let x = read xs :: Int
  return (m, x)

right (Right x) = x

getIntegerInLine :: String -> String
getIntegerInLine line =
  takeWhile isDigit $ dropWhile (not . isDigit) line

parseOutput :: String -> [String] -> TestData
parseOutput fn allLines =
  let lines = map (read . getIntegerInLine) allLines
      execsDone = lines !! 4
      unique = lines !! 17
      total = lines !! 28
      (m, id) = right $ parse fileNameP fn fn
  in MkData m id execsDone unique total 600

main = do
  -- Get all files in the current dir
  allFiles <- getDirectoryContents "."
  -- Filter the ones that are output files (.out)
  let outputs = filter ((== ".out") . takeExtension) allFiles
  -- Iterate through each file
  parsedData  <- forM outputs $ \f -> do
    handle    <- openFile f ReadMode
    contents  <- hGetContents handle
    putStrLn $ show (f, lines contents !! 1)
    let assocDirName  = getIntegerInLine (lines contents !! 1)
        assocDirStats = "./" ++ assocDirName ++ "/output/fuzzer_stats"
    handle'   <- openFile assocDirStats ReadMode
    contents' <- hGetContents handle'
    return $ parseOutput f $ lines contents'
  let sorted = sort parsedData
  let (naive,(medium,smart)) = second (splitAt 20) (splitAt 20 sorted)
  putStrLn $ show (naive, medium, smart)
