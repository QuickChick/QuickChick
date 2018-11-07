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

data Kind = Fuzz | Rand
  deriving (Eq, Ord)

instance Show Kind where
  show Fuzz = "fuzz"
  show Rand = "rand"

skind "fuzz" = Fuzz
skind "rand" = Rand

data Mode = Naive | Medium | Smart
  deriving (Eq, Ord, Show)

smode "arbitrary"  = Naive
smode "arbmedium" = Medium
smode "smart"  = Smart


data TestData = MkData { kind      :: !Kind
                       , mode      :: !Mode
                       , mutant    :: !Int
                       , successes :: !Int
                       , failures  :: !Int
                       , time      :: !Double
                       } deriving (Eq, Ord, Show)



fileNameP :: GenParser Char st (Kind, Mode, Int)
fileNameP = do
  _ <- many1 (noneOf "/")
  char '/'
  k <- skind <$> (string "fuzz" <|> string "rand")
  string "_SSNI_"
  m <- smode <$> (try (string "arbitrary") <|> string "arbmedium" <|> string "smart")
  char '_'
  xs <- many1 digit
  let x = read xs :: Int
  return (k, m, x)

right (Right x) = x

getIntegerInLine :: String -> String
getIntegerInLine line =
  takeWhile isDigit $ dropWhile (not . isDigit) line

parseStatsFuzz :: Double -> String -> [String] -> TestData
parseStatsFuzz time fn allLines =
  let lines = map (read . getIntegerInLine) allLines
      execsDone = lines !! 4
      -- should be 1
      unique = lines !! 17
      total = lines !! 28
      (k, m, id) = right $ parse fileNameP fn fn
  in MkData k m id (execsDone - total) unique time

parseOutputFuzz :: String -> Double
parseOutputFuzz s = 0.42

parse_fuzz_dir dir = do
  -- Get all files in the current dir
  allFiles <- map ((dir ++ "/") ++) <$> getDirectoryContents dir
  -- Filter the ones that are output files (.out)
  let outputs = filter ((== ".out") . takeExtension) allFiles
  -- Iterate through each file
  parsedData  <- forM outputs $ \f -> do
    handle    <- openFile f ReadMode
    contents  <- hGetContents handle
    -- putStrLn $ show (f, lines contents !! 1)
    let assocDirName  = getIntegerInLine (lines contents !! 1)
        timeTaken = parseOutputFuzz contents
        assocDirStats = dir ++ "/" ++ assocDirName 
    handle'   <- openFile assocDirStats ReadMode
    contents' <- hGetContents handle'
    return $ parseStatsFuzz timeTaken f $ lines contents'
  let sorted = sort parsedData
  let (naive,(medium,smart)) = second (splitAt 20) (splitAt 20 sorted)
  return $ (naive, medium, smart)

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
  user <- many1 (noneOf "u")
  string "user "
  system <- many1 (noneOf "s")
  string "system "
  elapsed <- many1 (noneOf "e")
  -- in Minutes
  return $ read user 

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

parseOutputRand :: String -> String -> TestData
parseOutputRand fn contents =
  -- Drop three first lines
  let _ : _ : _ : rest = lines contents
  -- Parse the next three lines for data (always at least 3)
      (s,d,f) = stats fn (take 3 rest) (0,0,0)
      (_ : timeLine : _) = reverse rest
      (k, m,id) = right $ parse fileNameP fn fn
      t = right $ parse timeP fn timeLine
  in MkData k m id s f t

parse_rand_dir dir = do
  -- Get all files in the current dir
  allFiles <- map ((dir ++ "/") ++) <$> getDirectoryContents dir
  -- Filter the ones that are output files (.out)
  let outputs = filter ((== ".out") . takeExtension) allFiles
  -- Iterate through each file
  parsedData <- forM outputs $ \f -> do
    handle   <- openFile f ReadMode
    contents <- hGetContents handle
    return (parseOutputRand f contents)
  let sorted = sort parsedData
  let (naive,(medium,smart)) = second (splitAt 20) (splitAt 20 sorted)
  putStrLn $ show (naive, medium, smart)

main = do
  randoms <- parse_rand_dir "output_random_10M"
  fuzz    <- parse_fuzz_dir "output_fuzz_run1"
  putStrLn $ show (randoms, fuzz)
