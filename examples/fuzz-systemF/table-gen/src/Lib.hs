{-# LANGUAGE DeriveGeneric #-}
module Lib where

import System.Directory
import System.FilePath
import System.IO

import GHC.Generics
import Control.DeepSeq

import Control.Monad
import Control.Arrow (second)

import Text.ParserCombinators.Parsec

import Data.List
import Data.Either
import Data.Char
import Data.Maybe

import Debug.Trace

-- Hard coded product of configurations.
-- The order of the constructors is the order of the columns!
data Mode = Smart
          | Naive
          | Fuzz
  deriving (Eq, Ord, Show, Generic, Read)

instance NFData Mode

data SingleRun = Run { mode   :: !Mode
                     , mutant :: !Int
                     , failed :: !Bool
                     , time   :: !Double
                     , execs  :: !Int
                     , discs  :: !Int
                     } deriving (Eq, Ord, Show, Generic)

instance NFData SingleRun

right (Right x) = x
right x = error (show x)

-- mode-maxexecs-mutantid-runid
parseFileName :: String -> (Mode, Int, Int, Int)
parseFileName s =
  let (m  , _:r1) = break (=='-') s 
      (me , _:r2) = break (=='-') r1
      (mid, _:r3) = break (=='-') r2
      (rid, _   ) = break (=='.') r3
  in (read m, read me, read mid, read rid)

-- | Parse the line of real time (in seconds)
realP :: GenParser Char st Double
realP = do
  string "real\t"
  elapsed_minutes <- many1 (noneOf "m")
  char 'm'
  elapsed_seconds <- many1 (noneOf "s")
  let elapsed = (read elapsed_minutes) * 60.0 + (read elapsed_seconds)
  return elapsed

isPassFailLine :: String -> Maybe Bool
isPassFailLine ('+':'+':'+':_) = Just True
isPassFailLine ('*':'*':'*':_) = Just False
isPassFailLine _ = Nothing

isRealLine :: String -> String -> Maybe Double
isRealLine fn line =
  case parse realP fn line of
    Right d  -> Just d
    Left err -> Nothing

getData :: String -> (String -> Maybe a) -> [String] -> a
getData desc fun lines =
  let mapped = map fun lines
  in case catMaybes mapped of
       [x] -> x
       []  -> error $ "No options for (" ++ desc ++ "): " ++ show lines

parseRandomFile :: Mode -> String -> String -> SingleRun
parseRandomFile m fn contents =
  -- Drop all but the last 5 lines
  let allLines = lines contents
      (_mode, _maxExecs, mutantId, _runId) = parseFileName fn
      isFail = getData (fn ++ "- Pass/Fail") isPassFailLine allLines
      runs = 0 -- TODO 
      discards = 0 -- TODO
      t = getData (fn ++ "Real") (isRealLine fn) allLines
  in
  Run { mode = m
      , mutant = mutantId
      , failed = isFail
      , time   = t
      , execs = runs
      , discs = discards
      } 

parseRandomDir :: Mode -> String -> IO [SingleRun]
parseRandomDir mode dir = do
  -- Get all files in the current dir
  allFiles <- map ((dir ++ "/") ++) <$> getDirectoryContents dir
  -- Filter the ones that are output files (.out)
  let outputs = filter ((== ".out") . takeExtension) allFiles
  -- Iterate through each file
  allRuns <- forM outputs $ \f -> do
    handle   <- openFile f ReadMode
    contents <- hGetContents handle
    let result = parseRandomFile mode f contents
    result `deepseq` hClose handle
    return result
  return allRuns


{-


-- | Fuzz result parsing

getIntegerInLine :: String -> String
getIntegerInLine line =
  takeWhile isDigit $ dropWhile (not . isDigit) line

parseStatsFuzz :: Mode -> String -> [String] -> TestData
parseStatsFuzz m fn allLines =
  let lines = map (read . getIntegerInLine) allLines
      startTime = lines !! 0
      endTime   = lines !! 1
      execsDone = lines !! 4
      -- Next line should be 0 or 1. Assert?
      uniqueCrashes = lines !! 17
      mutantId = read $ getIntegerInLine $ takeBaseName fn
  in MkData m mutantId execsDone uniqueCrashes (fromIntegral $ endTime - startTime)

parseFuzzDir :: Bool -> Mode -> String -> IO [TestData]
parseFuzzDir b mode dir = do
  -- Get all files in the current dir
  allFiles <- map ((dir ++ "/") ++) <$> getDirectoryContents dir
  -- Filter the ones that are output files (.out)
  let outputs = filter ((== ".out") . takeExtension) allFiles
  -- Iterate through each file
  testData  <- forM outputs $ \f -> do
--    putStrLn $ "Handing file: " ++ f
    handle    <- openFile f ReadMode
    contents  <- hGetContents handle
    -- putStrLn $ show (f, lines contents !! 1)
    -- Grab the associated filename:
    -- Second like looks like the following:
    -- Extracted ML file: /tmp/QuickChick/164446/QuickChicke154eb.ml
    -- The first integer in line (164446 here) is the name of the AFL stats file in the output
    let assocDirName  = getIntegerInLine (lines contents !! if b then 1 else 23)
        assocDirStats = dir ++ "/" ++ assocDirName 
    handle'   <- openFile assocDirStats ReadMode
    contents' <- hGetContents handle'
    return $ parseStatsFuzz mode f $ lines contents'
  return testData

-- | Random result parsing

-- Read a stat
-- e.g.
-- 12451 : true
-- 241 : ()
-- 123 : false
numberP :: GenParser Char st (String, Int)
numberP = do
  x <- read <$> many1 digit
  spaces
  char ':'
  spaces
  s <- string "true" <|> string "\"()\"" <|> string "false"
  return (s,x)

-- | Parse the line of time (in milli)
timeP :: GenParser Char st Double
timeP = do
  -- | ignore user/system
  user <- many1 (noneOf "u")
  string "user "
  system <- many1 (noneOf "s")
  string "system "
  -- | returns in 0.01 seconds
  elapsed_minutes <- many1 (noneOf ":")
  -- traceM elapsed_minutes
  char ':'
  elapsed_secs  <- many1 (noneOf ".:e")
  -- traceM elapsed_secs
  char '.' <|> char 'e'
  elapsed_milli  <- many1 (noneOf "e")
  -- traceM elapsed_milli
  let elapsed = (read elapsed_minutes) * 60.0 * 1000.0 + (read elapsed_secs) * 1000.0 + (read elapsed_milli) * 10.0
  return elapsed

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

parseOutputRand :: Mode -> String -> String -> TestData
parseOutputRand m fn contents =
  -- Drop three first lines
  let _ : _ : _ : rest = lines contents
  -- Parse the next three lines for data (always at least 3)
      (s,d,f) = stats fn (take 3 rest) (0,0,0)
      (_ : timeLine : _) = reverse rest
      mutantId = read $ getIntegerInLine $ takeBaseName fn
      t = right $ parse timeP fn timeLine
  in MkData m mutantId (s+d+f) f t

-- real	2m15.185s
realP :: GenParser Char st Double
realP = do
  string "real\t"
  min <- read <$> many1 digit
  string "m"
  sec <- read <$> many1 digit
  string "."
  milli <- read <$> many1 digit
  return $ min * 60.0 * 1000.0 + sec * 1000.0 + milli

parseOutputRandReg :: Mode -> String -> String -> TestData
parseOutputRandReg m fn contents =
  trace fn $ 
  -- Drop three first lines
  let rest = drop (if length (lines contents) < 15 then 5 else 12) $ lines contents
  -- Parse the next three lines for data (always at least 3)
      (s,d,f) = stats fn (take 3 rest) (0,0,0)
      timeLine : _ = drop 2 $ reverse rest
      mutantId = read $ getIntegerInLine $ takeBaseName fn
      t = right $ parse realP fn timeLine
  in MkData m mutantId (s+d+f) f t

parseRandDir :: Bool -> Mode -> String -> IO [TestData]
parseRandDir b mode dir = do
  -- Get all files in the current dir
  allFiles <- map ((dir ++ "/") ++) <$> getDirectoryContents dir
  -- Filter the ones that are output files (.out)
  let outputs = filter ((== ".out") . takeExtension) allFiles
  -- Iterate through each file
  testData <- forM outputs $ \f -> do
    handle   <- openFile f ReadMode
    contents <- hGetContents handle
    let result = (if b then parseOutputRand else parseOutputRandReg) mode f contents
    result `deepseq` hClose handle
    return result
  return testData

-- | QcFuzz result parsing

-- TODO: For register machine, also need to parse non-failed runs
-- *** Failed after 7631 tests and 0 shrinks. (108144 discards)
failedP :: GenParser Char st (Int, Int, Int)
failedP = do
  string "*** Failed after "
  successful <- read <$> many1 digit
  spaces
  string "tests and 0 shrinks. ("
  discards   <- read <$> many1 digit
  return (successful, discards, 1)

-- *** Gave up! Passed only 296848 tests
-- Discarded: 2000000
gaveUpP :: GenParser Char st Int
gaveUpP = do
  string "*** Gave up! Passed only "
  successful <- read <$> many1 digit
  return successful

gaveUpDiscardedP :: GenParser Char st Int
gaveUpDiscardedP = do
  string "Discarded: "
  discarded <- read <$> many1 digit
  return discarded

parseFailLines :: String -> String -> String -> (Int, Int, Int)
parseFailLines fn "" failLine = right $ parse failedP fn failLine
parseFailLines fn gaveUpLine discardLine =
  let s = right $ parse gaveUpP fn gaveUpLine
      d = right $ parse gaveUpDiscardedP fn discardLine
  in (s, d, 0)

parseOutputQcFuzz :: Mode -> String -> [String] -> TestData
parseOutputQcFuzz m fn lines =
  let failLine1 = lines !! 21
      failLine2 = lines !! 22
      timeLine = lines !! 24
      (s,d,f) = parseFailLines fn failLine1 failLine2 
      time = right $ parse timeP fn timeLine
      mutantId = read $ getIntegerInLine $ takeBaseName fn
  in MkData m mutantId (s+d+f) f time

parseOutputQcFuzzReg :: Mode -> String -> [String] -> TestData
parseOutputQcFuzzReg m fn lines =
  let adjust x = if length lines > 35 then x else x - 14
      failLine1 = lines !! adjust 33
      failLine2 = lines !! adjust 34
      timeLine = lines !! adjust 37
      (s,d,f) = parseFailLines fn failLine1 failLine2 
      time = right $ parse realP fn timeLine
      mutantId = read $ getIntegerInLine $ takeBaseName fn
  in MkData m mutantId (s+d+f) f time

parseQcFuzzDir :: Bool -> Mode -> String -> IO [TestData]
parseQcFuzzDir b mode dir = do
  -- Get all files in the current dir
  allFiles <- map ((dir ++ "/") ++) <$> getDirectoryContents dir
  -- Filter the ones that are output files (.out)
  let outputs = filter ((== ".out") . takeExtension) allFiles
  -- Iterate through each file
  testData <- forM outputs $ \f -> do
    handle   <- openFile f ReadMode
    contents <- hGetContents handle
    return $ (if b then parseOutputQcFuzz else parseOutputQcFuzzReg) mode f $ lines contents
  return testData
-}
