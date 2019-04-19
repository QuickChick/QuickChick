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

import System.Environment(getArgs)
import Data.Colour.Names
import Data.Colour
import Control.Lens hiding (noneOf)
import Data.Default.Class
import Graphics.Rendering.Chart
import Graphics.Rendering.Chart.Backend.Cairo

import qualified Data.Vector as V
import Statistics.LinearRegression (linearRegression)
  
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


right (Right x) = x
right x = error (show x)

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
      mutantId = getIntegerInLine fn
  in MkData  m id (execsDone - total) unique time

parseOutputFuzz :: String -> Double
parseOutputFuzz s =
  let (_:_:times:rest) = reverse $ lines s in
  let times' = case times of
                 't' : _ -> let (_:_:x:_) = rest in x
                 _ -> times in
--  traceShow (s, times, times') $ 
  right $ parse timeElapsedP times' times'

timeElapsedP :: GenParser Char st Double
timeElapsedP = do
  user <- many1 (noneOf "u")
  string "user "
  system <- many1 (noneOf "s")
  string "system "
--  traceM user
--  traceM system
  -- returns in seconds
  let parseMinuteBased () = do
        elapsed_minutes <- many1 (noneOf ":")
--        traceM elapsed_minutes
        char ':'
        elapsed_secs  <- many1 (noneOf ".:e")
--        traceM elapsed_secs
        char '.' <|> char 'e'
--        elapsed_micro  <- many1 (noneOf "e")
--        traceM elapsed_micro
        let elapsed = (read elapsed_minutes) * 60 + (read elapsed_secs) -- + (read elapsed_micro) / 100
        return elapsed
  elapsed <- (try $ parseMinuteBased ()) <|> (do hours <- many1 (noneOf ":")
--                                                 traceM hours
                                                 char ':'
                                                 minutes <- parseMinuteBased ()
--                                                 traceShowM minutes
                                                 return (read hours * 60 * 60 + minutes))
  -- in Minutes
  return $ (elapsed / 60)
  
parse_fuzz_dir dir = do
  -- Get all files in the current dir
  allFiles <- map ((dir ++ "/") ++) <$> getDirectoryContents dir
  -- Filter the ones that are output files (.out)
  let outputs = filter ((== ".out") . takeExtension) allFiles
  -- Iterate through each file
  parsedData  <- forM outputs $ \f -> do
    handle    <- openFile f ReadMode
    contents  <- hGetContents handle
--    putStrLn $ show (f, lines contents !! 1)
    let assocDirName  = getIntegerInLine (lines contents !! 1)
        timeTaken = parseOutputFuzz contents
        assocDirStats = dir ++ "/" ++ assocDirName 
    handle'   <- openFile assocDirStats ReadMode
    contents' <- hGetContents handle'
    return $ parseStatsFuzz timeTaken f $ lines contents'
  let sorted = sort parsedData
      naive  = filter (\d -> mode d == Naive ) sorted
      medium = filter (\d -> mode d == Medium) sorted
      smart  = filter (\d -> mode d == Smart ) sorted
  return (naive, medium, smart)

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
      naive  = filter (\d -> mode d == Naive ) sorted
      medium = filter (\d -> mode d == Medium) sorted
      smart  = filter (\d -> mode d == Smart ) sorted
  return (naive, medium, smart)

inf :: Double
inf = 42424242

calc_mttf_random :: TestData -> Double
calc_mttf_random info
  | failures info == 0 = inf
  | otherwise = time info / (fromIntegral (failures info))

-- Fuzz has one failure per
calc_mttf_fuzz :: [TestData] -> Double
calc_mttf_fuzz infos =
  let infos' = filter ((==1) .failures) infos in
  if null infos' then inf
  else sum (map time infos') / (fromIntegral $ length infos)

data Benchmark = Bench { bname :: String
                       , bmuts :: [Int]
                       , btime :: [Double]
                       }
                 deriving (Show)
                       
main = do
  (nr, mr, sr) <- parse_rand_dir "output_random_10M"
  fuzz    <- forM [1..5] $ \i -> parse_fuzz_dir $ "output_fuzz_run" ++ show i
  fuzz_arb <- parse_fuzz_dir "output_fuzz_arbitrary_1h"
  fuzz_seeded  <- parse_fuzz_dir "output_fuzz_arbitrary_1h_seeded"
  fuzz_seeded2 <- parse_fuzz_dir "output_fuzz_arbitrary_2h_seeded"

  -- Randoms
  let mkBench name times = Bench name [0..19] $ map calc_mttf_random times
      nrb = mkBench "naive-random" nr
      mrb = mkBench "med-random"   mr
      srb = mkBench "smart-random" sr

  -- Fuzzs
  let afs  = (\(n,_,_) -> n) fuzz_arb
      afss1 = (\(n,_,_) -> n) fuzz_seeded
      afss2 = (\(n,_,_) -> n) fuzz_seeded2
      afss = transpose [afss1, afss2]
      mfs = transpose $ map (\(_,m,_) -> m) fuzz
      sfs = transpose $ map (\(_,_,s) -> s) fuzz
      mkFuzz name times = Bench name [0..19] $ map calc_mttf_fuzz times
      afb  = mkFuzz "naive-fuzz" (map return afs)
      afbs = mkFuzz "naive-fuzz-seeded" (afss)
--      afb' = mkFuzz "naive-fuzz-seeded2" (map return afs2)
      mfb = mkFuzz "med-fuzz" mfs
      sfb = mkFuzz "smart-fuzz" sfs

  renderableToFile def "arbitraries.png"  $ chart fromIntegral ( * 60) [nrb, afb, afbs]
  renderableToFile def "medium-smart.png" $ chart fromIntegral ( * 60) [mrb, srb, mfb, sfb]

calculateLine :: (Int -> Double) -> (Double -> Double) -> Benchmark -> [(Double, Double)]
calculateLine xlogger ylogger bs =
  zip (map xlogger $ bmuts bs) (map ylogger $ btime bs)

chart :: (Int -> Double) -> (Double -> Double) -> [Benchmark] -> Renderable ()
chart xlogger ylogger inputData = toRenderable layout 
    where layout = layout_title .~ "Random vs Fuzz" 
                 $ layout_x_axis  . laxis_generate .~ scaledAxis (def{_la_labelf = \x -> map ("mutant id: " ++) ((_la_labelf def) x)}) (0, xlogger 20)
                 $ layout_y_axis  . laxis_generate .~ scaledAxis (def{_la_labelf = \x -> map (++ "sec") ((_la_labelf def) x)})
                                                                 (0, ylogger (1.2 * (maximum $ filter (< inf) $ concatMap btime inputData)))
                 $ layout_plots .~ lines
                 $ def

          colors = [ opaque red, opaque blue, opaque green , opaque grey ]

          lines = map (\(c,d) -> toPlot $ plot_lines_values .~ [d]
                                        $ plot_lines_style  .  line_color .~ c
                                        $ def
                      ) (zip colors (map (calculateLine xlogger ylogger) inputData))

-- 
--          bars = map (\(c,d) -> toPlot $ plot_errbars_values .~ (
--                                       let errps = map (\d -> ErrPoint (ErrValue (xlogger $ listLength d) 
--                                                                                 (xlogger $ listLength d) 
--                                                                                 (xlogger $ listLength d))
--                                                                       (ErrValue (ylogger $ if not $ isNaN (time_min d) then time_min d 
--                                                                                           else time d - (time_max d - time d))
--                                                                                 (ylogger $ time d) 
--                                                                                 (ylogger $ if not $ isNaN (time_max d) then time_max d 
--                                                                                           else time d + (time d - time_min d))
--                                                                       )) d in
--                                       errps)
--                                   $ plot_errbars_line_style  .  line_color .~ c
--                                   $ def
--                     ) (zip colors inputData)

-- 
--chart nrd mrd srd = toRenderable layout 
--  where
--    nr_line = plot_lines_values .~ [nrd]
--            $ plot_lines_style  . line_color .~ opaque blue
--            $ plot_lines_title .~ "naive"
--            $ def
-- 
--    mr_line = plot_lines_values .~ [mrd]
--            $ plot_lines_style  . line_color .~ opaque blue
--            $ plot_lines_title .~ "medium"
--            $ def
-- 
--    sr_line = plot_lines_values .~ [srd]
--            $ plot_lines_style  . line_color .~ opaque blue
--            $ plot_lines_title .~ "smart"
--            $ def
-- 
-- 
-- 
----    sinusoid2 = plot_points_style .~ filledCircles 2 (opaque red)
----              $ plot_points_values .~ [ (x,(am x)) | x <- [0,7..400]]
----              $ plot_points_title .~ "am points"
----              $ def
-- 
--    layout :: Layout LogValue Double
--    layout = layout_title .~ "Random vs Fuzz"
--           $ layout_plots .~ [toPlot nr_line, toPlot mr_line, toPlot sr_line]
-- 
--           $ def


