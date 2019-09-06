module Main where

import Control.Monad
import Data.List

import System.Directory
import System.FilePath
import System.IO

import Text.Printf

import Lib

import Statistics.Test.MannWhitneyU
import Statistics.Types
import Statistics.Test.Types
import qualified Data.Vector.Unboxed as V

import Control.Lens hiding (noneOf)
import Data.Default.Class
import Graphics.Rendering.Chart
import Graphics.Rendering.Chart.Backend.Cairo


import Debug.Trace

--  let testPerMutant  = transpose $ map sort testData
----  putStrLn "Original:"
----  putStrLn $ show testData
----  putStrLn "Transposed:"
----  putStrLn $ show testPerMutant
-- 
--      -- Leo TODO: Read random testing reference and figure out what to do with outliers.
--  let    totalPerMutant = map (\tds -> foldl1 (\acc td -> acc{ execsDone = execsDone acc + execsDone td
--                                                          , failures  = failures acc  + failures td
--                                                          , time      = time acc      + time td
--                                                          }) tds) testPerMutant
--  return $ (sort totalPerMutant, testPerMutant)

{-
mttf_ :: TestData -> (Double, String)
mttf_ td
        | failures td == 0 = (time td, "*")
        | otherwise        = (time td / (fromIntegral $ failures td), "")

mttf :: TestData -> String
mttf td =
  let (m, star) = mttf_ td in
  if star == "*" then
    let m' = (round ( m / 3600000.0) :: Int) in
    printf "%dh (t/o)" (if m' > 8 then 8 else m')
  else
    let m' = m / 1000.0 in
    if m' < 10.0 then printf "%.3f" m'
    else printf "%.1f" m'
--  printf "%.2f%s" (fst $ mttf_ td) (snd $ mttf_ td)

execsPerSec :: [[TestData]] -> [Double]
execsPerSec tds  =
  let perMethod = transpose tds
      execs = map (sum . map execsDone) perMethod
      times = map (sum . map time     ) perMethod
  in traceShow (execs, times) $ map (\(e,t) -> 1000.0 * fromIntegral e / t) $ zip execs times

--QuickChick & \qccrowbar & \toolname & \begin{tabular}{c}
--                                         QuickChick\\
--                                         (hand-written)\\
--                                      \end{tabular}\\

printMode :: Mode -> String
printMode RandomSmart = "\\begin{tabular}{c}QuickChick\\\\(hand-written)\\\\ \\end{tabular}"
printMode RandomDumb  = "QuickChick"
printMode FuzzSmart   = "\\qccrowbar (hand-written)"
printMode FuzzDumb    = "\\qccrowbar"
printMode QcFuzzSmart = "\\toolname (hand-written)"
printMode QcFuzzDumb  = "\\toolname"

tablify :: String -> [([TestData], [[TestData]])] -> IO ()
tablify fn allData = do
  let rows = transpose $ map fst allData
  outFile <- openFile fn WriteMode
--  putStrLn $ show rows
--  putStrLn $ show rows
--  hPutStrLn outFile $ "\\begin{tabular}{" ++ replicate 6 'c' ++ "}\\\\"
--  putStrLn $ show $ head rows
  hPutStr outFile "Injected Fault \\# & "
  hPutStrLn outFile $ concat (intersperse " & "  $ map (printMode . mode) $ head rows) ++ "\\\\"
  hPutStrLn outFile "\\hline"
--  hPutStrLn outFile "QC Smart & QC-AFL Smart & QcFuzz Smart & QC Dumb & QC-AFL Dumb & QcFuzz Dumb\\\\"
  forM_ (zip [1..] rows) $ \(mut,row) -> do
    hPutStr outFile $ show mut ++ " & "
    hPutStrLn outFile $ concat (intersperse " & " $ map mttf row) ++ "\\\\"
  hClose outFile

  tabFile <- openFile ("table-" ++ fn) WriteMode
--  putStrLn $ show rows
--  putStrLn $ show rows
--  hPutStrLn outFile $ "\\begin{tabular}{" ++ replicate 6 'c' ++ "}\\\\"
--  putStrLn $ show $ head rows
  hPutStrLn tabFile $ concat (intersperse " & "  $ map (printMode . mode) $ head rows) ++ "\\\\"
  hPutStrLn tabFile "\\hline"
--  hPutStrLn outFile "QC Smart & QC-AFL Smart & QcFuzz Smart & QC Dumb & QC-AFL Dumb & QcFuzz Dumb\\\\"
  hPutStrLn tabFile $ concat (intersperse " & " $ map (printf "%.1f") (execsPerSec rows)) ++ "\\\\"
--  forM_ rows $ \row -> hPutStrLn outFile $ concat (intersperse " & " $ map mttf row) ++ "\\\\"
  hClose tabFile

-}
  -- Calculate P-values:
--  let [rsVPM, fsVPM, qsVPM, rdVMP, fdVMP, qdVPM] = map snd allData
--      rsVec = map (\tds -> let td = head tds in V.fromList $ replicate (10) (time td / fromIntegral (failures td))) rsVPM
--      qdVec = map (V.fromList . map time) qdVPM
----  putStrLn $ show $ map sort rsVPM
----  putStrLn $ show rsVec
----  putStrLn $ show qdVec
--  forM_ (zip rsVec qdVec) $ \(rsv, qdv) ->
--     putStrLn $ show $ mannWhitneyUtest BGreater (mkPValue 0.05) rsv qdv
  
--stack :: IO ()
--stack = do
----  all <- getDirectoryContents "stack/random_smart"
----  putStrLn $ show all
-- 
----  putStrLn "Stack/rs"
--  randomSmart <- parseDir (parseRandDir True)  RandomSmart "stack/random_smart"
--  fuzzSmart   <- parseDir (parseFuzzDir True)  FuzzSmart   "stack/fuzz_smart"
--  qcSmart     <- parseDir (parseQcFuzzDir True) QcFuzzSmart     "stack/qcfuzz_smart"
--  randomDumb  <- parseDir (parseRandDir True)  RandomDumb  "stack/random_dumb"
--  fuzzDumb    <- parseDir (parseFuzzDir True)  FuzzDumb    "stack/fuzz_dumb"
--  qcDumb      <- parseDir (parseQcFuzzDir True) QcFuzzDumb      "stack/qcfuzz"

--  tablify "stack.tex" $ [randomSmart, fuzzSmart, qcSmart, randomDumb, fuzzDumb, qcDumb]
--  tablify "stack.tex" $ [randomDumb, fuzzDumb, qcDumb, randomSmart]
--  outFile <- openFile "stack.tex" WriteMode
----  putStrLn $ show randomSmart
--  hPutStrLn outFile "Random Smart & Fuzz Smart & QcFuzz & Random Dumb & Fuzz Dumb\\\\"
--  let perMutant = transpose [randomSmart, fuzzSmart, qcFuzz, randomDumb, fuzzDumb]
--  forM_ perMutant $ \[rs, fs, q, rd, fd] ->
--    hPutStrLn outFile $ printf "%s & %s & %s & %s & %s\\\\" (mttf rs) (mttf fs) (mttf q) (mttf rd) (mttf fd)
--  hClose outFile

main = do
  smartRuns <- parseRandomDir Smart "../output_smart/"
  naiveRuns <- parseRandomDir Naive "../output_naive/"
  fuzzRuns  <- parseRandomDir Fuzz  "../output_fuzz/"
  putStrLn $ show fuzzRuns

--register :: IO ()
--register = do
-- 
----  putStrLn "Reg/rs"
--  randomSmart <- parseDir (parseRandDir False)  RandomSmart "register/random_smart"
----  putStrLn "Reg/fs"
--  fuzzSmart   <- parseDir (parseFuzzDir False)  FuzzSmart   "register/fuzz_smart"
----  putStrLn "Reg/qs"
--  qcSmart     <- parseDir (parseQcFuzzDir False) QcFuzzSmart      "register/qcfuzz_smart"
----  putStrLn "Reg/rd"
--  randomDumb  <- parseDir (parseRandDir False)  RandomDumb  "register/random_dumb"
--  fuzzDumb    <- parseDir (parseFuzzDir False)  FuzzDumb    "register/fuzz_dumb"
--  qcDumb      <- parseDir (parseQcFuzzDir False) QcFuzzDumb      "register/qcfuzz"
-- 
----  putStrLn $ show $ transpose [randomSmart, fuzzSmart, qcSmart, randomDumb, fuzzDumb, qcDumb]
----  putStrLn $ show $ map sort $ transpose [randomSmart, fuzzSmart, qcSmart, randomDumb, fuzzDumb, qcDumb]
----  tablify "register.tex" $ [randomSmart, fuzzSmart, qcSmart, randomDumb, fuzzDumb, qcDumb]
--  tablify "register.tex" $ [randomDumb, fuzzDumb, qcDumb, randomSmart]  
----  putStrLn $ show fuzzSmart
--  putStrLn $ show randomSmart
--  putStrLn $ show randomDumb
--  putStrLn $ show fuzzDumb
--  putStrLn $ show qcFuzz
--  let mttf_ :: TestData -> (Double, String)
--      mttf_ td
--        | failures td == 0 = (time td, "*")
--        | otherwise        = (time td / (fromIntegral $ failures td), "")
-- 
--      mttf :: TestData -> String
--      mttf td = printf "%.2f%s" (fst $ mttf_ td) (snd $ mttf_ td)
-- 
--  outFile <- openFile "register.tex" WriteMode
-- 
--  hPutStrLn outFile "Random Smart & Fuzz Smart & QcFuzz & Random Dumb & Fuzz Dumb\\\\"
--  let perMutant = transpose [randomSmart, fuzzSmart, qcFuzz, randomDumb, fuzzDumb]
--  forM_ perMutant $ \[rs, fs, q, rd, fd] ->
--    hPutStrLn outFile $ printf "%s & %s & %s & %s & %s\\\\" (mttf rs) (mttf fs) (mttf q) (mttf rd) (mttf fd)
--  hClose outFile

{-
chart_ifc = do
  (e, r) <- parse_rand_dir "data/final-output"

--  print ("e", e)
--  print ("r", r)
  let evs = map calc_mttf_random e
      rvs = map calc_mttf_random r
      combined = map (\(a,b) -> [a,b]) $ sort $ zip rvs evs

      layout = 
--            layout_title .~ "Random vs Hybrid Generator Performance" ++ btitle
--          $ layout_title_style . font_size .~ 10
            layout_x_axis . laxis_generate .~ autoIndexAxis alabels
          $ layout_y_axis . laxis_generate .~ scaledAxis (def{_la_labelf = \x -> map (++ "ms") ((_la_labelf def) x)}) (0, 275)
--          $ layout_y_axis . laxis_override .~ axisGridHide
          $ layout_left_axis_visibility . axis_show_ticks .~ False
          $ layout_plots .~ [ plotBars bars2 ]
          $ def :: Layout PlotIndex Double
     
      bars2 = plot_bars_titles .~ ["Random","Hybrid"]
          $ plot_bars_values .~ addIndexes combined
          $ plot_bars_style .~ BarsClustered
          $ plot_bars_spacing .~ BarsFixGap 5 5
          $ plot_bars_item_styles .~ map mkstyle (cycle defaultColorSeq)
          $ def
     
      alabels = map show [0..32]
     
      btitle = if True then "" else " (no borders)"
      bstyle = if True then Just (solidLine 1.0 $ opaque black) else Nothing
      mkstyle c = (solidFillStyle c, bstyle)

  print $ average $ map time r
  print $ average $ map time e
  print $ average rvs
  print $ average evs
  renderableToFile def "ifc-chart.png" $ toRenderable layout


-}
