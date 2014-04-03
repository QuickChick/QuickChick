#!/bin/bash
sed -i 's/#ifdef __GLASGOW_HASKELL__//' Extracted.hs
sed -i 's/import qualified GHC.Base//' Extracted.hs
sed -i 's/#else//' Extracted.hs
sed -i 's/-- HUGS//' Extracted.hs
sed -i 's/import qualified IOExts//' Extracted.hs
sed -i 's/unsafeCoerce = IOExts.unsafeCoerce//' Extracted.hs
sed -i 's/#endif//' Extracted.hs

sed -i '1i\
{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}' Extracted.hs

sed -i 's/^import qualified Prelude/\
import qualified Prelude\
import qualified System.Random as SR\
import qualified Debug.Trace as DT\
import qualified Data.Bits as DB\
import qualified Data.Char as DC\
import Text.Show.Functions\
import System.IO.Unsafe\
import qualified Control.DeepSeq as DS\
import qualified GHC.Base/' Extracted.hs

for datatype in Result0 # Add your own here
do
    if grep --quiet $datatype Extracted.hs; then
        sed -i 's/import qualified GHC.Base/import qualified GHC.Base\
\
deriving instance Prelude.Show'" $datatype/" Extracted.hs
    else
        echo ""
    fi
done

echo "main :: GHC.Base.IO ()" >> Extracted.hs
echo "main = Prelude.print exMain" >> Extracted.hs

# Make sure that the haskell program is generated again on next build
touch Extraction.v
