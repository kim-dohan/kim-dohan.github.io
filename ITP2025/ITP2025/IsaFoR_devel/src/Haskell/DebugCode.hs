{-
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012)
License: LGPL (see file COPYING.LESSER)
-}
module DebugCode(refTime, debug) where

import System.IO.Unsafe;
import Data.Time.Clock;

refTime :: UTCTime;
refTime = unsafePerformIO (getCurrentTime);

showTimeDiff :: NominalDiffTime -> String;
showTimeDiff d = Prelude.show d;

debug :: ([Prelude.Char] -> [Prelude.Char]) -> [Prelude.Char] -> a -> a;
debug i t x = unsafePerformIO (getCurrentTime >>= (\ti -> (Prelude.putStrLn ("(" 
  ++ showTimeDiff (diffUTCTime ti refTime) ++ ") - " ++ i [] ++ ": " ++ t) >> return x)));
