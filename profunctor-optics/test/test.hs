import Control.Monad
import System.Exit (exitFailure)
import System.IO (BufferMode(..), hSetBuffering, stdout, stderr)

tests :: IO [Bool]
tests = sequence [] -- [CI.tests, CW.tests, F.tests] 

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  hSetBuffering stderr LineBuffering

  results <- tests

  unless (and results) exitFailure
