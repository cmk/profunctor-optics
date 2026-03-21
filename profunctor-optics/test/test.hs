import Control.Monad
import System.Exit (exitFailure)
import System.IO (BufferMode(..), hSetBuffering, stdout, stderr)

import qualified Test.Carrier as Carrier
import qualified Test.Data.List.Optic as ListOptic
import qualified Test.Data.Sequence.Optic as SeqOptic
import qualified Test.Data.Tree.Optic as TreeOptic

tests :: IO [Bool]
tests = sequence
  [ Carrier.tests
  , ListOptic.tests
  , SeqOptic.tests
  , TreeOptic.tests
  ]

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  hSetBuffering stderr LineBuffering

  results <- tests

  unless (and results) exitFailure
