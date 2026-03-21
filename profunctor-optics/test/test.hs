import Control.Monad
import System.Exit (exitFailure)
import System.IO (BufferMode(..), hSetBuffering, stdout, stderr)

import qualified Test.Carrier as Carrier
import qualified Test.Data.List.Optic as ListOptic
import qualified Test.Data.Map.Optic as MapOptic
import qualified Test.Data.Set.Optic as SetOptic
import qualified Test.Data.IntMap.Optic as IntMapOptic
import qualified Test.Data.IntSet.Optic as IntSetOptic
import qualified Test.Data.Profunctor.Optic.Sort as SortOptic
import qualified Test.Data.Sequence.Optic as SeqOptic
import qualified Test.Data.Tree.Optic as TreeOptic

tests :: IO [Bool]
tests = sequence
  [ Carrier.tests
  , ListOptic.tests
  , MapOptic.tests
  , SetOptic.tests
  , IntMapOptic.tests
  , IntSetOptic.tests
  , SortOptic.tests
  , SeqOptic.tests
  , TreeOptic.tests
  ]

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  hSetBuffering stderr LineBuffering

  results <- tests

  unless (and results) exitFailure
