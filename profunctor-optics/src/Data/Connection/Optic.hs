module Data.Connection.Optic (
    dual
  , just
  , binord
  , ordbin
  , connected
) where

import Data.Connection (Conn)
import Data.Prd
import Data.Profunctor.Optic.Grate
import Data.Profunctor.Optic.Import
import qualified Data.Connection as C

dual :: Prd a => Prd b => Conn a b -> Grate' (Down b) (Down a)
dual = connected . C.dual

just :: Prd a => Prd b => Conn a b -> Grate' (Maybe a) (Maybe b)
just = connected . C.just

ordbin :: Grate' Ordering Bool
ordbin = connected C.ordbin 

binord :: Grate' Bool Ordering
binord = connected C.binord
