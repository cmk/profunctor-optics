{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE RankNTypes             #-}
module Data.Tuple.Optic where

{-
 (
    -- * Fold & Ixfold
    type Field
  , _1
  , _2
  , _3
  , _4
  , _5
  , _6
  , _7
  , _8
  , _9
  , _10
  , co1
  , pmapped
  , curried
  , swapped
) where
-}

import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Setter
import Data.Profunctor.Optic.Type hiding (Rep)
import Data.Profunctor.Optic.View hiding (to, from)

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------


--dimap (\ ~(a, b, c) -> (b, (a, c))) (\ ~(b, (a, c)) -> (a, b, c))


-- >>> (1,2,3) ^. t32
-- 2
-- >>> over t32 (+1) (1,2,3)
-- (1,3,3)
t32 :: Lens (a, b1, c) (a, b2, c) b1 b2
t32 = matching (\ ~(a, b, c) -> (a, (b, c))) (\ ~(a, (b, c)) -> (a, b, c)) . first'
