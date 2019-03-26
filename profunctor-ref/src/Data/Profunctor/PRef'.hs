{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ExistentialQuantification     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# LANGUAGE RankNTypes #-}


{-# LANGUAGE ScopedTypeVariables, TypeOperators , KindSignatures, GADTs, DataKinds #-}

--for tupled constraints
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}


{-# LANGUAGE TypeApplications #-}

{-# LANGUAGE TemplateHaskell #-}
-- {-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ConstraintKinds, DeriveFunctor #-}
-- {-# LANGUAGE PolyKinds #-}
-- {-# LANGUAGE ImpredicativeTypes #-}

module Data.Profunctor.PRef' where


import Data.Ref
import Data.Profunctor.Optic
import Control.Concurrent.STM (STM)
import Control.Monad.Trans.Reader (ReaderT(..))


import Data.Function ((&)) 

--------------------------------------------------------------------------------
--  PRef'
--------------------------------------------------------------------------------


--Note that PRef r c a a is distinct from PRef' r c a in that it has
-- a read-only Ref and a write-only Ref of the same type, rather than one Ref for both reading and writing.
-- Because the Refs are existentialized this makes certain opimitations (e.g 'atomicModifyRef') 
-- unavaliable to a PRef r c a a.
--
-- Note that for TVars 'atomicModifyRef' is equiv / makes no difference
data PRef' r c a = forall s. PRef' (Optic' c s a) !(r s) 

instance Functor (PRef' r c)


newtype LocalRef c s a = 
  LocalRef { unLocalRef :: Ref m r => forall r. ReaderT (PRef' STRef c s) (ST r) a }


{-

modifyPRef' :: Ref r m => PRef' r Mapping a -> (a -> a) -> m ()
modifyPRef' (PRef' o rs) f = modifyRef' rs $ over o f

atomicModifyPRef' :: ARef r m => PRef' r Strong a -> (a -> (a, x)) -> m x
atomicModifyPRef' (PRef' o rs) f = atomicModifyRef' rs ssa
    where ssa = withLens o $ \sa sas -> \s -> let (a, x) = f . sa $! s in (sas s a, x)

-}


