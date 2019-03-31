{-# LANGUAGE TemplateHaskell, CPP #-}

-- | Declare safe top-level mutable variables which scope like ordinary values.
module Data.Profunctor.Reference.Global
    ( -- * Using this module
      -- $doc

      -- * IORef
      declareIORef

      -- * Control.Concurrent
    , declareMVar, declareEmptyMVar
   -- , declareSampleVar
    , declareChan
    , declareQSem, declareQSemN

      -- * STM
    , declareTVar
    , declareTMVar, declareEmptyTMVar
    , declareTChan

      -- * Type synonyms
    , Declare
    , DeclareInit
    , DeclareSem
    ) where

import Control.Monad
import Language.Haskell.TH

import Data.IORef
--import Data.Profunctor.Reference.PRef 

import Control.Concurrent
import Control.Concurrent.STM

import System.IO.Unsafe ( unsafePerformIO )

{- $doc
Declare a top-level variable like so:
>import Data.Profunctor.Reference.Global 
>import Control.Concurrent
>
>declareChan "ch"  [t| Maybe Char |]
>
>main = do
>    writeChan ch (Just 'x')
>    readChan  ch >>= print
This will create a module-level binding
>ch :: Chan (Maybe Char)
The `declareChan` syntax is a Template Haskell declaration splice.  The type of
channel contents is given inside a Template Haskell type quotation.  The
@TemplateHaskell@ extension must be enabled.
The scope of this variable can be controlled through the usual module
import/export mechanism.  If another module defines a @'Chan'@ also named @ch@,
there is no implicit relationship between the two.
Some declarations take an initalizer as an expression quotation.  The variable
will initially hold an unevaluated thunk for this expression.
>declareIORef "ref"
>    [t| Int |]
>    [e| 3   |]
>
>main = do
>    readIORef  ref >>= print
>    writeIORef ref 5
>    readIORef  ref >>= print
For safety, it's important not to create polymorphic references.  As a
conservative restriction, this library statically forbids syntactically
polymorphic types for reference contents.  If you need to store polymorphic
values in a reference, you can create a wrapper type with
@-XPolymorphicComponents@.
-}


-- | The type of macros for declaring variables.
type Declare     = String -> Q Type          -> Q [Dec]

-- | The type of macros for declaring variables with initializers.
type DeclareInit = String -> Q Type -> Q Exp -> Q [Dec]

-- | The type of macros for declaring semaphores.
type DeclareSem  = String -> Q Exp           -> Q [Dec]

polymorphic :: Type -> Bool
polymorphic (ForallT _ _ _) = True
polymorphic (VarT   _)      = True
polymorphic (ConT   _)      = False
polymorphic (TupleT _)      = False
polymorphic ArrowT          = False
polymorphic ListT           = False
polymorphic (AppT s t) = polymorphic s || polymorphic t
polymorphic (SigT t _) = polymorphic t

declare :: Q Type -> Q Exp -> String -> Q [Dec]
declare mty newRef nameStr = do
    let name = mkName nameStr
    ty <- mty
    when (polymorphic ty) $
        error ("Data.Profunctor.Reference.Global: cannot declare ref of polymorphic type " ++
               show (ppr ty))

    body <- [| unsafePerformIO $newRef |]

    return [
        SigD name ty
      , ValD (VarP name) (NormalB body) []
      , PragmaD (InlineP name NoInline ConLike AllPhases) ] -- TODO this is probably wrong

declareRef :: Name -> Q Exp -> String -> Q Type -> Q [Dec]
declareRef refTy newRef nameStr mty
    = declare (appT (conT refTy) mty) newRef nameStr

declareSem :: Name -> Q Exp -> String -> Q [Dec]
declareSem semTy = declare (conT semTy)

-- | Declare an @'IORef'@ with an initial value.
--
-- >declareIORef "foo" [t| Char |] [e| 'x' |]
declareIORef     :: DeclareInit
declareIORef     name ty ex = declareRef ''IORef     [| newIORef     $ex |] name ty

-- | Declare an @'MVar'@ with an initial value.
--
-- >declareMVar "foo" [t| Char |] [e| 'x' |]
declareMVar      :: DeclareInit
declareMVar      name ty ex = declareRef ''MVar      [| newMVar      $ex |] name ty

{-
-- | Declare a @'SampleVar'@ with an initial value.
--
-- >declareSampleVar "foo" [t| Char |] [e| 'x' |]
declareSampleVar :: DeclareInit
declareSampleVar name ty ex = declareRef ''SampleVar [| newSampleVar $ex |] name ty
-}
-- | Declare a @'TVar'@ with an initial value.
--
-- >declareTVar "foo" [t| Char |] [e| 'x' |]
declareTVar      :: DeclareInit
declareTVar      name ty ex = declareRef ''TVar      [| newTVarIO    $ex |] name ty

-- | Declare a @'TMVar'@ with an initial value.
--
-- >declareTMVar "foo" [t| Char |] [e| 'x' |]
declareTMVar     :: DeclareInit
declareTMVar     name ty ex = declareRef ''TMVar     [| newTMVarIO   $ex |] name ty

-- | Declare an empty @'MVar'@.
--
-- >declareEmptyMVar "foo" [t| Char |]
declareEmptyMVar  :: Declare
declareEmptyMVar  = declareRef ''MVar  [| newEmptyMVar    |]

-- | Declare an empty @'TMVar'@.
--
-- >declareEmptyTMVar "foo" [t| Char |]
declareEmptyTMVar :: Declare
declareEmptyTMVar = declareRef ''TMVar [| newEmptyTMVarIO |]

-- | Declare an empty @'Chan'@.
--
-- >declareChan "foo" [t| Char |]
declareChan       :: Declare
declareChan       = declareRef ''Chan  [| newChan         |]

-- | Declare an empty @'TChan'@.
--
-- >declareTChan "foo" [t| Char |]
declareTChan      :: Declare
declareTChan      = declareRef ''TChan [| newTChanIO      |]


-- | Declare a @'QSem'@ with the specified quantity.
--
-- >declareQSem "foo" [e| 3 |]
declareQSem  :: DeclareSem
declareQSem  name ex = declareSem ''QSem  [| newQSem  $ex |] name

-- | Declare a @'QSemN'@ with the specified quantity.
--
-- >declareQSemN "foo" [e| 3 |]
declareQSemN :: DeclareSem
declareQSemN name ex = declareSem ''QSemN [| newQSemN $ex |] name
