{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Data.Profunctor.Optic.Fold (
    -- * Fold0
    Fold0
  , fold0
  , afold0
  , failing
  , toFold0
  , fromFold0
    -- * Fold
  , Fold
  , Cofold
  , fold_
  , foldr_
  , afold
  , folding
  , foldVl
  , acofold
  , cofolding
  , cofoldVl
    -- * Fold1
  , Fold1
  , Cofold1
  , fold1_
  , folding1
  , foldVl1
  , cofolding1
  , cofoldVl1
    -- * Optics
  , folded0
  , filtered
  , folded
  , cofolded
  , folded_
  , foldedr_
  , folded1 
  , folded1_
  , afolded
  , afoldedr
  , afolded1
  , acolist
  , acolist1
    -- * Operators
  , folds0
  , (^?)
  , preview 
  , previews
  , preuse
  , preuses
  , folds
  , cofolds
  , foldsa
  , cofoldsa
  , (^..)
  , lists
  , lists1
  , foldsr
  , foldsl
  , foldsr'
  , foldsl'
  , foldsrM
  , foldslM
  , traverses_
    -- * IO
  , tries
  , tries_
  , catches
  , catches_
  , handles
  , handles_
  , halts
  , halts_
  , skips
  , skips_
    -- * EndoM
  , EndoM(..)
    -- * Classes
  , Strong(..)
  , Choice(..)
  , Closed(..)
  , Representable(..)
  , Corepresentable(..)
) where

import Control.Applicative as A
import Control.Monad (void)
import Control.Monad.Reader as Reader hiding (lift)
import Control.Monad.State as State hiding (lift)
import Control.Monad.IO.Unlift
import Data.Foldable (Foldable, traverse_)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe
import Data.Monoid
import Data.NonNull 
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Combinator
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Traversal
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Prism
import Data.Profunctor.Rep.Foldl (Unfoldl(..))
import Data.Profunctor.Rep.Foldr (Unfoldr(..))
import qualified Data.List as L
import qualified Data.List.NonEmpty as L1
import qualified Data.Profunctor.Rep.Foldl1 as L1
import qualified Data.Profunctor.Rep.Foldl as L
import qualified Data.Profunctor.Rep.Foldr as R
import Control.Exception (Exception (..))
import qualified Control.Exception as Ex

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XRankNTypes
-- >>> import Control.Exception hiding (catches)
-- >>> import Data.Functor.Identity
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import qualified Data.List.NonEmpty as NE
-- >>> import Data.Int
-- >>> import Data.Map as Map
-- >>> import Data.Maybe
-- >>> import Data.Monoid
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'Fold0'
---------------------------------------------------------------------

-- | Obtain a 'Fold0' directly.
--
-- @
-- 'fold0' . 'preview' ≡ id
-- 'fold0' ('view' o) ≡ o . 'just'
-- @
--
-- >>> preview (fold0 listToMaybe) "foo"
-- Just 'f'
--
fold0 :: (s -> Maybe a) -> Fold0 s a
fold0 f = coercer . lmap (\s -> maybe (Left s) Right (f s)) . right'
{-# INLINE fold0 #-}

-- | TODO: Document
--
afold0 :: ((a -> Maybe r) -> s -> Maybe r) -> AFold0 r s a
afold0 f = afold $ (Alt #.) #. f .# (getAlt #.) 
{-# INLINE afold0 #-}

infix 3 `failing`

-- | If the first 'Fold0' has no focus then try the second one.
--
failing :: AFold0 a s a -> AFold0 a s a -> Fold0 s a
failing a b = fold0 $ \s -> maybe (preview b s) Just (preview a s)
{-# INLINE failing #-}

-- | Obtain a 'Fold0' from a 'View'.
--
-- @
-- 'toFold0' o ≡ o . 'just'
-- 'toFold0' o ≡ 'fold0' ('view' o)
-- @
--
toFold0 :: View s (Maybe a) -> Fold0 s a
toFold0 = (. just)
{-# INLINE toFold0 #-}

-- | Obtain a 'View' from a 'Fold0' 
--
-- > 'fromFold0' = 'to' . 'preview'
--
fromFold0 ::  AFold0 a s a -> View s (Maybe a)
fromFold0 = (\f -> coercer . lmap f) . preview
{-# INLINE fromFold0 #-}

---------------------------------------------------------------------
-- Fold
---------------------------------------------------------------------

-- | Obtain a 'Fold' directly.
--
-- @ 
-- 'fold_' ('lists' o) ≡ o
-- 'fold_' f ≡ 'to' f . 'foldVl' 'traverse_'
-- 'fold_' f ≡ 'coercer' . 'lmap' f . 'lift' 'traverse_'
-- @
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- This can be useful to lift operations from @Data.List@ and elsewhere into a 'Fold'.
--
-- >>> [1,2,3,4] ^.. fold_ tail
-- [2,3,4]
--
fold_ :: Foldable f => (s -> f a) -> Fold s a
fold_ f = coercer . lmap f . foldVl traverse_
{-# INLINE fold_ #-}

-- | Obtain a 'Fold' directly from a continuation.
--
-- This allows for folds with no 'Data.Foldable.Foldable' instance.
--
foldr_ :: (s -> Unfoldr a) -> Fold s a
foldr_ f = coercer . lmap f . foldVl R.traverse_
{-# INLINE foldr_ #-}

-- | TODO: Document
--
-- @ 
-- 'afold' :: ((a -> r) -> s -> r) -> 'AFold' r s a
-- @
--
afold :: ((a -> r) -> s -> r) -> ATraversal (Const r) s t a b
afold f = atraversal $ (Const #.) #. f .# (getConst #.)
{-# INLINE afold #-}

-- | Obtain a 'Fold' from a 'Traversable' functor.
--
-- @
-- 'folding' f ≡ 'traversed' . 'to' f
-- 'folding' f ≡ 'foldVl' 'traverse' . 'to' f
-- @
--
folding :: Traversable f => (s -> a) -> Fold (f s) a
folding f = foldVl traverse . coercer . lmap f
{-# INLINE folding #-}

-- | Obtain a 'Fold' from a Van Laarhoven 'Fold'.
--
foldVl :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Fold s a
foldVl f = coercer . traversalVl f . coercer
{-# INLINE foldVl #-}

-- | TODO: Document
--
acofold :: ((r -> b) -> r -> t) -> ACofold r t b
acofold f = acotraversal $ (.# getConst) #. f .# (.# Const)
{-# INLINE acofold #-}

-- | TODO: Document
--
-- > 'cofoldVl' 'cotraverse' . 'from' f
--
cofolding :: Distributive g => (b -> t) -> Cofold (g t) b
cofolding f = cofoldVl cotraverse . coercel . rmap f
{-# INLINE cofolding #-}

-- | Obtain a 'Cofold' from a Van Laarhoven 'Cofold'.
--
cofoldVl :: (forall f. Coapplicative f => (f a -> b) -> f s -> t) -> Cofold t b
cofoldVl f = coercel . cotraversalVl f . coercel
{-# INLINE cofoldVl #-}

---------------------------------------------------------------------
-- Fold1
---------------------------------------------------------------------

-- | Obtain a 'Fold1' directly.
--
-- @ 
-- 'fold1_' ('lists1' o) ≡ o
-- 'fold1_' f ≡ 'to' f . 'foldVl1' 'traverse1_'
-- 'fold1_' f ≡ 'coercer' . 'lmap' f . 'lift' 'traverse1_'
-- @
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- This can be useful to represent operations from @Data.List.NonEmpty@ and elsewhere into a 'Fold1'.
--
fold1_ :: Foldable1 f => (s -> f a) -> Fold1 s a
fold1_ f = coercer . lmap f . foldVl1 traverse1_
{-# INLINE fold1_ #-}

-- | Obtain a 'Fold1' from a 'Traversable1' functor.
--
-- @
-- 'folding1' f ≡ 'traversed1' . 'to' f
-- 'folding1' f ≡ 'foldVl1' 'traverse1' . 'to' f
-- @
--
folding1 :: Traversable1 f => (s -> a) -> Fold1 (f s) a
folding1 f = foldVl1 traverse1 . coercer . lmap f
{-# INLINE folding1 #-}

-- | Obtain a 'Fold1' from a Van Laarhoven 'Fold1'.
--
-- See 'Data.Profunctor.Optic.Property'.
--
foldVl1 :: (forall f. Apply f => (a -> f b) -> s -> f t) -> Fold1 s a
foldVl1 f = coercer . represent f . coercer
{-# INLINE foldVl1 #-}

-- | TODO: Document
--
-- > 'cofolding1' f = 'cofoldVl1' 'cotraverse1' . 'from' f
--
cofolding1 :: Distributive1 g => (b -> t) -> Cofold1 (g t) b
cofolding1 f = cofoldVl1 cotraverse1 . coercel . rmap f
{-# INLINE cofolding1 #-}

-- | Obtain a 'Cofold1' from a Van Laarhoven 'Cofold1'.
--
cofoldVl1 :: (forall f. Coapply f => (f a -> b) -> f s -> t) -> Cofold1 t b
cofoldVl1 f = coercel . cotraversalVl1 f . coercel
{-# INLINE cofoldVl1 #-}

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | The canonical 'Fold0'. 
--
-- >>> [Just 1, Nothing] ^.. folded . folded0
-- [1]
--
folded0 :: Fold0 (Maybe a) a
folded0 = fold0 id
{-# INLINE folded0 #-}

-- | Filter another optic.
--
-- >>> [1..10] ^.. folded . filtered even
-- [2,4,6,8,10]
--
filtered :: (a -> Bool) -> Fold0 a a
filtered p = traversalVl0 (\point f a -> if p a then f a else point a) . coercer
{-# INLINE filtered #-}

-- | Obtain a 'Fold' from a 'Traversable' functor.
--
folded :: Traversable f => Fold (f a) a
folded = folding id
{-# INLINE folded #-}

-- | TODO: Document
--
-- > 'cofoldVl' 'cotraverse' . 'from' f
--
cofolded :: Distributive g => Cofold (g b) b
cofolded = cofolding id
{-# INLINE cofolded #-}

-- | The canonical 'Fold'.
--
-- @
-- 'Data.Foldable.foldMap' ≡ 'withForget' 'folded_''
-- @
--
folded_ :: Foldable f => Fold (f a) a
folded_ = fold_ id
{-# INLINE folded_ #-}

-- | Obtain a 'Fold' from a 'MonoFoldable'.
--
-- @since 0.0.3
foldedr_ :: Fold (Unfoldr a) a
foldedr_ = foldr_ id
{-# INLINE foldedr_ #-}

-- | Obtain a 'Fold1' from a 'Traversable1' functor.
--
folded1 :: Traversable1 f => Fold1 (f a) a
folded1 = folding1 id
{-# INLINE folded1 #-}

-- | The canonical 'Fold1'.
--
-- @
-- 'Data.Semigroup.Foldable.foldMap1' ≡ 'withForget' 'folded1_''
-- @
--
folded1_ :: Foldable1 f => Fold1 (f a) a
folded1_ = fold1_ id
{-# INLINE folded1_ #-}

-- | TODO: Document
--
afolded :: Foldable f => Monoid r => AFold r (f a) a
afolded = afold foldMap
{-# INLINE afolded #-}

-- | TODO: Document
--
-- @since 0.0.3
afoldedr :: Monoid r => AFold r (Unfoldr a) a
afoldedr = afold R.foldMap
{-# INLINE afoldedr #-}

-- | TODO: Document
--
afolded1 :: Foldable1 f => Semigroup r => AFold r (f a) a
afolded1 = afold foldMap1
{-# INLINE afolded1 #-}

-- | Right list unfold over an optic.
--
acolist :: ACofold a [b] (Maybe (b, a))
acolist = acofold L.unfoldr
{-# INLINE acolist #-}

-- | Right non-empty list unfold over an optic.
--
acolist1 :: ACofold a (NonEmpty b) (b, Maybe a)
acolist1 = acofold L1.unfoldr
{-# INLINE acolist1 #-}

--abytestring :: ACofold a Words.ByteString (Maybe (Word8, a))
--abytestring = acofold Words.unfoldr

--foldedBytes :: Fold BL.ByteString Word8
--foldedBytes = foldr_ R.bytes

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | TODO: Document
--
folds0 :: AFold0 r s a -> (a -> Maybe r) -> s -> Maybe r
folds0 o = (getAlt #.) #. folds o .# (Alt #.)
{-# INLINE folds0 #-}

infix 8 ^?

-- | An infk alias for 'preview''.
--
-- @
-- ('^?') ≡ 'flip' 'preview''
-- @
--
-- Perform a safe 'head' of a 'Fold' or 'Traversal' or retrieve 'Just'
-- the result from a 'View' or 'Lens'.
--
-- When using a 'Traversal' as a partial 'Lens', or a 'Fold' as a partial
-- 'View' this can be a convenient way to extract the optional value.
--
-- >>> Left 4 ^? left'
-- Just 4
-- >>> Right 4 ^? left'
-- Nothing
--
(^?) :: s -> AFold0 a s a -> Maybe a
(^?) = flip preview
{-# INLINE (^?) #-}

-- | TODO: Document
--
preview :: MonadReader s m => AFold0 a s a -> m (Maybe a)
preview = flip previews id
{-# INLINE preview #-}

-- | TODO: Document
--
previews :: MonadReader s m => AFold0 r s a -> (a -> r) -> m (Maybe r)
previews o f = Reader.asks (folds0 o (Just . f))
{-# INLINE previews #-}

-- | TODO: Document
--
preuse :: MonadState s m => AFold0 a s a -> m (Maybe a)
preuse = flip preuses id
{-# INLINE preuse #-}

-- | TODO: Document
--
preuses :: MonadState s m => AFold0 r s a -> (a -> r) -> m (Maybe r)
preuses o f = State.gets $ previews o f
{-# INLINE preuses #-}

-- | Map an optic to a monoid and combine the results.
--
-- @
-- 'Data.Foldable.foldMap' = 'folds' 'folded_'
-- @
--
-- >>> ala Sum (folds folded) [1..4]
-- 10
-- >>> folds bitraversed (\x -> [x, x + 1]) (1,3)
-- [1,2,3,4]
--
folds :: ATraversal (Const r) s t a b -> (a -> r) -> s -> r
folds o = (getConst #.) #. traverses o .# (Const #.)
{-# INLINE folds #-}

-- | TODO: Document
--
-- >>> cofolds (from succ) (*2) 3
-- 7
--
-- Compare 'Data.Profunctor.Optic.View.reviews'.
--
cofolds :: ACotraversal (Const r) s t a b -> (r -> b) -> r -> t
cofolds o = (.# Const) #. cotraverses o .# (.# getConst) 
{-# INLINE cofolds #-}

-- | TODO: Document
--
foldsa :: Applicative f => AFold (f a) s a -> s -> f a
foldsa = flip folds pure
{-# INLINE foldsa #-} 

-- | TODO: Document
--
cofoldsa :: Coapplicative f => ACofold (f b) t b -> f b -> t
cofoldsa = flip cofolds copure
{-# INLINE cofoldsa #-} 

infix 8 ^..

-- | Infix alias of 'lists'.
--
-- @
-- 'Data.Foldable.toList' xs ≡ xs '^..' 'folding'
-- ('^..') ≡ 'flip' 'lists'
-- @
--
-- >>> [[1,2], [3 :: Int64]] ^.. id
-- [[[1,2],[3]]]
-- >>> [[1,2], [3 :: Int64]] ^.. traversed
-- [[1,2],[3]]
-- >>> [[1,2], [3 :: Int64]] ^.. traversed . traversed
-- [1,2,3]
-- >>> (1,2) ^.. bitraversed
-- [1,2]
--
--
(^..) :: s -> AFold (Endo [a]) s a -> [a]
(^..) = flip lists
{-# INLINE (^..) #-}

-- | Collect the fock of an optic into a list.
--
-- @
-- 'lists' 'folded_' = 'Data.Foldable.toList'
-- @
--
lists :: AFold (Endo [a]) s a -> s -> [a]
lists o = foldsr o (:) []
{-# INLINE lists #-}

-- | Extract a 'NonEmpty' of the fock of an optic.
--
-- @
-- 'lists1' 'folded1_' = 'Data.Semigroup.Foldable.toNonEmpty'
-- @
--
-- >>> lists1 bitraversed1 ('h' :| "ello", 'w' :| "orld")
-- ('h' :| "ello") :| ['w' :| "orld"]
--
lists1 :: AFold (L1.Nedl a) s a -> s -> NonEmpty a
lists1 l = L1.runNedl . folds l (L1.Nedl . (:|))
{-# INLINE lists1 #-}

-- | Right fold over an optic.
--
-- >>> foldsr folded (+) 0 [1..5::Int64]
-- 15
--
foldsr :: AFold (Endo r) s a -> (a -> r -> r) -> r -> s -> r
foldsr o f r = (`appEndo` r) . folds o (Endo . f)
{-# INLINE foldsr #-}
  
-- | Left fold over an optic.
--
foldsl :: AFold ((Endo-Dual) r) s a -> (r -> a -> r) -> r -> s -> r
foldsl o f r = (`appEndo` r) . getDual . folds o (Dual . Endo . flip f)
{-# INLINE foldsl #-}

-- | Strict right fold over an optic.
--
foldsr' :: AFold ((Endo-Dual) (Endo r)) s a -> (a -> r -> r) -> r -> s -> r
foldsr' o f r xs = foldsl o f' (Endo id) xs `appEndo` r where f' (Endo k) x = Endo $ \ z -> k $! f x z
{-# INLINE foldsr' #-}

-- | Strict left fold over an optic.
--
-- @
-- 'Data.Foldable.foldl'' ≡ 'foldsl'' 'folding'
-- @
--
foldsl' :: AFold (Endo (Endo r)) s a -> (r -> a -> r) -> r -> s -> r
foldsl' o f r s = foldsr o f' (Endo id) s `appEndo` r where f' x (Endo k) = Endo $ \z -> k $! f z x
{-# INLINE foldsl' #-}

{- 
safeHead [] = print "Ouch!" >> return 'x'
safeHead (x:_) = print x >> return x

foo a r = safeHead a >>= (\x -> return $ x : r)

λ> foldsrM folded_ foo "" ["alpha","beta","gamma"]
'g'
'b'
'a'
"abg"

λ> foldslM folded_ foo "" ["alpha","beta","gamma"]
"Ouch!"
'x'
'x'
"xgamma"
-}

-- | Monadic right fold over an optic.
--
-- >>> foldsrM folded_ (\x y -> Identity (x++y)) "" ["foo","bar","baz"]
-- Identity "foobarbaz"
--
foldsrM :: Monad m => AFold ((Endo-Dual) (EndoM m r)) s a -> (a -> r -> m r) -> r -> s -> m r
foldsrM o f r xs = foldsl o f' mempty xs `appEndoM` r where f' e a = e <> EndoM (f a) -- f x z >>= k
{-# INLINE foldsrM #-}

-- | Monadic left fold over an optic.
--
foldslM :: Monad m => AFold (Endo (EndoM m r)) s a -> (r -> a -> m r) -> r -> s -> m r
foldslM o f r xs = foldsr o f' mempty xs `appEndoM` r where f' a e = e <> EndoM (`f` a)
{-# INLINE foldslM #-}

-- | Applicative fold over an optic.
--
-- @
-- 'Data.Foldable.traverse_' ≡ 'traverses_' 'folded'
-- @
--
-- >>> traverses_ bitraversed putStrLn ("hello","world")
-- hello
-- world
--
traverses_ :: Applicative f => AFold (Endo (f ())) s a -> (a -> f r) -> s -> f ()
traverses_ p f = foldsr p (\a fu -> void (f a) *> fu) (pure ())
{-# INLINE traverses_ #-}

---------------------------------------------------------------------
-- Exception handling
---------------------------------------------------------------------

-- | Test for synchronous exceptions that match a given optic.
--
-- In the style of 'safe-exceptions' this function rethrows async exceptions 
-- synchronously in order to preserve async behavior,
-- 
-- @
-- 'tries' :: 'MonadUnliftIO' m => 'AFold0' e 'Ex.SomeException' e -> m a -> m ('Either' e a)
-- 'tries' 'exception' :: 'MonadUnliftIO' m => 'Exception' e => m a -> m ('Either' e a)
-- @
--
tries :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> m (Either e a)
tries o a = withRunInIO $ \run -> run (Right `liftM` a) `Ex.catch` \e ->
  if isJust (e ^? async) then throwM e else run $ maybe (throwM e) (return . Left) (preview o e)
{-# INLINE tries #-}

-- | A variant of 'tries' that returns synchronous exceptions.
--
tries_ :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> m (Maybe a)
tries_ o a = preview right' `liftM` tries o a
{-# INLINE tries_ #-}

-- | Catch synchronous exceptions that match a given optic.
--
-- Rethrows async exceptions synchronously in order to preserve async behavior.
--
-- @
-- 'catches' :: 'MonadUnliftIO' m => 'AFold0' e 'Ex.SomeException' e -> m a -> (e -> m a) -> m a
-- 'catches' 'exception' :: 'MonadUnliftIO' m => Exception e => m a -> (e -> m a) -> m a
-- @
--
-- >>> catches (only Overflow) (throwIO Overflow) (\_ -> return "caught")
-- "caught"
--
catches :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> (e -> m a) -> m a
catches o a ea = withRunInIO $ \run -> run a `Ex.catch` \e ->
  if isJust (e ^? async) then throwM e else run $ maybe (throwM e) ea (preview o e)
{-# INLINE catches #-}

-- | Catch synchronous exceptions that match a given optic, discarding the match.
--
-- >>> catches_ (only Overflow) (throwIO Overflow) (return "caught")
-- "caught"
--
catches_ :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> m a -> m a
catches_ o x y = catches o x $ const y
{-# INLINE catches_ #-}

-- | Flipped variant of 'catches'.
--
-- >>> handles (only Overflow) (\_ -> return "caught") $ throwIO Overflow
-- "caught"
--
handles :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> (e -> m a) -> m a -> m a
handles o = flip $ catches o
{-# INLINE handles #-}

-- | Flipped variant of 'catches_'.
--
-- >>> handles_ (only Overflow) (return "caught") $ throwIO Overflow
-- "caught"
--
handles_ :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> m a -> m a
handles_ o = flip $ catches_ o
{-# INLINE handles_ #-}

{-
f x = if x < 10 then return x else Ex.throw Ex.Overflow
exfold = premapM f (generalize list)
xs = [1, 2, 500, 4] :: [Integer]
foldlM (halt @Ex.ArithException exfold) xs


buildlM sync (halts @Ex.ArithException sync exfold) xs

foldlM (halts @Ex.Overflow sync exfold) xs
foldlM (halts overflow exfold) xs

-- >>> foldlM (halts underflow exfold) xs
-- *** Exception: arithmetic overflow
-- >>> foldlM (halts overflow exfold) xs
-- (Just (),[1,2])
-- >>> foldlM (halts @Ex.ArithException sync exfold) xs
-- (Just arithmetic overflow,[1,2])
-}

halts :: Exception ex => MonadUnliftIO m => AFold0 e ex e -> L.FoldlM m a b -> L.FoldlM m a (Maybe e, b)
halts o (L.FoldlM step begin done) = L.FoldlM step' begin' done'
  where
    begin' =
      do
        y <- begin
        return (Nothing, y)

    step' x'@(Just _, _) _ = return x'
    step' (Nothing, x1) a =
      do
        x2Either <- tries o $ step x1 a
        case x2Either of
            Left e   -> return (Just e, x1)
            Right x2 -> return (Nothing, x2)

    done' (eMaybe, x) =
      do
        b <- done x
        return (eMaybe, b)
{-# INLINE halts #-}

halts_ :: Exception ex => MonadUnliftIO m => AFold0 e ex e -> L.FoldlM m a b -> L.FoldlM m a b
halts_ o = fmap snd . halts o
{-# INLINE halts_ #-}

skips :: Exception ex => MonadUnliftIO m => AFold0 e ex e -> L.FoldlM m a b -> L.FoldlM m a ([e], b)
skips o (L.FoldlM step begin done) = L.FoldlM step' begin' done'
  where
    begin' =
      do
        y <- begin
        return (id, y)

    step' (es, x1) a =
      do
        x2Either <- tries o $ step x1 a
        case x2Either of
            Left e   -> return (es . (e :), x1)
            Right x2 -> return (es, x2)

    done' (es, x) =
      do
        b <- done x
        return (es [], b)
{-# INLINE skips #-}

skips_ :: Exception ex => MonadUnliftIO m => AFold0 e ex e -> L.FoldlM m a b -> L.FoldlM m a b
skips_ o = fmap snd . skips o
{-# INLINE skips_ #-}

throwM :: MonadIO m => Exception e => e -> m a
throwM = liftIO . Ex.throwIO
{-# INLINE throwM #-}

---------------------------------------------------------------------
-- EndoM
---------------------------------------------------------------------

newtype EndoM m a = EndoM { appEndoM :: a -> m a }

instance Monad m => Semigroup (EndoM m a) where
    (EndoM f) <> (EndoM g) = EndoM (f <=< g)
    {-# INLINE (<>) #-}

instance Monad m => Monoid (EndoM m a) where
    mempty = EndoM return
    {-# INLINE mempty #-}

    mappend = (<>)
    {-# INLINE mappend #-}
