module Data.Profunctor.Optic.Lens where

import Control.Arrow ((&&&))

import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Operators
import Data.Void (Void, absurd)


{- Hedgehog predicates
viewUpdate :: Eq s => Lens_ s s a a -> s -> Bool
viewUpdate (Lens_ v u) s = u ((v s), s) == s

updateView :: Eq a => Lens_ s s a a -> a -> s -> Bool
updateView (Lens_ v u) a s = v (u (a, s)) == a

updateUpdate :: Eq s => Lens_ s s a a -> a -> a -> s -> Bool
updateUpdate (Lens_ v u) a1 a2 s = u (a2, (u (a1, s))) == u (a2, s)

-}

lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens sa sbt = dimap (sa &&& id) (uncurry . flip $ sbt) . first'


cloneLens :: ALens s t a b -> Lens s t a b
cloneLens l = withLens l $ \x y p -> lens x y p


withLens :: ALens s t a b -> ((s -> a) -> (s -> b -> t) -> r) -> r
withLens l f = case l (Lens_ id $ \_ b -> b) of Lens_ x y -> f x y

{-
-------------------------------------------------------------------------------
-- Common Lenses
-------------------------------------------------------------------------------

-- | Lift a 'Lens' so it can run under a function (or other corepresentable profunctor).
--
-- @
-- 'inside' :: 'Lens' s t a b -> 'Lens' (e -> s) (e -> t) (e -> a) (e -> b)
-- @
--
--
-- >>> (\x -> (x-1,x+1)) ^. inside _1 $ 5
-- 4
--
-- >>> runState (modify (1:) >> modify (2:)) ^. (inside _2) $ []
-- [2,1]
inside :: Corepresentable p => ALens s t a b -> Lens (p e s) (p e t) (p e a) (p e b)
inside l f es = o <$> f i where
  i = cotabulate $ \ e -> ipos $ l sell (cosieve es e)
  o ea = cotabulate $ \ e -> ipeek (cosieve ea e) $ l sell (cosieve es e)
{-# INLINE inside #-}

{-
-- | Lift a 'Lens' so it can run under a function (or any other corepresentable functor).
insideF :: F.Representable f => ALens s t a b -> Lens (f s) (f t) (f a) (f b)
insideF l f es = o <$> f i where
  i = F.tabulate $ \e -> ipos $ l sell (F.index es e)
  o ea = F.tabulate $ \ e -> ipeek (F.index ea e) $ l sell (F.index es e)
{-# INLINE inside #-}
-}

-- | Merge two lenses, getters, setters, folds or traversals.
--
-- @
-- 'chosen' ≡ 'choosing' 'id' 'id'
-- @
--
-- @
-- 'choosing' :: 'Control.Lens.Getter.Getter' s a     -> 'Control.Lens.Getter.Getter' s' a     -> 'Control.Lens.Getter.Getter' ('Either' s s') a
-- 'choosing' :: 'Control.Lens.Fold.Fold' s a       -> 'Control.Lens.Fold.Fold' s' a       -> 'Control.Lens.Fold.Fold' ('Either' s s') a
-- 'choosing' :: 'Lens'' s a      -> 'Lens'' s' a      -> 'Lens'' ('Either' s s') a
-- 'choosing' :: 'Control.Lens.Traversal.Traversal'' s a -> 'Control.Lens.Traversal.Traversal'' s' a -> 'Control.Lens.Traversal.Traversal'' ('Either' s s') a
-- 'choosing' :: 'Control.Lens.Setter.Setter'' s a    -> 'Control.Lens.Setter.Setter'' s' a    -> 'Control.Lens.Setter.Setter'' ('Either' s s') a
-- @
choosing :: Functor f
       => LensLike f s t a b
       -> LensLike f s' t' a b
       -> LensLike f (Either s s') (Either t t') a b
choosing l _ f (Left a)   = Left <$> l f a
choosing _ r f (Right a') = Right <$> r f a'
{-# INLINE choosing #-}

-- | This is a 'Lens' that updates either side of an 'Either', where both sides have the same type.
--
-- @
-- 'chosen' ≡ 'choosing' 'id' 'id'
-- @
--
-- >>> Left a^.chosen
-- a
--
-- >>> Right a^.chosen
-- a
--
-- >>> Right "hello"^.chosen
-- "hello"
--
-- >>> Right a & chosen *~ b
-- Right (a * b)
--
-- @
-- 'chosen' :: 'Lens' ('Either' a a) ('Either' b b) a b
-- 'chosen' f ('Left' a)  = 'Left' '<$>' f a
-- 'chosen' f ('Right' a) = 'Right' '<$>' f a
-- @
chosen :: IndexPreservingLens (Either a a) (Either b b) a b
chosen pafb = cotabulate $ \weaa -> cosieve (either id id `lmap` pafb) weaa <&> \b -> case extract weaa of
  Left _  -> Left  b
  Right _ -> Right b
{-# INLINE chosen #-}

-- | 'alongside' makes a 'Lens' from two other lenses or a 'Getter' from two other getters
-- by executing them on their respective halves of a product.
--
-- >>> (Left a, Right b)^.alongside chosen chosen
-- (a,b)
--
-- >>> (Left a, Right b) & alongside chosen chosen .~ (c,d)
-- (Left c,Right d)
--
-- @
-- 'alongside' :: 'Lens'   s t a b -> 'Lens'   s' t' a' b' -> 'Lens'   (s,s') (t,t') (a,a') (b,b')
-- 'alongside' :: 'Getter' s   a   -> 'Getter' s'    a'    -> 'Getter' (s,s')        (a,a')
-- @
alongside :: LensLike (AlongsideLeft f b') s  t  a  b
          -> LensLike (AlongsideRight f t) s' t' a' b'
          -> LensLike f (s, s') (t, t') (a, a') (b, b')
alongside l1 l2 f (a1, a2)
  = getAlongsideRight $ l2 ?? a2 $ \b2 -> AlongsideRight
  $ getAlongsideLeft  $ l1 ?? a1 $ \b1 -> AlongsideLeft
  $ f (b1,b2)
{-# INLINE alongside #-}

-- | This 'Lens' lets you 'view' the current 'pos' of any indexed
-- store comonad and 'seek' to a new position. This reduces the API
-- for working these instances to a single 'Lens'.
--
-- @
-- 'ipos' w ≡ w 'Control.Lens.Getter.^.' 'locus'
-- 'iseek' s w ≡ w '&' 'locus' 'Control.Lens.Setter..~' s
-- 'iseeks' f w ≡ w '&' 'locus' 'Control.Lens.Setter.%~' f
-- @
--
-- @
-- 'locus' :: 'Lens'' ('Context'' a s) a
-- 'locus' :: 'Conjoined' p => 'Lens'' ('Pretext'' p a s) a
-- 'locus' :: 'Conjoined' p => 'Lens'' ('PretextT'' p g a s) a
-- @
locus :: IndexedComonadStore p => Lens (p a c s) (p b c s) a b
locus f w = (`iseek` w) <$> f (ipos w)
{-# INLINE locus #-}
-}

-- | There is a `Unit` in everything.
united :: forall a. Lens' a ()
united = lens (const ()) const

-- | There is everything in `Void`.
devoid :: forall a. Lens' Void a
devoid = lens absurd const

-- do we really need these?
_1 :: Lens (a,c) (b,c) a b
_1 = first'

_2 :: Lens (c,a) (c,b) a b
_2 = second'
