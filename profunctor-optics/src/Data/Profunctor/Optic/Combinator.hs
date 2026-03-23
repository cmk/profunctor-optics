{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
module Data.Profunctor.Optic.Combinator (
    -- * Constructors
    -- ** Main
    star
  , unstar
  , ixmap
  , representing
  , ixrepresenting
    -- ** Dual
  , costar
  , uncostar
  , cxmap
  , corepresenting
  , cxrepresenting
    -- ** Cx algebra
  , cxjoin
  , cxreturn
  , cxunit
  , cxstrength
    -- * Transforms
    -- ** Main
  , (%)
  , reix
  , ixsum
  , ixany
  , ixhead
  , ixlast
  , arr
  , (***)
  , (&&&)
  , (<<*>>)
  , liftR2
  , pappend
  , divide
  , divideWith
  , cochoose
  , cochooseWith
    -- ** Dual
  , (#)
  , recx
  , cxsum
  , coarr
  , (+++)
  , (|||)
  , choose
  , chooseWith
  , codivide
  , codivideWith
    -- * Optics
  , constL
  , constR
  , shiftedL
  , shiftedR
  , coercedL
  , coercedR
    -- * Operators
  , over
    -- ** Main
  , ixover
  , reps
  , ixreps
    -- ** Dual
  , cxover
  , coreps
  , cxreps
) where


import Data.Profunctor.Strong
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Import
import qualified Data.Bifunctor as B
import qualified Data.Semigroup as S

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XRankNTypes
-- >>> import Data.Char
-- >>> import Data.Function ((&))
-- >>> import Data.Semigroup
-- >>> import qualified Data.Bifunctor as B
-- >>> import qualified Data.Map.Lazy as Map
-- >>> :load Data.Profunctor.Optic
-- >>> import Prelude

---------------------------------------------------------------------
-- Constructors
---------------------------------------------------------------------

-- ** Main

-- | TODO: Document
--
star :: Applicative f => Star f a a
star = Star pure
{-# INLINE star #-}

-- | TODO: Document
--
unstar :: Coapplicative f => Star f a b -> a -> b
unstar f = copure . runStar f
{-# INLINE unstar #-}

-- | 'dimap' for indexed optics. Maps over the outer types of an
-- 'Ixoptic' without affecting the index.
--
-- @since 0.0.3
ixmap :: Profunctor p => (s -> a) -> (b -> t) -> Ixoptic p k s t a b
ixmap sa bt = dimap (fmap sa) bt
{-# INLINE ixmap #-}

-- | TODO: Document
--
representing :: Representable p => ((a -> Rep p b) -> s -> Rep p t) -> Optic p s t a b
representing f = tabulate . f . sieve
{-# INLINE representing #-}

-- | TODO: Document
--
-- @since 0.0.3
ixrepresenting :: Representable p => ((i -> a -> Rep p b) -> s -> Rep p t) -> Ixoptic p i s t a b
ixrepresenting f = representing $ \ab -> f (curry ab) . snd
{-# INLINE ixrepresenting #-}

-- ** Dual

-- | TODO: Document
--
costar :: Coapplicative f => Costar f a a
costar = Costar copure
{-# INLINE costar #-}

-- | TODO: Document
--
uncostar :: Applicative f => Costar f a b -> a -> b
uncostar f = runCostar f . pure
{-# INLINE uncostar #-}

-- | 'dimap' for coindexed optics. Maps over the outer types of a
-- 'Cxoptic' without affecting the coindex.
--
-- @since 0.0.3
cxmap :: Profunctor p => (s -> a) -> (b -> t) -> Cxoptic p k s t a b
cxmap sa bt = dimap sa (fmap bt)
{-# INLINE cxmap #-}

-- | TODO: Document
--
corepresenting :: Corepresentable p => ((Corep p a -> b) -> Corep p s -> t) -> Optic p s t a b
corepresenting f = cotabulate . f . cosieve
{-# INLINE corepresenting #-}

-- | TODO: Document
--
-- @since 0.0.3
cxrepresenting :: Corepresentable p => ((i -> Corep p a -> b) -> Corep p s -> t) -> Cxoptic p i s t a b
cxrepresenting f = corepresenting $ \ab -> const . f (flip ab)
{-# INLINE cxrepresenting #-}

-- | Collapse a coindexed profunctor where the coindex matches the focus.
--
-- @'cxjoin' ≡ 'dimap' 'fork' 'apply' '.' 'first''@
--
cxjoin :: Strong p => Cx p a a b -> p a b
cxjoin = dimap fork apply . first'

-- | Lift a profunctor into a coindexed profunctor by ignoring the coindex.
--
cxreturn :: Profunctor p => p a b -> Cx p k a b
cxreturn = rmap const

-- | Extract a profunctor from a self-coindexed profunctor.
--
-- @'cxjoin' '.' 'cxunit' ≡ 'id'@
--
cxunit :: Strong p => Cx' p a b -> p a b
cxunit p = dimap fork apply (first' p)

-- | 'Cx'' is freely 'Strong'.
--
-- See <https://r6research.livejournal.com/27858.html>.
--
cxstrength :: Profunctor p => Cx' p a b -> Cx' p (a, c) (b, c)
cxstrength = dimap fst (B.first @(,))

---------------------------------------------------------------------
-- Transforms
---------------------------------------------------------------------

-- ** Main

infixr 8 %

-- | Monoidally combine indices between subsequent levels of optic.
--
-- Its precedence is one lower than that of function composition, which allows /./ to be nested in /%/.
--
-- If you only need the final index then use /./.
--
-- >>> ixtoListOf (ix "*" traversed . ix "+" traversed) ["foo", "bar"]
-- [("",'f'),("+",'o'),("++",'o'),("",'b'),("+",'a'),("++",'r')]
-- >>> ixtoListOf (ix "*" traversed % ix "+" traversed) ["foo", "bar"]
-- [("",'f'),("+",'o'),("++",'o'),("*",'b'),("*+",'a'),("*++",'r')]
--
-- @since 0.0.3
(%) :: Monoid i => Representable p => Ixoptic p i c1 c2 b1 b2 -> Ixoptic p i b1 b2 a1 a2 -> Ixoptic p i c1 c2 a1 a2
f % g = ixrepresenting . runCoindex $ (Coindex . ixreps) f <<<< (Coindex . ixreps) g
{-# INLINE (%) #-}
{-
f % g = representing $ \ia1a2 (ic,c1) ->
          (fmap flip . flip . ixrepn) f ic c1 $ \ib b1 ->
            (fmap flip . flip . ixrepn) g ib b1 $ \ia a1 -> ia1a2 (ib <> ia, a1)
  where ixrepn o h = curry $ reps o $ uncurry h
-}

-- | Map over the indices of an indexed optic.
--
-- See also 'Data.Profunctor.Optic.Iso.reixed'.
--
-- @since 0.0.3
reix :: Profunctor p => (k1 -> k2) -> (k2 -> k1) -> Ixoptic p k1 s t a b -> Ixoptic p k2 s t a b
reix kl lk = (. lmap (first' kl)) . (lmap (first' lk) .)
{-# INLINE reix #-}

-- | Lift a numeric index into a sum monoid.
--
-- @since 0.0.3
ixsum :: Profunctor p => Ixoptic p k s t a b -> Ixoptic p (Sum k) s t a b
ixsum = reix Sum getSum
{-# INLINE ixsum #-}

-- | TODO: Document
--
ixany :: Profunctor p => Ixoptic p Bool s t a b -> Ixoptic p Any s t a b
ixany = reix Any getAny
{-# INLINE ixany #-}

-- | TODO: Document
--
-- @since 0.0.3
ixhead :: Profunctor p => Ixoptic p i s t a b -> Ixoptic p (S.First i) s t a b
ixhead = reix S.First S.getFirst

-- | TODO: Document
--
-- @since 0.0.3
ixlast :: Profunctor p => Ixoptic p i s t a b -> Ixoptic p (S.Last i) s t a b
ixlast = reix S.Last S.getLast

-- | TODO: Document
--
arr :: Traversing p => (a -> b) -> p a b
arr = tabulate . (pure .)
{-# INLINE arr #-}

infixr 3 ***

-- | Profunctor variant of 'Control.Arrow.***'.
--
(***) :: Traversing1 p => p a1 b1 -> p a2 b2 -> p (a1 , a2) (b1 , b2)
p *** q = dimap fst (,) p <<*>> lmap snd q
{-# INLINE (***) #-}

infixr 3 &&&

-- | Profunctor variant of 'Control.Arrow.&&&'.
--
(&&&) ::  Traversing1 p => p a b1 -> p a b2 -> p a (b1 , b2)
p &&& q = liftR2 (,) p q
{-# INLINE (&&&) #-}

infixl 4 <<*>>

-- | Profunctor variant of '<*>'.
--
(<<*>>) :: Traversing1 p => p a (b -> c) -> p a b -> p a c
(<<*>>) = liftR2 ($)
{-# INLINE (<<*>>) #-}

liftR2 :: Traversing1 p => (b -> c -> d) -> p a b -> p a c -> p a d
liftR2 f x y = tabulate $ \s -> liftF2 f (sieve x s) (sieve y s)
{-# INLINE liftR2 #-}

-- | TODO: Document
--
pappend :: Traversing1 p => p a b -> p a b -> p a b
pappend = divideWith fork
{-# INLINE pappend #-}

-- | TODO: Document
--
divide :: Traversing1 p => p a1 b -> p a2 b -> p (a1 , a2) b
divide = divideWith id
{-# INLINE divide #-}

-- | Profunctor variant of < hackage.haskell.org/package/contravariant/docs/Data-Functor-Contravariant-Divisible.html#v:divideWith divideWith >.
--
divideWith :: Traversing1 p => (a -> (a1 , a2)) -> p a1 b -> p a2 b -> p a b
divideWith f p q = dimap f fst $ p *** q
{-# INLINE divideWith #-}

-- | TODO: Document
--
cochoose :: Traversing1 p => p a b1 -> p a b2 -> p a (b1, b2)
cochoose = cochooseWith id
{-# INLINE cochoose #-}

-- | TODO: Document
--
cochooseWith :: Traversing1 p => ((b1 , b2) -> b) -> p a b1 -> p a b2 -> p a b
cochooseWith f p q = dimap fork f $ p *** q
{-# INLINE cochooseWith #-}

-- ** Dual

infixr 8 #

-- | Compose two coindexed traversals, combining indices.
--
-- Its precedence is one lower than that of function composition, which allows /./ to be nested in /#/.
--
-- If you only need the final index then use /./.
--
-- >>> cxfoldMapOf (cxfrom Map.mapWithKey # cxfrom Map.mapWithKey) (\k r a -> Map.singleton k (a + r)) 1.0 $ Map.fromList [("k",Map.fromList [("l",2.0)])]
-- fromList [("k",fromList [("l",fromList [("kl",3.0)])])]
--
-- @since 0.0.3
(#) :: Monoid i => Corepresentable p => Cxoptic p i c1 c2 b1 b2 -> Cxoptic p i b1 b2 a1 a2 -> Cxoptic p i c1 c2 a1 a2
f # g = cxrepresenting . runCoindex $ (Coindex . cxreps) f <<<< (Coindex . cxreps) g
{-
f # g = corepresenting $ \a1ka2 c1 kc ->
          (fmap flip . flip . cxrepn) f kc c1 $ \kb b1 ->
            (fmap flip . flip . cxrepn) g kb b1 $ \ka a1 -> a1ka2 a1 (kb <> ka)
  where cxrepn o f = flip $ coreps o $ flip f
{-# INLINE (#) #-}
-}

-- | Map over the indices of a coindexed optic.
--
-- See also 'Data.Profunctor.Optic.Iso.recxed'.
--
-- @since 0.0.3
recx :: Profunctor p => (k1 -> k2) -> (k2 -> k1) -> Cxoptic p k1 s t a b -> Cxoptic p k2 s t a b
recx kl lk = (. rmap (. kl)) . (rmap (. lk) .)
{-# INLINE recx #-}

-- | Lift a numeric co-index into a sum monoid.
--
-- @since 0.0.3
cxsum :: Profunctor p => Cxoptic p k s t a b -> Cxoptic p (Sum k) s t a b
cxsum = recx Sum getSum
{-# INLINE cxsum #-}

-- | TODO: Document
--
coarr :: Cotraversing p => (a -> b) -> p a b
coarr = cotabulate . (. copure)
{-# INLINE coarr #-}

infixr 2 +++

-- | Profunctor variant of 'Control.Arrow.+++'.
--
(+++) :: Cotraversing1 p => p a1 b1 -> p a2 b2 -> p (a1 + a2) (b1 + b2)
p +++ q = cotabulate $ B.bimap (cosieve p) (cosieve q) . coapply
{-# INLINE (+++) #-}

infixr 2 |||

-- | Profunctor variant of 'Control.Arrow.|||'.
--
(|||) :: Cotraversing1 p => p a1 b -> p a2 b -> p (a1 + a2) b
p ||| q = cotabulate $ either (cosieve p) (cosieve q) . coapply
{-# INLINE (|||) #-}

-- | TODO: Document
--
choose :: Cotraversing1 p => p a1 b -> p a2 b -> p (a1 + a2) b
choose = chooseWith id
{-# INLINE choose #-}

-- | Profunctor variant of < hackage.haskell.org/package/contravariant/docs/Data-Functor-Contravariant-Divisible.html#v:chooseWith chooseWith >.
--
chooseWith :: Cotraversing1 p => (a -> (a1 + a2)) -> p a1 b -> p a2 b -> p a b
chooseWith f p q = dimap f join $ p +++ q
{-# INLINE chooseWith #-}

-- | TODO: Document
--
codivide :: Cotraversing1 p => p a b1 -> p a b2 -> p a (b1 + b2)
codivide = codivideWith id
{-# INLINE codivide #-}

-- | TODO: Document
--
codivideWith :: Cotraversing1 p => ((b1 + b2) -> b) -> p a b1 -> p a b2 -> p a b
codivideWith f p q = dimap Left f $ p +++ q
{-# INLINE codivideWith #-}

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

constL :: Profunctor p => b -> Optic p a c b c
constL = lmap . const
{-# INLINE constL #-}

constR :: Profunctor p => c -> Optic p a c a b
constR = rmap . const
{-# INLINE constR #-}

shiftedL :: Profunctor p => Optic p b (c + d) (a + b) c
shiftedL = dimap Right Left
{-# INLINE shiftedL #-}

shiftedR :: Profunctor p => Optic p (a , b) c b (c , d)
shiftedR = dimap snd fst
{-# INLINE shiftedR #-}

coercedL :: Profunctor p => CoercingL p => Optic p c b a b
coercedL = B.first absurd . lmap absurd
{-# INLINE coercedL #-}

coercedR :: Profunctor p => CoercingR p => Optic p a c a b
coercedR = rmap absurd . contramap absurd
{-# INLINE coercedR #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Map over an 'Optic'.
--
-- @
-- 'over' o 'id' ≡ 'id'
-- 'over' o f '.' 'over' o g ≡ 'over' o (f '.' g)
-- 'over' '.' 'setter' ≡ 'id'
-- 'over' '.' 'resetter' ≡ 'id'
-- @
--
-- >>> over fmapped (+1) (Just 1)
-- Just 2
-- >>> over fmapped (*10) [1,2,3]
-- [10,20,30]
-- >>> over first (+1) (1,2)
-- (2,2)
-- >>> over first show (10,20)
-- ("10",20)
--
-- /Benchmark: 1.00x vs direct (Lens), 0.89x vs fmap (Traversal). See "Data.Profunctor.Optic.Bench"./
--
over :: Optic (->) s t a b -> (a -> b) -> s -> t
over = id
{-# INLINE over #-}

-- ** Main

-- | Indexed 'over': apply a key-dependent function through an indexed optic.
--
-- Routes through 'Conjoin' wrapping internally.
--
-- /Benchmark: 1.08x vs direct mapWithKey (Conjoin overhead negligible). See "Data.Profunctor.Optic.Bench"./
--
-- @since 0.0.3
ixover :: Monoid i => Ixoptic (->) i s t a b -> (i -> a -> b) -> s -> t
ixover o f = (unConjoin #. corepresenting o .# Conjoin) f mempty
{-# INLINE ixover #-}

-- | TODO: Document
--
reps :: Representable p => Optic p s t a b -> ((a -> Rep p b) -> s -> Rep p t)
reps o = sieve . o . tabulate
{-# INLINE reps #-}

-- | TODO: Document
--
-- @since 0.0.3
ixreps :: Representable p => Monoid i => Ixoptic p i s t a b -> (i -> a -> Rep p b) -> s -> Rep p t
ixreps o f = curry (reps o $ uncurry f) mempty
{-# INLINE ixreps #-}

-- ** Dual

-- | Coindexed 'over': apply a coindex-dependent function through a coindexed optic.
--
-- Routes through 'Conjoin' wrapping internally (dual of 'overWithKey').
--
-- /Benchmark: ~1.08x overhead (same Conjoin path as 'overWithKey'). See "Data.Profunctor.Optic.Bench"./
--
-- @since 0.0.3
cxover :: Monoid i => Cxoptic (->) i s t a b -> (i -> a -> b) -> s -> t
cxover o f = (unConjoin #. representing o .# Conjoin) f mempty
{-# INLINE cxover #-}

-- | TODO: Document
--
coreps :: Corepresentable p => Optic p s t a b -> ((Corep p a -> b) -> Corep p s -> t)
coreps o = cosieve . o . cotabulate
{-# INLINE coreps #-}

-- | TODO: Document
--
-- @since 0.0.3
cxreps :: Corepresentable p => Monoid i => Cxoptic p i s t a b -> (i -> Corep p a -> b) -> Corep p s -> t
cxreps o f = flip (coreps o $ flip f) mempty
{-# INLINE cxreps #-}
