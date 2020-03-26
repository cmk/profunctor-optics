{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Combinator (
    -- * Constructors
    parr
  , coarr
  , star
  , costar
  , unstar
  , uncostar
    -- * Indexed constructors
  , reix
  , recx
  , ixsum
  , cxsum
  , ixany
  , ixhead
  , ixlast
    -- * Miscellaneous optics
  , ixmap
  , cxmap
  , constl
  , constr
  , shiftl
  , shiftr
  , coercel 
  , coercer
  , represent
  , ixrepresent
  , corepresent
  , cxrepresent
    -- * Operations on representable profunctors
  , (.)
  , (.~)
  , (..~)
  , over
  , (%)
  , (%~)
  , (%%~)
  , overWithKey
  , (#)
  , (#~)
  , (##~)
  , reoverWithKey
  , (*~)
  , (**~)
  , reps
  , repsWithKey
  , (/~)
  , (//~)
  , coreps
  , corepsWithKey
    -- * Arrow-style combinators
  , (<<*>>)
  , (****)
  , (++++)
  , (&&&&)
  , (||||)
  , liftR2
    -- * Divisible-style combinators
  , divide
  , divide'
  , codivide
  , codivide'
  , choose
  , choose'
  , cochoose
  , cochoose'
  , pappend
) where


import Control.Monad.State hiding (join)
import Data.Function
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

parr :: Traversing p => (a -> b) -> p a b 
parr = tabulate . (pure .)
{-# INLINE parr #-}

coarr :: Cotraversing p => (a -> b) -> p a b
coarr = cotabulate . (. copure)
{-# INLINE coarr #-}

star :: Applicative f => Star f a a
star = Star pure
{-# INLINE star #-}

costar :: Coapplicative f => Costar f a a
costar = Costar copure
{-# INLINE costar #-}

unstar :: Coapplicative f => Star f a b -> a -> b
unstar f = copure . runStar f
{-# INLINE unstar #-}

uncostar :: Applicative f => Costar f a b -> a -> b
uncostar f = runCostar f . pure
{-# INLINE uncostar #-}

-- | Map over the indices of an indexed optic.
--
-- See also 'Data.Profunctor.Optic.Iso.reixed'.
--
-- @since 0.0.3
reix :: Profunctor p => (k1 -> k2) -> (k2 -> k1) -> Ixoptic p k1 s t a b -> Ixoptic p k2 s t a b
reix kl lk = (. lmap (first' kl)) . (lmap (first' lk) .)
{-# INLINE reix #-}

-- | Map over the indices of a coindexed optic.
--
-- See also 'Data.Profunctor.Optic.Iso.recxed'.
--
-- @since 0.0.3
recx :: Profunctor p => (k1 -> k2) -> (k2 -> k1) -> Cxoptic p k1 s t a b -> Cxoptic p k2 s t a b
recx kl lk = (. rmap (. kl)) . (rmap (. lk) .)
{-# INLINE recx #-}

-- | Lift a numeric index into a sum monoid.
--
-- @since 0.0.3
ixsum :: Profunctor p => Ixoptic p k s t a b -> Ixoptic p (Sum k) s t a b
ixsum = reix Sum getSum
{-# INLINE ixsum #-}

-- | Lift a numeric co-index into a sum monoid.
--
-- @since 0.0.3
cxsum :: Profunctor p => Cxoptic p k s t a b -> Cxoptic p (Sum k) s t a b
cxsum = recx Sum getSum
{-# INLINE cxsum #-}

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
{-

cxjoin :: Strong p => Cx p a a b -> p a b
cxjoin = peval

cxreturn :: Profunctor p => p a b -> Cx p k a b
cxreturn = rmap const

cxunit :: Strong p => Cx' p :-> p
cxunit p = dimap fork apply (first' p)

-- | 'Cx'' is freely strong.
--
-- See <https://r6research.livejournal.com/27858.html>.
--
cxfirst :: Profunctor p => Cx' p a b -> Cx' p (a, c) (b, c)
cxfirst = dimap fst (B.first @(,))

cxpastro :: Profunctor p => Iso (Cx' p a b) (Cx' p c d) (Pastro p a b) (Pastro p c d)
cxpastro = dimap (\p -> Pastro apply p fork) (\(Pastro l m r) -> dimap (fst . r) (\y a -> l (y, (snd (r a)))) m)
-}

---------------------------------------------------------------------
-- Operations on arbitrary profunctors
---------------------------------------------------------------------

-- | TODO: Document
--
-- @since 0.0.3
ixmap :: Profunctor p => (s -> a) -> (b -> t) -> Ixoptic p k s t a b
ixmap sa bt = dimap (fmap sa) bt
{-# INLINE ixmap #-}

-- | TODO: Document
--
-- @since 0.0.3
cxmap :: Profunctor p => (s -> a) -> (b -> t) -> Cxoptic p k s t a b 
cxmap sa bt = dimap sa (fmap bt)
{-# INLINE cxmap #-}

constl :: Profunctor p => b -> Optic p a c b c
constl = lmap . const
{-# INLINE constl #-}

constr :: Profunctor p => c -> Optic p a c a b
constr = rmap . const
{-# INLINE constr #-}

shiftl :: Profunctor p => Optic p b (c + d) (a + b) c
shiftl = dimap Right Left
{-# INLINE shiftl #-}

shiftr :: Profunctor p => Optic p (a , b) c b (c , d)
shiftr = dimap snd fst
{-# INLINE shiftr #-}

coercel :: Profunctor p => CoercingL p => Optic p c b a b
coercel = B.first absurd . lmap absurd
{-# INLINE coercel #-}

coercer :: Profunctor p => CoercingR p => Optic p a c a b
coercer = rmap absurd . contramap absurd
{-# INLINE coercer #-}

-- | TODO: Document
--
represent :: Representable p => ((a -> Rep p b) -> s -> Rep p t) -> Optic p s t a b
represent f = tabulate . f . sieve
{-# INLINE represent #-}

-- | TODO: Document
--
-- @since 0.0.3
ixrepresent :: Representable p => ((i -> a -> Rep p b) -> s -> Rep p t) -> Ixoptic p i s t a b
ixrepresent f = represent $ \ab -> f (curry ab) . snd
{-# INLINE ixrepresent #-}

-- | TODO: Document
--
corepresent :: Corepresentable p => ((Corep p a -> b) -> Corep p s -> t) -> Optic p s t a b
corepresent f = cotabulate . f . cosieve
{-# INLINE corepresent #-}

-- | TODO: Document
--
-- @since 0.0.3
cxrepresent :: Corepresentable p => ((i -> Corep p a -> b) -> Corep p s -> t) -> Cxoptic p i s t a b
cxrepresent f = corepresent $ \ab -> const . f (flip ab)
{-# INLINE cxrepresent #-}

---------------------------------------------------------------------
-- Operations on representable profunctors
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
over :: Optic (->) s t a b -> (a -> b) -> s -> t
over = id
{-# INLINE over #-}

infixr 4 .~, ..~

-- | Set the focus of an 'Optic'.
--
(.~) :: Optic (->) s t a b -> b -> s -> t
(.~) o b = o (const b)
{-# INLINE (.~) #-}

-- | Map over an 'Optic'.
--
-- >>> (10,20) & first ..~ show 
-- ("10",20)
--
(..~) :: Optic (->) s t a b -> (a -> b) -> s -> t
(..~) = over
{-# INLINE (..~) #-}

infixr 8 %

-- | Monoidally combine indices between subsequent levels of optic.
--
-- Its precedence is one lower than that of function composition, which allows /./ to be nested in /%/.
--
-- If you only need the final index then use /./.
--
-- >>> listsWithKey (ix "*" traversed . ix "+" traversed) ["foo", "bar"]
-- [("",'f'),("+",'o'),("++",'o'),("",'b'),("+",'a'),("++",'r')]
-- >>> listsWithKey (ix "*" traversed % ix "+" traversed) ["foo", "bar"]
-- [("",'f'),("+",'o'),("++",'o'),("*",'b'),("*+",'a'),("*++",'r')]
--
-- @since 0.0.3
(%) :: Monoid i => Representable p => Ixoptic p i c1 c2 b1 b2 -> Ixoptic p i b1 b2 a1 a2 -> Ixoptic p i c1 c2 a1 a2
f % g = ixrepresent . runCoindex $ (Coindex . repsWithKey) f <<<< (Coindex . repsWithKey) g
{-# INLINE (%) #-}
{-
f % g = represent $ \ia1a2 (ic,c1) -> 
          (fmap flip . flip . ixrepn) f ic c1 $ \ib b1 -> 
            (fmap flip . flip . ixrepn) g ib b1 $ \ia a1 -> ia1a2 (ib <> ia, a1)
  where ixrepn o h = curry $ reps o $ uncurry h
-}

infixr 4 %~, %%~, #~, ##~

-- | Set the focus of an indexed optic.
--
-- /Note/: This function is different from the equivalent in the /lens/ package.
-- The /profunctor-optics/ equivalent of /%~/ from /lens/ is '..~'.
--
-- @since 0.0.3
(%~) :: Monoid i => Ixoptic (->) i s t a b -> (i -> b) -> s -> t
(%~) o = overWithKey o . (const .)
{-# INLINE (%~) #-}

-- | Map over an indexed optic.
--
-- @since 0.0.3
(%%~) :: Monoid i => Ixoptic (->) i s t a b -> (i -> a -> b) -> s -> t
(%%~) = overWithKey
{-# INLINE (%%~) #-}

-- | TODO: Document
--
-- @since 0.0.3
overWithKey :: Monoid i => Ixoptic (->) i s t a b -> (i -> a -> b) -> s -> t
overWithKey o f = (unConjoin #. corepresent o .# Conjoin) f mempty
{-# INLINE overWithKey #-}

infixr 8 #

-- | Compose two coindexed traversals, combining indices.
--
-- Its precedence is one lower than that of function composition, which allows /./ to be nested in /#/.
--
-- If you only need the final index then use /./.
--
-- >>> cofoldsWithKey (rxfrom Map.mapWithKey # rxfrom Map.mapWithKey) (\k r a -> Map.singleton k (a + r)) 1.0 $ Map.fromList [("k",Map.fromList [("l",2.0)])]
-- fromList [("k",fromList [("l",fromList [("kl",3.0)])])]
--
-- @since 0.0.3
(#) :: Monoid i => Corepresentable p => Cxoptic p i c1 c2 b1 b2 -> Cxoptic p i b1 b2 a1 a2 -> Cxoptic p i c1 c2 a1 a2
f # g = cxrepresent . runCoindex $ (Coindex . corepsWithKey) f <<<< (Coindex . corepsWithKey) g
{-
f # g = corepresent $ \a1ka2 c1 kc -> 
          (fmap flip . flip . cxrepn) f kc c1 $ \kb b1 -> 
            (fmap flip . flip . cxrepn) g kb b1 $ \ka a1 -> a1ka2 a1 (kb <> ka)
  where cxrepn o f = flip $ coreps o $ flip f
{-# INLINE (#) #-}
-}

-- | Set the focus of a coindexed optic.
--
-- @since 0.0.3
(#~) :: Monoid i => Cxoptic (->) i s t a b -> (i -> b) -> s -> t 
(#~) o = reoverWithKey o . (const .)
{-# INLINE (#~) #-}

-- | Map over a coindexed optic.
-- 
-- @since 0.0.3
(##~) :: Monoid i => Cxoptic (->) i s t a b -> (i -> a -> b) -> s -> t 
(##~) = reoverWithKey
{-# INLINE (##~) #-}

-- | TODO: Document
--
-- @since 0.0.3
reoverWithKey :: Monoid i => Cxoptic (->) i s t a b -> (i -> a -> b) -> s -> t
reoverWithKey o f = (unConjoin #. represent o .# Conjoin) f mempty
{-# INLINE reoverWithKey #-}

infixr 4 *~, **~, /~, //~

-- | Set the focus of a representable optic.
--
-- @since 0.0.3
(*~) :: Optic (Star f) s t a b -> f b -> s -> f t
(*~) o b = o **~ (const b)
{-# INLINE (*~) #-}

-- | Map over a representable optic.
--
-- >>> [66,97,116,109,97,110] & traversed **~ \a -> ("na", chr a)
-- ("nananananana","Batman")
--
-- @since 0.0.3
(**~) :: Optic (Star f) s t a b -> (a -> f b) -> s -> f t
(**~) o = runStar #. o .# Star
{-# INLINE (**~) #-}

-- | TODO: Document
--
reps :: Representable p => Optic p s t a b -> ((a -> Rep p b) -> s -> Rep p t)
reps o = sieve . o . tabulate
{-# INLINE reps #-}

-- | TODO: Document
--
-- @since 0.0.3
repsWithKey :: Representable p => Monoid i => Ixoptic p i s t a b -> (i -> a -> Rep p b) -> s -> Rep p t
repsWithKey o f = curry (reps o $ uncurry f) mempty
{-# INLINE repsWithKey #-}

-- | Set the focus of a co-representable optic.
--
-- @since 0.0.3
(/~) :: Optic (Costar f) s t a b -> b -> f s -> t
(/~) o b = o //~ (const b)
{-# INLINE (/~) #-}

-- | Map over a co-representable optic.
--
-- @since 0.0.3
(//~) :: Optic (Costar f) s t a b -> (f a -> b) -> f s -> t
(//~) o = runCostar #. o .# Costar
{-# INLINE (//~) #-}

-- | TODO: Document
--
coreps :: Corepresentable p => Optic p s t a b -> ((Corep p a -> b) -> Corep p s -> t)
coreps o = cosieve . o . cotabulate
{-# INLINE coreps #-}

-- | TODO: Document
--
-- @since 0.0.3
corepsWithKey :: Corepresentable p => Monoid i => Cxoptic p i s t a b -> (i -> Corep p a -> b) -> Corep p s -> t
corepsWithKey o f = flip (coreps o $ flip f) mempty
{-# INLINE corepsWithKey #-}

---------------------------------------------------------------------
-- Arrow-style combinators
---------------------------------------------------------------------

infixl 4 <<*>>

-- | Profunctor variant of '<*>'.
--
(<<*>>) :: Traversing1 p => p a (b -> c) -> p a b -> p a c
(<<*>>) = liftR2 ($)
{-# INLINE (<<*>>) #-}

infixr 3 ****

-- | Profunctor variant of '***'.
--
(****) :: Traversing1 p => p a1 b1 -> p a2 b2 -> p (a1 , a2) (b1 , b2)
p **** q = dimap fst (,) p <<*>> lmap snd q
{-# INLINE (****) #-}

infixr 2 ++++

-- | Profunctor variant of '+++'.
--
(++++) :: Cotraversing1 p => p a1 b1 -> p a2 b2 -> p (a1 + a2) (b1 + b2)
p ++++ q = cotabulate $ B.bimap (cosieve p) (cosieve q) . coapply
{-# INLINE (++++) #-}

infixr 3 &&&&

-- | Profunctor variant of '&&&'.
--
(&&&&) ::  Traversing1 p => p a b1 -> p a b2 -> p a (b1 , b2)
p &&&& q = liftR2 (,) p q
{-# INLINE (&&&&) #-}

infixr 2 ||||

-- | Profunctor variant of '|||'.
--
(||||) :: Cotraversing1 p => p a1 b -> p a2 b -> p (a1 + a2) b
p |||| q = cotabulate $ either (cosieve p) (cosieve q) . coapply
{-# INLINE (||||) #-}

liftR2 :: Traversing1 p => (b -> c -> d) -> p a b -> p a c -> p a d
liftR2 f x y = tabulate $ \s -> liftF2 f (sieve x s) (sieve y s)
{-# INLINE liftR2 #-}

---------------------------------------------------------------------
-- Divisible-style combinators
---------------------------------------------------------------------

-- | Profunctor variant of < hackage.haskell.org/package/contravariant/docs/Data-Functor-Contravariant-Divisible.html#v:divide divide >.
--
divide :: Traversing1 p => (a -> (a1 , a2)) -> p a1 b -> p a2 b -> p a b
divide f p q = dimap f fst $ p **** q
{-# INLINE divide #-}

divide' :: Traversing1 p => p a1 b -> p a2 b -> p (a1 , a2) b
divide' = divide id
{-# INLINE divide' #-}

codivide :: Cotraversing1 p => ((b1 + b2) -> b) -> p a b1 -> p a b2 -> p a b
codivide f p q = dimap Left f $ p ++++ q
{-# INLINE codivide #-}

codivide' :: Cotraversing1 p => p a b1 -> p a b2 -> p a (b1 + b2)
codivide' = codivide id
{-# INLINE codivide' #-}

-- | Profunctor variant of < hackage.haskell.org/package/contravariant/docs/Data-Functor-Contravariant-Divisible.html#v:choose choose >.
--
choose :: Cotraversing1 p => (a -> (a1 + a2)) -> p a1 b -> p a2 b -> p a b 
choose f p q = dimap f join $ p ++++ q
{-# INLINE choose #-}

choose' :: Cotraversing1 p => p a1 b -> p a2 b -> p (a1 + a2) b 
choose' = choose id
{-# INLINE choose' #-}

cochoose :: Traversing1 p => ((b1 , b2) -> b) -> p a b1 -> p a b2 -> p a b
cochoose f p q = dimap fork f $ p **** q
{-# INLINE cochoose #-}

cochoose' :: Traversing1 p => p a b1 -> p a b2 -> p a (b1, b2)
cochoose' = cochoose id
{-# INLINE cochoose' #-}

pappend :: Traversing1 p => p a b -> p a b -> p a b
pappend = divide fork
{-# INLINE pappend #-}

{-
pushl :: Closed p => Traversing1 p => p a c -> p b c -> p a (b -> c)
pushl p q = curry' $ divide id p q
{-# INLINE pushl #-}

pushr :: Closed p => Traversing1 p => p (a , b) c -> p a b -> p a c
pushr = (<<*>>) . curry' 
{-# INLINE pushr #-}
-}
