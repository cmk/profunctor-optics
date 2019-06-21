module Data.Profunctor.Optic.Over (
    module Data.Profunctor.Optic.Over 
  , module Export
) where


import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Review (re)
import Data.Profunctor.Optic.Type.Task hiding (Context)
import Data.Profunctor.Optic.Prelude hiding (Bifunctor(..))

import Data.Profunctor.Optic.Grate (overGrate, forgotten)
import Data.Profunctor.Mapping as Export

import Control.Applicative (liftA)
import Control.Monad.State as State
import Control.Monad.Writer as Writer
import Control.Monad.Reader as Reader

import Control.Monad.IO.Unlift
import UnliftIO.Exception

--import Data.ByteString (ByteString)
import qualified Control.Exception as Ex

import Data.Profunctor.Optic.Prism
-- TODO put this into doctests
--import Data.Tuple
import Data.Char
import Control.Arrow

import Control.Selective hiding (Over(..))

import Data.Semiring

lift :: (Monoid a, Semiring a) => a -> Over' a a
lift a = over $ \ f y -> a >< f zero <> y

lower :: (Monoid a, Semiring a) => Over' a a -> a
lower a = mapOf a (one <>) zero

-- >>> lower $ zero' + one' :: Int
-- 1
-- >>> lower $ zero' . one' :: Int
-- 0
zero' :: (Monoid a, Semiring a) => Over' a a
zero' = over $ const id

one' :: (Monoid a, Semiring a) => Over' a a
one' = over id

infixl 6 +

(+) :: (Monoid a, Semiring a) => Over' a a -> Over' a a -> Over' a a
(+) = add

add :: (Monoid a, Semiring a) => Over' a a -> Over' a a -> Over' a a
add f g = over $ \h -> (f %~ h) . (g %~ h)



grating :: Functor f => (((s -> f a) -> f b) -> t) -> Over s t a b
grating f = dimap pureTaskF (f . runTask) . map'

unlifting' :: MonadUnliftIO m => Over (m a) (m b) a b
unlifting' = grating withRunInIO

masking' :: MonadUnliftIO m => Over (m a) (m b) a b
masking' = grating mask

clonem :: Forget r1 a1 b1 -> Forget (Maybe r1) a1 b2
clonem = mapOf forgotten (Just .)

---------------------------------------------------------------------
-- Over
---------------------------------------------------------------------

{-
 
over_complete :: Over s t a b -> Bool
over_complete o = tripping o $ mapOf . over 

import Data.Functor.Rep
over :: ((a -> b) -> s -> t) -> Over s t a b
over f = wander $ \g s -> tabulate $ \idx -> f (flip index idx . g) s
-}

-- See http://conal.net/blog/posts/semantic-editor-combinators
over :: ((a -> b) -> s -> t) -> Over s t a b
over f = dimap (Store id) (\(Store g s) -> f g s) . map'


-- | This 'Over' can be used to map contravariantly over the input of a 'Profunctor'.
--
-- The most common 'Profunctor' to use this with is @(->)@.
--
-- >>> (arg %~ f) g x
-- g (f x)
--
-- >>> (arg %~ show) length [1,2,3]
-- 7
--
-- >>> (arg %~ f) h x y
-- h (f x) y
--
-- Map over the arg of the res of a function -- i.e., its second
-- arg:
--
-- >>> (mapped . arg %~ f) h x y
-- h x (f y)
--
-- @
-- 'arg' :: 'Over' (b -> r) (a -> r) a b
-- @
-- 
arg :: Profunctor p => Over (p b r) (p a r) a b
arg = over lmap
{-# INLINE arg #-}

-- | res :: Over (r -> b) (r -> a) b a

res :: Profunctor p => Over (p r a) (p r b) a b
res = over rmap


-- |Using 'set' one can set instead of modify a value using Semantic Editor Combinators
--  for example '(first.set) 1' will set the first value of a tuple to 1
--sets :: a -> b -> a
setting :: Over b (a -> c) a c
setting = over const

-- |Semantic Editor Combinator for Maybe
--just ::  (a -> b) -> Maybe a -> Maybe b
--just = monad

-- |Semantic Editor Combinator for monads
--monad :: Monad m => (a -> b) -> m a -> m b
--monad = liftM -- (>>= return . f)

-- |Semantic Editor Combinator for monadicaly transforming a monadic value
--binds :: Monad m => (a -> m b) -> m a -> m b
--binds f = over (>>= f)




--composed :: Over (a -> b -> s) (a -> b -> t) s t
--composed = over ((.)(.)(.))

{-
currying :: Over a (b -> c) (a, b) c
currying = over curry

uncurrying :: Over (a, b) c a (b -> c)
uncurrying = over uncurry
-}

grated :: Over (a -> b) (s -> t) ((s -> a) -> b) t
grated = over overGrate

reover :: Over (s -> a) ((a -> b) -> s -> t) b t
reover = over between


-- | This 'setter' can be used to modify all of the values in an 'Applicative'.
--
-- @
-- 'lift' ≡ 'over' 'lifted'
-- @
--
-- >>> over lifted f [a,b,c]
-- [f a,f b,f c]
--
-- >>> set lifted b (Just a)
-- Just b
lifted :: Applicative f => Over (f a) (f b) a b
lifted = over liftA
{-# INLINE lifted #-}

-- |Semantic Editor Combinator on each value of a functor
fmapped :: Functor f => Over (f a) (f b) a b
fmapped = over fmap

foldMapped :: (Foldable f, Monoid m) => Over (f a) m a m
foldMapped = over foldMap

filtered :: (Selective f, Alternative f) => Over (f a) (f b) a (Maybe b)
filtered = over filter


-- | Semantic Editor Combinator applying the given function only when the given predicate
--  yields true for an input value.

branched' :: (a -> Bool) -> (a -> a) -> (a -> a)
branched' p f a = if p a then f a else a

-- See https://hackage.haskell.org/package/build-1.0/docs/Build-Task.html#t:Tasks
branched :: (k -> Bool) -> Over' (k -> v) v
branched p = over $ \modify f a -> if p a then modify (f a) else f a

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------


-- mapOf l id ≡ id
-- mapOf l f . mapOf l g ≡ mapOf l (f . g)
--
-- 'mapOf' ('cayley' a) ('Data.Semiring.one' <>) 'Data.Semiring.zero' ≡ a
--
-- ^ @
-- mapOf :: Over s t a b -> (a -> r) -> s -> r
-- mapOf :: Monoid r => Fold s t a b -> (a -> r) -> s -> r
-- @
mapOf :: Optic (->) s t a b -> (a -> b) -> s -> t
mapOf = over id

infixr 4 %~

(%~) :: Optic (->) s t a b -> (a -> b) -> s -> t
(%~) = mapOf
{-# INLINE (%~) #-}

remapOf :: Optic (Re (->) a b) s t a b -> (t -> s) -> (b -> a)
remapOf = re

-- set l y (set l x a) ≡ set l y a
-- \c -> set (over . runCayley $ c) zero one ≡ lowerCayey c
set :: Optic (->) s t a b -> s -> b -> t
set o s b = o (const b) s


infixr 4 .~

(.~) :: Optic (->) s t a b -> s -> b -> t
(.~) = set
{-# INLINE (.~) #-}



infix 4 .=

(.=) :: MonadState s m => b -> Optic (->) s s a b -> m ()
b .= o = assign o b
{-# INLINE (.=) #-}


assign :: MonadState s m => Optic (->) s s a b -> b -> m ()
assign o b = State.modify $ o (const b)
{-# INLINE assign #-}

modifying :: MonadState s m => Optic (->) s s a b -> (a -> b) -> m ()
modifying l f = State.modify (l %~ f)
{-# INLINE modifying #-}

infix 4 %=
{-# INLINE (%=) #-}

(%=) :: MonadState s m => Optic (->) s s a b -> (a -> b) -> m ()
l %= f = modifying l f


(<~) :: MonadState s m => b -> m (Optic (->) s s a b) -> m ()
l <~ mb = mb >>= (l .=)
{-# INLINE (<~) #-}

(%%=) :: MonadState s m => (t -> s -> (b, s)) -> t -> m b
l %%= f = do
  (r, s) <- State.gets (l f)
  State.put s
  return r

{-# INLINE (%%=) #-}

infix 4 %%=



{- |
Modify state and return the modified (new) value.

@
l '<%=' f = do
  l '%=' f
  'use' l
@
-}
--(<%=) :: MonadState s m => LensLike ((,) b) s s a b -> (a -> b) -> m b
l <%= f = l %%= (\a -> (a, a)) . f
{-# INLINE (<%=) #-}

{- |
Modify state and return the old value (i.e. as it was before the modificaton).

@
l '<<%=' f = do
  old <- 'use' l
  l '%=' f
  return old
@
-}
--(<<%=) :: MonadState s m => LensLike ((,) a) s s a b -> (a -> b) -> m a
l <<%= f = l %%= (\a -> (a, f a))
{-# INLINE (<<%=) #-}

{- |
Set state and return the old value.

@
l '<<.=' b = do
  old <- 'use' l
  l '.=' b
  return old
@
-}
--(<<.=) :: MonadState s m => LensLike ((,) a) s s a b -> b -> m a
l <<.= b = l %%= (\a -> (a, b))
{-# INLINE (<<.=) #-}

{- |
Set state and return new value.

@
l '<.=' b = do
  l '.=' b
  return b
@
-}
--(<.=) :: MonadState s m => LensLike ((,) b) s s a b -> b -> m b
l <.= b = l <%= const b
{-# INLINE (<.=) #-}

{- |
('<?=') is a version of ('<.=') that wraps the value into 'Just' before setting.

@
l '<?=' b = do
  l '.=' Just b
  'return' b
@

It can be useful in combination with 'at'.
-}
--(<?=) :: MonadState s m => LensLike ((,) b) s s a (Maybe b) -> b -> m b
l <?= b = l %%= const (b, Just b)
{-# INLINE (<?=) #-}



infix  4 ?=
-- infix  4 <<.=, <<%=, <%=, <.=, <?=
-- infix  4 +=, -=, *=, //=
infixr 2 <~
infixl 1 &~


s &~ l = State.execState l s
{-# INLINE (&~) #-}

l ?= b = undefined --l .= Just b
{-# INLINE (?=) #-}



reset :: Optic (Re (->) a b) s t a b -> b -> s -> a
reset = set . re

appendOver :: Semigroup a => Over s t a a -> a -> s -> t
appendOver o = o . (<>)

{- |
('<>~') appends a value monoidally to the target.

>>> ("hello", "goodbye") & both <>~ " world!"
("hello world!", "goodbye world!")
-}
infixr 4 <>~
{-# INLINE (<>~) #-}

(<>~) :: Semigroup a => Over s t a a -> a -> s -> t
(<>~) p a = appendOver p a


{- |
('?~') is a version of ('.~') that wraps the value into 'Just' before setting.

@
l ?~ b = l .~ Just b
@

It can be useful in combination with 'at':

>>> Map.empty & at 3 ?~ x
fromList [(3,x)]
-}
--(?~) :: Over s t a (Maybe b) -> b -> s -> t
(?~) :: Optic (->) (Maybe a1) t a2 b -> a1 -> b -> t
o ?~ b = set o (Just b)
{-# INLINE (?~) #-}

infixr 4 ?~

--setJust :: Optic (->) s t a (Maybe b) -> b -> s -> t
--setJust :: Over s t a (Maybe b) -> b -> s -> t
setJust :: Optic (->) (Maybe s) t a b -> s -> b -> t
setJust o = set o . Just


-- | Logically '||' the target(s) of a 'Bool'-valued 'Lens' or 'Over'.
--
-- >>> both ||~ True $ (False,True)
-- (True,True)
--
-- >>> both ||~ False $ (False,True)
-- (False,True)
--
-- @
-- ('||~') :: 'Over'' s 'Bool'    -> 'Bool' -> s -> s
-- ('||~') :: 'Iso'' s 'Bool'       -> 'Bool' -> s -> s
-- ('||~') :: 'Lens'' s 'Bool'      -> 'Bool' -> s -> s
-- ('||~') :: 'Traversal'' s 'Bool' -> 'Bool' -> s -> s
-- @
(||~):: Optic (->) s t Bool Bool -> Bool -> s -> t
o ||~ n = o (|| n)
{-# INLINE (||~) #-}

-- | Logically '&&' the target(s) of a 'Bool'-valued 'Lens' or 'Over'.
--
-- >>> both &&~ True $ (False, True)
-- (False,True)
--
-- >>> both &&~ False $ (False, True)
-- (False,False)
--
-- @
-- ('&&~') :: 'Over'' s 'Bool'    -> 'Bool' -> s -> s
-- ('&&~') :: 'Iso'' s 'Bool'       -> 'Bool' -> s -> s
-- ('&&~') :: 'Lens'' s 'Bool'      -> 'Bool' -> s -> s
-- ('&&~') :: 'Traversal'' s 'Bool' -> 'Bool' -> s -> s
-- @
(&&~) :: Optic (->) s t Bool Bool -> Bool -> s -> t
o &&~ n = o (&& n)
{-# INLINE (&&~) #-}

-----------------------------------------------------------------------------
-- Writer Operations
-----------------------------------------------------------------------------

-- | Write to a fragment of a larger 'Writer' format.
--scribe :: (MonadWriter t m, Monoid s) => AOver s t a b -> b -> m ()
scribe :: (MonadWriter t m, Monoid s) => Optic (->) s t a b -> b -> m ()
scribe o b = tell (set o mempty b)
{-# INLINE scribe #-}

-- | This is a generalization of 'pass' that allows you to modify just a
-- portion of the resing 'MonadWriter'.
passing :: MonadWriter s m => Optic (->) s s a b -> m (r, a -> b) -> m r
passing o m = pass $ do
  (a, uv) <- m
  return (a, o uv)
{-# INLINE passing #-}

-- | This is a generalization of 'censor' that allows you to 'censor' just a
-- portion of the resing 'MonadWriter'.
--censoring :: MonadWriter w m => Over w w u v -> (u -> v) -> m a -> m a
censoring :: MonadWriter s m => Optic (->) s s a b -> (a -> b) -> m c -> m c
censoring o uv = censor $ o uv
{-# INLINE censoring #-}

-----------------------------------------------------------------------------
-- Reader Operations
-----------------------------------------------------------------------------

-- | Modify the value of the 'Reader' env associated with the target of a
-- 'Over', 'Lens', or 'Traversal'.
--
-- @
-- 'locally' l 'id' a ≡ a
-- 'locally' l f '.' locally l g ≡ 'locally' l (f '.' g)
-- @
--
-- >>> (1,1) & locally _1 (+1) (uncurry (+))
-- 3
--
-- >>> "," & locally ($) ("Hello" <>) (<> " world!")
-- "Hello, world!"
--
-- @
-- locally :: MonadReader s m => 'Iso' s s a b       -> (a -> b) -> m r -> m r
-- locally :: MonadReader s m => 'Lens' s s a b      -> (a -> b) -> m r -> m r
-- locally :: MonadReader s m => 'Traversal' s s a b -> (a -> b) -> m r -> m r
-- locally :: MonadReader s m => 'Over' s s a b    -> (a -> b) -> m r -> m r
-- @
locally :: MonadReader s m => Optic (->) s s a b -> (a -> b) -> m r -> m r
locally o f = Reader.local $ o f
{-# INLINE locally #-}
