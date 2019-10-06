module Data.Profunctor.Optic.Setter where


import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Review (re)
import Data.Profunctor.Task
import Data.Profunctor.Optic.Prelude hiding (Bifunctor(..))
import Data.Profunctor.Optic.Grate (overGrate, withGrate, env, forgotten)
--import Data.Profunctor.Mapping as Export

import Control.Applicative (liftA)
import Control.Monad.State as State
import Control.Monad.Writer as Writer
import Control.Monad.Reader as Reader

--import Data.ByteString (ByteString)
import qualified Control.Exception as Ex

import Data.Profunctor.Optic.Prism
-- TODO put this into doctests
--import Data.Tuple
import Data.Char



import qualified Data.Functor.Rep as F


{-
fromGrate :: Grate s t a b -> Setter s t a b
fromGrate x = withGrate x (\sabt -> setting $ overGrate sabt)
-}

over :: (Representable p, F.Representable (Rep p)) => ((a -> b) -> s -> t) -> p a b -> p s t
over f = wander $ \g s -> F.tabulate $ \idx -> f (extract idx g) s

extract :: F.Representable f => F.Rep f -> (a -> f c) -> a -> c
extract i g = flip F.index i . g

{-

arr :: Decisive f => (b -> c) -> Costar f b c
arr f = Costar (f . copure)

--filtered :: (Selective f, Alternative f) => Setter (f a) (f b) a (Maybe b)
--filtered = setting filter

lift :: (Monoid a, Semiring a) => a -> Setter' a a
lift a = setting $ \ f y -> a >< f zero <> y

lower :: (Monoid a, Semiring a) => Setter' a a -> a
lower a = mapOf a (one <>) zero

-- >>> lower $ zero' + one' :: Int
-- 1
-- >>> lower $ zero' . one' :: Int
-- 0
zero' :: (Monoid a, Semiring a) => Setter' a a
zero' = setting $ const id

one' :: (Monoid a, Semiring a) => Setter' a a
one' = setting id

add :: (Monoid a, Semiring a) => Setter' a a -> Setter' a a -> Setter' a a
add f g = setting $ \h -> (f %~ h) . (g %~ h)
-}


grating :: Functor f => (((s -> f a) -> f b) -> t) -> Setter s t a b
grating f = dimap pureTaskF (f . runTask) . wander collect

--unlifting' :: MonadUnliftIO m => Setter (m a) (m b) a b
--unlifting' = grating withRunInIO

masking' :: Setter (IO a) (IO b) a b
masking' = grating Ex.mask

clonem :: Forget r1 a1 b1 -> Forget (Maybe r1) a1 b2
clonem = mapOf forgotten (Just .)

---------------------------------------------------------------------
-- Setter
---------------------------------------------------------------------

collectOf :: (Applicative f, Distributive f)
          => Optic (Star (WrappedApplicative f)) s t a b
          -> (a -> f b) -> s -> f t
collectOf o f = unwrapApplicative . runStar (o (Star (WrapApplicative . f)))

{-



import Data.Functor.Rep
setting :: ((a -> b) -> s -> t) -> Setter s t a b
setting f = wander $ \g s -> tabulate $ \idx -> f (flip index idx . g) s


setter_complete :: Setter s t a b -> Setter s t a b
setter_complete = mapOf . setting

In soundness proof, we have to eta-expand g:

setter_sound_proof :: ()
setter_sound_proof =
    (\f g s -> setting (setting f) g s)
    ===
    (\f g s -> f (\x -> g x) s)
Another way is to say that collectOf and collecting are the basic operations:

setter_complete_2 :: Setter s t a b -> Setter s t a b
setter_complete_2 o = collecting (collectOf o)

-}

-- | 'setting' promotes a \"semantic editor combinator\" to a modify-only lens.
--
-- To demote a lens to a semantic edit combinator, use the section @(l %~)@ or @mapOf l@.
--
-- >>> [("The",0),("quick",1),("brown",1),("fox",2)] & setting map . fstL %~ length
-- [(3,0),(5,1),(5,1),(3,2)]
--
-- /Caution/: In order for the generated family to be well-defined, you must ensure that the two functors laws hold:
--
-- * @sec id === id@
--
-- * @sec f . sec g === sec (f . g)@
--
-- See <http://conal.net/blog/posts/semantic-editor-combinators>
--
setting :: ((a -> b) -> s -> t) -> Setter s t a b
setting sec = dimap (Store id) (\(Store g s) -> sec g s) . wander collect

-- | 'resetting' promotes a \"semantic editor combinator\" to a form of grate that can only lift unary functions.
--
-- /Caution/: In order for the generated family to be well-defined, you must ensure that the two functors laws hold:
--
-- * @sec id === id@
--
-- * @sec f . sec g === sec (f . g)@
--
--resetting :: ((a -> b) -> s -> t) -> Grate s t a b
--resetting sec f = sec (f . pure) . extract


-- | This 'Setter' can be used to map contravariantly setting the input of a 'Profunctor'.
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
-- Map setting the arg of the res of a function -- i.e., its second
-- arg:
--
-- >>> (mapped . arg %~ f) h x y
-- h x (f y)
--
-- @
-- 'arg' :: 'Setter' (b -> r) (a -> r) a b
-- @
-- 
arg :: Profunctor p => Setter (p b r) (p a r) a b
arg = setting lmap
{-# INLINE arg #-}

-- | res :: Setter (r -> b) (r -> a) b a

res :: Profunctor p => Setter (p r a) (p r b) a b
res = setting rmap

-- |Using 'set' one can set instead of modify a value using Semantic Editor Combinators
--  for example '(first.set) 1' will set the first value of a tuple to 1
--sets :: a -> b -> a
sets :: Setter b (a -> c) a c
sets = setting const

grated :: Setter (a -> b) (s -> t) ((s -> a) -> b) t
grated = setting overGrate

modded :: Setter (b -> t) (((s -> a) -> b) -> t) s a
modded = setting env

composed :: Setter (s -> a) ((a -> b) -> s -> t) b t
composed = setting between

composing :: Setter (u -> v -> a) (u -> v -> b) a b
composing = setting ((.)(.)(.))

collecting :: Functor f => Distributive g => Setter (f a) (g (f b)) a (g b)
collecting = setting collect

-- | Semantic Editor Combinator for monadicaly transforming a monadic value
binding :: Monad m => Setter (m a) (m b) a (m b)
binding = setting (=<<)

-- |Semantic Editor Combinator on each value of a functor
fmapped :: Functor f => Setter (f a) (f b) a b
fmapped = setting fmap

foldMapped :: (Foldable f, Monoid m) => Setter (f a) m a m
foldMapped = setting foldMap

-- | This 'setter' can be used to modify all of the values in an 'Applicative'.
--
-- @
-- 'liftA' ≡ 'setting' 'liftedA'
-- @
--
-- >>> setting liftedA f [a,b,c]
-- [f a,f b,f c]
--
-- >>> set liftedA b (Just a)
-- Just b
liftedA :: Applicative f => Setter (f a) (f b) a b
liftedA = setting liftA

liftedM :: Monad m => Setter (m a) (m b) a b
liftedM = setting liftM

-- | Semantic Editor Combinator applying the given function only when the given predicate
--  yields true for an input value.
branching :: (a -> Bool) -> Setter' a a
branching p = setting $ \f a -> if p a then f a else a

-- See https://hackage.haskell.org/package/build-1.0/docs/Build-Task.html#t:Tasks
branched :: (k -> Bool) -> Setter' (k -> v) v
branched p = setting $ \mod f a -> if p a then mod (f a) else f a

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------


-- mapOf l id ≡ id
-- mapOf l f . mapOf l g ≡ mapOf l (f . g)
--
-- 'mapOf' ('cayley' a) ('Data.Semiring.one' <>) 'Data.Semiring.zero' ≡ a
--
-- ^ @
-- mapOf :: Setter s t a b -> (a -> r) -> s -> r
-- mapOf :: Monoid r => Fold s t a b -> (a -> r) -> s -> r
-- @
mapOf :: Optic (->) s t a b -> (a -> b) -> s -> t
mapOf = id

infixr 4 %~

(%~) :: Optic (->) s t a b -> (a -> b) -> s -> t
(%~) = id
{-# INLINE (%~) #-}

remapOf :: Optic (Re (->) a b) s t a b -> (t -> s) -> (b -> a)
remapOf = re

-- set l y (set l x a) ≡ set l y a
-- \c -> set (setting . runCayley $ c) zero one ≡ lowerCayey c
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

appendSetter :: Semigroup a => Setter s t a a -> a -> s -> t
appendSetter o = o . (<>)

{- |
('<>~') appends a value monoidally to the target.

>>> ("hello", "goodbye") & both <>~ " world!"
("hello world!", "goodbye world!")
-}
infixr 4 <>~
{-# INLINE (<>~) #-}

(<>~) :: Semigroup a => Setter s t a a -> a -> s -> t
(<>~) p a = appendSetter p a


{- |
('?~') is a version of ('.~') that wraps the value into 'Just' before setting.

@
l ?~ b = l .~ Just b
@

It can be useful in combination with 'at':

>>> Map.empty & at 3 ?~ x
fromList [(3,x)]
-}
--(?~) :: Setter s t a (Maybe b) -> b -> s -> t
(?~) :: Optic (->) (Maybe a1) t a2 b -> a1 -> b -> t
o ?~ b = set o (Just b)
{-# INLINE (?~) #-}

infixr 4 ?~

--setJust :: Optic (->) s t a (Maybe b) -> b -> s -> t
--setJust :: Setter s t a (Maybe b) -> b -> s -> t
setJust :: Optic (->) (Maybe s) t a b -> s -> b -> t
setJust o = set o . Just


-- | Logically '||' the target(s) of a 'Bool'-valued 'Lens' or 'Setter'.
--
-- >>> both ||~ True $ (False,True)
-- (True,True)
--
-- >>> both ||~ False $ (False,True)
-- (False,True)
--
-- @
-- ('||~') :: 'Setter'' s 'Bool'    -> 'Bool' -> s -> s
-- ('||~') :: 'Iso'' s 'Bool'       -> 'Bool' -> s -> s
-- ('||~') :: 'Lens'' s 'Bool'      -> 'Bool' -> s -> s
-- ('||~') :: 'Traversal'' s 'Bool' -> 'Bool' -> s -> s
-- @
(||~):: Optic (->) s t Bool Bool -> Bool -> s -> t
o ||~ n = o (|| n)
{-# INLINE (||~) #-}

-- | Logically '&&' the target(s) of a 'Bool'-valued 'Lens' or 'Setter'.
--
-- >>> both &&~ True $ (False, True)
-- (False,True)
--
-- >>> both &&~ False $ (False, True)
-- (False,False)
--
-- @
-- ('&&~') :: 'Setter'' s 'Bool'    -> 'Bool' -> s -> s
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
--scribe :: (MonadWriter t m, Monoid s) => ASetter s t a b -> b -> m ()
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
--censoring :: MonadWriter w m => Setter w w u v -> (u -> v) -> m a -> m a
censoring :: MonadWriter s m => Optic (->) s s a b -> (a -> b) -> m c -> m c
censoring o uv = censor $ o uv
{-# INLINE censoring #-}

-----------------------------------------------------------------------------
-- Reader Operations
-----------------------------------------------------------------------------

-- | Modify the value of the 'Reader' env associated with the target of a
-- 'Setter', 'Lens', or 'Traversal'.
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
-- locally :: MonadReader s m => 'Setter' s s a b    -> (a -> b) -> m r -> m r
-- @
locally :: MonadReader s m => Optic (->) s s a b -> (a -> b) -> m r -> m r
locally o f = Reader.local $ o f
{-# INLINE locally #-}
