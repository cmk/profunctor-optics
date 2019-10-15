module Data.Profunctor.Optic.Setter where


import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Review (re)
import Data.Profunctor.Task
import Data.Profunctor.Optic.Prelude hiding (Bifunctor(..))
import Data.Profunctor.Optic.Grate -- (withGrate, forgotten)

import Control.Applicative (liftA)
import Control.Monad.State as State hiding (lift)
import Control.Monad.Writer as Writer hiding (lift)
import Control.Monad.Reader as Reader hiding (lift)

import qualified Control.Exception as Ex

import Data.Profunctor.Optic.Prism



import qualified Data.Functor.Rep as F

import qualified Data.Functor.Contravariant.Rep as C
{-


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

---------------------------------------------------------------------
-- Setter
---------------------------------------------------------------------

--over' :: F.Representable (Rep p) => ((a -> b) -> s -> t) -> Over p s t a b
--over' f = lift $ \afb s -> F.tabulate $ \i -> f (flip F.index i . afb) s

{-
tabulate :: (a -> Rep f) -> f a

contramap f (tabulate g) = tabulate (g . f)
index :: f a -> a -> Rep f

foo :: F.Representable f => ((a -> b) -> s -> t) -> (a -> f b) -> s -> f t
foo f afb s = F.tabulate $ \i -> f (flip F.index i . afb) s
-}



-- | 'setting' promotes a \"semantic editor combinator\" to a modify-only lens.
--
-- To demote a lens to a semantic edit combinator, use the section @(l %~)@ or @mapOf l@.
--
-- >>> [("The",0),("quick",1),("brown",1),("fox",2)] & setting map . _1 %~ length
-- [(3,0),(5,1),(5,1),(3,2)]
--
-- /Caution/: In order for the generated family to be well-defined, you must ensure that the two functors laws hold:
--
-- * @sec id === id@
--
-- * @sec f . sec g === sec (f . g)@
--
-- See <http://conal.net/blog/posts/semantic-editor-combinators>.
--
setting :: ((a -> b) -> s -> t) -> Setter s t a b
setting sec = dimap (Store id) (\(Store g s) -> sec g s) . lift collect

-- | TODO: Document
--
grating :: Functor f => (((s -> f a) -> f b) -> t) -> Setter s t a b
grating f = dimap pureTaskF (f . runTask) . lift collect

-- | Every 'Grate' is a 'Setter'.
--
-- Note: this is needed b/c currently 'Corepresentable' does not entail 'Closed', 
-- though perhaps it should (see 'closed'')
--
--lowerGrate :: Grate s t a b -> Setter s t a b
--lowerGrate x = withGrate x (setting . lowerGrate')

-- | Every 'Grate' is an 'Setter'.
--
lowerGrate' :: (((s -> a) -> b) -> t) -> (a -> b) -> s -> t
lowerGrate' sabt ab s = sabt $ \sa -> ab (sa s)

---------------------------------------------------------------------
-- Primitive operators
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

-- | TODO: Document
--
remapOf :: Optic (Re (->) a b) s t a b -> (t -> s) -> (b -> a)
remapOf = re

-- | TODO: Document
--
over :: Optic (->) s t a b -> (a -> b) -> s -> t
over = id

infixr 4 %~

-- | TODO: Document
--
(%~) :: Optic (->) s t a b -> (a -> b) -> s -> t
(%~) = id
{-# INLINE (%~) #-}

infixr 4 .~

-- | TODO: Document
--
(.~) :: Optic (->) s t a b -> s -> b -> t
(.~) = set
{-# INLINE (.~) #-}

-- set l y (set l x a) ≡ set l y a
-- \c -> set (setting . runCayley $ c) zero one ≡ lowerCayey c

-- | Set all referenced fields to the given value.
--
set :: Optic (->) s t a b -> s -> b -> t
set o s b = o (const b) s

--set . re :: Colens s t a b -> s -> b -> a
reset :: Optic (Re (->) a b) s t a b -> b -> s -> a
reset = set . re

-- | Set all referenced fields to the given value.
--reset :: AResetter s t a b -> b -> s -> t
--reset l b = under l (const b)


appendSetter :: Semigroup a => Setter s t a a -> a -> s -> t
appendSetter o = o . (<>)

---------------------------------------------------------------------
-- Common setters
---------------------------------------------------------------------

-- | Map contravariantly by setting the input of a 'Profunctor'.
--
--
-- The most common profunctor to use this with is @(->)@.
--
-- >>> (dom %~ f) g x
-- g (f x)
--
-- >>> (dom %~ show) length [1,2,3]
-- 7
--
-- >>> (dom %~ f) h x y
-- h (f x) y
--
-- Map setting the second arg of a function:
--
-- >>> (mapped . dom %~ f) h x y
-- h x (f y)
--
dom :: Profunctor p => Setter (p b r) (p a r) a b
dom = setting lmap
{-# INLINE dom #-}

-- | A grate accessing the codomain of a function.
--
-- @
-- cod @(->) == lowerGrate range
-- @
--
cod :: Profunctor p => Setter (p r a) (p r b) a b
cod = setting rmap

-- | TODO: Document
--
masking :: Setter (IO a) (IO b) a b
masking = grating Ex.mask

-- | SEC for monadically transforming a monadic value
binding :: Monad m => Setter (m a) (m b) a (m b)
binding = setting (=<<)

-- | SEC on each value of a functor
mapped :: Functor f => Setter (f a) (f b) a b
mapped = setting fmap

-- | TODO: Document
--
foldMapped :: Foldable f => Monoid m => Setter (f a) m a m
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

-- | TODO: Document
--
liftedM :: Monad m => Setter (m a) (m b) a b
liftedM = setting liftM

-- | Set a value using an SEC.
--
sets :: Setter b (a -> c) a c
sets = setting const

-- | TODO: Document
--
zipped :: Setter (u -> v -> a) (u -> v -> b) a b
zipped = setting ((.)(.)(.))

-- | TODO: Document
--
grated :: Setter (a -> b) (s -> t) ((s -> a) -> b) t
grated = setting lowerGrate'

-- | TODO: Document
--
modded :: Setter (b -> t) (((s -> a) -> b) -> t) s a
modded = setting $ \sa bt sab -> bt (sab sa)

-- | TODO: Document
--
composed :: Setter (s -> a) ((a -> b) -> s -> t) b t
composed = setting between

-- | SEC applying the given function only when the given predicate
--  yields true for an input value.
branching :: (a -> Bool) -> Setter' a a
branching p = setting $ \f a -> if p a then f a else a

-- See https://hackage.haskell.org/package/build-1.0/docs/Build-Task.html#t:Tasks
--branched :: (k -> Bool) -> Setter' (k -> v) v
--branched p = setting $ \mod f a -> if p a then mod (f a) else f a

-----------------------------------------------------------------------------
-- Reader Operators
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

-----------------------------------------------------------------------------
-- Writer Operators
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

---------------------------------------------------------------------
-- State Operators
---------------------------------------------------------------------

infix 4 .=

-- | TODO: Document
--
(.=) :: MonadState s m => b -> Optic (->) s s a b -> m ()
b .= o = assign o b
{-# INLINE (.=) #-}

-- | TODO: Document
--
assign :: MonadState s m => Optic (->) s s a b -> b -> m ()
assign o b = State.modify $ o (const b)
{-# INLINE assign #-}

-- | TODO: Document
--
modifying :: MonadState s m => Optic (->) s s a b -> (a -> b) -> m ()
modifying l f = State.modify (l %~ f)
{-# INLINE modifying #-}

infix 4 %=
{-# INLINE (%=) #-}

-- | TODO: Document
--
(%=) :: MonadState s m => Optic (->) s s a b -> (a -> b) -> m ()
l %= f = modifying l f


-- | TODO: Document
--
(<~) :: MonadState s m => b -> m (Optic (->) s s a b) -> m ()
l <~ mb = mb >>= (l .=)
{-# INLINE (<~) #-}

-- | TODO: Document
--
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



-- infix  4 <<.=, <<%=, <%=, <.=, <?=
-- infix  4 +=, -=, *=, //=
infixr 2 <~
infixl 1 &~


s &~ l = State.execState l s
{-# INLINE (&~) #-}

--infix  4 ?=
--l ?= b = l .= Just b
--{-# INLINE (?=) #-}




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
