module Data.Profunctor.Optic.Setter (
    module Data.Profunctor.Optic.Setter 
  , module Export
) where


import Data.Profunctor.Optic.Type 
import Data.Profunctor.Optic.Operator
import Data.Profunctor.Optic.Prelude 

import Data.Profunctor.Mapping as Export

import Control.Applicative (liftA)
import Control.Monad.State as State
import Control.Monad.Writer as Writer
import Control.Monad.Reader as Reader


---------------------------------------------------------------------
-- Setter
---------------------------------------------------------------------

-- import Data.Functor.Rep
-- sets :: ((a -> b) -> s -> t) -> Setter s t a b
-- sets f = wander $ \g s -> tabulate $ \idx -> f (flip index idx . g) s
-- 

-- See http://conal.net/blog/posts/semantic-editor-combinators
sets :: ((a -> b) -> s -> t) -> Setter s t a b
sets f = dimap (Context id) (\(Context g s) -> f g s) . map'

--setter_complete :: Setter s t a b -> Setter s t a b
--setter_complete = sets . over

---------------------------------------------------------------------
-- Common setters
---------------------------------------------------------------------

resets :: Setter (s -> a) ((a -> b) -> s -> t) b t
resets = sets between

--composed :: Setter (a -> b -> s) (a -> b -> t) s t
--composed = sets ((.)(.)(.))

--curried :: Setter a (b -> c) (a, b) c
--curried = sets curry

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
lifted :: Applicative f => Setter (f a) (f b) a b
lifted = sets liftA
{-# INLINE lifted #-}

mapped :: Functor f => Setter (f a) (f b) a b
mapped = sets fmap

foldMapped :: (Foldable f, Monoid m) => Setter (f a) m a m
foldMapped = sets foldMap

{-
collecting
    :: (forall f. (Applicative f, Distributive f) => (a -> f b) -> s -> f t)
    -> Setter s t a b
collecting = roam
-}

-- | This 'Setter' can be used to map over the input of a 'Profunctor'.
--
-- The most common 'Profunctor' to use this with is @(->)@.
--
-- >>> (argument %~ f) g x
-- g (f x)
--
-- >>> (argument %~ show) length [1,2,3]
-- 7
--
-- >>> (argument %~ f) h x y
-- h (f x) y
--
-- Map over the argument of the result of a function -- i.e., its second
-- argument:
--
-- >>> (mapped . argument %~ f) h x y
-- h x (f y)
--
-- @
-- 'argument' :: 'Setter' (b -> r) (a -> r) a b
-- @
argument :: Profunctor p => Setter (p b r) (p a r) a b
argument = sets lmap
{-# INLINE argument #-}

outcome :: Profunctor p => Setter (p r a) (p r b) a b
outcome = sets rmap

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------


infixr 4 %~

(%~) :: Optic (->) s t a b -> (a -> b) -> s -> t
(%~) = over
{-# INLINE (%~) #-}


reover :: Optic (Re (->) a b) s t a b -> (t -> s) -> (b -> a)
reover = re

-- set l y (set l x a) ≡ set l y a
set :: Optic (->) s t a b -> s -> b -> t
set o s b = o (const b) s

set' :: ((a -> b) -> t) -> b -> t
set' o = o . const

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

appendOver :: Semigroup a => Setter s t a a -> a -> s -> t
appendOver o = o . (<>)

{- |
('<>~') appends a value monoidally to the target.

>>> ("hello", "goodbye") & both <>~ " world!"
("hello world!", "goodbye world!")
-}
infixr 4 <>~
{-# INLINE (<>~) #-}

(<>~) :: Semigroup a => Setter s t a a -> a -> s -> t
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
-- portion of the resulting 'MonadWriter'.
passing :: MonadWriter s m => Optic (->) s s a b -> m (r, a -> b) -> m r
passing o m = pass $ do
  (a, uv) <- m
  return (a, o uv)
{-# INLINE passing #-}

-- | This is a generalization of 'censor' that allows you to 'censor' just a
-- portion of the resulting 'MonadWriter'.
--censoring :: MonadWriter w m => Setter w w u v -> (u -> v) -> m a -> m a
censoring :: MonadWriter s m => Optic (->) s s a b -> (a -> b) -> m c -> m c
censoring o uv = censor $ o uv
{-# INLINE censoring #-}

-----------------------------------------------------------------------------
-- Reader Operations
-----------------------------------------------------------------------------

-- | Modify the value of the 'Reader' environment associated with the target of a
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
