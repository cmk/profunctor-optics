{-# LANGUAGE DeriveFunctor #-}

module Data.Profunctor.Optic.Setter (
    module Data.Profunctor.Optic.Setter 
  , module Export
) where


import Data.Profunctor.Optic.Types 
import Data.Profunctor.Optic.Operators

import Data.Profunctor.Mapping as Export

import Control.Monad.State as State
import Control.Monad.Writer as Writer
import Control.Monad.Reader as Reader


---------------------------------------------------------------------
-- Setter
---------------------------------------------------------------------

--setting :: ((a -> b) -> s -> t) -> Setter s t a b
--setting f = roam $ \g s -> tabulate $ \idx -> f (flip index idx . g) s

data Context a b t = Context (b -> t) a deriving Functor

-- See http://conal.net/blog/posts/semantic-editor-combinators
sets :: ((a -> b) -> s -> t) -> Setter s t a b
sets f = dimap (Context id) (\(Context g s) -> f g s) . map'

---------------------------------------------------------------------
-- Common setters
---------------------------------------------------------------------

mapped :: Functor f => Setter (f a) (f b) a b
mapped = sets fmap

---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------


infixr 4 %~

(%~) = over
{-# INLINE (%~) #-}

reover :: Optic (Re (->) a b) s t a b -> (t -> s) -> (b -> a)
reover = over . re

set :: Optic (->) s t a b -> s -> b -> t
set o s b = over o (const b) s

set' :: ((a -> b) -> t) -> b -> t
set' o = o . const

infixr 4 .~
{-# INLINE (.~) #-}

(.~) :: Optic (->) s t a b -> s -> b -> t
(.~) = set

infix 4 .=
{-# INLINE (.=) #-}

(.=)
  :: MonadState s m => b -> Optic (->) s s a b -> m ()
b .= o = assign o b

assign :: MonadState s m => Optic (->) s s a b -> b -> m ()
assign o b = State.modify (over o (const b))
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
appendOver p = over p . (<>)

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
l ?~ b = set l (Just b)
{-# INLINE (?~) #-}

infixr 4 ?~

--setJust :: Optic (->) s t a (Maybe b) -> b -> s -> t
--setJust :: Setter s t a (Maybe b) -> b -> s -> t
--setJust :: Optic (->) (Maybe a1) t a2 b -> a1 -> b -> t
setJust p = set p . Just


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
-- >>> (mapped.argument %~ f) h x y
-- h x (f y)
--
-- @
-- 'argument' :: 'Setter' (b -> r) (a -> r) a b
-- @
argument :: Profunctor p => Setter (p b r) (p a r) a b
argument = sets lmap
{-# INLINE argument #-}


-- | This 'setter' can be used to modify all of the values in a 'Monad'.
--
-- You sometimes have to use this rather than 'mapped' -- due to
-- temporary insanity 'Functor' was not a superclass of 'Monad' until
-- GHC 7.10.
--
-- @
-- 'liftM' ≡ 'over' 'lifted'
-- @
--
-- >>> over lifted f [a,b,c]
-- [f a,f b,f c]
--
-- >>> set lifted b (Just a)
-- Just b
--
-- If you want an 'IndexPreservingSetter' use @'setting' 'liftM'@.
lifted :: Monad m => Setter (m a) (m b) a b
lifted = sets liftM
{-# INLINE lifted #-}

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
--(||~):: ASetter s t Bool Bool -> Bool -> s -> t
l ||~ n = over l (|| n)
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
--(&&~) :: ASetter s t Bool Bool -> Bool -> s -> t
l &&~ n = over l (&& n)
{-# INLINE (&&~) #-}

-----------------------------------------------------------------------------
-- Writer Operations
-----------------------------------------------------------------------------

-- | Write to a fragment of a larger 'Writer' format.
--scribe :: (MonadWriter t m, Monoid s) => ASetter s t a b -> b -> m ()
scribe
  :: (MonadWriter t m, Monoid s) 
  => Optic (->) s t a b -> b -> m ()
scribe o b = tell (set o mempty b)
{-# INLINE scribe #-}

-- | This is a generalization of 'pass' that allows you to modify just a
-- portion of the resulting 'MonadWriter'.
--passing :: MonadWriter w m => Setter w w u v -> m (a, u -> v) -> m a
passing l m = pass $ do
  (a, uv) <- m
  return (a, over l uv)
{-# INLINE passing #-}

-- | This is a generalization of 'censor' that allows you to 'censor' just a
-- portion of the resulting 'MonadWriter'.
--censoring :: MonadWriter w m => Setter w w u v -> (u -> v) -> m a -> m a
censoring
  :: MonadWriter s m 
  => Optic (->) s s a b -> (a -> b) -> m c -> m c
censoring l uv = censor (over l uv)
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
--locally :: MonadReader s m => ASetter s s a b -> (a -> b) -> m r -> m r
locally l f = Reader.local (over l f)
{-# INLINE locally #-}
