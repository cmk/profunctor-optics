module Control.Monad.State.Optic (
    zoom
  , use
  , reuse
  , uses 
  , reuses
  , (.=)
  , assigns
  , (%=)
  , modifies
  , (?=)
  , (<>=)
  , (><=)
  , (+=)
  , (-=)
  , (*=)
  , (//=)
  , (&&=)
  , (||=)
) where

import Control.Monad.Reader as Reader
import Control.Monad.Writer as Writer hiding (Sum(..))
import Control.Monad.State as State
import Data.Profunctor.Optic
import Data.Profunctor.Optic.Import
import Data.Semiring
import Prelude (Num(..))

--import Control.Monad.State as State hiding (lift)


import Control.Monad (liftM)

{-
newtype Zoom m c a = Zoom { unZoom :: m (c, a) }

instance Monad m => Functor (Zoom m c) where
  fmap f (Zoom m) = Zoom (liftM (fmap f) m)

instance (Monoid c, Monad m) => Applicative (Zoom m c) where
  pure a = Zoom (return (mempty, a))
  Zoom f <*> Zoom x = Zoom $ do
    (a, f') <- f
    (b, x') <- x
    return (a <> b, f' x')

-- | Lift a stateful operation on a field to a stateful operation on the whole state.
-- This is a good way to call a \"subroutine\" that only needs access to part of the state.
--
-- @
-- zoom :: (Monad m, Monoid c) => Traversal' s a -> StateT a m c -> StateT s m c
-- @
--
-- Run the \"subroutine\" on each element of the traversal in turn and 'mconcat' all the results together.
--
-- @
-- zoom :: Monad m => Traversal' s a -> StateT a m () -> StateT s m ()
-- @
--
-- Run the \"subroutine\" on each element the traversal in turn.
zoom :: Monad m => ARepn' (Zoom m r) s a -> StateT a m r -> StateT s m r
zoom o m = StateT $ unZoom . traverseOf o (Zoom . (runStateT m))
-}

-- ^ @
-- zoom :: Functor m => Lens' ta a -> StateT a m c -> StateT ta m c
-- zoom :: (Monoid c, Applicative m) => Traversal' ta a -> StateT a m c -> StateT ta m c
-- @
zoom :: Functor m => Optic' (Star (Compose m ((,) c))) ta a -> StateT a m c -> StateT ta m c
zoom o (StateT m) = StateT . out . o . into $ m
 where
  into f = Star (Compose . f)
  out (Star f) = getCompose . f


-- | Replace the target(s) of a settable in a monadic state.
--
-- This is an infix version of 'assigns'.
--
-- >>> execState (do first .= 1; second .= 2) (3,4)
-- (1,2)
--
-- >>> execState (both .= 3) (1,2)
-- (3,3)
--
-- @
-- ('.=') :: 'MonadState' s m => 'Iso'' s a       -> a -> m ()
-- ('.=') :: 'MonadState' s m => 'Lens'' s a      -> a -> m ()
-- ('.=') :: 'MonadState' s m => 'Traversal'' s a -> a -> m ()
-- ('.=') :: 'MonadState' s m => 'Setter'' s a    -> a -> m ()
-- @
--
(.=) :: MonadState s m => ASetter s s a b -> b -> m ()
o .= b = State.modify (o .~ b)
{-# INLINE (.=) #-}

-- | Replace the target(s) of a settable in a monadic state.
--
-- @
-- 'assigns' :: 'MonadState' s m => 'Iso'' s a       -> a -> m ()
-- 'assigns' :: 'MonadState' s m => 'Lens'' s a      -> a -> m ()
-- 'assigns' :: 'MonadState' s m => 'Grate'' s a     -> a -> m ()
-- 'assigns' :: 'MonadState' s m => 'Setter'' s a    -> a -> m ()
-- 'assigns' :: 'MonadState' s m => 'Traversal'' s a -> a -> m ()
-- @
--
assigns :: MonadState s m => ASetter s s a b -> b -> m ()
assigns o b = State.modify (set o b)
{-# INLINE assigns #-}

-- | Map over the target(s) of a 'Setter' in a monadic state.
--
-- This is an infix version of 'modifies'.
--
-- >>> execState (do first %= (+1) ;second %= (+2)) (1,2)
-- (2,4)
--
-- >>> execState (do both %= (+1)) (1,2)
-- (2,3)
--
-- @
-- ('%=') :: 'MonadState' s m => 'Iso'' s a       -> (a -> a) -> m ()
-- ('%=') :: 'MonadState' s m => 'Lens'' s a      -> (a -> a) -> m ()
-- ('%=') :: 'MonadState' s m => 'Grate'' s a     -> (a -> a) -> m ()
-- ('%=') :: 'MonadState' s m => 'Setter'' s a    -> (a -> a) -> m ()
-- ('%=') :: 'MonadState' s m => 'Traversal'' s a -> (a -> a) -> m ()
-- @
--
(%=) :: MonadState s m => ASetter s s a b -> (a -> b) -> m ()
o %= f = State.modify (o %~ f)
{-# INLINE (%=) #-}

-- | Map over the target(s) of a 'Setter' in a monadic state.
--
-- @
-- 'modifies' :: 'MonadState' s m => 'Iso'' s a       -> (a -> a) -> m ()
-- 'modifies' :: 'MonadState' s m => 'Lens'' s a      -> (a -> a) -> m ()
-- 'modifies' :: 'MonadState' s m => 'Grate'' s a     -> (a -> a) -> m ()
-- 'modifies' :: 'MonadState' s m => 'Setter'' s a    -> (a -> a) -> m ()
-- 'modifies' :: 'MonadState' s m => 'Traversal'' s a -> (a -> a) -> m ()
-- @
--
modifies :: MonadState s m => ASetter s s a b -> (a -> b) -> m ()
modifies o f = State.modify (over o f)
{-# INLINE modifies #-}

-- | Replace the target(s) of a settable optic with 'Just' a new value.
--
-- >>> execState (do first ?= 1; second ?= 2) (Just 1, Nothing)
-- (Just 1,Just 2)
--
-- @
-- ('?=') :: 'MonadState' s m => 'Iso'' s ('Maybe' a)       -> a -> m ()
-- ('?=') :: 'MonadState' s m => 'Lens'' s ('Maybe' a)      -> a -> m ()
-- ('?=') :: 'MonadState' s m => 'Grate'' s ('Maybe' a)     -> a -> m ()
-- ('?=') :: 'MonadState' s m => 'Setter'' s ('Maybe' a)    -> a -> m ()
-- ('?=') :: 'MonadState' s m => 'Traversal'' s ('Maybe' a) -> a -> m ()
-- @
--
(?=) :: MonadState s m => ASetter s s a (Maybe b) -> b -> m ()
o ?= b = State.modify (o ?~ b)
{-# INLINE (?=) #-}

infixr 4 <>=, ><=
-- | Modify the target(s) of a settable optic by adding a value.
--
-- >>> execState (both <>= False) (False,True)
-- (False,True)
--
-- >>> execState (both <>= "!!!") ("hello","world")
-- ("hello!!!","world!!!")
--
-- @
-- ('<>=') :: 'MonadState' s m => 'Semigroup' a => 'Iso'' s a -> a -> m ()
-- ('<>=') :: 'MonadState' s m => 'Semigroup' a => 'Lens'' s a -> a -> m ()
-- ('<>=') :: 'MonadState' s m => 'Semigroup' a => 'Grate'' s a -> a -> m ()
-- ('<>=') :: 'MonadState' s m => 'Semigroup' a => 'Setter'' s a -> a -> m ()
-- ('<>=') :: 'MonadState' s m => 'Semigroup' a => 'Traversal'' s a -> a -> m ()
-- @
--
(<>=) :: MonadState s m => Semigroup a => ASetter' s a -> a -> m ()
o <>= a = State.modify (o <>~ a)
{-# INLINE (<>=) #-}

-- | Modify the target(s) of a settable optic by mulitiplying by a value.
--
-- >>> execState (both ><= False) (False,True)
-- (False,False)
--
-- @
-- ('><=') :: 'MonadState' s m => 'Semiring' a => 'Iso'' s a -> a -> m ()
-- ('><=') :: 'MonadState' s m => 'Semiring' a => 'Lens'' s a -> a -> m ()
-- ('><=') :: 'MonadState' s m => 'Semiring' a => 'Grate'' s a -> a -> m ()
-- ('><=') :: 'MonadState' s m => 'Semiring' a => 'Setter'' s a -> a -> m ()
-- ('><=') :: 'MonadState' s m => 'Semiring' a => 'Traversal'' s a -> a -> m ()
-- @
--
(><=) :: MonadState s m => Semiring a => ASetter' s a -> a -> m ()
o ><= a = State.modify (o ><~ a)
{-# INLINE (><=) #-}

infix 4 %%=

(%%=) :: Monad m => Monoid r => ATraversal (Writer r) s s a b -> (a -> (r, b)) -> StateT s m r
-- ^ @
-- (%%=) :: Monad m => Lens s s a b -> (a -> (c, b)) -> StateT s m c
-- @
--
-- Modify a field of the state while returning another value.
--
-- @
-- (%%=) :: (Monad m, Monoid c) => Traversal s s a b -> (a -> (c, b)) -> StateT s m c
-- @
--
-- Modify each field of the state and return the 'mconcat' of the other values.
o %%= f = state (swp . runWriter . traverseOf o (writer . swp . f))

infixr 4 +=, -=, *=

(+=), (-=), (*=) :: (Monad m, Num a) => ASetter' s a -> a -> StateT s m ()
o += a = o %= (+ a)
o -= a = o %= subtract a
o *= a = o %= (* a)

infixr 4 //=

(//=) :: (Monad m, Fractional a) => ASetter' s a -> a -> StateT s m ()
o //= a = o %= (/ a)

infixr 4 &&=, ||=

(&&=), (||=) :: Monad m => ASetter' s Bool -> Bool -> StateT s m ()
o &&= a = o %= (&& a)
o ||= a = o %= (|| a)



infix 4 %!=

-- | Strictly modify a field of the state.
(%!=) :: Monad m => ASetter s s a b -> (a -> b) -> StateT s m ()
o %!= f = modify' (o %~ f)

infixr 4 +!=, -!=, *!=

(+!=), (-!=), (*!=) :: (Monad m, Num a) => ASetter' s a -> a -> StateT s m ()
o +!= a = o %!= (+ a)
o -!= a = o %!= subtract a
o *!= a = o %!= (* a)

infixr 4 //!=

(//!=) :: (Monad m, Fractional a) => ASetter' s a -> a -> StateT s m ()
o //!= a = o %!= (/ a)

infixr 4 &&!=, ||!=

(&&!=), (||!=) :: Monad m => ASetter' s Bool -> Bool -> StateT s m ()
o &&!= a = o %!= (&& a)
o ||!= a = o %!= (|| a)

infixr 4 <>!=

(<>!=) :: (Monad m, Semigroup a) => ASetter' s a -> a -> StateT s m ()
o <>!= a = o %!= (<> a)



{-
infixr 4 +=, -=, *=
(+=), (-=), (*=) (MonadState s m, Num a) => ASetter' s a -> a -> m ()
-- | Modify the target(s) of a 'Lens'', 'Iso', 'Setter' or 'Traversal' by adding a value.
--
-- Example:
--
-- @
-- 'fresh' :: 'MonadState' 'Int' m => m 'Int'
-- 'fresh' = do
--   'id' '+=' 1
--   'Control.Lens.Getter.use' 'id'
-- @
--
-- >>> execState (do _1 += c; _2 += d) (a,b)
-- (a + c,b + d)
--
-- >>> execState (do _1.at 1.non 0 += 10) (Map.fromList [(2,100)],"hello")
-- (fromList [(1,10),(2,100)],"hello")
--
-- @
-- ('+=') :: ('MonadState' s m, 'Num' a) => 'Setter'' s a    -> a -> m ()
-- ('+=') :: ('MonadState' s m, 'Num' a) => 'Iso'' s a       -> a -> m ()
-- ('+=') :: ('MonadState' s m, 'Num' a) => 'Lens'' s a      -> a -> m ()
-- ('+=') :: ('MonadState' s m, 'Num' a) => 'Traversal'' s a -> a -> m ()
-- @
o += b = State.modify (o +~ b)
{-# INLINE (+=) #-}

-- | Modify the target(s) of a 'Lens'', 'Iso', 'Setter' or 'Traversal' by subtracting a value.
--
-- >>> execState (do _1 -= c; _2 -= d) (a,b)
-- (a - c,b - d)
--
-- @
-- ('-=') :: ('MonadState' s m, 'Num' a) => 'Setter'' s a    -> a -> m ()
-- ('-=') :: ('MonadState' s m, 'Num' a) => 'Iso'' s a       -> a -> m ()
-- ('-=') :: ('MonadState' s m, 'Num' a) => 'Lens'' s a      -> a -> m ()
-- ('-=') :: ('MonadState' s m, 'Num' a) => 'Traversal'' s a -> a -> m ()
-- @
o -= b = State.modify (o -~ b)
{-# INLINE (-=) #-}

-- | Modify the target(s) of a 'Lens'', 'Iso', 'Setter' or 'Traversal' by multiplying by value.
--
-- >>> execState (do _1 *= c; _2 *= d) (a,b)
-- (a * c,b * d)
--
-- @
-- ('*=') :: ('MonadState' s m, 'Num' a) => 'Setter'' s a    -> a -> m ()
-- ('*=') :: ('MonadState' s m, 'Num' a) => 'Iso'' s a       -> a -> m ()
-- ('*=') :: ('MonadState' s m, 'Num' a) => 'Lens'' s a      -> a -> m ()
-- ('*=') :: ('MonadState' s m, 'Num' a) => 'Traversal'' s a -> a -> m ()
-- @
o *= b = State.modify (o *~ b)
{-# INLINE (*=) #-}

-- | Modify the target(s) of a 'Lens'', 'Iso', 'Setter' or 'Traversal' by dividing by a value.
--
-- >>> execState (do _1 //= c; _2 //= d) (a,b)
-- (a / c,b / d)
--
-- @
-- ('//=') :: ('MonadState' s m, 'Fractional' a) => 'Setter'' s a    -> a -> m ()
-- ('//=') :: ('MonadState' s m, 'Fractional' a) => 'Iso'' s a       -> a -> m ()
-- ('//=') :: ('MonadState' s m, 'Fractional' a) => 'Lens'' s a      -> a -> m ()
-- ('//=') :: ('MonadState' s m, 'Fractional' a) => 'Traversal'' s a -> a -> m ()
-- @
(//=) :: (MonadState s m, Fractional a) => ASetter' s a -> a -> m ()
o //= a = State.modify (o //~ a)
{-# INLINE (//=) #-}

-- | Raise the target(s) of a numerically valued 'Lens', 'Setter' or 'Traversal' to a non-negative integral power.
--
-- @
-- ('^=') ::  ('MonadState' s m, 'Num' a, 'Integral' e) => 'Setter'' s a    -> e -> m ()
-- ('^=') ::  ('MonadState' s m, 'Num' a, 'Integral' e) => 'Iso'' s a       -> e -> m ()
-- ('^=') ::  ('MonadState' s m, 'Num' a, 'Integral' e) => 'Lens'' s a      -> e -> m ()
-- ('^=') ::  ('MonadState' s m, 'Num' a, 'Integral' e) => 'Traversal'' s a -> e -> m ()
-- @
(^=) :: (MonadState s m, Num a, Integral e) => ASetter' s a -> e -> m ()
o ^= e = State.modify (o ^~ e)
{-# INLINE (^=) #-}

-- | Raise the target(s) of a numerically valued 'Lens', 'Setter' or 'Traversal' to an integral power.
--
-- @
-- ('^^=') ::  ('MonadState' s m, 'Fractional' a, 'Integral' e) => 'Setter'' s a    -> e -> m ()
-- ('^^=') ::  ('MonadState' s m, 'Fractional' a, 'Integral' e) => 'Iso'' s a       -> e -> m ()
-- ('^^=') ::  ('MonadState' s m, 'Fractional' a, 'Integral' e) => 'Lens'' s a      -> e -> m ()
-- ('^^=') ::  ('MonadState' s m, 'Fractional' a, 'Integral' e) => 'Traversal'' s a -> e -> m ()
-- @
(^^=) :: (MonadState s m, Fractional a, Integral e) => ASetter' s a -> e -> m ()
o ^^= e = State.modify (o ^^~ e)
{-# INLINE (^^=) #-}

-- | Raise the target(s) of a numerically valued 'Lens', 'Setter' or 'Traversal' to an arbitrary power
--
-- >>> execState (do _1 **= c; _2 **= d) (a,b)
-- (a**c,b**d)
--
-- @
-- ('**=') ::  ('MonadState' s m, 'Floating' a) => 'Setter'' s a    -> a -> m ()
-- ('**=') ::  ('MonadState' s m, 'Floating' a) => 'Iso'' s a       -> a -> m ()
-- ('**=') ::  ('MonadState' s m, 'Floating' a) => 'Lens'' s a      -> a -> m ()
-- ('**=') ::  ('MonadState' s m, 'Floating' a) => 'Traversal'' s a -> a -> m ()
-- @
(**=) :: (MonadState s m, Floating a) => ASetter' s a -> a -> m ()
o **= a = State.modify (o **~ a)
{-# INLINE (**=) #-}

infix  4 %@=, .@=, .=, +=, *=, -=, //=, ^=, ^^=, **=, &&=, <>=, ||=, %=, <.=, ?=, <?=

infix 4 &&=, ||=

(&&=), (||=) :: MonadState s m => ASetter' s Bool -> Bool -> m ()
-- | Modify the target(s) of a 'Lens'', 'Iso', 'Setter' or 'Traversal' by taking their logical '&&' with a value.
--
-- >>> execState (do _1 &&= True; _2 &&= False; _3 &&= True; _4 &&= False) (True,True,False,False)
-- (True,False,False,False)
--
-- @
-- ('&&=') :: 'MonadState' s m => 'Setter'' s 'Bool'    -> 'Bool' -> m ()
-- ('&&=') :: 'MonadState' s m => 'Iso'' s 'Bool'       -> 'Bool' -> m ()
-- ('&&=') :: 'MonadState' s m => 'Lens'' s 'Bool'      -> 'Bool' -> m ()
-- ('&&=') :: 'MonadState' s m => 'Traversal'' s 'Bool' -> 'Bool' -> m ()
-- @
o &&= b = State.modify (o &&~ b)
{-# INLINE (&&=) #-}

-- | Modify the target(s) of a 'Lens'', 'Iso, 'Setter' or 'Traversal' by taking their logical '||' with a value.
--
-- >>> execState (do _1 ||= True; _2 ||= False; _3 ||= True; _4 ||= False) (True,True,False,False)
-- (True,True,True,False)
--
-- @
-- ('||=') :: 'MonadState' s m => 'Setter'' s 'Bool'    -> 'Bool' -> m ()
-- ('||=') :: 'MonadState' s m => 'Iso'' s 'Bool'       -> 'Bool' -> m ()
-- ('||=') :: 'MonadState' s m => 'Lens'' s 'Bool'      -> 'Bool' -> m ()
-- ('||=') :: 'MonadState' s m => 'Traversal'' s 'Bool' -> 'Bool' -> m ()
-- @
o ||= b = State.modify (o ||~ b)
{-# INLINE (||=) #-}

-- | Run a monadic action, and set all of the targets of a 'Lens', 'Setter' or 'Traversal' to its result.
--
-- @
-- ('<~') :: 'MonadState' s m => 'Iso' s s a b       -> m b -> m ()
-- ('<~') :: 'MonadState' s m => 'Lens' s s a b      -> m b -> m ()
-- ('<~') :: 'MonadState' s m => 'Traversal' s s a b -> m b -> m ()
-- ('<~') :: 'MonadState' s m => 'Setter' s s a b    -> m b -> m ()
-- @
--
-- As a reasonable mnemonic, this lets you store the result of a monadic action in a 'Lens' rather than
-- in a local variable.
--
-- @
-- do foo <- bar
--    ...
-- @
--
-- will store the result in a variable, while
--
-- @
-- do foo '<~' bar
--    ...
-- @
--
-- will store the result in a 'Lens', 'Setter', or 'Traversal'.
(<~) :: MonadState s m => ASetter s s a b -> m b -> m ()
o <~ mb = mb >>= (o .=)
{-# INLINE (<~) #-}

-- | Set with pass-through
--
-- This is useful for chaining assignment without round-tripping through your 'Monad' stack.
--
-- @
-- do x <- 'Control.Lens.Tuple._2' '<.=' ninety_nine_bottles_of_beer_on_the_wall
-- @
--
-- If you do not need a copy of the intermediate result, then using @l '.=' d@ will avoid unused binding warnings.
--
-- @
-- ('<.=') :: 'MonadState' s m => 'Setter' s s a b    -> b -> m b
-- ('<.=') :: 'MonadState' s m => 'Iso' s s a b       -> b -> m b
-- ('<.=') :: 'MonadState' s m => 'Lens' s s a b      -> b -> m b
-- ('<.=') :: 'MonadState' s m => 'Traversal' s s a b -> b -> m b
-- @
(<.=) :: MonadState s m => ASetter s s a b -> b -> m b
o <.= b = do
  o .= b
  return b
{-# INLINE (<.=) #-}

-- | Set 'Just' a value with pass-through
--
-- This is useful for chaining assignment without round-tripping through your 'Monad' stack.
--
-- @
-- do x <- 'Control.Lens.At.at' "foo" '<?=' ninety_nine_bottles_of_beer_on_the_wall
-- @
--
-- If you do not need a copy of the intermediate result, then using @l '?=' d@ will avoid unused binding warnings.
--
-- @
-- ('<?=') :: 'MonadState' s m => 'Setter' s s a ('Maybe' b)    -> b -> m b
-- ('<?=') :: 'MonadState' s m => 'Iso' s s a ('Maybe' b)       -> b -> m b
-- ('<?=') :: 'MonadState' s m => 'Lens' s s a ('Maybe' b)      -> b -> m b
-- ('<?=') :: 'MonadState' s m => 'Traversal' s s a ('Maybe' b) -> b -> m b
-- @
(<?=) :: MonadState s m => ASetter s s a (Maybe b) -> b -> m b
o <?= b = do
  o ?= b
  return b
{-# INLINE (<?=) #-}
-}


