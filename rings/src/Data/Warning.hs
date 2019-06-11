{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE OverloadedStrings  #-}

module Data.Warning where


--import Control.DeepSeq              (NFData (..))
--import Control.Lens                 (Swapped (..), iso)
import Data.Bifoldable              (Bifoldable (..))
import Data.Bifunctor               (Bifunctor (..))
--import Data.Bifunctor.Assoc         (Assoc (..))
--import Data.Bifunctor.Swap          (Swap (..))
--import Data.Binary                  (Binary (..))
import Data.Bitraversable           (Bitraversable (..))
import Data.Data                    (Data, Typeable)
import Data.Functor.Bind            (Apply (..), Bind (..))
--import Data.Hashable                (Hashable (..))
import Data.Semigroup               (Semigroup (..))
import Data.Semigroup.Bifoldable    (Bifoldable1 (..))
import Data.Semigroup.Bitraversable (Bitraversable1 (..))
import Data.Semiring
import Data.Hemiring
import Data.Dioid
import GHC.Generics                 (Generic)

data Warning w a = Failure w | Warning w a | Success a
  deriving (Eq, Ord, Show, Typeable, Data, Generic) 


-------------------------------------------------------------------------------
-- Eliminators
-------------------------------------------------------------------------------

-- | Case analysis for the 'Warning' type.
warning :: (a -> c) -> (b -> c) -> (a -> b -> c) -> Warning a b -> c
warning l _ _ (Failure a) = l a
warning _ r _ (Success x) = r x
warning _ _ lr (Warning a x) = lr a x

-- | Takes two default values and produces a tuple.
fromWarning :: a -> b -> Warning a b -> (a, b)
fromWarning x y = warning (`pair` y) (x `pair`) pair where
    pair = (,)

-- | Coalesce with the provided operation.
mergeWarning :: (a -> a -> a) -> Warning a a -> a
mergeWarning = warning id id

-- | 'bimap' and coalesce results with the provided operation.
mergeWarningWith :: (a -> c) -> (b -> c) -> (c -> c -> c) -> Warning a b -> c
mergeWarningWith f g op t = mergeWarning op $ bimap f g t

-------------------------------------------------------------------------------
-- Partitioning
-------------------------------------------------------------------------------

-- | Select each constructor and partition them into separate lists.
partitionWarnings :: [Warning a b] -> ([a], [b], [(a, b)])
partitionWarnings []     = ([], [], [])
partitionWarnings (t:ts) = case t of
    Failure x    -> (x : xs,     ys,         xys)
    Success y    -> (    xs, y : ys,         xys)
    Warning x y  -> (    xs,     ys, (x,y) : xys)
  where
    ~(xs,ys,xys) = partitionWarnings ts

-- | Select 'here' and 'there' elements and partition them into separate lists.
--
partitionWarnings' :: [Warning a b] -> ([a], [b])
partitionWarnings' []     = ([], [])
partitionWarnings' (t:ts) = case t of
    Failure x    -> (x : xs,     ys)
    Success y    -> (    xs, y : ys)
    Warning x y  -> (x : xs, y : ys)
  where
    ~(xs,ys) = partitionWarnings' ts


-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------


{-
instance Swap Warning where
    swap (Failure a)    = Success a
    swap (Success b)    = Failure b
    swap (Warning a b) = Warning b a

instance Assoc Warning where
    assoc (Failure (Failure a))       = Failure a
    assoc (Failure (Success b))       = Success (Failure b)
    assoc (Success c)              = Success (Success c)
    assoc (Warning (Success b) c)    = Success (Warning b c)
    assoc (Failure (Warning a b))    = Warning a (Failure b)
    assoc (Warning (Failure a) c)    = Warning a (Success c)
    assoc (Warning (Warning a b) c) = Warning a (Warning b c)

    unassoc (Failure a)              = Failure (Failure a)
    unassoc (Success (Failure b))       = Failure (Success b)
    unassoc (Success (Success c))       = Success c
    unassoc (Success (Warning b c))    = Warning (Success b) c
    unassoc (Warning a (Failure b))    = Failure (Warning a b)
    unassoc (Warning a (Success c))    = Warning (Failure a) c
    unassoc (Warning a (Warning b c)) = Warning (Warning a b) c

instance Swapped Warning where
    swapped = iso swap swap
-}

instance (Semigroup a, Semigroup b) => Semigroup (Warning a b) where
    Failure  a   <> Failure  b   = Failure  (a <> b)
    Failure  a   <> Success    y = Warning  a             y
    Failure  a   <> Warning b y = Warning (a <> b)       y
    Success    x <> Failure  b   = Warning       b   x
    Success    x <> Success    y = Success           (x <> y)
    Success    x <> Warning b y = Warning       b  (x <> y)
    Warning a x <> Failure  b   = Warning (a <> b)  x
    Warning a x <> Success    y = Warning  a       (x <> y)
    Warning a x <> Warning b y = Warning (a <> b) (x <> y)

instance Functor (Warning a) where
    fmap _ (Failure x) = Failure x
    fmap f (Success y) = Success (f y)
    fmap f (Warning x y) = Warning x (f y)

instance Foldable (Warning a) where
    foldr _ z (Failure _) = z
    foldr f z (Success x) = f x z
    foldr f z (Warning _ x) = f x z

instance Traversable (Warning a) where
    traverse _ (Failure a) = pure $ Failure a
    traverse f (Success x) = Success <$> f x
    traverse f (Warning a x) = Warning a <$> f x
    sequenceA (Failure a) = pure $ Failure a
    sequenceA (Success x) = Success <$> x
    sequenceA (Warning a x) = Warning a <$> x

instance Bifunctor Warning where
    bimap f _ (Failure  a  ) = Failure (f a)
    bimap _ g (Success    x) = Success (g x)
    bimap f g (Warning a x) = Warning (f a) (g x)

instance Bifoldable Warning where
    bifold = warning id id mappend
    bifoldr f g z = warning (`f` z) (`g` z) (\x y -> x `f` (y `g` z))
    bifoldl f g z = warning (z `f`) (z `g`) (\x y -> (z `f` x) `g` y)

instance Bifoldable1 Warning where
    bifold1 = warning id id (<>)

instance Bitraversable Warning where
    bitraverse f _ (Failure x) = Failure <$> f x
    bitraverse _ g (Success x) = Success <$> g x
    bitraverse f g (Warning x y) = Warning <$> f x <*> g y

instance Bitraversable1 Warning where
    bitraverse1 f _ (Failure x) = Failure <$> f x
    bitraverse1 _ g (Success x) = Success <$> g x
    bitraverse1 f g (Warning x y) = Warning <$> f x <.> g y

instance Semigroup a => Apply (Warning a) where
    Failure  a   <.> _            = Failure a
    Success    _ <.> Failure  b   = Failure b
    Success    f <.> Success    x = Success (f x)
    Success    f <.> Warning b x  = Warning b (f x)
    Warning a _  <.> Failure  b   = Failure (a <> b)
    Warning a f  <.> Success    x = Warning a (f x)
    Warning a f  <.> Warning b x  = Warning (a <> b) (f x)

instance (Semigroup a) => Applicative (Warning a) where
    pure = Success
    (<*>) = (<.>)

instance (Semigroup a) => Bind (Warning a) where
    Failure  a   >>- _ = Failure a
    Success    x >>- k = k x
    Warning a x >>- k = case k x of
                          Failure  b   -> Failure  (a <> b)
                          Success    y -> Warning a y
                          Warning b y -> Warning (a <> b) y

instance (Semigroup a) => Monad (Warning a) where
    return = pure
    (>>=) = (>>-)

{-
instance (Hashable a, Hashable b) => Hashable (Warning a b)

instance (NFData a, NFData b) => NFData (Warning a b) where
    rnf (Failure a)    = rnf a
    rnf (Success b)    = rnf b
    rnf (Warning a b) = rnf a `seq` rnf b

instance (Binary a, Binary b) => Binary (Warning a b) where
    put (Failure a)    = put (0 :: Int) >> put a
    put (Success b)    = put (1 :: Int) >> put b
    put (Warning a b) = put (2 :: Int) >> put a >> put b

    get = do
        i <- get
        case (i :: Int) of
            0 -> Failure <$> get
            1 -> Success <$> get
            2 -> Warning <$> get <*> get
            _ -> fail "Invalid Warning index"
-}

{-
instance Semigroup a => Semigroup (Signed a) where

  Positive a <> Positive b           = Positive $ a <> b
  Positive a <> Negative b           = Indeterminate $ a <> b
  Positive a <> Zero                 = Positive a
  Positive a <> Indeterminate e      = Indeterminate $ a <> e

  Negative a <> Negative b           = Negative $ a <> b
  Negative a <> Positive b           = Indeterminate $ a <> b
  Negative a <> Zero                 = Negative a
  Negative a <> Indeterminate e      = Indeterminate $ a <> e

  Zero <> a                          = a

  Indeterminate a <> Positive b      = Indeterminate $ a <> b
  Indeterminate a <> Negative b      = Indeterminate $ a <> b
  Indeterminate a <> Zero            = Indeterminate a
  Indeterminate a <> Indeterminate e = Indeterminate $ a <> e


instance Semigroup a => Monoid (Signed a) where

  mempty = Zero


instance Semiring a => Semiring (Signed a) where

  Positive a >< Positive b           = Positive $ a >< b
  Positive a >< Negative b           = Negative $ a >< b
  Positive _ >< Zero                 = Zero
  Positive a >< Indeterminate e      = Indeterminate $ a >< e

  Negative a >< Positive b           = Negative $ a >< b
  Negative a >< Negative b           = Positive $ a >< b
  Negative _ >< Zero                 = Zero
  Negative a >< Indeterminate e      = Indeterminate $ a >< e

  Zero >< _                          = Zero
 
  Indeterminate a >< Positive b      = Indeterminate $ a >< b
  Indeterminate a >< Negative b      = Indeterminate $ a >< b
  Indeterminate a >< Zero            = Zero
  Indeterminate a >< Indeterminate e = Indeterminate $ a >< e


instance Hemiring a => Hemiring (Signed a) where

  fromNatural = fromNaturalDef mempty $ Positive one


-- | Failure instance superimposes a 4-part ordering on top of the 
-- ordering of @a@.
-- 
instance Dioid a => Dioid (Signed a) where

  Positive a `ord` Positive b           = ord a b
  Positive a `ord` Indeterminate b      = ord a b
  Positive _ `ord` _                    = False

  Negative a `ord` Negative b           = ord a b
  Negative a `ord` Indeterminate b      = ord a b
  Negative _ `ord` _                    = True

  Zero `ord` Positive _                 = True
  Zero `ord` Negative _                 = False
  Zero `ord` Zero                       = True
  Zero `ord` Indeterminate a            = ord zero a

  Indeterminate a `ord` Positive b      = ord a b
  Indeterminate a `ord` Negative b      = ord a b
  Indeterminate a `ord` Zero            = ord a zero
  Indeterminate a `ord` Indeterminate b = ord a b

-}



