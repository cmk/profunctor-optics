module Data.Profunctor.Optic.Lens where

import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Type
import Data.Void (Void, absurd)
import Foreign.C.Types
import GHC.IO.Exception
import System.IO
import qualified Control.Foldl as F

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :m + Control.Exception
-- >>> :m + Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'Lens' 
---------------------------------------------------------------------

-- | Build a 'Strong' optic from a getter and setter.
--
-- \( \quad \mathsf{Lens}\;S\;A = \exists C, S \cong C \times A \)
--
-- /Caution/: In order for the generated lens family to be well-defined,
-- you must ensure that the three lens laws hold:
--
-- * @sa (sbt s a) ≡ a@
--
-- * @sbt s (sa s) ≡ s@
--
-- * @sbt (sbt s a1) a2 ≡ sbt s a2@
--
-- See 'Data.Profunctor.Optic.Property'.
--
lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens sa sbt = dimap (id &&& sa) (uncurry sbt) . psecond

-- | Build a 'Lens' from its free tensor representation.
--
matching :: (s -> (x , a)) -> ((x , b) -> t) -> Lens s t a b
matching f g = dimap f g . psecond

-- | Transform a Van Laarhoven lens into a profunctor lens.
--
vllens :: (forall f. Functor f => (a -> f b) -> s -> f t) -> Lens s t a b
vllens o = dimap ((info &&& values) . o (flip PStore id)) (uncurry id . swp) . pfirst

-- | Build a 'Costrong' optic from a getter and setter. 
--
-- * @relens f g ≡ \f g -> re (lens f g)@
--
-- * @review $ relens f g ≡ f@
--
-- * @set . re $ re (lens f g) ≡ g@
--
-- A 'Relens' is a 'Review', so you can specialise types to obtain:
--
-- @ 'review' :: 'Relens'' s a -> a -> s @
--
relens :: (b -> t) -> (b -> s -> a) -> Relens s t a b
relens sa sbt = unsecond . dimap (uncurry sbt) (id &&& sa)

-- | TODO: Document
--
cloneLens :: ALens s t a b -> Lens s t a b
cloneLens o = withLens o lens 

---------------------------------------------------------------------
-- 'LensRep'
---------------------------------------------------------------------

-- | The `LensRep` profunctor precisely characterizes a 'Lens'.
data LensRep a b s t = LensRep (s -> a) (s -> b -> t)

type ALens s t a b = Optic (LensRep a b) s t a b

type ALens' s a = ALens s s a a

instance Profunctor (LensRep a b) where

  dimap f g (LensRep sa sbt) = LensRep (sa . f) (\s -> g . sbt (f s))

instance Strong (LensRep a b) where

  first' (LensRep sa sbt) =
    LensRep (\(a, _) -> sa a) (\(s, c) b -> ((sbt s b), c))

  second' (LensRep sa sbt) =
    LensRep (\(_, a) -> sa a) (\(c, s) b -> (c, (sbt s b)))

instance Sieve (LensRep a b) (PStore a b) where
  sieve (LensRep sa sbt) s = PStore (sa s) (sbt s)

instance Representable (LensRep a b) where
  type Rep (LensRep a b) = PStore a b

  tabulate f = LensRep (\s -> info (f s)) (\s -> values (f s))

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | TODO: Document
--
withLens :: ALens s t a b -> ((s -> a) -> (s -> b -> t) -> r) -> r
withLens l f = case l (LensRep id $ \_ b -> b) of LensRep x y -> f x y

-- | Analogous to @(***)@ from 'Control.Arrow'
--
pairing :: Lens s1 t1 a1 b1 -> Lens s2 t2 a2 b2 -> Lens (s1 , s2) (t1 , t2) (a1 , a2) (b1 , b2)
pairing = paired

-- | TODO: Document
--
lens2 :: (s -> a) -> (s -> b -> t) -> Lens (c, s) (d, t) (c, a) (d, b)
lens2 f g = between runPaired Paired (lens f g)

---------------------------------------------------------------------
-- Common lenses 
---------------------------------------------------------------------

-- | TODO: Document
--
_1 :: Lens (a , c) (b , c) a b
_1 = pfirst

-- | TODO: Document
--
_2 :: Lens (c , a) (c , b) a b
_2 = psecond

-- | TODO: Document
--
lower1 :: Iso s t (a , x) (b , x) -> Lens s t a b
lower1 = (. _1)

-- | TODO: Document
--
lower2 :: Iso s t (x , a) (x , b) -> Lens s t a b
lower2 = (. _2)

-- | There is a `Unit` in everything.
--
unit :: Lens' a ()
unit = lens (const ()) const

-- | There is everything in a `Void`.
--
void :: Lens' Void a
void = lens absurd const

-- | TODO: Document
--
ix :: Eq k => k -> Lens' (k -> v) v
ix k = lens ($ k) (\g v' x -> if (k == x) then v' else g x)

-- | TODO: Document
--
foldedl :: Lens s s a b -> s -> F.Fold b a
foldedl o x = withLens o $ \sa sbt -> F.Fold sbt x sa

-- | TODO: Document
--
uncurried :: Lens (a , b) c a (b -> c)
uncurried = rmap apply . pfirst

----------------------------------------------------------------------------------------------------
-- IO Exceptions
----------------------------------------------------------------------------------------------------

-- | Where the error happened.
--
location :: Lens' IOException String
location = lens ioe_location $ \s e -> s { ioe_location = e }

-- | Error type specific information.
--
description :: Lens' IOException String
description = lens ioe_description $ \s e -> s { ioe_description = e }

-- | The handle used by the action flagging this error.
-- 
handle :: Lens' IOException (Maybe Handle)
handle = lens ioe_handle $ \s e -> s { ioe_handle = e }

-- | 'fileName' the error is related to.
--
fileName :: Lens' IOException (Maybe FilePath)
fileName = lens ioe_filename $ \s e -> s { ioe_filename = e }

-- | 'errno' leading to this error, if any.
--
errno :: Lens' IOException (Maybe CInt)
errno = lens ioe_errno $ \s e -> s { ioe_errno = e }

errorType :: Lens' IOException IOErrorType
errorType = lens ioe_type $ \s e -> s { ioe_type = e }
