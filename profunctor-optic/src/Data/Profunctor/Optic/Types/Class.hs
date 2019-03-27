{-# LANGUAGE UndecidableSuperClasses, TypeOperators , GADTs, DataKinds, KindSignatures, TypeFamilies #-}

{-# LANGUAGE TupleSections, FlexibleInstances, ConstraintKinds, PolyKinds, UndecidableInstances #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Profunctor.Optic.Types.Class (
    module Export
  , module Data.Profunctor.Optic.Types.Class
) where


import Data.Bifunctor                  as Export
-- import Data.Bitraversable              as Export 
import Data.Distributive               as Export
import Data.Tagged                     as Export
import Data.Functor.Const              as Export
import Data.Functor.Identity           as Export
import Data.Profunctor                 as Export
import Data.Profunctor.Types           as Export
import Data.Profunctor.Choice          as Export
import Data.Profunctor.Strong          as Export
import Data.Profunctor.Closed          as Export
import Data.Profunctor.Mapping         as Export
import Data.Profunctor.Traversing      as Export
import Data.Profunctor.Composition     as Export

--import Data.Kind (Constraint, Type)

import Data.Constraint
-- $setup
-- >>> :set -XTypeApplications
-- >>> :set -XScopedTypeVariables
-- >>> :set -XOverloadedStrings
-- >>> import Data.IORef
-- >>> import Data.Monoid (Sum(..))
-- >>> import Data.Profunctor.Optic


instance Class (Profunctor p) (Strong p) where cls = Sub Dict
instance Class (Profunctor p) (Costrong p) where cls = Sub Dict
instance Class (Profunctor p) (Choice p) where cls = Sub Dict
instance Class (Profunctor p) (Cochoice p) where cls = Sub Dict
instance Class (Profunctor p) (Closed p) where cls = Sub Dict
instance Class (Choice p, Strong p) (Traversing p) where cls = Sub Dict
instance Class (Traversing p, Closed p) (Mapping p) where cls = Sub Dict

instance (Traversing p, Traversing q) :=> Traversing (Procompose p q) where ins = Sub Dict

--instance () :=> Profunctor (Forget r) where ins = Sub Dict
--instance () :=> Profunctor (PRef r Profunctor) where ins = Sub Dict
--instance () :=> Profunctor (PRef r Mapping) where ins = Sub Dict
-- need e.g. (Profunctor p :- Strong p) :- (Profunctor (Ref r Profunctor) :- Profunctor (Ref r Strong))
--instance Profunctor (Ref r c :=> Traversing (Procompose p q) where ins = Sub Dict

{-
instance Foo a => Foo [a]
you can capture the relationship between the instance head and its body with

instance Foo a :=> Foo [a] where ins = Sub Dict

a :=> (Enum (Dict a))Source#	 
() :=> (Bounded Bool)Source#	 
() :=> (Bounded Char)Source#	 
() :=> (Bounded Int)


Profunctor (Tagged :: * -> * -> *)	 
Profunctor (Forget r)	 
Arrow p => Profunctor (WrappedArrow p)	 
Functor f => Profunctor (Costar f)	 
Functor f => Profunctor (Star f)	 
Profunctor (Copastro p)	 
Profunctor (Cotambara p)	 
Profunctor (Pastro p)	 
Profunctor p => Profunctor (Tambara p)	 
Profunctor (Environment p)	 
Profunctor p => Profunctor (Closure p)	 
Profunctor (CopastroSum p)	 
Profunctor (CotambaraSum p)	 
Profunctor (PastroSum p)	 
Profunctor p => Profunctor (TambaraSum p)	 
Profunctor (FreeTraversing p)	 
Profunctor p => Profunctor (CofreeTraversing p)	 
Profunctor (FreeMapping p)	 
Profunctor p => Profunctor (CofreeMapping p)	 
Profunctor p => Profunctor (Codensity p)	 
Profunctor (Coyoneda p)	 
Profunctor (Yoneda p)	 
Profunctor ((->) :: * -> * -> *)	 
Functor w => Profunctor (Cokleisli w)	 
(Profunctor p, Profunctor q) => Profunctor (Rift p q)	 
(Profunctor p, Profunctor q) => Profunctor (Procompose p q)	 
(Profunctor p, Profunctor q) => Profunctor (Ran p q)	 
(Functor f, Profunctor p) => Profunctor (Cayley f p)	 
Functor f => Profunctor (Joker f :: * -> * -> *)	 
Contravariant f => Profunctor (Clown f :: * -> * -> *)	 
(Profunctor p, Profunctor q) => Profunctor (Sum p q)	 
(Profunctor p, Profunctor q) => Profunctor (Product p q)	 
(Functor f, Profunctor p) => Profunctor (Tannen f p)	 
(Profunctor p, Functor f, Functor g) => Profunctor (Biff p f g)	 

Monad m => Strong (Kleisli m)	 
Strong (Forget r)	 
Arrow p => Strong (WrappedArrow p)	
Arrow is Strong Category

Functor m => Strong (Star m)	 
Strong (Pastro p)	 
Profunctor p => Strong (Tambara p)	 
Strong p => Strong (Closure p)	 
Strong (FreeTraversing p)	 
Profunctor p => Strong (CofreeTraversing p)	 
Strong (FreeMapping p)	 
Profunctor p => Strong (CofreeMapping p)	 
Strong p => Strong (Coyoneda p)	 
Strong p => Strong (Yoneda p)	 
Strong ((->) :: * -> * -> *)	 
(Strong p, Strong q) => Strong (Procompose p q)	 
(Functor f, Strong p) => Strong (Cayley f p)	 
Contravariant f => Strong (Clown f :: * -> * -> *)	 
(Strong p, Strong q) => Strong (Product p q)	 
(Functor f, Strong p) => Strong (Tannen f p)	 

Monad m => Choice (Kleisli m)	 
Choice (Tagged :: * -> * -> *)	 
Monoid r => Choice (Forget r)	 
ArrowChoice p => Choice (WrappedArrow p)	 
Traversable w => Choice (Costar w)	 
Applicative f => Choice (Star f)	 
Choice p => Choice (Tambara p)	 
Choice (PastroSum p)	 
Profunctor p => Choice (TambaraSum p)	 
Choice (FreeTraversing p)	 
Profunctor p => Choice (CofreeTraversing p)	 
Choice (FreeMapping p)	 
Profunctor p => Choice (CofreeMapping p)	 
Choice p => Choice (Coyoneda p)	 
Choice p => Choice (Yoneda p)	 
Choice ((->) :: * -> * -> *)	 
Comonad w => Choice (Cokleisli w)	
extract approximates costrength

(Choice p, Choice q) => Choice (Procompose p q)	 
(Functor f, Choice p) => Choice (Cayley f p)	 
Functor f => Choice (Joker f :: * -> * -> *)	 
(Choice p, Choice q) => Choice (Product p q)	 
(Functor f, Choice p) => Choice (Tannen f p)	 

(Distributive f, Monad f) => Closed (Kleisli f)	 
Closed (Tagged :: * -> * -> *)	 
Functor f => Closed (Costar f)	 
Distributive f => Closed (Star f)	 
Closed (Environment p)	 
Profunctor p => Closed (Closure p)	 
Closed (FreeMapping p)	 
Profunctor p => Closed (CofreeMapping p)	 
Closed p => Closed (Coyoneda p)	 
Closed p => Closed (Yoneda p)	 
Closed ((->) :: * -> * -> *)	 
Functor f => Closed (Cokleisli f)	 
(Closed p, Closed q) => Closed (Procompose p q)	 
(Closed p, Closed q) => Closed (Product p q)	 
(Functor f, Closed p) => Closed (Tannen f p)	 

(Monad m, Distributive m) => Mapping (Kleisli m)	 
(Applicative m, Distributive m) => Mapping (Star m)	 
Mapping (FreeMapping p)	 
Profunctor p => Mapping (CofreeMapping p)	 
Mapping p => Mapping (Coyoneda p)	 
Mapping p => Mapping (Yoneda p)	 
Mapping ((->) :: * -> * -> *)	 
(Mapping p, Mapping q) => Mapping (Procompose p q)	

MonadFix m => Costrong (Kleisli m)	 
Costrong (Tagged :: * -> * -> *)	 
ArrowLoop p => Costrong (WrappedArrow p)	 
Functor f => Costrong (Costar f)	 
Costrong (Copastro p)	 
Costrong (Cotambara p)	 
Costrong p => Costrong (Coyoneda p)	 
Costrong p => Costrong (Yoneda p)	 
Costrong ((->) :: * -> * -> *)	 
Functor f => Costrong (Cokleisli f)	 
(Corepresentable p, Corepresentable q) => Costrong (Procompose p q)	 
(Costrong p, Costrong q) => Costrong (Product p q)	 
(Functor f, Costrong p) => Costrong (Tannen f p)	

Applicative f => Cochoice (Costar f)	 
Traversable f => Cochoice (Star f)	 
Cochoice (CopastroSum p)	 
Cochoice (CotambaraSum p)	 
Cochoice p => Cochoice (Coyoneda p)	 
Cochoice p => Cochoice (Yoneda p)	 
Cochoice ((->) :: * -> * -> *)	 
(Cochoice p, Cochoice q) => Cochoice (Product p q)	 
(Functor f, Cochoice p) => Cochoice (Tannen f p)	 


Monad m => Traversing (Kleisli m)	 
Monoid m => Traversing (Forget m)	 
Applicative m => Traversing (Star m)	 
Traversing (FreeTraversing p)	 
Profunctor p => Traversing (CofreeTraversing p)	 
Traversing (FreeMapping p)	 
Profunctor p => Traversing (CofreeMapping p)	 
Traversing p => Traversing (Coyoneda p)	 
Traversing p => Traversing (Yoneda p)	 
Traversing ((->) :: * -> * -> *)	 
(Traversing p, Traversing q) => Traversing (Procompose p q)	 

(Monad m, Functor m) => Sieve (Kleisli m) m	 
Functor f => Sieve (Star f) f	 
Sieve (Forget r) (Const r :: * -> *)	 
Sieve ((->) :: * -> * -> *) Identity	 
(Sieve p f, Sieve q g) => Sieve (Procompose p q) (Compose g f)	 

Functor f => Cosieve (Costar f) f	 
Cosieve (Tagged :: * -> * -> *) (Proxy :: * -> *)	 
Cosieve ((->) :: * -> * -> *) Identity	 
Functor w => Cosieve (Cokleisli w) w	 
(Cosieve p f, Cosieve q g) => Cosieve (Procompose p q) (Compose f g)	 




-}





--foo = (Strong (->)) \\ ((cls :: (Strong (->))) :- (Profunctor (Strong (->))))

--bar = (Choice Tagged) \\ (cls :: (Choice Tagged) :- (Profunctor Tagged))





-- Entailment relationships not already given by 'profunctors':
class Equalizing (p :: * -> * -> *)
instance Equalizing p

class (Strong p, Choice p) => AffineTraversing p
instance (Strong p, Choice p) => AffineTraversing p

class (Bifunctor p, Choice p) => Reviewing p
instance (Bifunctor p, Choice p) => Reviewing p

class (Bicontravariant p, Strong p) => Getting p
instance (Bicontravariant p, Strong p) => Getting p

class (Bicontravariant p, Traversing p) => Folding p
instance (Bicontravariant p, Traversing p) => Folding p

class (Bicontravariant p, Choice p, Traversing p) => AffineFolding p
instance (Bicontravariant p, Choice p, Traversing p) => AffineFolding p


class Bicontravariant p where
    cimap :: (b -> a) -> (d -> c) -> p a c -> p b d
    cimap f g = cofirst f . cosecond g

    cofirst :: (b -> a) -> p a c -> p b c
    cofirst f = cimap f id

    cosecond :: (c -> b) -> p a b -> p a c
    cosecond = cimap id

    {-# MINIMAL cimap | (cofirst, cosecond) #-}


instance Bicontravariant (Forget r) where

    cimap f _ (Forget p) = Forget (p . f)



