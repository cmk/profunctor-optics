{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}

#ifndef MIN_VERSION_template_haskell
#define MIN_VERSION_template_haskell(x,y,z) (defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 706)
#endif

-- Language.Haskell.TH was not marked as Safe before template-haskell-2.12.0
#if MIN_VERSION_template_haskell(2,12,0)
--{-# LANGUAGE Safe #-}
#else
{-# LANGUAGE Trustworthy #-}
#endif

{-# LANGUAGE  FlexibleContexts #-}
{-# LANGUAGE  FlexibleInstances #-}
{-# LANGUAGE  MultiParamTypeClasses #-}
{-# LANGUAGE  FunctionalDependencies #-}
module Data.Profunctor.Optic.TH.Internal
(
  -- * Name utilities
  HasName(..),
  newNames,

  -- * Type variable utilities
  HasTypeVars(..),
  typeVars,
  substTypeVars,

  -- * Miscellaneous utilities
  inlinePragma,
  conAppsT,
  quantifyType, quantifyType',
)
where

import qualified Data.Map as Map
import           Data.Map (Map)
import qualified Data.Set as Set
import           Data.Set (Set)
import           Data.List (nub)
import           Data.Maybe
import           Data.Profunctor.Optic
import           Language.Haskell.TH

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative
import           Data.Monoid
import           Data.Traversable (traverse)
#endif

class Field1 s t a b | s -> a, t -> b, s b -> t, t a -> s where
  {- |
Gives access to the 1st field of a tuple (up to 5-tuples).

Getting the 1st component:

>>> (1,2,3,4,5) ^. _1
1

Setting the 1st component:

>>> (1,2,3) & _1 .~ 10
(10,2,3)

Note that this lens is lazy, and can set fields even of 'undefined':

>>> set _1 10 undefined :: (Int, Int)
(10,*** Exception: Prelude.undefined

This is done to avoid violating a lens law stating that you can get back what you put:

>>> view _1 . set _1 10 $ (undefined :: (Int, Int))
10

The implementation (for 2-tuples) is:

@
'_1' f t = (,) '<$>' f    ('fst' t)
             '<*>' 'pure' ('snd' t)
@

or, alternatively,

@
'_1' f ~(a,b) = (\\a' -> (a',b)) '<$>' f a
@

(where @~@ means a <https://wiki.haskell.org/Lazy_pattern_match lazy pattern>).

'_2', '_3', '_4', and '_5' are also available (see below).
  -}
  _1 :: forall f. Functor f => (a -> f b) -> s -> f t
instance Field1 (a,b) (a',b) a a' where
  _1 k ~(a,b) = (\a' -> (a',b)) <$> k a
  {-# INLINE _1 #-}

instance Field1 (a,b,c) (a',b,c) a a' where
  _1 k ~(a,b,c) = (\a' -> (a',b,c)) <$> k a
  {-# INLINE _1 #-}

instance Field1 (a,b,c,d) (a',b,c,d) a a' where
  _1 k ~(a,b,c,d) = (\a' -> (a',b,c,d)) <$> k a
  {-# INLINE _1 #-}

instance Field1 (a,b,c,d,e) (a',b,c,d,e) a a' where
  _1 k ~(a,b,c,d,e) = (\a' -> (a',b,c,d,e)) <$> k a
  {-# INLINE _1 #-}

class Field2 s t a b | s -> a, t -> b, s b -> t, t a -> s where
  _2 :: forall f. Functor f => (a -> f b) -> s -> f t 

instance Field2 (a,b) (a,b') b b' where
  _2 k ~(a,b) = (\b' -> (a,b')) <$> k b
  {-# INLINE _2 #-}

instance Field2 (a,b,c) (a,b',c) b b' where
  _2 k ~(a,b,c) = (\b' -> (a,b',c)) <$> k b
  {-# INLINE _2 #-}

instance Field2 (a,b,c,d) (a,b',c,d) b b' where
  _2 k ~(a,b,c,d) = (\b' -> (a,b',c,d)) <$> k b
  {-# INLINE _2 #-}

instance Field2 (a,b,c,d,e) (a,b',c,d,e) b b' where
  _2 k ~(a,b,c,d,e) = (\b' -> (a,b',c,d,e)) <$> k b
  {-# INLINE _2 #-}

class Field3 s t a b | s -> a, t -> b, s b -> t, t a -> s where
  _3 :: forall f. Functor f => (a -> f b) -> s -> f t

instance Field3 (a,b,c) (a,b,c') c c' where
  _3 k ~(a,b,c) = (\c' -> (a,b,c')) <$> k c
  {-# INLINE _3 #-}

instance Field3 (a,b,c,d) (a,b,c',d) c c' where
  _3 k ~(a,b,c,d) = (\c' -> (a,b,c',d)) <$> k c
  {-# INLINE _3 #-}

instance Field3 (a,b,c,d,e) (a,b,c',d,e) c c' where
  _3 k ~(a,b,c,d,e) = (\c' -> (a,b,c',d,e)) <$> k c
  {-# INLINE _3 #-}


-- | Has a 'Name'
class HasName t where
  -- | Extract (or modify) the 'Name' of something
  name :: Lens' t Name

instance HasName TyVarBndr where
  name = lensVl tyVarBndrT
    where tyVarBndrT f (PlainTV n) = PlainTV <$> f n
          tyVarBndrT f (KindedTV n k) = (`KindedTV` k) <$> f n

instance HasName Name where
  name = id

-- | On @template-haskell-2.11.0.0@ or later, if a 'GadtC' or 'RecGadtC' has
-- multiple 'Name's, the leftmost 'Name' will be chosen.
instance HasName Con where
  name = lensVl conT
    where
      conT f (NormalC n tys)       = (`NormalC` tys) <$> f n
      conT f (RecC n tys)          = (`RecC` tys) <$> f n
      conT f (InfixC l n r)        = (\n' -> InfixC l n' r) <$> f n
      conT f (ForallC bds ctx con) = ForallC bds ctx <$> (flip runStar con $ name (Star f))
      conT f (GadtC ns argTys retTy) =
	(\n -> GadtC [n] argTys retTy) <$> f (head ns)
      conT f (RecGadtC ns argTys retTy) =
	(\n -> RecGadtC [n] argTys retTy) <$> f (head ns)

-- | Generate many new names from a given base name.
newNames :: String {- ^ base name -} -> Int {- ^ count -} -> Q [Name]
newNames base n = sequence [ newName (base++show i) | i <- [1..n] ]

-- | Provides for the extraction of free type variables, and alpha renaming.
class HasTypeVars t where
  -- When performing substitution into this traversal you're not allowed
  -- to substitute in a name that is bound internally or you'll violate
  -- the 'Traversal' laws, when in doubt generate your names with 'newName'.
  typeVarsEx :: Set Name -> Traversal' t Name

instance HasTypeVars TyVarBndr where
  typeVarsEx s = traversalVl $ \f b -> if Set.member (b ^. name) s then pure b else flip runStar b $ name (Star f)

instance HasTypeVars Name where
  typeVarsEx s = traversalVl $ \f n -> if Set.member n s then pure n else f n

instance HasTypeVars Type where
  typeVarsEx s = traversalVl tyT -- $ \f (VarT n)            -> VarT <$> typeVarsEx' s f n
    where 
      typeVarsEx' :: Applicative f => HasTypeVars t => Set Name -> (Name -> f Name) -> t -> f t 
      typeVarsEx' s = withTraversal $ typeVarsEx s
 
      tyT f (VarT n) = VarT <$> typeVarsEx' s f n
      tyT f (AppT l r) = AppT <$> typeVarsEx' s f l <*> typeVarsEx' s f r
      tyT f (SigT t k) = (`SigT` k) <$> typeVarsEx' s f t
      tyT f (ForallT bs ctx ty) = ForallT bs <$> typeVarsEx' s' f ctx <*> typeVarsEx' s' f ty where s' = s `Set.union` Set.fromList (bs ^.. typeVars)
      tyT _ t                   = pure t


{-
typeSelf :: Traversal' Type Type
typeSelf = traversalVl $ \f -> \case
  ForallT tyVarBndrs ctx ty ->
    let go (KindedTV nam kind) = KindedTV <$> pure nam <*> f kind
        go (PlainTV nam)       = pure (PlainTV nam)
    in ForallT <$> traverse go tyVarBndrs <*> traverse f ctx <*> f ty
  AppT ty1 ty2              -> AppT <$> f ty1 <*> f ty2
  SigT ty kind              -> SigT <$> f ty <*> f kind
  InfixT ty1 nam ty2        -> InfixT <$> f ty1 <*> pure nam <*> f ty2
  UInfixT ty1 nam ty2       -> UInfixT <$> f ty1 <*> pure nam <*> f ty2
  ParensT ty                -> ParensT <$> f ty
  ty                        -> pure ty
-}
#if !MIN_VERSION_template_haskell(2,10,0)
instance HasTypeVars Pred where
  typeVarsEx s = traversalVl $ \f (ClassP n ts) -> ClassP n <$> typeVarsEx s f ts
  typeVarsEx s = traversalVl $ \f (EqualP l r)  -> EqualP <$> typeVarsEx s f l <*> typeVarsEx s f r
#endif
{-
instance HasTypeVars Con where
  typeVarsEx s = traversalVl $ \f (NormalC n ts) ->
    NormalC n <$> (traverse . _2) (typeVarsEx s f) ts
  typeVarsEx s = traversalVl $ \f (RecC n ts) ->
    RecC n <$> (traverse . _3) (typeVarsEx s f) ts
  typeVarsEx s = traversalVl $ \f (InfixC l n r) ->
    InfixC <$> g l <*> pure n <*> g r
      where g (i, t) = (,) i <$> typeVarsEx s f t
  typeVarsEx s = traversalVl $ \f (ForallC bs ctx c) ->
    ForallC bs <$> typeVarsEx s' f ctx <*> typeVarsEx s' f c
      where s' = s `Set.union` Set.fromList (bs ^.. typeVars)
#if MIN_VERSION_template_haskell(2,11,0)
  typeVarsEx s = traversalVl $ \f (GadtC ns argTys retTy) ->
    GadtC ns <$> (traverse . _2) (typeVarsEx s f) argTys
             <*> typeVarsEx s f retTy
  typeVarsEx s = traversalVl $ \f (RecGadtC ns argTys retTy) ->
    RecGadtC ns <$> (traverse . _3) (typeVarsEx s f) argTys
                <*> typeVarsEx s f retTy
#endif
-}
instance HasTypeVars t => HasTypeVars [t] where
  typeVarsEx s = traversed . typeVarsEx s

instance HasTypeVars t => HasTypeVars (Maybe t) where
  typeVarsEx s = traversed . typeVarsEx s

-- Traverse /free/ type variables
typeVars :: HasTypeVars t => Traversal' t Name
typeVars = typeVarsEx mempty

-- Substitute using a map of names in for /free/ type variables
substTypeVars :: HasTypeVars t => Map Name Name -> t -> t
substTypeVars m = over typeVars $ \n -> fromMaybe n (Map.lookup n m)

-- | Generate an INLINE pragma.
inlinePragma :: Name -> [DecQ]
#if MIN_VERSION_template_haskell(2,8,0)
inlinePragma methodName = [pragInlD methodName Inline FunLike AllPhases]
#else
inlinePragma methodName = [pragInlD methodName (inlineSpecNoPhase True False)]
#endif

-- | Apply arguments to a type constructor.
conAppsT :: Name -> [Type] -> Type
conAppsT conName = foldl AppT (ConT conName)

-- | Template Haskell wants type variables declared in a forall, so we find
-- all free type variables in a given type and declare them.
quantifyType :: Cxt -> Type -> Type
quantifyType = quantifyType' Set.empty

-- | This function works like 'quantifyType' except that it takes a list of
-- variables to exclude from quantification.
quantifyType' :: Set Name -> Cxt -> Type -> Type
quantifyType' exclude c t = ForallT vs c t
  where
    vs = map PlainTV
       $ filter (`Set.notMember` exclude)
       $ nub -- stable order
       $ lists typeVars t
