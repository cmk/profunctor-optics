{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}

#ifndef MIN_VERSION_template_haskell
#define MIN_VERSION_template_haskell(x,y,z) (defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 706)
#endif

#ifndef MIN_VERSION_containers
#define MIN_VERSION_containers(x,y,z) 1
#endif

#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE TemplateHaskellQuotes #-}
#else
{-# LANGUAGE TemplateHaskell #-}
#endif


{- |
Module      :  Lens.Micro.TH
Copyright   :  (C) 2013-2016 Eric Mertens, Edward Kmett, Artyom Kazak; 2018 Monadfix
License     :  BSD-style (see the file LICENSE)
-}
module Data.Profunctor.Optic.TH
(
  -- * Dealing with “not in scope” errors
  -- $errors-note

  -- * Using this module in GHCi
  -- $ghci-note

  -- * 'View' and 'Fold'
  -- $view-fold-note

  -- * Generating lenses
  makeOptics,
  makeOpticsFor,
  makeOpticsWith,

  -- * Default lens rules
  OpticRules,
  DefName(..),
  opticRules,
  opticRulesFor,
  classyRules,
  camelCaseFields,

  -- * Configuring lens rules
  opticField,
  opticClass,
  createClass,
  simpleOptics,
  generateSignatures,
  generateUpdateableOptics,
  generateLazyPatterns,
) where

import           Control.Monad
import           Control.Monad.Trans.State
import           Data.Char
import           Data.Data
import           Data.Either
import           Data.Either.Optic
import qualified Data.Map as Map
import           Data.Map (Map)
import           Data.Monoid
import qualified Data.Set as Set
import           Data.Set (Set)
import           Data.Functor.Identity
import           Data.List (nub, findIndices, stripPrefix, isPrefixOf)
import           Data.Maybe
import           Data.Tuple.Optic
import           Data.Profunctor.Optic
import           Data.Profunctor.Optic.Prelude hiding (elem)
import           Data.Profunctor.Optic.TH.Internal
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative
import           Data.Traversable (traverse, sequenceA)
#endif


------------------------------------------------------------------------
-- Field generation parameters
------------------------------------------------------------------------

{- |
Rules used to generate lenses. The fields are intentionally not exported; to create your own rules, see lenses in the “Configuring lens rules” section. You'd have to customise one of the existing rulesets; for an example of doing that, see 'makeOpticsWith'.
-}
data OpticRules = OpticRules
  { _simpleOptics    :: Bool
  , _generateSigs    :: Bool
  , _generateClasses :: Bool
  , _allowIsos       :: Bool
  , _allowUpdates    :: Bool -- Allow Lens/Traversal (otherwise View/Fold)
  , _lazyPatterns    :: Bool
  -- Type Name -> Field Names -> Target Field Name -> Definition Names
  , _fieldToDef      :: Name -> [Name] -> Name -> [DefName]
  -- Type Name -> (Class Name, Top Method)
  , _classyOptics    :: Name -> Maybe (Name, Name)
  }

{- |
Name to give to a generated lens (used in 'opticField').
-}
data DefName
  = TopName Name          -- ^ Simple top-level definiton name
  | MethodName Name Name  -- ^ 'makeFields'-style class name and method name
  deriving (Show, Eq, Ord)


------------------------------------------------------------------------
-- Miscellaneous utility functions
------------------------------------------------------------------------

liftState :: Monad m => m a -> StateT s m a
liftState act = StateT (\s -> liftM (flip (,) s) act)

-- Utilities

-- @fromSet@ wasn't always there, and we need compatibility with
-- containers-0.4 to compile on GHC 7.4.
fromSet :: (k -> v) -> Set.Set k -> Map.Map k v
#if MIN_VERSION_containers(0,5,0)
fromSet = Map.fromSet
#else
fromSet f x = Map.fromDistinctAscList [ (k,f k) | k <- Set.toAscList x ]
#endif

-- like 'rewrite' from uniplate
rewrite :: (Data a, Data b) => (a -> Maybe a) -> b -> b
rewrite f mbA = case cast mbA of
  Nothing -> gmapT (rewrite f) mbA
  Just a  -> let a' = gmapT (rewrite f) a
             in  fromJust . cast $ fromMaybe a' (f a')

-- like 'children' from uniplate
children :: Data a => a -> [a]
children = catMaybes . gmapQ cast

elemOf :: Eq a => AFold (Endo [a]) s a -> a -> s -> Bool
elemOf l x s = elem x (s ^.. l)

lengthOf :: AFold (Endo [a]) s a -> s -> Int
lengthOf l s = length (s ^.. l)

setOf :: Ord a => AFold (Endo [a]) s a -> s -> Set a
setOf o s = Set.fromList (s ^.. o)

forallt :: Traversal' Type ([TyVarBndr], Cxt, Type)
forallt = traversalVl foralltVl
  where foralltVl f (ForallT a b c) = (\(x, y, z) -> ForallT x y z) <$> f (a, b, c)
        foralltVl _ other = pure other



{- $errors-note

When you use Template Haskell, the order of declarations suddenly starts to matter. For instance, if you try to use 'makeOptics', 'makeFields', etc before the type is defined, you'll get a “not in scope” error:

@
'makeOptics' ''Foo

data Foo = Foo {_foo :: Int}
@

@
Not in scope: type constructor or class ‘Foo’ …
    In the Template Haskell quotation ''Foo
@

You can't refer to generated lenses before you call 'makeOptics', either:

@
data Foo = Foo {_foo :: Int}

bar :: Lens' Foo Int
bar = foo

'makeOptics' ''Foo
@

@
Not in scope: ‘foo’ …
    Perhaps you meant one of these:
      data constructor ‘Foo’ (line 1), ‘_foo’ (line 1)
@
-}

{- $ghci-note

You can use 'makeOptics' and friends to define lenses right from GHCi, but it's slightly tricky.

First, enable Template Haskell:

>>> :set -XTemplateHaskell

Then define a bogus type (you can use any name in place of @M@, and you can use the same name many times), and follow the definition by the actual Template Haskell command you want to use:

>>> data M; makeOptics ''Foo

This will generate lenses for @Foo@ and you'll be able to use them from GHCi.

If you want, you can define the type and lenses for it simultaneously with @:{@ and @:}@:

@
>>> :{
data Foobar = Foobar {
  _foo :: Int,
  _bar :: Bool }
  deriving (Eq, Show)

makeOptics ''Foobar
:}
@
-}

{- $view-fold-note

When updates are forbidden (by using 'generateUpdateableOptics'), or when a field simply can't be updated (for instance, in the presence of @forall@), instead of 'Lens' and 'Traversal' we generate 'View' and 'Fold'.
-}



{- |
Generate optics for a data type or a newtype.

To use it, you have to enable Template Haskell first:

@
\{\-\# LANGUAGE TemplateHaskell \#\-\}
@

Then, after declaring the datatype (let's say @Foo@), add @makeOptics ''Foo@ on a separate line (if you do it before the type is declared, you'll get a “not in scope” error – see the section at the top of this page):

@
data Foo = Foo {
  _x :: Int,
  _y :: Bool }

'makeOptics' ''Foo
@

This would generate the following optics, which can be used to access the fields of @Foo@:

@
x :: 'Lens'' Foo Int
x = lensVl $ \f foo -> (\\x' -> foo {_x = x'}) '<$>' f (_x foo)

y :: 'Lens'' Foo Bool
y = lensVl $ \f foo -> (\\y' -> foo {_y = y'}) '<$>' f (_y foo)
@

(If you don't want a lens to be generated for some field, don't prefix it with “_”.)

If you want to create optics for many types, you can do it all in one place like this (of course, instead you just can use 'makeOptics' several times if you feel it would be more readable):

@
data Foo = ...
data Bar = ...
data Quux = ...

'concat' '<$>' 'mapM' 'makeOptics' [''Foo, ''Bar, ''Quux]
@

When the data type has type parameters, it's possible for a lens to do a polymorphic update – i.e. change the type of the thing along with changing the type of the field. For instance, with this type

@
data Foo a = Foo {
  _x :: a,
  _y :: Bool }
@

the following lenses would be generated:

@
x :: 'Lens' (Foo a) (Foo b) a b
y :: 'Lens'' (Foo a) Bool
@

However, when there are several fields using the same type parameter, type-changing updates are no longer possible:

@
data Foo a = Foo {
  _x :: a,
  _y :: a }
@

generates

@
x :: 'Lens'' (Foo a) a
y :: 'Lens'' (Foo a) a
@

Finally, when the type has several constructors, some of fields may not be /always/ present – for those, a 'Traversal' is generated instead. For instance, in this example @y@ can be present or absent:

@
data FooBar
  = Foo { _x :: Int, _y :: Bool }
  | Bar { _x :: Int }
@

and the following accessors would be generated:

@
x :: 'Lens'' FooBar Int
y :: 'Traversal'' FooBar Bool
@

-}
makeOptics :: Name -> DecsQ
makeOptics = makeFieldOptics opticRules

{- |
Like 'makeOptics', but lets you choose your own names for lenses:

@
data Foo = Foo {foo :: Int, bar :: Bool}

'makeOpticsFor' [(\"foo\", \"fooLens\"), (\"bar\", \"_bar\")] ''Foo
@

would create lenses called @fooLens@ and @_bar@. This is useful, for instance, when you don't want to prefix your fields with underscores and want to prefix /lenses/ with underscores instead.

If you give the same name to different fields, it will generate a 'Traversal' instead:

@
data Foo = Foo {slot1, slot2, slot3 :: Int}

'makeOpticsFor' [(\"slot1\", \"slots\"),
               (\"slot2\", \"slots\"),
               (\"slot3\", \"slots\")] ''Foo
@

would generate

@
slots :: 'Traversal'' Foo Int
slots = traversalVl $ \f foo -> Foo '<$>' f (slot1 foo)
                                    '<*>' f (slot2 foo)
                                    '<*>' f (slot3 foo)
@
-}
makeOpticsFor :: [(String, String)] -> Name -> DecsQ
makeOpticsFor fields = makeFieldOptics (opticRulesFor fields)

{- |
Generate lenses with custom parameters.

To see what exactly you can customise, look at the “Configuring lens rules” section. Usually you would build upon the 'opticRules' configuration, which is used by 'makeOptics':

@
'makeOptics' = 'makeOpticsWith' 'opticRules'
@

Here's an example of generating lenses that would use lazy patterns:

@
data Foo = Foo {_x, _y :: Int}

'makeOpticsWith' ('opticRules' '&' 'generateLazyPatterns' '.~' True) ''Foo
@

When there are several modifications to the rules, the code looks nicer when you use 'flip':

@
'flip' 'makeOpticsWith' ''Foo $
  'opticRules'
    '&' 'generateLazyPatterns' '.~' True
    '&' 'generateSignatures'   '.~' False
@
-}
makeOpticsWith :: OpticRules -> Name -> DecsQ
makeOpticsWith = makeFieldOptics

{- |
Generate simple (monomorphic) lenses even when type-changing lenses are possible – i.e. 'Lens'' instead of 'Lens' and 'Traversal'' instead of 'Traversal'. Just in case, here's an example of a situation when type-changing lenses would be normally generated:

@
data Foo a = Foo { _foo :: a }
@

Generated lens:

@
foo :: 'Lens' (Foo a) (Foo b) a b
@

Generated lens with 'simpleOptics' turned on:

@
foo :: 'Lens'' (Foo a) a
@

This option is disabled by default.
-}
simpleOptics :: Lens' OpticRules Bool
simpleOptics = lensVl $ \f r -> fmap (\x -> r { _simpleOptics = x}) (f (_simpleOptics r))

{- |
Supply type signatures for the generated lenses.

This option is enabled by default. Disable it if you want to write the signature by yourself – for instance, if the signature should be more restricted, or if you want to write haddocks for the lens (as haddocks are attached to the signature and not to the definition).
-}
generateSignatures :: Lens' OpticRules Bool
generateSignatures = lensVl $ \f r -> fmap (\x -> r { _generateSigs = x}) (f (_generateSigs r))

{- |
Generate “updateable” optics. When turned off, 'Fold's will be generated instead of 'Traversal's and 'View's will be generated instead of 'Lens'es.

This option is enabled by default. Disabling it can be useful for types with invariants (also known as “types with smart constructors”) – if you generate updateable optics, anyone would be able to use them to break your invariants.
-}
generateUpdateableOptics :: Lens' OpticRules Bool
generateUpdateableOptics = lensVl $ \f r -> fmap (\x -> r { _allowUpdates = x}) (f (_allowUpdates r))

{- |
Generate lenses using lazy pattern matches. This can allow fields of an undefined value to be initialized with lenses:

@
data Foo = Foo {_x :: Int, _y :: Bool}
  deriving Show

'makeOpticsWith' ('opticRules' '&' 'generateLazyPatterns' '.~' True) ''Foo
@

@
>>> 'undefined' '&' x '.~' 8 '&' y '.~' True
Foo {_x = 8, _y = True}
@

(Without 'generateLazyPatterns', the result would be just 'undefined'.)

This option is disabled by default. The downside of enabling it is that it can lead to space-leaks and code-size\/compile-time increases when lenses are generated for large records.

When you have a lazy lens, you can get a strict lens from it by composing with ('$!'):

@
strictLens = ('$!') . lazyLens
@
-}
generateLazyPatterns :: Lens' OpticRules Bool
generateLazyPatterns = lensVl $ \f r -> fmap (\x -> r { _lazyPatterns = x}) (f (_lazyPatterns r))

{- |
This lets you choose which fields would have lenses generated for them and how would those lenses be called. To do that, you provide a function that would take a field name and output a list (possibly empty) of lenses that should be generated for that field.

Here's the full type of the function you have to provide:

@
'Name' ->     -- The datatype lenses are being generated for
['Name'] ->   -- A list of all fields of the datatype
'Name' ->     -- The current field
['DefName']   -- A list of lens names
@

Most of the time you won't need the first 2 parameters, but sometimes they are useful – for instance, the list of all fields would be useful if you wanted to implement a slightly more complicated rule like “if some fields are prefixed with underscores, generate lenses for them, but if no fields are prefixed with underscores, generate lenses for /all/ fields”.

As an example, here's a function used by default. It strips “_” off the field name, lowercases the next character after “_”, and skips the field entirely if it doesn't start with “_”:

@
\\_ _ n ->
  case 'nameBase' n of
    \'_\':x:xs -> ['TopName' ('mkName' ('toLower' x : xs))]
    _        -> []
@

You can also generate classes (i.e. what 'makeFields' does) by using @'MethodName' className lensName@ instead of @'TopName' lensName@.
-}
opticField :: Lens' OpticRules (Name -> [Name] -> Name -> [DefName])
opticField  = lensVl $ \f r -> fmap (\x -> r { _fieldToDef = x}) (f (_fieldToDef r))

{- |
This lets you choose whether a class would be generated for the type itself (like 'makeClassy' does). If so, you can choose the name of the class and the name of the type-specific lens.

For 'makeOptics' and 'makeFields' this is just @const Nothing@. For 'makeClassy' this function is defined like this:

@
\\n ->
  case 'nameBase' n of
    x:xs -> Just ('mkName' ("Has" ++ x:xs), 'mkName' ('toLower' x : xs))
    []   -> Nothing
@
-}
opticClass :: Lens' OpticRules (Name -> Maybe (Name, Name))
opticClass  = lensVl $ \f r -> fmap (\x -> r { _classyOptics = x }) (f (_classyOptics r))

{- |
Decide whether generation of classes is allowed at all.

If this is disabled, neither 'makeFields' nor 'makeClassy' would work, regardless of values of 'opticField' or 'opticClass'. On the other hand, if 'opticField' and 'opticClass' don't generate any classes, enabling this won't have any effect.
-}
createClass :: Lens' OpticRules Bool
createClass  = lensVl $ \f r -> fmap (\x -> r { _generateClasses = x}) (f (_generateClasses r))

{- |
Lens rules used by default (i.e. in 'makeOptics'):

* 'generateSignatures' is turned on
* 'generateUpdateableOptics' is turned on
* 'generateLazyPatterns' is turned off
* 'simpleOptics' is turned off
* 'opticField' strips “_” off the field name, lowercases the next character after “_”, and skips the field entirely if it doesn't start with “_” (you can see how it's implemented in the docs for 'opticField')
* 'opticClass' isn't used (i.e. defined as @const Nothing@)
-}
opticRules :: OpticRules
opticRules = OpticRules
  { _simpleOptics    = False
  , _generateSigs    = True
  , _generateClasses = False
  , _allowIsos       = True
  , _allowUpdates    = True
  , _lazyPatterns    = False
  , _classyOptics    = const Nothing
  , _fieldToDef      = \_ _ n ->
       case nameBase n of
         '_':x:xs -> [TopName (mkName (toLower x:xs))]
         _        -> []
  }

{- |
A modification of 'opticRules' used by 'makeOpticsFor' (the only difference is that a simple lookup function is used for 'opticField').
-}
opticRulesFor
  :: [(String, String)] -- ^ @[(fieldName, lensName)]@
  -> OpticRules
opticRulesFor fields = opticRules & opticField .~ mkNameLookup fields

mkNameLookup :: [(String,String)] -> Name -> [Name] -> Name -> [DefName]
mkNameLookup kvs _ _ field =
  [ TopName (mkName v) | (k,v) <- kvs, k == nameBase field]

_head = setter f
  where f _ [] = []
        f g (a:as) = (g a):as
{- |
Lens rules used by 'makeFields':

* 'generateSignatures' is turned on
* 'generateUpdateableOptics' is turned on
* 'generateLazyPatterns' is turned off
* 'simpleOptics' is turned on (unlike in 'opticRules')
* 'opticField' is more complicated – it takes fields which are prefixed with the name of the type they belong to (e.g. “fooFieldName” for “Foo”), strips that prefix, and generates a class called “HasFieldName” with a single method called “fieldName”. If some fields are prefixed with underscores, underscores would be stripped too, but then fields without underscores won't have any lenses generated for them. Also note that e.g. “foolish” won't have a lens called “lish” generated for it – the prefix must be followed by a capital letter (or else it wouldn't be camel case).
* 'opticClass' isn't used (i.e. defined as @const Nothing@)
-}
camelCaseFields :: OpticRules
camelCaseFields = defaultFieldRules

camelCaseNamer :: Name -> [Name] -> Name -> [DefName]
camelCaseNamer tyName fields field = maybeToList $ do

  fieldPart <- stripPrefix expectedPrefix (nameBase field)
  method    <- computeMethod fieldPart
  let cls = "Has" ++ fieldPart
  return (MethodName (mkName cls) (mkName method))

  where
  expectedPrefix = optUnderscore ++ over _head toLower (nameBase tyName)

  optUnderscore  = ['_' | any (isPrefixOf "_" . nameBase) fields ]

  computeMethod (x:xs) | isUpper x = Just (toLower x : xs)
  computeMethod _                  = Nothing

defaultFieldRules :: OpticRules
defaultFieldRules = OpticRules
  { _simpleOptics    = True
  , _generateSigs    = True
  , _generateClasses = True
  , _allowIsos       = True
  , _allowUpdates    = True
  , _lazyPatterns    = False
  , _classyOptics    = const Nothing
  , _fieldToDef      = camelCaseNamer
  }

underscoreNoPrefixNamer :: Name -> [Name] -> Name -> [DefName]
underscoreNoPrefixNamer _ _ n =
  case nameBase n of
    '_':x:xs -> [TopName (mkName (toLower x:xs))]
    _        -> []

{- |
Lens rules used by 'makeClassy':

* 'generateSignatures' is turned on
* 'generateUpdateableOptics' is turned on
* 'generateLazyPatterns' is turned off
* 'simpleOptics' is turned on (unlike in 'opticRules')
* 'opticField' is the same as in 'opticRules'
* 'opticClass' just adds “Has” to the name of the type (so for “Person” the generated class would be called “HasPerson” and the type-specific lens in that class would be called “person”)
-}
classyRules :: OpticRules
classyRules = OpticRules
  { _simpleOptics    = True
  , _generateSigs    = True
  , _generateClasses = True
  , _allowIsos       = False -- generating Isos would hinder "subtyping"
  , _allowUpdates    = True
  , _lazyPatterns    = False
  , _classyOptics    = \n ->
        case nameBase n of
          x:xs -> Just (mkName ("Has" ++ x:xs), mkName (toLower x:xs))
          []   -> Nothing
  , _fieldToDef      = underscoreNoPrefixNamer
  }

-- FieldTH.hs

{--



-- | Make lenses for all records in the given declaration quote. All record
-- syntax in the input will be stripped off.
--
-- /e.g./
--
-- @
-- declareLenses [d|
--   data Foo = Foo { fooX, fooY :: 'Int' }
--     deriving 'Show'
--   |]
-- @
--
-- will create
--
-- @
-- data Foo = Foo 'Int' 'Int' deriving 'Show'
-- fooX, fooY :: 'Lens'' Foo Int
-- @
declareLenses :: DecsQ -> DecsQ
declareLenses
  = declareLensesWith
  $ opticRules
  & opticField .~ \_ _ n -> [TopName n]

-- | Similar to 'makeOpticsFor', but takes a declaration quote.
declareLensesFor :: [(String, String)] -> DecsQ -> DecsQ
declareLensesFor fields
  = declareLensesWith
  $ opticRulesFor fields
  & opticField .~ \_ _ n -> [TopName n]

-- | Generate a 'Control.Lens.Type.Prism' for each constructor of each data type.
--
-- /e.g./
--
-- @
-- declarePrisms [d|
--   data Exp = Lit Int | Var String | Lambda{ bound::String, body::Exp }
--   |]
-- @
--
-- will create
--
-- @
-- data Exp = Lit Int | Var String | Lambda { bound::String, body::Exp }
-- _Lit :: 'Prism'' Exp Int
-- _Var :: 'Prism'' Exp String
-- _Lambda :: 'Prism'' Exp (String, Exp)
-- @
declarePrisms :: DecsQ -> DecsQ
declarePrisms = declareWith $ \dec -> do
  emit =<< liftDeclare (makeDecPrisms True dec)
  return dec


-- | @ declareFields = 'declareLensesWith' 'defaultFieldRules' @
declareFields :: DecsQ -> DecsQ
declareFields = declareLensesWith defaultFieldRules

-- | Declare lenses for each records in the given declarations, using the
-- specified 'OpticRules'. Any record syntax in the input will be stripped
-- off.
declareLensesWith :: OpticRules -> DecsQ -> DecsQ
declareLensesWith rules = declareWith $ \dec -> do
  emit =<< lift (makeFieldOpticsForDec' rules dec)
  return $ stripFields dec


-- Declaration quote stuff

declareWith :: (Dec -> Declare Dec) -> DecsQ -> DecsQ
declareWith fun = (runDeclare . traverseDataAndNewtype fun =<<)

-- | Monad for emitting top-level declarations as a side effect. We also track
-- the set of field class 'Name's that have been created and consult them to
-- avoid creating duplicate classes.
type Declare = WriterT (Endo [Dec]) (StateT (Set Name) Q)

liftDeclare :: Q a -> Declare a
liftDeclare = lift . lift

runDeclare :: Declare [Dec] -> DecsQ
runDeclare dec = do
  (out, endo) <- evalStateT (runWriterT dec) Set.empty
  return $ out ++ appEndo endo []

emit :: [Dec] -> Declare ()
emit decs = tell $ Endo (decs++)

-- | Traverse each data, newtype, data instance or newtype instance
-- declaration.
traverseDataAndNewtype :: (Applicative f) => (Dec -> f Dec) -> [Dec] -> f [Dec]
traverseDataAndNewtype f decs = traverse go decs
  where
    go dec = case dec of
      DataD{} -> f dec
      NewtypeD{} -> f dec
      DataInstD{} -> f dec
      NewtypeInstD{} -> f dec

      -- Recurse into instance declarations because they main contain
      -- associated data family instances.
#if MIN_VERSION_template_haskell(2,11,0)
      InstanceD moverlap ctx inst body -> InstanceD moverlap ctx inst <$> traverse go body
#else
      InstanceD ctx inst body -> InstanceD  ctx inst <$> traverse go body
#endif
      _ -> pure dec

stripFields :: Dec -> Dec
stripFields dec = case dec of
#if MIN_VERSION_template_haskell(2,11,0)
  DataD ctx tyName tyArgs kind cons derivings ->
    DataD ctx tyName tyArgs kind (map deRecord cons) derivings
  NewtypeD ctx tyName tyArgs kind con derivings ->
    NewtypeD ctx tyName tyArgs kind (deRecord con) derivings
  DataInstD ctx tyName tyArgs kind cons derivings ->
    DataInstD ctx tyName tyArgs kind (map deRecord cons) derivings
  NewtypeInstD ctx tyName tyArgs kind con derivings ->
    NewtypeInstD ctx tyName tyArgs kind (deRecord con) derivings
#else
  DataD ctx tyName tyArgs cons derivings ->
    DataD ctx tyName tyArgs (map deRecord cons) derivings
  NewtypeD ctx tyName tyArgs con derivings ->
    NewtypeD ctx tyName tyArgs (deRecord con) derivings
  DataInstD ctx tyName tyArgs cons derivings ->
    DataInstD ctx tyName tyArgs (map deRecord cons) derivings
  NewtypeInstD ctx tyName tyArgs con derivings ->
    NewtypeInstD ctx tyName tyArgs (deRecord con) derivings
#endif
  _ -> dec

deRecord :: Con -> Con
deRecord con@NormalC{} = con
deRecord con@InfixC{} = con
deRecord (ForallC tyVars ctx con) = ForallC tyVars ctx $ deRecord con
deRecord (RecC conName fields) = NormalC conName (map dropFieldName fields)
#if MIN_VERSION_template_haskell(2,11,0)
deRecord con@GadtC{} = con
deRecord (RecGadtC ns fields retTy) = GadtC ns (map dropFieldName fields) retTy
#endif

#if MIN_VERSION_template_haskell(2,11,0)
dropFieldName :: VarBangType   -> BangType
#else
dropFieldName :: VarStrictType -> StrictType
#endif
dropFieldName (_, str, typ) = (str, typ)
--}

------------------------------------------------------------------------
-- Field generation entry point
------------------------------------------------------------------------

-- Compute the field optics for the type identified by the given type name.
-- Lenses will be computed when possible, Traversals otherwise.
makeFieldOptics :: OpticRules -> Name -> DecsQ
makeFieldOptics rules = (`evalStateT` Set.empty) . makeFieldOpticsForDatatype rules <=< D.reifyDatatype

type HasFieldClasses = StateT (Set Name) Q

addFieldClassName :: Name -> HasFieldClasses ()
addFieldClassName n = modify $ Set.insert n

-- | Compute the field optics for a deconstructed datatype Dec
-- When possible build an Iso otherwise build one optic per field.
makeFieldOpticsForDatatype :: OpticRules -> D.DatatypeInfo -> HasFieldClasses [Dec]
makeFieldOpticsForDatatype rules info =
  do perDef <- liftState $ do
       fieldCons <- traverse normalizeConstructor cons
       let allFields  = lists (folded . second . folded . first . folded) fieldCons
       let defCons    = over normFieldLabels (expandName allFields) fieldCons
           allDefs    = setOf (normFieldLabels . folded) defCons
       sequenceA (fromSet (buildScaffold rules s defCons) allDefs)

     let defs = Map.toList perDef
     case _classyOptics rules tyName of
       Just (className, methodName) ->
         makeClassyDriver rules className methodName s defs
       Nothing -> do decss <- traverse (makeFieldOptic rules) defs
                     return (concat decss)

  where
  tyName = D.datatypeName info
  s      = D.datatypeType info
  cons   = D.datatypeCons info

  -- Traverse the field labels of a normalized constructor
  normFieldLabels :: Traversal [(Name,[(a,Type)])] [(Name,[(b,Type)])] a b
  normFieldLabels = traversed . second . traversed . first

  -- Map a (possibly missing) field's name to zero-to-many optic definitions
  expandName :: [Name] -> Maybe Name -> [DefName]
  expandName allFields = concatMap (_fieldToDef rules tyName allFields) . maybeToList

normalizeConstructor ::
  D.ConstructorInfo ->
  Q (Name, [(Maybe Name, Type)]) -- ^ constructor name, field name, field type

normalizeConstructor con =
  return (D.constructorName con,
          zipWith checkForExistentials fieldNames (D.constructorFields con))
  where
    fieldNames =
      case D.constructorVariant con of
        D.RecordConstructor xs -> fmap Just xs
        D.NormalConstructor    -> repeat Nothing
        D.InfixConstructor     -> repeat Nothing

    -- Fields mentioning existentially quantified types are not
    -- elligible for TH generated optics.
    checkForExistentials _ fieldtype
      | any (\tv -> D.tvName tv `Set.member` used) unallowable
      = (Nothing, fieldtype)
      where
        used        = setOf typeVars fieldtype
        unallowable = D.constructorVars con
    checkForExistentials fieldname fieldtype = (fieldname, fieldtype)

makeClassyDriver ::
  OpticRules ->
  Name ->
  Name ->
  Type {- ^ Outer 's' type -} ->
  [(DefName, (OpticType, OpticStab, [(Name, Int, [Int])]))] ->
  HasFieldClasses [Dec]
makeClassyDriver rules className methodName s defs = sequenceA (cls ++ inst)

  where
  cls | _generateClasses rules = [liftState $ makeClassyClass className methodName s defs]
      | otherwise = []

  inst = [makeClassyInstance rules className methodName s defs]

makeClassyClass ::
  Name ->
  Name ->
  Type {- ^ Outer 's' type -} ->
  [(DefName, (OpticType, OpticStab, [(Name, Int, [Int])]))] ->
  DecQ
makeClassyClass className methodName s defs = do
  let ss   = map (\(_, (_, ostab, _)) -> stabToS ostab) defs
  (sub,s') <- unifyTypes (s : ss)
  c <- newName "c"
  let vars = lists typeVars s'
      fd   | null vars = []
           | otherwise = [FunDep [c] vars]


  classD (cxt[]) className (map PlainTV (c:vars)) fd
    $ sigD methodName (return (''Lens' `conAppsT` [VarT c, s']))
    : concat
      [ [sigD defName (return ty)
        ,valD (varP defName) (normalB body) []
        ] ++
        inlinePragma defName
      | (TopName defName, (_, stab, _)) <- defs
      , let body = appsE [varE '(.), varE methodName, varE defName]
      , let ty   = quantifyType' (Set.fromList (c:vars))
                                 (stabToContext stab)
                 $ stabToOptic stab `conAppsT`
                       [VarT c, applyTypeSubst sub (stabToA stab)]
      ]

makeClassyInstance ::
  OpticRules ->
  Name ->
  Name ->
  Type {- ^ Outer 's' type -} ->
  [(DefName, (OpticType, OpticStab, [(Name, Int, [Int])]))] ->
  HasFieldClasses Dec
makeClassyInstance rules className methodName s defs = do
  methodss <- traverse (makeFieldOptic rules') defs

  liftState $ instanceD (cxt[]) (return instanceHead)
    $ valD (varP methodName) (normalB (varE 'id)) []
    : map return (concat methodss)

  where
  instanceHead = className `conAppsT` (s : map VarT vars)
  vars         = lists typeVars s
  rules'       = rules { _generateSigs    = False
                       , _generateClasses = False
                       }

data OpticType
  = ViewType
  | IsoType
  | LensType
  | AffineType
  | TraversalType
  | OptionType
  | FoldType
  deriving Show

opticTypeName :: Bool -> OpticType -> Name
opticTypeName typeChanging  IsoType           = if typeChanging
                                                  then ''Iso
                                                  else ''Iso'
opticTypeName _typeChanging ViewType          = ''View
opticTypeName typeChanging  LensType          = if typeChanging
                                                  then ''Lens
                                                  else ''Lens'
opticTypeName typeChanging  AffineType    = if typeChanging
                                                  then ''Affine
                                                  else ''Affine'
opticTypeName typeChanging  TraversalType     = if typeChanging
                                                  then ''Traversal
                                                  else ''Traversal'
opticTypeName _typeChanging OptionType         = ''Option
opticTypeName _typeChanging FoldType          = ''Fold

-- Compute the positional location of the fields involved in
-- each constructor for a given optic definition as well as the
-- type of clauses to generate and the type to annotate the declaration
-- with.
buildScaffold ::
  OpticRules                                                                ->
  Type                              {- outer type                       -} ->
  [(Name, [([DefName], Type)])]     {- normalized constructors          -} ->
  DefName                           {- target definition                -} ->
  Q (OpticType, OpticStab, [(Name, Int, [Int])])
              {- ^ optic type, definition type, field count, target fields -}
buildScaffold rules s cons defName =

  do (s',t,a,b) <- buildStab s (concatMap snd consForDef)

     let prev o s = getFirst $ withFold o (First . Just) s

         defType
           | Just (_,cx,a') <- prev forallt a =
               let optic | lensCase   = ViewType
                        {-- | affineCase = OptionType --}
                         | otherwise  = FoldType
               in OpticSa cx optic s' a'

           -- View and Fold are always simple
           | not (_allowUpdates rules) =
               let optic | lensCase   = ViewType
                        {-- | affineCase = OptionType --}
                         | otherwise  = FoldType
               in OpticSa [] optic s' a

           -- Generate simple Lens and Traversal where possible
           | _simpleOptics rules || s' == t && a == b =
               let optic | isoCase && _allowIsos rules = IsoType
                         | lensCase                    = LensType
                        {-- | affineCase                  = AffineType --}
                         | otherwise                   = TraversalType
               in OpticSa [] optic s' a

           -- Generate type-changing Lens and Traversal otherwise
           | otherwise =
               let optic | isoCase && _allowIsos rules = IsoType
                         | lensCase                    = LensType
                        {-- | affineCase                  = AffineType --}
                         | otherwise                   = TraversalType
               in OpticStab optic s' t a b

         opticType | has forallt a             = ViewType
                   | not (_allowUpdates rules) = ViewType
                   | isoCase                   = IsoType
                   | otherwise                 = LensType

     return (opticType, defType, scaffolds)
  where

  consForDef :: [(Name, [Either Type Type])]
  consForDef = over (fmapped . second . fmapped) categorize cons

  scaffolds :: [(Name, Int, [Int])]
  scaffolds = [ (n, length ts, rightIndices ts) | (n,ts) <- consForDef ]

  rightIndices :: [Either Type Type] -> [Int]
  rightIndices = findIndices (has right)

  -- Right: types for this definition
  -- Left : other types
  categorize :: ([DefName], Type) -> Either Type Type
  categorize (defNames, t)
    | defName `elem` defNames = Right t
    | otherwise               = Left  t

  lensCase :: Bool
  lensCase = all (\x -> lengthOf (second . folded . right) x == 1) consForDef

  --affectedFields :: [Int]
  --affectedFields = lists (folded . t33 . to length) scaffolds

  --lensCase :: Bool
  --lensCase = all (== 1) affectedFields

  --affineCase :: Bool
  --affineCase = all (<= 1) affectedFields

  isoCase :: Bool
  isoCase = case scaffolds of 
              [(_,1,[0])] -> True
              _           -> False


data OpticStab = OpticStab     OpticType Type Type Type Type
               | OpticSa   Cxt OpticType Type Type

stabToType :: OpticStab -> Type
stabToType (OpticStab  c s t a b) = quantifyType [] (opticTypeName True c `conAppsT` [s,t,a,b])
stabToType (OpticSa cx c s   a  ) = quantifyType cx (opticTypeName False c `conAppsT` [s,a])

stabToOpticType :: OpticStab -> OpticType
stabToOpticType (OpticStab c _ _ _ _) = c
stabToOpticType (OpticSa _ c _ _) = c

stabToContext :: OpticStab -> Cxt
stabToContext OpticStab{}        = []
stabToContext (OpticSa cx _ _ _) = cx

stabToOptic :: OpticStab -> Name
stabToOptic (OpticStab c _ _ _ _) = opticTypeName True c
stabToOptic (OpticSa _ c _ _) = opticTypeName False c

stabToS :: OpticStab -> Type
stabToS (OpticStab _ s _ _ _) = s
stabToS (OpticSa _ _ s _) = s

stabToA :: OpticStab -> Type
stabToA (OpticStab _ _ _ a _) = a
stabToA (OpticSa _ _ _ a) = a


-- Compute the s t a b types given the outer type 's' and the
-- categorized field types. Left for fixed and Right for visited.
-- These types are "raw" and will be packaged into an 'OpticStab'
-- shortly after creation.
buildStab :: Type -> [Either Type Type] -> Q (Type,Type,Type,Type)
buildStab s categorizedFields =
  do (subA,a) <- unifyTypes targetFields
     let s' = applyTypeSubst subA s

     -- compute possible type changes
     sub <- sequenceA (fromSet (newName . nameBase) unfixedTypeVars)
     let (t,b) = over both (substTypeVars sub) (s',a)

     return (s',t,a,b)

  where
  (fixedFields, targetFields) = partitionEithers categorizedFields
  fixedTypeVars               = setOf typeVars fixedFields
  unfixedTypeVars             = setOf typeVars s Set.\\ fixedTypeVars

-- | Build the signature and definition for a single field optic.
-- In the case of a singleton constructor irrefutable matches are
-- used to enable the resulting lenses to be used on a bottom value.
makeFieldOptic ::
  OpticRules ->
  (DefName, (OpticType, OpticStab, [(Name, Int, [Int])])) ->
  HasFieldClasses [Dec]
makeFieldOptic rules (defName, (_, defType, cons)) = do
  locals <- get
  addName
  liftState $ do cls <- mkCls locals
                 sequenceA (cls ++ sig ++ def)
  where
  mkCls locals = case defName of
                 MethodName c n | _generateClasses rules ->
                  do classExists <- isJust <$> lookupTypeName (show c)
                     return (if classExists || Set.member c locals then [] else [makeFieldClass defType c n])
                 _ -> return []

  addName = case defName of
            MethodName c _ -> addFieldClassName c
            _              -> return ()

  sig = case defName of
          _ | not (_generateSigs rules) -> []
          TopName n -> [sigD n (return (stabToType defType))]
          MethodName{} -> []

  fun n = funD n [funDef] : inlinePragma n

  def = case defName of
          TopName n      -> fun n
          MethodName c n -> [makeFieldInstance defType c (fun n)]

  funDef = makeFieldClause rules (stabToOpticType defType) cons

------------------------------------------------------------------------
-- Field class generation
------------------------------------------------------------------------

makeFieldClass :: OpticStab -> Name -> Name -> DecQ
makeFieldClass defType className methodName =
  classD (cxt []) className [PlainTV s, PlainTV a] [FunDep [s] [a]]
         [sigD methodName (return methodType)]
  where
  methodType = quantifyType' (Set.fromList [s,a])
                             (stabToContext defType)
             $ stabToOptic defType `conAppsT` [VarT s,VarT a]
  s = mkName "s"
  a = mkName "a"

-- | Build an instance for a field. If the field’s type contains any type
-- families, will produce an equality constraint to avoid a type family
-- application in the instance head.
makeFieldInstance :: OpticStab -> Name -> [DecQ] -> DecQ
makeFieldInstance defType className decs =
  containsTypeFamilies a >>= pickInstanceDec
  where
  s = stabToS defType
  a = stabToA defType

  containsTypeFamilies = go <=< D.resolveTypeSynonyms
    where
    go (ConT nm) = (\i -> case i of FamilyI d _ -> isTypeFamily d; _ -> False)
                   <$> reify nm
    go ty = or <$> traverse go (children ty)

#if MIN_VERSION_template_haskell(2,11,0)
  isTypeFamily OpenTypeFamilyD{}       = True
  isTypeFamily ClosedTypeFamilyD{}     = True
#elif MIN_VERSION_template_haskell(2,9,0)
  isTypeFamily (FamilyD TypeFam _ _ _) = True
  isTypeFamily ClosedTypeFamilyD{}     = True
#else
  isTypeFamily (FamilyD TypeFam _ _ _) = True
#endif
  isTypeFamily _ = False

  pickInstanceDec hasFamilies
    | hasFamilies = do
        placeholder <- VarT <$> newName "a"
        mkInstanceDec
          [return (D.equalPred placeholder a)]
          [s, placeholder]
    | otherwise = mkInstanceDec [] [s, a]

  mkInstanceDec context headTys =
    instanceD (cxt context) (return (className `conAppsT` headTys)) decs

makeFieldClause :: OpticRules -> OpticType -> [(Name, Int, [Int])] -> ClauseQ
makeFieldClause rules opticType cons =
  case opticType of
    IsoType             -> makeIsoClause cons irref
    ViewType            -> makeViewClause cons
    LensType            -> makeLensClause cons irref
    AffineType      -> makeAffineClause cons irref
    TraversalType       -> makeTraversalClause cons irref
    OptionType           -> makeOptionClause cons
    FoldType            -> makeFoldClause cons
  where
    irref = _lazyPatterns rules && length cons == 1

------------------------------------------------------------------------
-- Optic clause generators
------------------------------------------------------------------------

modifyAt :: Int -> (a -> a) -> [a] -> [a]
modifyAt i f ls
  | i < 0 = ls
  | otherwise = go i ls
  where
    go 0 (x:xs) = f x : xs
    go n (x:xs) = x : go (n-1) xs
    go _ [] = []

ixat :: Int -> Setter [a] [a] a a
ixat i = setter $ modifyAt i


-- | Obtain a clause that constructs an Iso.
makeIsoClause :: [(Name, Int, [Int])] -> Bool -> ClauseQ
makeIsoClause fields irref = case fields of
  [(conName, 1, [0])] -> do
    x <- newName "x"
    clause []
           (normalB $ appsE
             [ varE 'iso
             , lamE [irrefP $ conP conName [varP x]] (varE x)
             , conE conName
             ])
           []
  _ -> error "Iso works only for types with one constructor and one field"
  where
    irrefP = if irref then tildeP else id

-- | Obtain a lens clause that updates the field at the given index. When irref
-- is 'True' the value with be matched with an irrefutable pattern.
makeLensClause :: [(Name, Int, [Int])] -> Bool -> ClauseQ
makeLensClause cons irref = do
  f <- newName "f"
  s <- newName "s"
  clause
    []
    (normalB $ appsE
      [ varE 'lensVl
      , lamE [varP f, varP s] $ caseE (varE s)
        [ makeLensMatch irrefP f conName fieldCount fields
        | (conName, fieldCount, fields) <- cons
        ]
      ])
    []
  where
    irrefP = if irref then tildeP else id

-- | Make a lens match. Used for both lens and affine traversal generation.
makeLensMatch :: (PatQ -> PatQ) -> Name -> Name -> Int -> [Int] -> Q Match
makeLensMatch irrefP f conName fieldCount = \case
  [field] -> do
    xs <- newNames "x" fieldCount
    y  <- newName "y"

    let body = appsE
          [ varE 'fmap
          , lamE [varP y] . appsE $
            conE conName : map varE (set (ixat field) y xs)
          , appE (varE f) . varE $ xs !! field
          ]

    -- Con xfirst .. x_n -> fmap (\y_i -> Con xfirst .. y_i .. x_n) (f x_i)
    match (irrefP . conP conName $ map varP xs)
          (normalB body)
          []
  _       -> error "Lens focuses on exactly one field"

-- | Obtain a view clause that retrieves the field at the given index.
makeViewClause :: [(Name, Int, [Int])] -> ClauseQ
makeViewClause cons = do
  s <- newName "s"
  clause
    []
    (normalB $ appsE
      [ varE 'to
      , lamE [varP s] $ caseE (varE s)
        [ makeViewMatch conName fieldCount fields
        | (conName, fieldCount, fields) <- cons
        ]
      ])
    []
  where
    makeViewMatch conName fieldCount = \case
      [field] -> do
        x <- newName "x"
        -- Con _ .. x_i .. _ -> x_i
        match (conP conName . set (ixat field) (varP x) $ replicate fieldCount wildP)
              (normalB $ varE x)
              []
      _       -> error "View focuses on exactly one field"

makeAffineClause :: [(Name, Int, [Int])] -> Bool -> ClauseQ
makeAffineClause cons irref = do
  point <- newName "point"
  f     <- newName "f"
  s     <- newName "s"
  clause
    []
    (normalB $ appsE
      [ varE 'affineVl
      , lamE [varP point, varP f, varP s] $ caseE (varE s)
        [ makeAffineMatch point f conName fieldCount fields
        | (conName, fieldCount, fields) <- cons
        ]
      ])
    []
  where
    irrefP = if irref then tildeP else id

    makeAffineMatch point f conName fieldCount = \case
      [] -> do
        xs <- newNames "x" fieldCount
        -- Con xfirst ... x_n -> point (Con xfirst .. x_n)
        match (irrefP . conP conName $ map varP xs)
              (normalB $ varE point `appE` appsE (conE conName : map varE xs))
              []
      [field] -> makeLensMatch irrefP f conName fieldCount [field]
      _ -> error "Affine traversal focuses on at most one field"

makeTraversalClause :: [(Name, Int, [Int])] -> Bool -> ClauseQ
makeTraversalClause cons irref = do
  f <- newName "f"
  s <- newName "s"
  clause
    []
    (normalB $ appsE
      [ varE 'traversalVl
      , lamE [varP f, varP s] $ caseE (varE s)
        [ makeTraversalMatch f conName fieldCount fields
        | (conName, fieldCount, fields) <- cons
        ]
      ])
    []
  where
    irrefP = if irref then tildeP else id

    makeTraversalMatch f conName fieldCount fields = do
      xs <- newNames "x" fieldCount
      case fields of
        [] -> -- Con xfirst .. x_n -> pure (Con xfirst .. x_n)
          match (irrefP . conP conName $ map varP xs)
                (normalB $ varE 'pure `appE` appsE (conE conName : map varE xs))
                []
        _ -> do
          ys <- newNames "y" $ length fields

          let xs' = foldr (\(i, x) -> set (ixat i) x) xs (zip fields ys)

              mkFx i = varE f `appE` varE (xs !! i)

              body0 = appsE
                [ varE 'pure
                , lamE (map varP ys) $ appsE $ conE conName : map varE xs'
                ]

              body = foldl (\acc i -> infixApp acc (varE '(<*>)) $ mkFx i)
                           body0
                           fields

          -- Con xfirst .. x_n ->
          --  pure (\yfirst .. y_k -> Con xfirst .. yfirst .. x_l .. y_k .. x_n)
          --    <*> f x_i_yfirst <*> .. <*> f x_i_y_k
          match (irrefP . conP conName $ map varP xs)
                (normalB body)
                []

makeOptionClause :: [(Name, Int, [Int])] -> ClauseQ
makeOptionClause cons = do
  s <- newName "s"
  clause
    []
    (normalB $ appsE
      [ varE 'option
      , lamE [varP s] $ caseE (varE s)
        [ makeOptionMatch conName fieldCount fields
        | (conName, fieldCount, fields) <- cons
        ]
      ])
    []
  where
    makeOptionMatch conName fieldCount fields = do
      xs <- newNames "x" $ length fields

      let args = foldr (\(i, x) -> set (ixat i) (varP x))
                       (replicate fieldCount wildP)
                       (zip fields xs)

          body = case xs of
            -- Con _ .. _ -> Nothing
            []  -> conE 'Nothing
            -- Con _ .. x_i .. _ -> Just x_i
            [x] -> conE 'Just `appE` varE x
            _   -> error "Option focuses on at most one field"

      match (conP conName args)
            (normalB body)
            []

makeFoldClause :: [(Name, Int, [Int])] -> ClauseQ
makeFoldClause cons = do
  f <- newName "f"
  s <- newName "s"
  clause
    []
    (normalB $ appsE
      [ varE 'foldVl
      , lamE [varP f, varP s] $ caseE (varE s)
        [ makeFoldMatch f conName fieldCount fields
        | (conName, fieldCount, fields) <- cons
        ]
      ])
    []
  where
    makeFoldMatch f conName fieldCount fields = do
      xs <- newNames "x" $ length fields

      let args = foldr (\(i, x) -> set (ixat i) (varP x))
                       (replicate fieldCount wildP)
                       (zip fields xs)

          fxs = case xs of
            [] -> [varE 'pure `appE` conE '()]
            _  -> map (\x -> varE f `appE` varE x) xs

          -- Con _ .. xfirst .. _ .. x_k .. _ -> f xfirst *> .. f x_k
          body = appsE
            [ foldr1 (\fx -> infixApp fx (varE '(*>))) fxs
            ]

      match (conP conName args)
            (normalB body)
            []

------------------------------------------------------------------------
-- Unification logic
------------------------------------------------------------------------

-- The field-oriented optic generation supports incorporating fields
-- with distinct but unifiable types into a single definition.

-- Unify the given list of types, if possible, and return the
-- substitution used to unify the types for unifying the outer
-- type when building a definition's type signature.
unifyTypes :: [Type] -> Q (Map Name Type, Type)
unifyTypes (x:xs) = foldM (uncurry unify1) (Map.empty, x) xs
unifyTypes []     = fail "unifyTypes: Bug: Unexpected empty list"


-- Attempt to unify two given types using a running substitution
unify1 :: Map Name Type -> Type -> Type -> Q (Map Name Type, Type)
unify1 sub (VarT x) y
  | Just r <- Map.lookup x sub = unify1 sub r y
unify1 sub x (VarT y)
  | Just r <- Map.lookup y sub = unify1 sub x r
unify1 sub x y
  | x == y = return (sub, x)
unify1 sub (AppT f1 x1) (AppT f2 x2) =
  do (sub1, f) <- unify1 sub  f1 f2
     (sub2, x) <- unify1 sub1 x1 x2
     return (sub2, AppT (applyTypeSubst sub2 f) x)
unify1 sub x (VarT y)
  | elemOf typeVars y (applyTypeSubst sub x) =
      fail "Failed to unify types: occurs check"
  | otherwise = return (Map.insert y x sub, x)
unify1 sub (VarT x) y = unify1 sub y (VarT x)

-- TODO: Unify contexts
unify1 sub (ForallT v1 [] t1) (ForallT v2 [] t2) =
     -- This approach works out because by the time this code runs
     -- all of the type variables have been renamed. No risk of shadowing.
  do (sub1,t) <- unify1 sub t1 t2
     v <- fmap nub (traverse (limitedSubst sub1) (v1++v2))
     return (sub1, ForallT v [] t)

unify1 _ x y = fail ("Failed to unify types: " ++ show (x,y))

-- Perform a limited substitution on type variables. This is used
-- when unifying rank-2 fields when trying to achieve a View or Fold.
limitedSubst :: Map Name Type -> TyVarBndr -> Q TyVarBndr
limitedSubst sub (PlainTV n)
  | Just r <- Map.lookup n sub =
       case r of
         VarT m -> limitedSubst sub (PlainTV m)
         _ -> fail "Unable to unify exotic higher-rank type"
limitedSubst sub (KindedTV n k)
  | Just r <- Map.lookup n sub =
       case r of
         VarT m -> limitedSubst sub (KindedTV m k)
         _ -> fail "Unable to unify exotic higher-rank type"
limitedSubst _ tv = return tv

-- Apply a substitution to a type. This is used after unifying
-- the types of the fields in unifyTypes.
applyTypeSubst :: Map Name Type -> Type -> Type
applyTypeSubst sub = rewrite aux
  where
  aux (VarT n) = Map.lookup n sub
  aux _        = Nothing
