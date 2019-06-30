
module Test.Property (module Export) where
{-
    ( module Data.GenProperty
    , forAllUnchecked
    , forAllValid
    , forAllInvalid
      -- * Tests for GenProperty instances
    , genGeneratesValid
    , genGeneratesInvalid
      -- * Standard tests involving functions
      -- ** Standard tests involving validity
    , producesValidsOnGen
    , producesValidsOnValids
    , producesValid
    , producesValidsOnArbitrary
    , producesValidsOnGens2
    , producesValidsOnValids2
    , producesValid2
    , producesValidsOnArbitrary2
    , producesValidsOnGens3
    , producesValidsOnValids3
    , producesValid3
    , producesValidsOnArbitrary3
      -- ** Standard tests involving functions that can fail
    , CanFail(..)
    , succeedsOnGen
    , succeedsOnValid
    , succeeds
    , succeedsOnArbitrary
    , succeedsOnGens2
    , succeedsOnValids2
    , succeeds2
    , succeedsOnArbitrary2
    , failsOnGen
    , failsOnInvalid
    , failsOnGens2
    , failsOnInvalid2
    , validIfSucceedsOnGen
    , validIfSucceedsOnValid
    , validIfSucceedsOnArbitrary
    , validIfSucceeds
    , validIfSucceedsOnGens2
    , validIfSucceedsOnValids2
    , validIfSucceeds2
    , validIfSucceedsOnArbitrary2
    , validIfSucceedsOnGens3
    , validIfSucceedsOnValids3
    , validIfSucceeds3
    , validIfSucceedsOnArbitrary3
      -- ** Standard tests involving equivalent of functions
      -- *** Simple functions
      -- **** One argument
    , equivalentOnGen
    , equivalentOnValid
    , equivalent
    , equivalentOnArbitrary
      -- **** Two arguments
    , equivalentOnGens2
    , equivalentOnValids2
    , equivalent2
    , equivalentOnArbitrary2
      -- **** Three arguments
    , equivalentOnGens3
    , equivalentOnValids3
    , equivalent3
    , equivalentOnArbitrary3
      -- *** First function can fail
      -- **** One argument
    , equivalentWhenFirstSucceedsOnGen
    , equivalentWhenFirstSucceedsOnValid
    , equivalentWhenFirstSucceeds
    , equivalentWhenFirstSucceedsOnArbitrary
      -- **** Two arguments
    , equivalentWhenFirstSucceedsOnGens2
    , equivalentWhenFirstSucceedsOnValids2
    , equivalentWhenFirstSucceeds2
    , equivalentWhenFirstSucceedsOnArbitrary2
      -- *** Second function can fail
      -- **** One argument
    , equivalentWhenSecondSucceedsOnGen
    , equivalentWhenSecondSucceedsOnValid
    , equivalentWhenSecondSucceeds
    , equivalentWhenSecondSucceedsOnArbitrary
      -- **** Two arguments
    , equivalentWhenSecondSucceedsOnGens2
    , equivalentWhenSecondSucceedsOnValids2
    , equivalentWhenSecondSucceeds2
    , equivalentWhenSecondSucceedsOnArbitrary2
      -- *** Both functions can fail
      -- **** One argument
    , equivalentWhenSucceedOnGen
    , equivalentWhenSucceedOnValid
    , equivalentWhenSucceed
    , equivalentWhenSucceedOnArbitrary
      -- **** Two arguments
    , equivalentWhenSucceedOnGens2
    , equivalentWhenSucceedOnValids2
    , equivalentWhenSucceed2
    , equivalentWhenSucceedOnArbitrary2
      -- ** Standard tests involving inverse functions
    , inverseFunctionOnGen
    , inverseFunctionOnValid
    , inverseFunction
    , inverseFunctionOnArbitrary
    , inverseFunctionIfFirstSucceedsOnGen
    , inverseFunctionIfFirstSucceedsOnValid
    , inverseFunctionIfFirstSucceeds
    , inverseFunctionIfFirstSucceedsOnArbitrary
    , inverseFunctionIfSecondSucceedsOnGen
    , inverseFunctionIfSecondSucceedsOnValid
    , inverseFunctionIfSecondSucceeds
    , inverseFunctionIfSecondSucceedsOnArbitrary
    , inverseFunctionIfSucceedOnGen
    , inverseFunctionIfSucceedOnValid
    , inverseFunctionIfSucceed
    , inverseFunctionIfSucceedOnArbitrary
      -- ** Properties involving idempotent
    , idempotentOnGen
    , idempotentOnValid
    , idempotent
    , idempotentOnArbitrary
      -- * Properties of relations
      -- ** Reflexive
    , reflexiveOnElem
    , reflexiveOnGen
    , reflexiveOnValid
    , reflexive
    , reflexiveOnArbitrary
      -- ** Transitive
    , transitiveOnElems
    , transitiveOnGens
    , transitiveOnValid
    , transitive
    , transitiveOnArbitrary
      -- ** Antisymmetry
    , antisymmetricOnElemsWithEquality
    , antisymmetryOnGensWithEquality
    , antisymmetryOnGens
    , antisymmetryOnValid
    , antisymmetry
    , antisymmetryOnArbitrary
      -- ** Antireflexive
    , antireflexiveOnElem
    , antireflexiveOnGen
    , antireflexiveOnValid
    , antireflexive
    , antireflexiveOnArbitrary
      -- ** Symmetric
    , symmetricOnElems
    , symmetryOnGens
    , symmetryOnValid
    , symmetry
    , symmetryOnArbitrary
      -- * Properties of operations
      -- ** Identity element
      -- *** Left Identity
    , leftIdentityOnElemWithEquality
    , leftIdentityOnGenWithEquality
    , leftIdentityOnGen
    , leftIdentityOnValid
    , leftIdentity
    , leftIdentityOnArbitrary
      -- *** Right Identity
    , rightIdentityOnElemWithEquality
    , rightIdentityOnGenWithEquality
    , rightIdentityOnGen
    , rightIdentityOnValid
    , rightIdentity
    , rightIdentityOnArbitrary
      -- *** Identity
    , identityOnGen
    , identityOnValid
    , identity
    , identityOnArbitrary
      -- ** Associative
    , associativeOnGens
    , associativeOnValids
    , associative
    , associativeOnArbitrary
      -- ** Commutative
    , commutativeOnGens
    , commutativeOnValids
    , commutative
    , commutativeOnArbitrary
    ) where
-}

import Test.Property.Function as Export
import Test.Property.Operation as Export
import Test.Property.Util as Export
import Test.Property.Relation as Export
