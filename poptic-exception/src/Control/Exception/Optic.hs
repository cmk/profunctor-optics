module Control.Exception.Optic where

import Control.Monad.IO.Unlift
import Data.Monoid (First(..))
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Prism
import Data.Profunctor.Optic.Fold (preview)
import Data.Profunctor.Optic.Review (review)
import UnliftIO.Exception


exception :: Exception a => Prism' SomeException a
exception = prism' toException fromException

trying :: MonadUnliftIO m => Exception s => AGetter (First a) s t a b -> m r -> m (Either a r)
trying l = tryJust (preview l)

throwing :: MonadIO m => Exception t => AReview b s t a b -> b -> m r
throwing o = throwIO . review o

catching :: MonadUnliftIO m => Exception s => AGetter (First a) s t a b -> m r -> (a -> m r) -> m r
catching l = catchJust (preview l)

catching_ :: MonadUnliftIO m => Exception s => AGetter (First a) s t a b -> m r -> m r -> m r
catching_ l a b = catchJust (preview l) a (const b)

handling :: MonadUnliftIO m => Exception s => AGetter (First a) s t a b -> (a -> m r) -> m r -> m r
handling l = flip (catching l)

