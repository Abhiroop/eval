module Panic (
  FatalError(FatalError, fatalErrorMessage),
  panic,
) where


import Data.Typeable (Typeable)
import Control.Exception as X

-- | Uncatchable exceptions thrown and never caught.
newtype FatalError = FatalError { fatalErrorMessage :: String }
  deriving (Show, Typeable)

instance Exception FatalError

panic :: String -> a
panic a = throw (FatalError a)
