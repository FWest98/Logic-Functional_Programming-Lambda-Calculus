\begin{code}

module Helpers where

import Data.Set(Set, toList)

lookupSet :: Eq a => a -> Set (a, b) -> Maybe b
lookupSet key = lookup key . toList

\end{code}
