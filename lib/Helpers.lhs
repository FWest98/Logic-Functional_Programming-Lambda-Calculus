\begin{code}

module Helpers where

import Data.Set(Set, toList)
import Data.Tuple (swap)

lookupSet :: Eq a => a -> Set (a, b) -> Maybe b
lookupSet key = lookup key . toList

lookupSetReverse :: Eq b => b -> Set (a, b) -> Maybe a
lookupSetReverse value = lookup value . map swap . toList

\end{code}
