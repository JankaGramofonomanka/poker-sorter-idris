module Interfaces

import Data.Fin

public export
interface Enum a where
  numValues : Nat

  toEnum : Fin numValues -> a

  fromEnum : a -> Fin numValues
