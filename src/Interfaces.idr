module Interfaces

public export
interface Enum a where
  partial
  toEnum : Nat -> a

  fromEnum : a -> Nat
