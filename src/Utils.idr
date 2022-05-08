module Utils


import Data.List
import Data.List1
import Data.Vect

public export
return : Monad m => a -> m a
return = pure

public export
ofLength : Nat -> List a -> Bool
ofLength n l = length l == n

{-  Returns all lists that can be made by concatenating a list from the first 
    set of list with a list from the second.
-}
public export
allConcats : List (List a) -> List (List a) -> List (List a)
allConcats l1s l2s = do
  l1 <- l1s
  l2 <- l2s

  return (l1 ++ l2)

public export
allConcatsVect : List (Vect n a) -> List (Vect m a) -> List (Vect (n + m) a)
allConcatsVect l1s l2s = do
  l1 <- l1s
  l2 <- l2s

  return (l1 ++ l2)

-- sort in descending order according to an ordering
public export
sortDescBy : (a -> a -> Ordering) -> List a -> List a
sortDescBy = sortBy . flip

-- TODO: get rid of `believe_me`
public export
sortByVect : (a -> a -> Ordering) -> Vect n a -> Vect n a
sortByVect cmp v = believe_me $ Data.Vect.fromList $ sortBy cmp (toList v)

public export
sortVect : Ord a => Vect n a -> Vect n a
sortVect = sortByVect compare

public export
sortDescByVect : (a -> a -> Ordering) -> Vect n a -> Vect n a
sortDescByVect = sortByVect . flip

-- sort a list in descending order
public export
sortDesc : Ord a => List a -> List a
sortDesc = sortDescBy compare

public export
sortDescVect : Ord a => Vect n a -> Vect n a
sortDescVect = sortDescByVect compare

public export
vecToList : Vect n a -> List a
vecToList Nil = Nil
vecToList (x :: xs) = x :: vecToList xs

public export
subsequences : List a -> List (List a)
subsequences xs = Nil :: nonEmptySubsequences xs where
  
  nonEmptySubsequences : List a -> List (List a)
  nonEmptySubsequences Nil = Nil
  nonEmptySubsequences (x :: xs) = [x] :: foldr f [] (nonEmptySubsequences xs)
    where
      f : List a -> List (List a) -> List (List a)
      f ys r = ys :: (x :: ys) :: r

public export
subsequencesOfLength : (n : Nat) -> List a -> List (Vect n a)
subsequencesOfLength Z _ = [Nil]
subsequencesOfLength (S k) Nil = Nil
subsequencesOfLength (S k) (x :: xs) = (map (x ::) (sol k xs)) ++ sol (S k) xs
  where
    sol : (p : Nat) -> List a -> List (Vect p a)
    sol = subsequencesOfLength

public export
subsequencesOfLengthVect : (n : Nat) -> Vect m a -> List (Vect n a)
subsequencesOfLengthVect Z _ = [Nil]
subsequencesOfLengthVect (S k) Nil = Nil
subsequencesOfLengthVect (S k) (x :: xs) = (map (x ::) (sol k xs)) ++ sol (S k) xs
  where
    sol : (p : Nat) -> Vect q a -> List (Vect p a)
    sol = subsequencesOfLengthVect

public export
filterLength : (n : Nat) -> List (List a) -> List (Vect n a)
filterLength n l = foldl (appendIfLengthIs n) [] l where
  appendIfLengthIs : (k : Nat) -> List (Vect k a) -> List a -> List (Vect k a)
  appendIfLengthIs k acc elem = case toVect k elem of
    Nothing => acc
    Just v  => acc ++ [v]

public export
maximum : Ord a => List1 a -> a
maximum (x ::: xs) = maximum' x xs where
  maximum' : a -> List a -> a
  maximum' x Nil = x
  maximum' x1 (x2 :: xs) = if x1 > x2 then maximum' x1 xs else maximum' x2 xs

public export
partial
listToList1 : List a -> List1 a
listToList1 (x :: xs) = x ::: xs

public export
list1ToList : List1 a -> List a
list1ToList (x ::: xs) = x :: xs

public export
headIfNonEmpty : (l : List a) -> (NonEmpty l) -> a
headIfNonEmpty l prf = head l

public export
vectToList : Vect n a -> List a
vectToList = toList

public export
data Has : Nat -> List a -> Type where
  HasZ : (l : List a) -> Has 0 l
  HasS : (x : a) -> (xs : List a) -> Has n xs -> Has (S n) (x :: xs)

public export
(!!) : (l : List a) -> (n : Nat) -> {auto 0 prf : Has (S n) l} -> a
(!!) (x :: xs) Z = x
(!!) (x :: xs) (S n) {prf = HasS _ _ prfPred} = (!!) xs n
infixl 9 !!
