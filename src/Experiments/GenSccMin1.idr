module Experiments.GenSccMin1

%default total

data Gen : Type -> Type where
  Empty : Gen a
  Pure : a -> Gen a
  Bind : Gen a -> (a -> Gen b) -> Gen b

data GenAlternatives : Type -> Type where
  Alternatives : List (Gen a) -> GenAlternatives a

mapGen : (a -> b) -> Gen a -> Gen b
mapGen f Empty = Empty
mapGen f (Pure x) = Pure (f x)
mapGen f (Bind m k) = Bind m ((mapGen f) . k)

infixl 2 <**>
(<**>) : Gen (a -> b) -> Gen a -> Gen b
Empty <**> _ = Empty
Pure f <**> g = mapGen f g
Bind m h <**> g = Bind m (\x => h x <**> g)

infixl 1 >>==
(>>==) : Gen a -> (a -> Gen b) -> Gen b
Empty >>== _ = Empty
Pure x >>== k = k x
Bind m h >>== k = Bind m (\x => h x >>== k)

Functor Gen where
  map = mapGen

Applicative Gen where
  pure = Pure
  (<*>) = (<**>)

Monad Gen where
  (>>=) = (>>==)

Functor GenAlternatives where
  map f (Alternatives xs) = Alternatives (map (mapGen f) xs)

Applicative GenAlternatives where
  pure x = Alternatives [Pure x]
  Alternatives fs <*> Alternatives xs = Alternatives (concatMap (\f => map (f <**>) xs) fs)

-- No Monad instance needed for this minimization slice.
