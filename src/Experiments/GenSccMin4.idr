module Experiments.GenSccMin4

%default total

data Gen : Type -> Type where
  Empty : Gen a
  Pure : a -> Gen a
  Bind : Gen a -> (a -> Gen b) -> Gen b

data GenAlternatives : Type -> Type where
  MkGenAlternatives : List (Gen a) -> GenAlternatives a

Functor Gen where
  map f Empty = Empty
  map f (Pure x) = Pure (f x)
  map f (Bind x g) = Bind x (\v => map f (g v))

infixl 3 <**>
(<**>) : Gen (a -> b) -> Gen a -> Gen b
Empty <**> _ = Empty
Pure f <**> g = map f g
Bind x g <**> y = Bind x (\v => g v <**> y)

Applicative Gen where
  pure = Pure
  (<*>) = (<**>)

infixl 1 >>==
(>>==) : Gen a -> (a -> Gen b) -> Gen b
Empty >>== _ = Empty
Pure x >>== f = f x
Bind x g >>== f = Bind x (\v => g v >>== f)

Monad Gen where
  (>>=) = (>>==)

export
mapAlternativesOf : (a -> b) -> Gen a -> GenAlternatives b
mapAlternativesOf f g = MkGenAlternatives [map f g]

export
listOf : Gen a -> Gen (List a)
listOf g = pure (::) <*> g <*> listOf g

export
suchThat : Gen a -> (a -> Bool) -> Gen a
suchThat g p = g >>= \x => if p x then pure x else suchThat g p

export
elements : List a -> Gen a
elements [] = Empty
elements (x :: xs) = pure x

export
elements' : List a -> Gen a
elements' xs = elements xs
