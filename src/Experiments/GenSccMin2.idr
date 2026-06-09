module Experiments.GenSccMin2

%default total

data E = Empty | NonEmpty

data Gen : Type -> Type where
  GEmpty : Gen a
  GPure : a -> Gen a
  GBind : Gen a -> (a -> Gen b) -> Gen b

isEmpty : Gen a -> Bool
isEmpty GEmpty = True
isEmpty _ = False

mapGen : (a -> b) -> Gen a -> Gen b
mapGen f GEmpty = GEmpty
mapGen f (GPure x) = GPure (f x)
mapGen f (GBind m k) = GBind m (\x => mapGen f (k x))

infixl 3 <**>
(<**>) : Gen (a -> b) -> Gen a -> Gen b
g <**> h with (isEmpty g) | (isEmpty h)
  _ <**> _ | True | _ = GEmpty
  _ <**> _ | _ | True = GEmpty
  GPure f <**> x | False | False = mapGen f x
  GBind m k <**> x | False | False = GBind m (\v => k v <**> x)

infixl 1 >>==
(>>==) : Gen a -> (a -> Gen b) -> Gen b
GEmpty >>== _ = GEmpty
GPure x >>== k = k x
GBind m k >>== h = GBind m (\v => k v >>== h)

Functor Gen where
  map = mapGen

Applicative Gen where
  pure = GPure
  (<*>) = (<**>)

Monad Gen where
  (>>=) = (>>==)
