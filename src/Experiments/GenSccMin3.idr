module Experiments.GenSccMin3

%default total

data E = ME | NE

minE : E -> E -> E
minE NE NE = NE
minE _ _ = ME

data Gen : E -> Type -> Type where
  Empty : Gen e a
  Pure : a -> Gen e a
  Raw : a -> Gen e a
  Bind : Gen e a -> (a -> Gen e b) -> Gen e b
  OneOf : List (Gen e a) -> Gen e a
  Labelled : String -> Gen e a -> Gen e a

isEmpty : Gen e a -> Bool
isEmpty Empty = True
isEmpty _ = False

mapG : (a -> b) -> Gen e a -> Gen e b
mapG f Empty = Empty
mapG f (Pure x) = Pure (f x)
mapG f (Raw x) = Raw (f x)
mapG f (Bind x g) = Bind x (\v => assert_total $ mapG f (g v))
mapG f (OneOf xs) = OneOf (map (\x => assert_total $ mapG f x) xs)
mapG f (Labelled l x) = Labelled l (mapG f x)

infixl 3 <**>
(<**>) : Gen e (a -> b) -> Gen e a -> Gen e b
g <**> h with (isEmpty g) | (isEmpty h)
  Empty <**> _ | _ | _ = Empty
  _ <**> Empty | _ | _ = Empty
  Pure f <**> x | _ | _ = mapG f x
  x <**> Pure y | _ | _ = mapG (\f => f y) x
  Raw f <**> Raw x | _ | _ = Raw (f x)
  Labelled l x <**> y | _ | False = Labelled l (x <**> y)
  x <**> Labelled l y | False | _ = Labelled l (x <**> y)
  OneOf xs <**> y | _ | False = OneOf (map (\x => assert_total $ x <**> y) xs)
  x <**> OneOf ys | False | _ = OneOf (map (\y => assert_total $ x <**> y) ys)
  Bind x f <**> Raw y | _ | _ = Bind x (\v => f v <**> Raw y)
  Raw y <**> Bind x f | _ | _ = Bind x (\v => Raw y <**> f v)
  Bind x f <**> Bind y g | _ | _ = Bind (Bind x (\u => mapG (\v => (u, v)) y)) (\(u, v) => f u <**> g v)

infixl 1 >>==
(>>==) : Gen e a -> (a -> Gen e b) -> Gen e b
Empty >>== _ = Empty
Pure x >>== f = f x
Raw x >>== f = f x
Bind x g >>== f = Bind x (\v => assert_total $ g v >>== f)
Labelled l x >>== f = Labelled l (x >>== f)
OneOf xs >>== f = OneOf (map (\x => assert_total $ x >>== f) xs)

Functor (Gen e) where
  map = mapG

Applicative (Gen e) where
  pure = Pure
  (<*>) = (<**>)

Monad (Gen e) where
  (>>=) = (>>==)
