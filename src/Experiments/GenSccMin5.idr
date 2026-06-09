module Experiments.GenSccMin5

%default total

data Gen : Type -> Type where
  Empty : Gen a
  Pure : a -> Gen a
  Raw : a -> Gen a
  Bind : Gen c -> (c -> Gen a) -> Gen a

isEmpty : Gen a -> Bool
isEmpty Empty = True
isEmpty _ = False

Functor Gen where
  map f Empty = Empty
  map f (Pure x) = Pure (f x)
  map f (Raw x) = Raw (f x)
  map f (Bind x g) = Bind x (\v => assert_total $ map f (g v))

private infixl 3 <**>
(<**>) : Gen (a -> b) -> Gen a -> Gen b

g <**> h with (isEmpty g) | (isEmpty h)
  Empty <**> _ | _ | _ = Empty
  _ <**> Empty | _ | _ = Empty
  Pure f <**> x | _ | _ = map f x
  x <**> Pure y | _ | _ = map (\f => f y) x
  Raw f <**> Raw x | _ | _ = Raw (f x)
  Bind x f <**> Raw y | _ | _ = Bind x (\c => assert_total $ f c <**> Raw y)
  Raw y <**> Bind x f | _ | _ = Bind x (\c => assert_total $ Raw y <**> f c)
  Bind x f <**> Bind y g | _ | _ = Bind (Bind x (\u => map (\v => (u, v)) y)) (\(u, v) => assert_total $ f u <**> g v)

Applicative Gen where
  pure = Pure
  (<*>) = (<**>)

private infixl 1 >>==
(>>==) : Gen a -> (a -> Gen b) -> Gen b
Empty >>== _ = Empty
Pure x >>== f = f x
Raw x >>== f = f x
Bind x g >>== f = Bind x (\v => assert_total $ g v >>== f)

Monad Gen where
  (>>=) = (>>==)
