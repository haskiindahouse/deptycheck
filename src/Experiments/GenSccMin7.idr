module Experiments.GenSccMin7

%default total

data NoWeaker : Bool -> Bool -> Type where
  Keep : NoWeaker b b
  LiftLeft : NoWeaker False True

minB : Bool -> Bool -> Bool
minB False _ = False
minB True x = x

minNoWeakerLeft : NoWeaker l r -> NoWeaker (minB l x) (minB r x)
minNoWeakerLeft Keep = Keep
minNoWeakerLeft LiftLeft = LiftLeft

minNoWeakerRight : NoWeaker l r -> NoWeaker (minB x l) (minB x r)
minNoWeakerRight Keep = Keep
minNoWeakerRight LiftLeft = LiftLeft

minNoWeaker : NoWeaker l1 r1 -> NoWeaker l2 r2 -> NoWeaker (minB l1 l2) (minB r1 r2)
minNoWeaker Keep Keep = Keep
minNoWeaker LiftLeft _ = LiftLeft
minNoWeaker _ LiftLeft = LiftLeft

data Gen : Bool -> Type -> Type where
  Empty : Gen False a
  Pure : a -> Gen b a
  Raw : a -> Gen b a
  OneOf : List (Gen b a) -> Gen b a
  Bind : {auto 0 nw : NoWeaker l r} -> Gen l c -> (c -> Gen r a) -> Gen (minB l r) a

isEmpty : Gen b a -> Bool
isEmpty Empty = True
isEmpty _ = False

Functor (Gen b) where
  map f Empty = Empty
  map f (Pure x) = Pure (f x)
  map f (Raw x) = Raw (f x)
  map f (OneOf xs) = OneOf (map (\g => assert_total $ map f g) xs)
  map f (Bind @{nw} x g) = Bind @{nw} x (\v => assert_total $ map f (g v))

private infixl 3 <**>
(<**>) : Gen bl (a -> b) -> Gen br a -> Gen (minB bl br) b

g <**> h with (isEmpty g) | (isEmpty h)
  Empty <**> _ | _ | _ = Empty
  _ <**> Empty | _ | _ = Empty
  Pure f <**> x | _ | _ = map f x
  x <**> Pure y | _ | _ = map (\f => f y) x
  Raw f <**> Raw x | _ | _ = Raw (f x)
  OneOf gs <**> y | _ | _ = OneOf (map (\g => assert_total $ g <**> y) gs)
  x <**> OneOf ys | _ | _ = OneOf (map (\y => assert_total $ x <**> y) ys)
  Bind @{nw} x f <**> Raw y | _ | _ = Bind @{minNoWeakerLeft nw} x (\c => assert_total $ f c <**> Raw y)
  Raw y <**> Bind @{nw} x f | _ | _ = Bind @{minNoWeakerRight nw} x (\c => assert_total $ Raw y <**> f c)
  Bind @{lnw} x f <**> Bind @{rnw} y g | _ | _ =
    Bind @{minNoWeaker lnw rnw} (Bind x (\u => map (\v => (u, v)) y))
      (\(u, v) => assert_total $ f u <**> g v)

Applicative (Gen b) where
  pure = Pure
  (<*>) = (<**>)

private infixl 1 >>==
(>>==) : Gen bl a -> (a -> Gen br b) -> Gen (minB bl br) b
Empty >>== _ = Empty
Pure x >>== f = f x
Raw x >>== f = f x
OneOf xs >>== f = OneOf (map (\g => assert_total $ g >>== f) xs)
Bind @{nw} x g >>== f = Bind @{minNoWeakerLeft nw} x (\v => assert_total $ g v >>== f)

Monad (Gen b) where
  (>>=) = (>>==)
