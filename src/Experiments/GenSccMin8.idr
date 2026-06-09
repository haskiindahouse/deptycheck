module Experiments.GenSccMin8

%default total

data NoWeaker : Bool -> Bool -> Type where
  NW : NoWeaker l r

minB : Bool -> Bool -> Bool
minB False _ = False
minB True x = x

minNoWeakerLeft : {x : Bool} -> NoWeaker l r -> NoWeaker (minB l x) (minB r x)
minNoWeakerLeft _ = NW

minNoWeakerRight : {x : Bool} -> NoWeaker l r -> NoWeaker (minB x l) (minB x r)
minNoWeakerRight _ = NW

minNoWeaker : NoWeaker l1 r1 -> NoWeaker l2 r2 -> NoWeaker (minB l1 l2) (minB r1 r2)
minNoWeaker _ _ = NW

data Gen : Bool -> Type -> Type where
  Empty : Gen False a
  Pure : a -> Gen True a
  Raw : a -> Gen True a
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

minRightFalse : (x : Bool) -> minB x False = False
minRightFalse False = Refl
minRightFalse True = Refl

minSame : (x : Bool) -> minB x x = x
minSame False = Refl
minSame True = Refl

minRightTrue : (x : Bool) -> minB x True = x
minRightTrue False = Refl
minRightTrue True = Refl

minAssoc : (x : Bool) -> (y : Bool) -> (z : Bool) -> minB (minB x y) z = minB x (minB y z)
minAssoc False _ _ = Refl
minAssoc True False _ = Refl
minAssoc True True False = Refl
minAssoc True True True = Refl

private infixl 3 <**>
(<**>) : Gen bl (a -> b) -> Gen br a -> Gen (minB bl br) b

Empty <**> _ = Empty
x <**> Empty = rewrite minRightFalse bl in Empty
Pure f <**> x = map f x
x <**> Pure y = rewrite minRightTrue bl in map (\f => f y) x
Raw f <**> Raw x = Raw (f x)
OneOf gs <**> y = OneOf (map (\g => assert_total $ g <**> y) gs)
x <**> OneOf ys = OneOf (map (\y => assert_total $ x <**> y) ys)
Bind @{nw} {l} {r} x f <**> Raw y =
  Bind @{nw} x (\c => rewrite minRightTrue r in assert_total $ f c <**> Raw y)
Raw y <**> Bind @{nw} x f = Bind @{minNoWeakerRight nw} x (\c => assert_total $ Raw y <**> f c)
Bind @{lnw} x f <**> Bind @{rnw} y g =
  Bind @{minNoWeaker lnw rnw} (Bind x (\u => map (\v => (u, v)) y))
    (\(u, v) => assert_total $ f u <**> g v)

private infixl 1 >>==
(>>==) : Gen bl a -> (a -> Gen br b) -> Gen (minB bl br) b
Empty >>== _ = Empty
Pure x >>== f = f x
Raw x >>== f = f x
OneOf xs >>== f = OneOf (map (\g => assert_total $ g >>== f) xs)
(>>==) (Bind @{nw} {l} {r} x g) {br} f =
  rewrite minAssoc l r br in
    Bind @{NW} x (\v => assert_total $ g v >>== f)
