{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TupleSections #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# HLINT ignore "Collapse lambdas" #-}
{-# HLINT ignore "Redundant lambda" #-}
{-# HLINT ignore "Unused LANGUAGE pragma" #-}
{-# HLINT ignore "Use const" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- System T

data B where
  Tt :: B
  Ff :: B

instance Show B where
  show :: B -> String
  show Tt = "Real"
  show Ff = "Fake"

data N where
  Z :: N
  S :: N -> N

instance Show N where
  show :: N -> String
  show = show . fromNat

split :: (a, b) -> (a -> b -> c) -> c
-- split = flip uncurry
split (x, y) f = f x y

cases :: B -> a -> a -> a
cases Tt x _ = x
cases Ff _ y = y

r :: N -> a -> (N -> a -> a) -> a
r Z s _ = s
r (S n) s t = t n (r n s t)

toNat :: Int -> N
toNat n = foldr (const S) Z [1 .. n]

fromNat :: N -> Int
fromNat Z = 0
fromNat (S n) = succ $ fromNat n

roundabout :: (N -> N -> a) -> Int -> Int -> a
roundabout f x y = f (toNat x) (toNat y)

(...) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(...) = (.) . (.)

---------------

bor :: B -> B -> B
bor = \a b -> cases a Tt b

band :: B -> B -> B
band = \a b -> cases a b Ff

bnot :: B -> B
bnot = \a -> cases a Ff Tt

------------
--- 3.14 ---
------------

z :: N -> B
z = \n -> r n Tt (\n' p -> Ff)

plus :: N -> N -> N
plus = \m n -> r n m (\i prev -> S prev)

minus :: N -> N -> N
minus = \m -> r m (\n -> Z) (\m' p -> \n -> r n (S m') (\n' q -> p n'))

-- >>> roundabout minus 0 5
-- 0
--
-- >>> roundabout minus 18 0
-- 18
--
-- >>> roundabout minus 7 2
-- 5

mult :: N -> N -> N
mult = \m -> r m (\n -> Z) (\m' p n -> plus (p n) n)

-- >>> roundabout mult 5 6
-- 30

mult' :: N -> N -> N
mult' = \m n -> r n Z (\i prev -> plus prev m)

-- >>> roundabout mult' 5 6
-- 30

pr :: N -> N
pr = \m -> r m Z (\m' p -> m')

-- >>> pr $ toNat 5
-- 4
--
-- >>> pr $ toNat 0
-- 0

eq :: N -> N -> B
eq = \m -> r m (\n -> r n Tt (\n' p -> Ff)) (\m' p -> \n -> r n Ff (\n' q -> p n'))

-- >>> roundabout eq 15 15
-- Real
--
-- >>> roundabout eq 15 0
-- Fake
--
-- >>> roundabout eq 0 15
-- Fake

neq :: N -> N -> B
neq = bnot ... eq

-- >>> fromNat $ pr $ toNat 5
-- 4

lt :: N -> N -> B
lt = \m -> r m (\n -> r n Ff (\n' p -> Tt)) (\m' p -> \n -> r n Ff (\n' q -> p n'))

-- lt = \m -> r m (\n -> r n Ff (\n' p -> Tt)) (\m' p -> \n -> r n Ff (\n' q -> bor (eq m n') q))

-- >>> (uncurry $ roundabout lt) <$> [(3, 1), (0, 16), (6, 14), (16, 0), (5, 5), (16, 6)]
-- [Fake,Real,Real,Fake,Fake,Fake]

lte :: N -> N -> B
lte = bnot ... gt

gt :: N -> N -> B
gt = \m n -> bnot (bor (lt m n) (eq m n))

-- >>> (uncurry $ roundabout gt) <$> [(3, 1), (0, 16), (6, 14), (16, 0), (5, 5), (16, 6)]
-- [Real,Fake,Fake,Real,Fake,Real]

gte :: N -> N -> B
gte = bnot ... lt

------------
--- 3.15 ---
------------

quotient :: N -> N -> N
quotient = \m n -> r m Z (\m' p -> cases (lte (mult n m') m) m' p)

-- >>> (uncurry $ roundabout quotient) <$> [(3, 4), (4, 3), (14, 3), (15, 3), (16, 3)]
-- [0,1,4,5,5]

remainder :: N -> N -> N
remainder = \m n -> minus m (mult (quotient m n) n)

-- >>> (uncurry $ roundabout remainder) <$> [(3, 4), (4, 3), (14, 3), (15, 3), (16, 3)]
-- [3,1,2,0,1]

------------
--- 3.16 ---
------------

divides :: N -> N -> B
divides = \m n -> eq (remainder m n) Z

prime :: N -> B
prime = \n -> r n Ff (\n' p -> cases (band (divides n n') (neq n' (toNat 1))) Ff (cases (eq n' (toNat 1)) Tt p))

-- >>> prime . toNat <$> [0..15]
-- [Fake,Fake,Real,Real,Fake,Real,Fake,Real,Fake,Fake,Fake,Real,Fake,Real,Fake,Fake]

-------------
--- BONUS ---
-------------

factorial :: N -> N
factorial = \m -> r m (toNat 1) (\m' p -> mult (S m') p)

-- >>> factorial . toNat <$> [0..7]
-- [1,1,2,6,24,120,720,5040]

expo :: N -> N -> N
expo = \m n -> r n (toNat 1) (\n' p -> mult m p)

-- >>> ((\x -> (x,) <$> [0..4]) <$> [0..3])
-- [[(0,0),(0,1),(0,2),(0,3),(0,4)],[(1,0),(1,1),(1,2),(1,3),(1,4)],[(2,0),(2,1),(2,2),(2,3),(2,4)],[(3,0),(3,1),(3,2),(3,3),(3,4)]]
--
-- >>> (uncurry expo <$>) <$> ((\x -> (toNat x,) . toNat <$> [0..4]) <$> [0..3])
-- [[1,0,0,0,0],[1,1,1,1,1],[1,2,4,8,16],[1,3,9,27,81]]
