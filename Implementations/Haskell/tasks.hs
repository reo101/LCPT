{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UnicodeSyntax #-}

{-# HLINT ignore "Use <$>" #-}
{-# HLINT ignore "Use fmap" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

import Control.Applicative (Alternative ((<|>)))
import Control.Arrow (Arrow (first, second))
import Control.Monad (ap, guard, join, liftM, liftM2, replicateM, forM)
import Control.Monad.Identity (Identity)
import Data.List (nub)
import Data.Maybe (fromJust)
import Data.Tuple (swap)
import Data.Unique (hashUnique, newUnique)

-------------
--- State ---
-------------

newtype StateT s m a = StateT {runStateT :: s -> m (s, a)}

execStateT :: (Monad m) => StateT s m a -> s -> m s
execStateT m s = liftM fst (runStateT m s)

evalStateT :: (Monad m) => StateT s m a -> s -> m a
evalStateT m s = liftM snd (runStateT m s)

get :: (Monad m) => StateT s m s
get = StateT $ \s -> return (s, s)

put :: (Monad m) => s -> StateT s m ()
put s = StateT $ const $ return (s, ())

modify :: (Monad m) => (s -> s) -> StateT s m ()
modify f = StateT $ \s -> return (f s, ())

instance (Monad m) => Functor (StateT s m) where
  fmap :: Monad m => (a -> b) -> StateT s m a -> StateT s m b
  fmap = liftM

instance (Monad m) => Applicative (StateT s m) where
  pure :: Monad m => a -> StateT s m a
  pure x = StateT $ return . (,x)

  (<*>) :: Monad m => StateT s m (a -> b) -> StateT s m a -> StateT s m b
  (<*>) = ap

instance (Monad m) => Monad (StateT s m) where
  (>>=) :: Monad m => StateT s m a -> (a -> StateT s m b) -> StateT s m b
  sma >>= fasmb = StateT $ \s -> do
    (s', a) <- runStateT sma s
    let sb = fasmb a
    runStateT sb s'

class MonadTrans t where
  lift :: (Monad m) => m a -> t m a

instance MonadTrans (StateT s) where
  lift :: Monad m => m a -> StateT s m a
  lift m = StateT $ \s -> do
    a <- m
    return (s, a)

--------------
--- genSym ---
--------------

genSym :: String -> IO String
genSym name = (name ++) . show . hashUnique <$> newUnique

-------------
--- Types ---
-------------

type Variable = String
type Index = Integer

data Λ
  = Var Variable
  | App Λ Λ
  | Abs Variable Λ
  deriving (Show, Eq)

data Λⁿ
  = Varⁿ Index
  | Appⁿ Λⁿ Λⁿ
  | Absⁿ Λⁿ
  deriving (Show, Eq)

type Γ = [(Variable, Index)]
type Γⁿ = [(Index, Variable)]

-- ♭ flat
f :: Γ -> Λ -> Λⁿ
f γ (Var x) = Varⁿ $ fromJust $ lookup x γ
f γ (App λ₁ λ₂) = Appⁿ (f γ λ₁) (f γ λ₂)
f γ (Abs x λ) = Absⁿ (f γ' λ)
  where
    γ' :: Γ
    γ' = γ₄
      where
        γ₂ = filter ((/= x) . fst) γ
        γ₃ = second succ <$> γ₂
        γ₄ = (x, 0) : γ₃

-- ♯ sharp
s :: Γⁿ -> Λⁿ -> IO Λ
s γⁿ (Varⁿ xⁿ) = do
  return $ Var $ fromJust $ lookup xⁿ γⁿ
s γⁿ (Appⁿ λⁿ₁ λⁿ₂) = do
  λ₁ <- s γⁿ λⁿ₁
  λ₂ <- s γⁿ λⁿ₂
  return $ App λ₁ λ₂
s γⁿ (Absⁿ λⁿ) = do
  new <- genSym "n"
  let γⁿ' :: Γⁿ
      γⁿ' = (0, new) : (first succ <$> γⁿ)
  λ <- s γⁿ' λⁿ
  return $ Abs new λ

-----------
--- SED ---
-----------

sed :: (Variable, Variable) -> Λ -> Λ
sed (x, y) (Var z) =
  Var $
    if z == x
      then y
      else z
sed (x, y) (App λ₁ λ₂) =
  App (sed (x, y) λ₁) (sed (x, y) λ₂)
sed (x, y) (Abs z λ) =
  Abs z $
    if z == x
      then λ
      else sed (x, y) λ

-----------
--- =α= ---
-----------

type Match = (Variable, Variable)
type Matches = [Match]

α :: Λ -> Λ -> IO Bool
α λ₁ λ₂ = evalStateT (αh λ₁ λ₂) []
  where
    αh :: Λ -> Λ -> StateT Matches IO Bool
    αh (Var x₁) (Var x₂) = do
      γ <- get
      if
          -- Are in relation
          | (x₁, x₂) `elem` γ ->
              return True
          -- Are not both in a relation,
          -- but one of them is with another
          | (||)
              (x₁ `elem` (fst <$> γ))
              (x₂ `elem` (snd <$> γ)) ->
              return False
          -- First time seeing both - bind
          -- Will only happen for globals ...
          | otherwise ->
              (modify ((x₁, x₂) :) >> return True)
    αh (App λ₁₁ λ₁₂) (App λ₂₁ λ₂₂) = do
      α₁ <- αh λ₁₁ λ₂₁
      α₂ <- αh λ₁₂ λ₂₂
      return $ (&&) α₁ α₂
    αh (Abs x₁ λ₁) (Abs x₂ λ₂) = do
      new <- lift $ genSym "x"
      let λ₁' = sed (x₁, new) λ₁
      let λ₂' = sed (x₂, new) λ₂
      -- ... since this handles the locals
      modify ((new, new) :)
      αh λ₁' λ₂'
    αh _ _ = do
      return False

-----------------
--- FREE VARS ---
-----------------

fv :: Λ -> [Variable]
fv (Var x) = [x]
fv (App λ₁ λ₂) = nub $ fv λ₁ ++ fv λ₂
fv (Abs x λ) = filter (/= x) $ fv λ

--------------------
--- PRETTY PRINT ---
--------------------

class PrettyPrint c where
  pprint :: c -> String

instance PrettyPrint Λ where
  pprint :: Λ -> String
  pprint (Var x) =
    x
  pprint (App λ₁ λ₂) =
    concat
      [ pprint λ₁
      , " "
      , pprint λ₂
      ]
  pprint (Abs x λ) =
    concat
      [ "("
      , "\\" -- "λ"
      , x
      , " -> " -- "."
      , pprint λ
      , ")"
      ]

instance PrettyPrint Λⁿ where
  pprint :: Λⁿ -> String
  pprint (Varⁿ n) =
    show n
  pprint (Appⁿ λⁿ₁ λⁿ₂) =
    concat
      [ pprint λⁿ₁
      , " "
      , pprint λⁿ₂
      ]
  pprint (Absⁿ λⁿ) =
    concat
      [ "("
      , "\\" -- "λ"
      , pprint λⁿ
      , ")"
      ]

-------------
--- TESTS ---
-------------

-- 0λ0
e1ⁿ :: Λⁿ
e1ⁿ = Appⁿ (Varⁿ 0) (Absⁿ (Varⁿ 0))

-- >>> s [(0,"t")] e1ⁿ
-- App (Var "t") (Abs "n1" (Var "n1"))

-- λ(λ0)(λ1)
e2ⁿ :: Λⁿ
e2ⁿ = Absⁿ (Appⁿ (Absⁿ (Varⁿ 0)) (Absⁿ (Varⁿ 1)))

-- >>> s [] e2ⁿ
-- Abs "n1" (App (Abs "n2" (Var "n2")) (Abs "n3" (Var "n1")))

e1 :: Λ
e1 = App (Var "b") (Abs "x" (Var "x"))

e2 :: Λ
e2 = App (Var "x") (Abs "y" (Var "y"))

-- >>> α e1 e2
-- False

------

e3 :: Λ
e3 = App (Var "x") (Abs "x" (Var "x"))

e4 :: Λ
e4 = App (Var "y") (Abs "y" (Var "a"))

-- >>> α e3 e4
-- False

------

complex :: Λ
complex = Abs "x" (App (App (App (Var "x") (Var "y")) (Abs "u" (App (App (Var "z") (Var "u")) (Abs "v" (App (Var "v") (Var "y")))))) (Var "z"))

-- >>> pprint complex
-- "(\\x -> x y (\\u -> z u (\\v -> v y)) z)"

-- Define IndexedComplexFV for Λ
icfv :: Γ
icfv = zip (fv complex) [0 ..]

-- Define IndexedComplexFVⁿ for Λⁿ
genicfvⁿ :: IO Γⁿ -- IO because of genSym
genicfvⁿ = do
  forM icfv $ \(_, i) -> do
    x' <- genSym "n"
    return (i, x')

-- ♭(complex)
complexⁿ :: Λⁿ
complexⁿ = f icfv complex

-- ♯(♭(complex))
gencomplex' :: IO Λ
gencomplex' = do
  icfvⁿ <- genicfvⁿ
  s icfvⁿ complexⁿ

-- >>> pprint complex
-- "(\\x -> x y (\\u -> z u (\\v -> v y)) z)"

-- >>> pprint complexⁿ
-- "(\\0 1 (\\3 0 (\\0 3)) 2)"

-- >>> pprint <$> gencomplex'
-- "(\\n1 -> n1 n2 (\\n3 -> n4 n3 (\\n5 -> n5 n2)) n4)"

works :: IO Bool
works = do
  complex' <- gencomplex'
  α complex complex'

-- >>> works
-- True
