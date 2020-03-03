module Main where

import Control.Applicative
import Control.Monad
import Data.Char
import Data.Foldable
import Data.Map
import Data.Ratio
import Numeric

subscribe :: Int -> Char
subscribe i = chr (ord '\x2080' + i)

data Nots = Arith
  deriving (Eq, Ord, Show)

data Expr = Var Int | Add Expr Expr | Zero | Neg Expr |
  Mul Expr Expr | One | Recip Expr
  deriving (Eq, Ord, Show)

showsNots :: Nots -> Expr -> ShowS
showsNots _ Var {} = showString "x"
showsNots Arith Add {} = showString " + "
showsNots Arith Zero {} = showString "0"
showsNots Arith Neg {} = showString "- "
showsNots Arith Mul {} = showString " \xd7 "
showsNots Arith One {} = showString "1"
showsNots Arith Recip {} = showString "/ "

showsPrecExpr :: Int -> Nots -> Expr -> ShowS
showsPrecExpr _ cs e @ (Var i) = showsNots cs e . showChar (subscribe i)
showsPrecExpr n cs e @ (Add x y) = showParen (n > 6)
  (showsPrecExpr 7 cs x . showsNots cs e . showsPrecExpr 7 cs y)
showsPrecExpr _ cs e @ Zero = showsNots cs e
showsPrecExpr n cs e @ (Neg x) = showParen (n > 7)
  (showsNots cs e . showsPrecExpr 8 cs x)
showsPrecExpr n cs e @ (Mul x y) = showParen (n > 8)
  (showsPrecExpr 9 cs x . showsNots cs e . showsPrecExpr 9 cs y)
showsPrecExpr _ cs e @ One = showsNots cs e
showsPrecExpr n cs e @ (Recip x) = showParen (n > 9)
  (showsNots cs e . showsPrecExpr 10 cs x)

showsExpr :: Nots -> Expr -> ShowS
showsExpr = showsPrecExpr 0

showExpr :: Nots -> Expr -> String
showExpr cs e = showsExpr cs e mempty

manglesExpr :: Expr -> ShowS
manglesExpr = let
  f _ e @ (Var i) = showChar 'v' . showInt i
  f n e @ (Add x y) = (\ k ->
    if n > 6 then showChar 'o' . k . showChar 'c' else k)
    (f 7 x . showChar 'a' . f 7 y)
  f _ e @ Zero = showChar 'z'
  f n e @ (Neg x) = (\ k ->
    if n > 7 then showChar 'o' . k . showChar 'c' else k)
    (showChar 'n' . f 8 x)
  f n e @ (Mul x y) = (\ k ->
    if n > 8 then showChar 'o' . k . showChar 'c' else k)
    (f 9 x . showChar 'm' . f 9 y)
  f _ e @ One = showChar 'w'
  f n e @ (Recip x) = (\ k ->
    if n > 9 then showChar 'o' . k . showChar 'c' else k)
    (showChar 'r' . f 10 x) in
  f 0

mangleExpr :: Expr -> String
mangleExpr e = manglesExpr e mempty

genExpr :: Int -> [Expr]
genExpr n = case n of
  0 -> Zero : One : [Var i | i <- [0 .. 1]]
  i -> genExpr 0 ++ do
    x <- genExpr (pred n)
    Neg x : Recip x : do
      y <- genExpr (pred n)
      [Add x y, Mul x y]

evalExpr :: (Eq a, Fractional a) => (Int -> a) -> Expr -> a
evalExpr f e = case e of
  Var i -> f i
  Add x y -> evalExpr f x + evalExpr f y
  Zero -> 0
  Neg x -> negate (evalExpr f x)
  Mul x y -> evalExpr f x * evalExpr f y
  One -> 1
  Recip x -> case evalExpr f x of
    0 -> 0
    y -> recip y

occurs :: Expr -> Map Int Int
occurs e = case e of
  Var i -> singleton i 1
  Add x y -> unionWith (+) (occurs x) (occurs y)
  Zero -> mempty
  Neg x -> occurs x
  Mul x y -> unionWith (+) (occurs x) (occurs y)
  One -> mempty
  Recip x -> occurs x

isAffine :: Expr -> Bool
isAffine = all (== 1) . occurs

occursPoint :: Expr -> Map Bool Int
occursPoint e = case e of
  Var i -> mempty
  Add x y -> unionWith (+) (occursPoint x) (occursPoint y)
  Zero -> singleton (toEnum 0) 1
  Neg x -> occursPoint x
  Mul x y -> unionWith (+) (occursPoint x) (occursPoint y)
  One -> singleton (toEnum 1) 1
  Recip x -> occursPoint x

isAffinePoint :: Expr -> Bool
isAffinePoint = all (== 1) . occursPoint

constrs :: Expr -> Int
constrs e = case e of
  Var i -> 1
  Add x y -> 1 + constrs x + constrs y
  Zero -> 1
  Neg x -> 1 + constrs x
  Mul x y -> 1 + constrs x + constrs y
  One -> 1
  Recip x -> 1 + constrs x

exprs :: Int -> IO ()
exprs n = traverse_ (putStrLn . showExpr Arith) (genExpr n)

data Eqn = Eqn Expr Expr
  deriving (Eq, Ord, Show)

showsEqn :: Nots -> Eqn -> ShowS
showsEqn cs (Eqn x y) = showsExpr cs x . showString " = " . showsExpr cs y

showEqn :: Nots -> Eqn -> String
showEqn cs e = showsEqn cs e mempty

manglesEqn :: Eqn -> ShowS
manglesEqn (Eqn x y) = manglesExpr x . showChar 'e' . manglesExpr y

mangleEqn :: Eqn -> String
mangleEqn e = manglesEqn e mempty

eqns :: Int -> IO ()
eqns n = let
  f :: Rational -> Rational -> Int -> Rational
  f a b = (a +) . (b *) . fromIntegral
  g :: Rational -> Rational -> Expr -> Rational
  g a b = evalExpr (f a b)
  xs = do
    x <- genExpr n
    y <- genExpr n
    -- Only irreflexive asymmetric equations are of interest...
    guard (x < y)
    -- ...as long as they are affine in all the variables...
    guard (isAffinePoint x && isAffinePoint y)
    guard (constrs x < 6 && constrs y < 6)
    -- ...if they are satisfied in a linear subspace
    -- (that is, they are not obviously false).
    guard (and [g a b x == g a b y | a <- [7, 11, 13], b <- [2, 3, 5]])
    pure (Eqn x y) in
  traverse_ (putStrLn . showEqn Arith) xs

main :: IO ()
main = do
  putStrLn "Once upon a time in an algebra..."
  exprs 1
  putStrLn "...until they came across an equational theory..."
  eqns 1
  putStrLn "...the end."
