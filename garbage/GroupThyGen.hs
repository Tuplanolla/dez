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

data Nots = Add | Mul
  deriving (Eq, Ord, Show)

data Expr = Var Int | Bin Expr Expr | Null | Un Expr
  deriving (Eq, Ord, Show)

showsNots :: Nots -> Expr -> ShowS
showsNots _ Var {} = showString "x"
showsNots Add Bin {} = showString " + "
showsNots Add Null {} = showString "0"
showsNots Add Un {} = showString "- "
showsNots Mul Bin {} = showString " \xd7 "
showsNots Mul Null {} = showString "1"
showsNots Mul Un {} = showString "/ "

showsPrecExpr :: Int -> Nots -> Expr -> ShowS
showsPrecExpr _ cs e @ (Var i) = showsNots cs e . showChar (subscribe i)
showsPrecExpr n cs e @ (Bin x y) = showParen (n > 6)
  (showsPrecExpr 7 cs x . showsNots cs e . showsPrecExpr 7 cs y)
showsPrecExpr _ cs e @ Null = showsNots cs e
showsPrecExpr n cs e @ (Un x) = showParen (n > 7)
  (showsNots cs e . showsPrecExpr 8 cs x)

showsExpr :: Nots -> Expr -> ShowS
showsExpr = showsPrecExpr 0

showExpr :: Nots -> Expr -> String
showExpr cs e = showsExpr cs e mempty

manglesExpr :: Expr -> ShowS
manglesExpr = let
  f _ e @ (Var i) = showChar 'v' . showInt i
  f n e @ (Bin x y) = (\ k ->
    if n > 6 then showChar 'o' . k . showChar 'c' else k)
    (f 7 x . showChar 'b' . f 7 y)
  f _ e @ Null = showChar 'n'
  f n e @ (Un x) = (\ k ->
    if n > 7 then showChar 'o' . k . showChar 'c' else k)
    (showChar 'u' . f 8 x) in
  f 0

mangleExpr :: Expr -> String
mangleExpr e = manglesExpr e mempty

genExpr :: Int -> [Expr]
genExpr n = case n of
  0 -> Null : [Var i | i <- [0 .. 1]]
  i -> genExpr 0 ++ do
    x <- genExpr (pred n)
    Un x : do
      y <- genExpr (pred n)
      [Bin x y]

evalExpr :: Fractional a => (Int -> a) -> Nots -> Expr -> a
evalExpr f cs @ Add e = case e of
  Var i -> f i
  Bin x y -> evalExpr f cs x + evalExpr f cs y
  Null -> 0
  Un x -> negate (evalExpr f cs x)
evalExpr f cs @ Mul e = case e of
  Var i -> f i
  Bin x y -> evalExpr f cs x * evalExpr f cs y
  Null -> 1
  Un x -> recip (evalExpr f cs x)

occurs :: Expr -> Map Int Int
occurs e = case e of
  Var i -> singleton i 1
  Bin x y -> unionWith (+) (occurs x) (occurs y)
  Null -> mempty
  Un x -> occurs x

isAffine :: Expr -> Bool
isAffine = all (== 1) . occurs

occursPoint :: Expr -> Map () Int
occursPoint e = case e of
  Var i -> mempty
  Bin x y -> unionWith (+) (occursPoint x) (occursPoint y)
  Null -> singleton (toEnum 0) 1
  Un x -> occursPoint x

isAffinePoint :: Expr -> Bool
isAffinePoint = all (== 1) . occursPoint

constrs :: Expr -> Int
constrs e = case e of
  Var i -> 1
  Bin x y -> 1 + constrs x + constrs y
  Null -> 1
  Un x -> 1 + constrs x

exprs :: Int -> IO ()
exprs n = traverse_ (putStrLn . showExpr Add) (genExpr n)

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
  g a b = evalExpr (f a b) Add
  xs = do
    x <- genExpr n
    y <- genExpr n
    -- Only irreflexive asymmetric equations are of interest...
    guard (x < y)
    guard (isAffinePoint x && isAffinePoint y)
    guard (constrs x < 6 && constrs y < 6)
    -- ...if they are satisfied in a linear subspace
    -- (that is, they are not obviously false).
    guard (and [g a b x == g a b y | a <- [7, 11, 13], b <- [2, 3, 5]])
    pure (Eqn x y) in
  traverse_ (putStrLn . showEqn Add) xs

main :: IO ()
main = do
  putStrLn "Once upon a time in an algebra..."
  exprs 1
  putStrLn "...until they came across an equational theory..."
  eqns 1
  putStrLn "...the end."
