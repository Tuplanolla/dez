-- stack ghci --package containers --package mtl --package text --package fgl --package graphviz -- GrowTrees.hs

{-# LANGUAGE
    DeriveFunctor, ImportQualifiedPost, NumDecimals, StandaloneDeriving,
    RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS -Wno-orphans -Wno-unused-matches #-}

module GrowTrees where

import Control.Applicative
import Control.Monad.State
import Data.Char
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Graph qualified as Graph
import Data.Graph.Inductive.PatriciaTree
import Data.GraphViz
import Data.GraphViz.Attributes.Complete
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe
import Data.Text.Lazy (unpack)
import Data.Tree
import Numeric
import Numeric.Natural

lexicographically :: [Ordering] -> Ordering
lexicographically [] = EQ
lexicographically [x] = x
lexicographically (x : xs) = case x of
  LT -> LT
  EQ -> lexicographically xs
  GT -> GT

instance Labellable () where
  toLabelValue () = toLabelValue ""

printPreview :: forall a b gr. (Labellable a, Labellable b, Ord b, Graph gr) =>
  gr a b -> String
printPreview g = let
  params :: forall n. GraphvizParams n a b () a
  params = nonClusteredParams {
    globalAttributes = [GraphAttrs [RankDir FromLeft]],
    fmtNode = \ (_, l) -> [toLabel l],
    fmtEdge = \ (_, _, l) -> [toLabel l]}
  dg = setDirectedness graphToDot params g in
  unpack (printDotGraph dg)

treeTakeWhileWrong :: forall a. (a -> Bool) -> Tree a -> Tree a
treeTakeWhileWrong f (Node a xs)
  | f a = Node a (fmap (treeTakeWhileWrong f) xs)
  | otherwise = Node a []

treeTakeWhile :: forall a. (a -> Bool) -> Tree a -> Maybe (Tree a)
treeTakeWhile f (Node a xs)
  | f a = Just (Node a (catMaybes (fmap (treeTakeWhile f) xs)))
  | otherwise = Nothing

compactDrawTree :: Tree String -> String
compactDrawTree = let
  f (x : _ : xs) = x : f xs
  f xs = xs in
  unlines . f . lines . drawTree

data Term a =
  Null a |
  Un a (Term a) |
  Bin a (Term a) (Term a) |
  Rel (Term a) (Term a)
  deriving (Functor, Show)

deriving instance forall a. Eq a => Eq (Term a)
deriving instance forall a. Ord a => Ord (Term a)

-- Bad idea!
{-
instance forall a. Eq a => Eq (Term a) where
  (==) (Null n) (Null n') = n == n'
  (==) (Un n x) (Un n' x') = n == n' &&
    x == x'
  (==) (Bin n x y) (Bin n' x' y') = n == n' &&
    ((x == x' && y == y') || (x == y' && y == x'))
  (==) (Rel x y) (Rel x' y') =
    ((x == x' && y == y') || (x == y' && y == x'))
  (==) _ _ = False
-}

termSize :: forall a. Term a -> Natural
termSize (Null _) = 0
termSize (Un _ x) = succ (termSize x)
termSize (Bin _ x y) = succ (termSize x + termSize y)
termSize (Rel x y) = succ (termSize x + termSize y)

fillHoles :: forall a. (a -> Term a) -> Term a -> [Term a]
fillHoles f (Null n) = pure (f n)
fillHoles f (Un n x) = fmap (Un n) (fillHoles f x)
fillHoles f (Bin n x y) =
  liftA2 (Bin n) (pure x) (fillHoles f y) <>
  liftA2 (Bin n) (fillHoles f x) (pure y)
fillHoles f (Rel x y) =
  liftA2 Rel (pure x) (fillHoles f y) <>
  liftA2 Rel (fillHoles f x) (pure y)

findHoles :: forall a. Term a -> [(a -> Term a) -> Term a]
findHoles (Null n) = pure ($ n)
findHoles (Un n x) = fmap (fmap (Un n)) (findHoles x)
findHoles (Bin n x y) =
  (liftA2 . liftA2) (Bin n) ((pure . pure) x) (findHoles y) <>
  (liftA2 . liftA2) (Bin n) (findHoles x) ((pure . pure) y)
findHoles (Rel x y) =
  (liftA2 . liftA2) Rel ((pure . pure) x) (findHoles y) <>
  (liftA2 . liftA2) Rel (findHoles x) ((pure . pure) y)

subscript :: Char -> Char
subscript x
  | ord '0' <= ord x && ord x <= ord '9' =
    chr ((ord '\8320' - ord '0') + ord x)
  | otherwise = x

showSubscript :: forall a. Integral a => a -> ShowS
showSubscript n = showString (fmap subscript (showInt n mempty))

drawTermsIxed :: forall a. Integral a => Term a -> ShowS
drawTermsIxed (Null n) = showString "x" . showSubscript n
-- Technically, the operator is `'\8902'`, but `'\9733'` often looks better.
drawTermsIxed (Un n x) = showString "(\9733" . showSubscript n . showString " " .
  drawTermsIxed x . showString ")"
drawTermsIxed (Bin n x y) = showString "(" .
  drawTermsIxed x . showString " \8743" . showSubscript n . showString " " .
  drawTermsIxed y . showString ")"
drawTermsIxed (Rel x y) =
  drawTermsIxed x . showString " = " .
  drawTermsIxed y

drawTermIxed :: forall a. Integral a => Term a -> String
drawTermIxed x = drawTermsIxed x mempty

drawTerms :: forall a. Integral a => Term a -> ShowS
drawTerms (Null _) = showString "x"
drawTerms (Un _ x) = showString "(\9733 " .
  drawTerms x . showString ")"
drawTerms (Bin _ x y) = showString "(" .
  drawTerms x . showString " \8743 " .
  drawTerms y . showString ")"
drawTerms (Rel x y) =
  drawTerms x . showString " = " .
  drawTerms y

drawTerm :: forall a. Integral a => Term a -> String
drawTerm x = drawTerms x mempty

-- The path `[x, (x + x), (x + (- x)), ((- x) + (- x))]` is missing!
growTreeWrong :: forall a. a -> Natural -> Tree (Term a)
growTreeWrong a 0 = pure (Null a)
growTreeWrong a n = let n' = pred n in
  Node (Null a) [
  growTreeWrong a n' >>= \ x ->
  pure (Un a x),
  growTreeWrong a n' >>= \ x ->
  growTreeWrong a n' >>= \ y ->
  pure (Bin a x y)]

growTreeFrom :: forall a. a -> Term a -> Natural -> Tree (Term a)
growTreeFrom _ x 0 = pure x
growTreeFrom a x n = let n' = pred n in
  Node x $
  findHoles x >>= \ f ->
  [f (const (Un a (Null a))), f (const (Bin a (Null a) (Null a)))] >>= \ y ->
  pure (growTreeFrom a y n')

growTree :: forall a. a -> Natural -> Tree (Term a)
growTree a = growTreeFrom a (Null a)

growTreeRooted :: forall a. a -> Natural -> Tree (Term a)
growTreeRooted a = growTreeFrom a (Rel (Null a) (Null a))

data Names = Names {
  nameNull :: Natural,
  nameUn :: Natural,
  nameBin :: Natural}
  deriving (Eq, Ord, Show)

defNames :: Names
defNames = Names {nameNull = 0, nameUn = 0, nameBin = 0}

type Fresh = State Names

gensymNull :: Fresh Natural
gensymNull = state $ \ n -> (nameNull n, n {nameNull = succ (nameNull n)})

gensymUn :: Fresh Natural
gensymUn = state $ \ n -> (nameUn n, n {nameUn = succ (nameUn n)})

gensymBin :: Fresh Natural
gensymBin = state $ \ n -> (nameBin n, n {nameBin = succ (nameBin n)})

labelingMachine :: Term Natural -> Fresh (Term Natural)
labelingMachine (Null _) =
  gensymNull >>= \ n ->
  pure (Null n)
labelingMachine (Un _ x) =
  gensymUn >>= \ n ->
  labelingMachine x >>= \ a ->
  pure (Un n a)
labelingMachine (Bin _ x y) =
  gensymBin >>= \ n ->
  labelingMachine x >>= \ a ->
  labelingMachine y >>= \ b ->
  pure (Bin n a b)
labelingMachine (Rel x y) =
  labelingMachine x >>= \ a ->
  labelingMachine y >>= \ b ->
  pure (Rel a b)

label :: Term Natural -> Term Natural
label x = evalState (labelingMachine x) defNames

type Assign a = ((Node, Map a Node), Gr a ())
--                ^ Node number to be assigned to the next unforeseen term.
--                      ^ Terms seen so far with their assigned node numbers.
--                                   ^ Graph built up to this point.

cseMachine :: forall a. Ord a =>
  Tree a -> State (Assign a) Node
--                           ^ Node number of the root term.
cseMachine (Node a xs) =
  traverse cseMachine xs >>= \ ks ->
  get >>= \ ((n, m), g) ->
  case Map.lookup a m of
    Nothing ->
      put ((succ n, Map.insert a n m),
        (insEdges (fmap (\ k -> toLEdge (n, k) ()) ks) . insNode (n, a))
        g) >>= \ () ->
      pure n
    Just i -> pure i

defAssign :: Assign (Term Natural)
defAssign = ((0, mempty), Graph.empty)

cse :: Tree (Term Natural) -> Gr (Term Natural) ()
cse x = snd (execState (cseMachine x) defAssign)

main :: IO ()
main = let
  n :: Natural
  n = 3
  t :: Tree (Term Natural)
  t = growTree 0 n
  t' :: Maybe (Tree (Term Natural))
  t' = treeTakeWhile (\ x -> termSize x <= n) (growTree 0 1e+3) in do
  if t' == Just t then
    putStrLn "Growth matches measure!" else
    putStrLn "Growth does not match measure!"
  putStr . compactDrawTree . fmap (show . termSize) $ t
  putStr . compactDrawTree . fmap drawTerm $ fmap label t
  preview . nmap drawTermIxed $ cse (fmap label t)
