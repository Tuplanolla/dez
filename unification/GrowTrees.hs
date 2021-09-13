{-# LANGUAGE ImportQualifiedPost, NumDecimals, RankNTypes #-}

-- stack ghci --package containers --package mtl --package fgl --package graphviz --package text -- GrowTrees.hs

module GrowTrees where

import Control.Applicative
import Control.Monad.State
import Data.Char
import Data.Foldable
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

instance Labellable () where
  toLabelValue () = toLabelValue ""

printPreview :: (Labellable a, Labellable b, Ord b, Graph gr) =>
  gr a b -> String
printPreview g = let
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

data Term =
  Null Natural |
  Un Natural Term |
  Bin Natural Term Term
  deriving (Eq, Ord, Show)

termSize :: Term -> Natural
termSize (Null n) = 0
termSize (Un n x) = succ (termSize x)
termSize (Bin n x y) = succ (termSize x + termSize y)

fillHoles :: (Natural -> Term) -> Term -> [Term]
fillHoles f (Null n) = pure (f n)
fillHoles f (Un n x) = fmap (Un n) (fillHoles f x)
fillHoles f (Bin n x y) =
  liftA2 (Bin n) (pure x) (fillHoles f y) <>
  liftA2 (Bin n) (fillHoles f x) (pure y)

findHoles :: Term -> [Term -> Term]
findHoles (Null n) = pure id
findHoles (Un n x) = fmap (fmap (Un n)) (findHoles x)
findHoles (Bin n x y) =
  (liftA2 . liftA2) (Bin n) ((pure . pure) x) (findHoles y) <>
  (liftA2 . liftA2) (Bin n) (findHoles x) ((pure . pure) y)

subscript :: Char -> Char
subscript x
  | ord '0' <= ord x && ord x <= ord '9' =
    chr ((ord '\8320' - ord '0') + ord x)
  | otherwise = x

showSubscript :: forall a. Integral a => a -> ShowS
showSubscript n = showString (fmap subscript (showInt n mempty))

drawTermsIxed :: Term -> ShowS
drawTermsIxed (Null n) = showString "x" . showSubscript n
drawTermsIxed (Un n x) = showString "(\172" . showSubscript n . showString " " .
  drawTermsIxed x . showString ")"
drawTermsIxed (Bin n x y) = showString "(" .
  drawTermsIxed x . showString " \8743" . showSubscript n . showString " " .
  drawTermsIxed y . showString ")"

drawTermIxed :: Term -> String
drawTermIxed x = drawTermsIxed x mempty

drawTerms :: Term -> ShowS
drawTerms (Null n) = showString "x"
drawTerms (Un n x) = showString "(\172 " .
  drawTerms x . showString ")"
drawTerms (Bin n x y) = showString "(" .
  drawTerms x . showString " \8743 " .
  drawTerms y . showString ")"

drawTerm :: Term -> String
drawTerm x = drawTerms x mempty

-- The path `[x, (x + x), (x + (- x)), ((- x) + (- x))]` is missing!
growTreeWrong :: Natural -> Tree Term
growTreeWrong 0 = pure (Null 0)
growTreeWrong n = let n' = pred n in
  Node (Null 0) [
  growTreeWrong n' >>= \ x ->
  pure (Un 0 x),
  growTreeWrong n' >>= \ x ->
  growTreeWrong n' >>= \ y ->
  pure (Bin 0 x y)]

-- Remove `f (Un (Null 0))` to generate associahedral trees.
growTreeFrom :: Term -> Natural -> Tree Term
growTreeFrom x 0 = pure x
growTreeFrom x n = let n' = pred n in
  Node x $
  findHoles x >>= \ f ->
  [f (Un 0 (Null 0)), f (Bin 0 (Null 0) (Null 0))] >>= \ y ->
  pure (growTreeFrom y n')

growTree :: Natural -> Tree Term
growTree = growTreeFrom (Null 0)

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

labelingMachine :: Term -> Fresh Term
labelingMachine (Null _) =
  gensymNull >>= \ n ->
  pure (Null n)
labelingMachine (Un n x) =
  gensymUn >>= \ n ->
  labelingMachine x >>= \ a ->
  pure (Un n a)
labelingMachine (Bin n x y) =
  gensymBin >>= \ n ->
  labelingMachine x >>= \ a ->
  labelingMachine y >>= \ b ->
  pure (Bin n a b)

label :: Term -> Term
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

defAssign :: Assign Term
defAssign = ((0, mempty), Graph.empty)

cse :: Tree Term -> Gr Term ()
cse x = snd (execState (cseMachine x) defAssign)

main :: IO ()
main = do
  let n = 3
  let t = growTree n
  let t' = treeTakeWhile (\ x -> termSize x <= n) (growTree 1e+3)
  if t' == Just t then
    putStrLn "Growth matches measure!" else
    putStrLn "Growth does not match measure!"
  putStr . compactDrawTree . fmap (show . termSize) $ t
  putStr . compactDrawTree . fmap drawTerm $ fmap label t
  preview . nmap drawTerm $ cse (fmap label t)
