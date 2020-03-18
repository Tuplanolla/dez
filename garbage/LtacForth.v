r :: Eq a => a -> ([a] -> [[a]] -> [[a]]) -> [a] -> [[a]]
r c k [] = k [] []
r c k (x : xs) = if x == c then
  r c (\ ys zs -> k [] (ys : zs)) xs else
  r c (\ ys zs -> k (x : ys) zs) xs

f, ff :: Eq a => a -> a -> [a] -> [[[a]]]
-- Fuse this by hand...
f c d = fmap (r d (:)) . r c (:)
-- ...to get this.
ff c d ws = let
  r k [] = k [] []
  r k (x : xs) = if x == c then
    r (\ ys zs -> k [] (let
      fr k [] = k [] []
      fr k (x : xs) = if x == d then
        fr (\ ys zs -> k [] (ys : zs)) xs else
        fr (\ ys zs -> k (x : ys) zs) xs in
      fr (:) ys : zs)) xs else
        r (\ ys zs -> k (x : ys) zs) xs in
  r (\ ys zs -> let
      fr k [] = k [] []
      fr k (x : xs) = if x == d then
        fr (\ ys zs -> k [] (ys : zs)) xs else
        fr (\ ys zs -> k (x : ys) zs) xs in
      fr (:) ys : zs) ws

-- These are on the house.

c :: Char
c = 'o'

d :: Char
d = 'a'

xs :: [Char]
xs = "PaQoRaSaToU"
