{-# LANGUAGE TypeOperators #-}

module Quickhull
    ( quickhull
    , Point
    , propagateR
    , segmentedPostscanr
    ) where

import Data.Array.Accelerate
import qualified Data.Array.Accelerate.Unsafe as Unsafe
import qualified Prelude as P

-- Accelerate backend
import Data.Array.Accelerate.Interpreter
-- import Data.Array.Accelerate.LLVM.Native
-- import Data.Array.Accelerate.LLVM.PTX

type Point = (Int, Int)

type Line = (Point, Point)

type SegmentedPoints = (Vector Bool, Vector Point)

input1 :: Acc (Vector Point)
input1 = use $ fromList (Z :. 15) [(1,4),(8,19),(5,9),(7,9),(4,2),(3,9),(9,16),(1,5),(9,11),(4,0),(8,18),(8,7),(7,18),(6,18),(4,19)]

pointIsLeftOfLine :: Exp Line -> Exp Point -> Exp Bool
pointIsLeftOfLine (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y > c
  where
    nx = y1 - y2
    ny = x2 - x1
    c = nx * x1 + ny * y1

nonNormalizedDistance :: Exp Line -> Exp Point -> Exp Int
nonNormalizedDistance (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y - c
  where
    nx = y1 - y2
    ny = x2 - x1
    c = nx * x1 + ny * y1

-- * Exercise 1
leftMostPoint :: Acc (Vector Point) -> Acc (Scalar Point)
leftMostPoint = fold min (T2 maxBound maxBound)

rightMostPoint :: Acc (Vector Point) -> Acc (Scalar Point)
rightMostPoint = fold max (T2 minBound minBound)

initialPartition :: Acc (Vector Point) -> Acc SegmentedPoints
initialPartition points =
  let
    p1 = the $ leftMostPoint points
    p2 = the $ rightMostPoint points
    line = T2 p1 p2

    -- * Exercise 2
    isUpper :: Acc (Vector Bool)
    isUpper = map (pointIsLeftOfLine line) points

    isLower :: Acc (Vector Bool)
    isLower = zipWith (\p pU -> cond (p == p1 || p == p2) (lift False) $ (not pU)) points isUpper


    -- * Exercise 3
    lowerIndices :: Acc (Vector Int)
    lowerIndices = prescanl (+) 0 (map boolToInt isLower)

    -- * Exercise 4
    upperIndices :: Acc (Vector Int)
    countUpper :: Acc (Scalar Int)
    T2 upperIndices countUpper = scanl' (+) 0 (map boolToInt isUpper)

    -- * Exercise 5
    permutation :: Acc (Vector (Z :. Int))
    permutation =
      let
        f :: Exp Point -> Exp Bool -> Exp Int -> Exp Int -> Exp (Z :. Int)
        f p upper idxLower idxUpper
          = cond (p == p1) (index1 0) $
            cond (p == p2) (index1 $ 1 + the countUpper) $
            cond (upper)   (index1 $ 1 + idxUpper) $
            (index1 $ 1 + the countUpper + 1 + idxLower)
      in
        zipWith4 f points isUpper lowerIndices upperIndices

    -- * Exercise 6
    empty :: Acc (Vector Point)
    empty = fill (index1 ((unindex1 (shape points)) + 1)) p1

    newPoints :: Acc (Vector Point)
    newPoints = permute const empty (permutation !) points

    -- * Exercise 7
    headFlags :: Acc (Vector Bool)
    headFlags = map (\p -> cond (p == p1 || p == p2) (lift True) $ (lift False)) newPoints
  in
    T2 headFlags newPoints

-- * Exercise 8
segmentedPostscanl :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedPostscanl f headFlags newPoints = map snd tupleResult
  where tupleResult = postscanl (\x y -> segmented x y) Unsafe.undef zippedList
        zippedList = zip headFlags newPoints
        segmented (T2 fx x) (T2 fy y) = T2 (fx || fy) (fy ? (y, f x y))

segmentedPostscanr :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedPostscanr f headFlags newPoints = map snd tupleResult
  where tupleResult = postscanr (\x y -> segmented x y) Unsafe.undef zippedList 
        zippedList = zip headFlags newPoints
        segmented (T2 fx x) (T2 fy y) = T2 (fx || fy) (fx ? (x, f x y))

-- * Exercise 9
propagateL :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateL = segmentedPostscanl const

propagateR :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateR = segmentedPostscanr (P.flip const)

-- * Exercise 10
propagateLine :: Acc SegmentedPoints -> Acc (Vector Line)
propagateLine (T2 headFlags points) = zip vecP1 vecP2
  where
    vecP1 = propagateL headFlags points
    vecP2 = propagateR headFlags points

-- * Exercise 11
shiftHeadFlagsL :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsL flags = generate (index1 lengthFlag) (\i -> getVal $ unindex1 i)
  where
    lengthFlag = unindex1 (shape flags)
    getVal i = cond (i == lengthFlag - 1) (lift False) $ flags !! (i + 1)
    
shiftHeadFlagsR :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsR flags = generate (index1 lengthFlag) (\i -> getVal $ unindex1 i)
  where
    lengthFlag = unindex1 (shape flags)
    getVal i = cond (i == 0) (lift False) $ flags !! (i - 1)

partition :: Acc SegmentedPoints -> Acc SegmentedPoints
partition (T2 headFlags points) =
  let
    vecLine :: Acc (Vector Line)
    vecLine = propagateLine (T2 headFlags points)

    headFlagsL = shiftHeadFlagsL headFlags
    headFlagsR = shiftHeadFlagsR headFlags

    -- * Exercise 12
    furthest :: Acc (Vector Point)
    furthest = propagateR headFlagsL $ map snd $ segmentedPostscanl max headFlagsR pointList
      where
        pointList :: Acc (Vector (Int, Point)) 
        pointList = zipWith (\line point -> T2 (nonNormalizedDistance line point) point) vecLine points

    -- * Exercise 13
    isLeft :: Acc (Vector Bool)
    isLeft = zipWith3 (\(T2 p1 p2) pf point -> pointIsLeftOfLine (T2 p1 pf) point) vecLine furthest points

    isRight :: Acc (Vector Bool)
    isRight = zipWith3 (\(T2 p1 p2) pf point -> pointIsLeftOfLine (T2 pf p2) point) vecLine furthest points

    -- * Exercise 14
    segmentIdxLeft :: Acc (Vector Int)
    segmentIdxLeft = segmentedPostscanl (+) headFlags (map boolToInt isLeft)

    segmentIdxRight :: Acc (Vector Int)
    segmentIdxRight = segmentedPostscanl (+) headFlags (map boolToInt isRight)

    -- * Exercise 15
    countLeft :: Acc (Vector Int)
    countLeft = propagateR headFlagsL segmentIdxLeft

    -- * Exercise 16
    segmentSize :: Acc (Vector Int)
    segmentSize = zipWith4 (\flag flagl l r -> cond (flag) (1) $ cond (flagl) (l+r+1) $ 0) headFlags headFlagsL segmentIdxLeft segmentIdxRight

    segmentOffset :: Acc (Vector Int)
    size :: Acc (Scalar Int)
    T2 segmentOffset size = scanl' (+) 0 segmentSize

    -- * Exercise 17
    permutation :: Acc (Vector (Z :. Int))
    permutation =
      let
        f :: Exp Bool -> Exp Point -> Exp Point -> Exp Bool -> Exp Bool -> Exp Int -> Exp Int -> Exp Int -> Exp Int -> Exp (Z :. Int)
        f flag p furthestP left right offset cntLeft idxLeft idxRight
          = cond (flag)           (index1 offset) $
            cond (p == furthestP) (index1 $ offset + cntLeft) $ 
            cond (left)           (index1 $ offset + idxLeft - 1) $
            cond (right)          (index1 $ offset + cntLeft  + idxRight) $
            ignore
      in
        zipWith9 f headFlags points furthest isLeft isRight segmentOffset countLeft segmentIdxLeft segmentIdxRight

    -- * Exercise 18
    empty :: Acc (Vector Point)
    empty = fill (index1 (the size)) (T2 0 0)

    newPoints :: Acc (Vector Point)
    newPoints = permute const empty (permutation !) points

    -- * Exercise 19
    newHeadFlags :: Acc (Vector Bool)
    newHeadFlags = zipWith3 f newPoints perFlag perFur
      where
        perFlag = permute const emptyflag (permutation !) headFlags
        perFur = permute const empty (permutation !) furthest
        f p flag fur = cond (flag || p == fur) (lift True) $ (lift False)
        emptyflag = fill (shape empty) (lift False)
  in
    T2 newHeadFlags newPoints

-- * Exercise 20
condition :: Acc SegmentedPoints -> Acc (Scalar Bool)
condition (T2 flags _) = map not (and flags)

-- * Exercise 21
quickhull' :: Acc (Vector Point) -> Acc (Vector Point)
quickhull' p = asnd (awhile condition partition (initialPartition p))

quickhull :: Vector Point -> Vector Point
quickhull = run1 quickhull'

-- * Bonus
quickhullSort' :: Acc (Vector Int) -> Acc (Vector Int)
quickhullSort' = undefined

quickhullSort :: Vector Int -> Vector Int
quickhullSort = run1 quickhullSort'
