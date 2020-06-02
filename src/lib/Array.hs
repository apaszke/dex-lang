-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

module Array (
  BaseType (..), LitVal (..), ArrayType, Array (..), ArrayRef (..),
  Vec (..), DimType (..), subArray, scalarFromArray, arrayFromScalar,
  loadArray, storeArray, newArrayRef, storeArrayNew, sizeOf, elemCount) where

import Control.Monad
import Control.Monad.Primitive (PrimState)
import Data.Text.Prettyprint.Doc
import qualified Data.Vector.Unboxed as V
import Foreign.Marshal.Alloc
import Foreign.Marshal.Array
import Foreign.Ptr
import Foreign.Storable  hiding (sizeOf)
import GHC.Generics

data Array    = Array    ArrayType Vec     deriving (Show, Eq, Generic)
data ArrayRef = ArrayRef ArrayType (Ptr ())  deriving (Show, Eq, Generic)

data LitVal = IntLit  Int
            | RealLit Double
            | BoolLit Bool
            | StrLit  String
              deriving (Show, Eq, Generic)

data Vec = IntVec    (V.Vector Int)
         | DoubleVec (V.Vector Double)
           deriving (Show, Eq, Generic)

data VecRef = IntVecRef    (V.MVector (PrimState IO) Int)
            | DoubleVecRef (V.MVector (PrimState IO) Double)
              deriving (Generic)

data BaseType = IntType | BoolType | RealType | StrType
                deriving (Show, Eq, Generic)

-- NOTE: The precomputed array of strides has n+1 elements for a dimension of size n!
-- NOTE: Strides are in elements, not in bytes
data DimType = Uniform Int
             | Precomputed (V.Vector Int)
           deriving (Show, Eq, Generic)
type ArrayType = ([DimType], BaseType)

offsetTo :: [DimType] -> Int -> Int
offsetTo (d:td) i = case d of
  Uniform _       -> i * elemCount td
  Precomputed vec -> vec V.! i
offsetTo [] 0 = 0
offsetTo [] _ = error "Non-zero index used on a scalar array"

sizeAt :: [DimType] -> Int -> Int
sizeAt (d:td) i = case d of
  Uniform _       -> elemCount td
  Precomputed vec -> vec V.! (i+1) - vec V.! i
sizeAt [] _ = error "Can't index into a scalar array"

elemCount :: [DimType] -> Int
elemCount (d:td) = case d of
  Uniform sz      -> sz * elemCount td
  Precomputed vec -> V.last vec
elemCount [] = 1

sizeOf :: BaseType -> Int
sizeOf _ = 8

subArray :: Int -> Array -> Array
subArray i (Array (dims@(_:_), b) vec) = Array (tail dims, b) vec'
  where offset = dims `offsetTo` i
        size   = dims `sizeAt` i
        vec'   = case vec of
                 IntVec    xs -> IntVec    $ V.slice offset size xs
                 DoubleVec xs -> DoubleVec $ V.slice offset size xs
subArray _ _ = error "Can't get subarray of rank-0 array"

scalarFromArray :: Array -> Maybe LitVal
scalarFromArray (Array ([], b) vec) = Just $ case b of
  IntType  -> IntLit  $ xs V.! 0       where IntVec    xs = vec
  BoolType -> BoolLit $ xs V.! 0 /= 0  where IntVec    xs = vec
  RealType -> RealLit $ xs V.! 0       where DoubleVec xs = vec
  _ -> error "Not implemented"
scalarFromArray _ = Nothing

arrayFromScalar :: LitVal -> Array
arrayFromScalar val = case val of
  IntLit  x -> Array ([], IntType ) $ IntVec $ V.fromList [x]
  BoolLit x -> Array ([], BoolType) $ IntVec $ V.fromList [x']
    where x' = case x of False -> 0
                         True  -> 1
  RealLit x -> Array ([], RealType) $ DoubleVec $ V.fromList [x]
  _ -> error "Not implemented"

loadArray :: ArrayRef -> IO Array
loadArray (ArrayRef ty@(dims,b) ptr) = liftM (Array ty) $ case b of
  IntType  -> liftM IntVec    $ peekVec size $ castPtr ptr
  BoolType -> liftM IntVec    $ peekVec size $ castPtr ptr
  RealType -> liftM DoubleVec $ peekVec size $ castPtr ptr
  _ -> error "Not implemented"
  where size = elemCount dims

storeArray :: ArrayRef -> Array -> IO ()
storeArray (ArrayRef _ ptr) (Array _ vec) = case vec of
  IntVec    v -> pokeVec (castPtr ptr) v
  DoubleVec v -> pokeVec (castPtr ptr) v

peekVec :: (V.Unbox a, Storable a) => Int -> Ptr a -> IO (V.Vector a)
peekVec size ptr = V.generateM size $ \i -> peek (ptr `advancePtr` i)

pokeVec :: (V.Unbox a, Storable a) => Ptr a -> V.Vector a -> IO ()
pokeVec ptr v = forM_ [0..(V.length v - 1)] $ \i -> do
  x <- V.indexM v i
  poke (ptr `advancePtr` i) x

-- TODO: free
newArrayRef :: ArrayType -> IO ArrayRef
newArrayRef ty@(dims, b) = do
  ptr <- mallocBytes $ elemCount dims * sizeOf b
  return $ ArrayRef ty ptr

storeArrayNew :: Array -> IO ArrayRef
storeArrayNew arr@(Array ty _) = do
  ref <- newArrayRef ty
  storeArray ref arr
  return ref

instance Pretty Array where
  pretty (Array _ _) = "<<TODO: array printing>>"
