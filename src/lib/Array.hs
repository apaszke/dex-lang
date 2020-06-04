-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

module Array (
  BaseType (..), LitVal (..), ArrayType, Array (..), ArrayRef (..),
  Vec (..), scalarFromArray, arrayFromScalar,
  loadArray, storeArray, sizeOf, arrayType, unsafeWithArrayPointer) where

import Control.Monad
import Control.Monad.Primitive (PrimState)
import qualified Data.Vector.Storable as V
import Foreign.Marshal.Array
import Foreign.Ptr
import Foreign.Storable  hiding (sizeOf)
import GHC.Generics

data Array    = Array    Vec                 deriving (Show, Eq, Generic)
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

type ArrayType = (Int, BaseType)

arrayType :: Array -> ArrayType
arrayType (Array (IntVec v))    = (V.length v, IntType)
arrayType (Array (DoubleVec v)) = (V.length v, RealType)

sizeOf :: BaseType -> Int
sizeOf _ = 8

scalarFromArray :: Array -> Maybe LitVal
scalarFromArray arr@(Array vec) = case size of
    1 -> Just $ case b of
      IntType  -> IntLit  $ xs V.! 0       where IntVec    xs = vec
      BoolType -> BoolLit $ xs V.! 0 /= 0  where IntVec    xs = vec
      RealType -> RealLit $ xs V.! 0       where DoubleVec xs = vec
      _ -> error "Not implemented"
    _ -> Nothing
  where
    (size, b) = arrayType arr

arrayFromScalar :: LitVal -> Array
arrayFromScalar val = case val of
  IntLit  x -> Array $ IntVec $ V.fromList [x]
  BoolLit x -> Array $ IntVec $ V.fromList [x']
    where x' = case x of False -> 0
                         True  -> 1
  RealLit x -> Array $ DoubleVec $ V.fromList [x]
  _ -> error "Not implemented"

loadArray :: ArrayRef -> IO Array
loadArray (ArrayRef (size, b) ptr) = Array <$> case b of
  IntType  -> liftM IntVec    $ peekVec size $ castPtr ptr
  BoolType -> liftM IntVec    $ peekVec size $ castPtr ptr
  RealType -> liftM DoubleVec $ peekVec size $ castPtr ptr
  _ -> error "Not implemented"

storeArray :: ArrayRef -> Array -> IO ()
storeArray (ArrayRef _ ptr) (Array vec) = case vec of
  IntVec    v -> pokeVec (castPtr ptr) v
  DoubleVec v -> pokeVec (castPtr ptr) v

peekVec :: Storable a => Int -> Ptr a -> IO (V.Vector a)
peekVec size ptr = V.generateM size $ \i -> peek (ptr `advancePtr` i)

pokeVec :: Storable a => Ptr a -> V.Vector a -> IO ()
pokeVec ptr v = forM_ [0..(V.length v - 1)] $ \i -> do
  x <- V.indexM v i
  poke (ptr `advancePtr` i) x

unsafeWithArrayPointer :: Array -> (Ptr () -> IO a) -> IO a
unsafeWithArrayPointer (Array vec) f = case vec of
  IntVec v    -> V.unsafeWith v (f . castPtr)
  DoubleVec v -> V.unsafeWith v (f . castPtr)

