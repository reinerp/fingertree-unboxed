{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, FlexibleInstances, TypeFamilies, FlexibleContexts, TypeSynonymInstances #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Sequence where

import Data.Monoid
import Data.FingerTree.Unboxed as F
import Data.Unboxed

newtype Size = Size { unSize :: Int }
newtype Elem a = Elem { unElem :: a }
newtype Seq a = Seq { unSeq :: FingerTree Size (Elem a) }

instance Monoid Size where
    {-# INLINE mappend #-}
    mappend (Size a) (Size b) = Size (a + b)
    {-# INLINE mempty #-}
    mempty = Size 0

instance Measured Size (Elem a) where
    {-# INLINE measure #-}
    measure _ = Size 1

$(F.defineFingerTree [t| Size |])
instance F.Unpacked1 (Node Size) where
    {-# INLINE mk1 #-}
    mk1 = mk
    {-# INLINE unMk1 #-}
    unMk1 = unMk
instance F.Unpacked1 (FingerTree Size) where
    {-# INLINE mk1 #-}
    mk1 = mk
    {-# INLINE unMk1 #-}
    unMk1 = unMk
instance F.Unbox Size


empty :: Seq a
empty = Seq F.empty

singleton :: a -> Seq a
singleton = Seq . F.singleton . Elem

(<|) :: a -> Seq a -> Seq a
el <| (Seq a) = Seq (Elem el F.<| a)

(><) :: Seq a -> Seq a -> Seq a
(Seq l) >< (Seq r) = Seq (l F.>< r)

(|>) :: Seq a -> a -> Seq a
(Seq a) |> el = Seq (a F.|> Elem el)

--null :: Seq a -> Bool
--null (Seq a) = F.null a

viewl :: Seq a -> ViewL Seq a
viewl (Seq a) = case F.viewl a of
    EmptyL -> EmptyL
    Elem h :< t -> h :< Seq t

length :: Seq a -> Int
length (Seq a) = unSize (F.measure a)

split :: Int -> Seq a -> (Seq a, Seq a)
split n (Seq a) = n `seq` case F.split (\(Size s) -> s>n) a of (l, r) -> (Seq l, Seq r)
