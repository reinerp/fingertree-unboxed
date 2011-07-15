{-# LANGUAGE   MultiParamTypeClasses,
                 FunctionalDependencies,
                 FlexibleInstances,
                 UndecidableInstances,
                 TemplateHaskell,
                 TypeFamilies,
                 FlexibleContexts,
                 ViewPatterns,
                 StandaloneDeriving,
                 ScopedTypeVariables,
                 GeneralizedNewtypeDeriving,
                 TypeSynonymInstances,
                 RecordWildCards,
                 NoMonomorphismRestriction,
                 UnboxedTuples, MagicHash, BangPatterns, RankNTypes #-}

-- rules for inlining:
--   * every function should be marked INLINABLE or INLINE, to allow specialisation on the type classes
--   * functions in type classes should be marked INLINE (because INLINABLE doesn't work, I think)

-- | A copy-paste reimplementation of Ross Paterson's Data.FingerTree for which the measurement is unboxed.
module Data.FingerTree.Unboxed (
	FingerTree,
        MaybeGroup(..),
	Measured(..),
	-- * Construction
	empty, singleton,
	(<|), (|>), (><),
--	fromList,
	-- * Deconstruction
--	null,
	ViewL(..), ViewR(..), viewl, viewr,
	split, SplitPred(..), -- takeUntil, dropUntil,
	-- * Transformation
--	reverse,
--	fmap', fmapWithPos, unsafeFmap,
--	traverse', traverseWithPos, unsafeTraverse,
        -- * Template Haskell
        defineFingerTree,
--        Elem(..),
        Node(..),
--        FingerTree',
        Polymorphic(..),
        Unbox,
        Unpacked1(..),
        dict, BigDict,
	) where

import Prelude hiding (null, reverse)

import Data.Unboxed.Derive
import Control.Applicative (Applicative(pure, (<*>)), (<$>))
import Data.Monoid
import Data.Foldable (Foldable(foldMap), toList)
import Data.Traversable (Traversable(traverse))
import qualified Language.Haskell.TH as TH
import Control.Monad(liftM2)
import GHC.Magic(inline)

data Digit a
	= One a
	| Two a a
	| Three a a a
	| Four a a a a
	deriving Show

-----------------------------------------------------------------------------------------------
-- Template Haskell part
-----------------------------------------------------------------------------------------------

$(declareType "defineNode_" [d| data Node v a = Node2 !v a a | Node3 !v a a a |])
-- | Finger trees with element type @a@, annotated with measures of type @v@.
-- The operations enforce the constraint @'Measured' v a@.
$(declareType "defineFingerTree_" 
   [d| data FingerTree v a
	= Empty
	| Single a
	| Deep !v !(Digit a) (FingerTree v (Node v a)) !(Digit a)
    |])

defineFingerTree :: TH.Q TH.Type -> TH.Q [TH.Dec]
defineFingerTree sizeTy = do
    t <- sizeTy
    nm <- TH.newName "a"
    let nodeTy = return $ TH.AppT (TH.AppT (TH.ConT ''Node) t) (TH.VarT nm)
        treeTy = return $ TH.AppT (TH.AppT (TH.ConT ''FingerTree) t) (TH.VarT nm)
    liftM2 (++) (defineNode_ nodeTy) (defineFingerTree_ treeTy)


--infixr 5 ><
infixr 5 <|, :<
--infixl 5 |>, :>

class Unpacked1 f where
    -- {-# INLINE mk1 #-}
    mk1 :: Polymorphic (f a) -> f a
    -- {-# INLINE unMk1 #-}
    unMk1 :: f a -> Polymorphic (f a)
class (Unpacked1 (Node v), Unpacked1 (FingerTree v)) => Unbox v

deriving instance (Show v, Show a) => Show (Polymorphic (Node v a))



----------------------------------------------------------------------------------------------------
--                                                   Types                                        --
----------------------------------------------------------------------------------------------------
-- | View of the left end of a sequence.
data ViewL s a
	= EmptyL 	-- ^ empty sequence
	| a :< s a	-- ^ leftmost element and the rest of the sequence
	deriving (Eq, Ord, Show, Read)

-- | View of the right end of a sequence.
data ViewR s a
	= EmptyR	-- ^ empty sequence
	| s a :> a	-- ^ the sequence minus the rightmost element,
			-- and the rightmost element
	deriving (Eq, Ord, Show, Read)

instance Functor s => Functor (ViewL s) where
	fmap f EmptyL           = EmptyL
	fmap f (x :< xs)        = f x :< fmap f xs

instance Functor s => Functor (ViewR s) where
	fmap f EmptyR           = EmptyR
	fmap f (xs :> x)        = fmap f xs :> f x


{-
instance (Unbox v, Measured v a) => Measured v (FingerTree v a) where
        measure f = case unMk1 f of
            Empty -> mempty
            Single x -> measure x
            Deep v _ _ _ -> v
        {-# INLINABLE measure #-}
--        {-# INLINE measure #-}
-}

instance Unbox v => Foldable (FingerTree v) where
        {-# INLINE foldMap #-}
--        {-# INLINABLE foldMap #-}
        foldMap f t = case unMk1 t of
            Empty -> mempty
            Single x -> f x
            Deep _ pr m sf -> 
               foldMap f pr `mappend` foldMap (foldMap f) m `mappend` foldMap f sf

instance (Unbox v, Measured v a, Eq a) => Eq (FingerTree v a) where
        {-# INLINE (==) #-}
	xs == ys = toList xs == toList ys

instance (Unbox v, Measured v a, Ord a) => Ord (FingerTree v a) where
        {-# INLINE compare #-}
	compare xs ys = compare (toList xs) (toList ys)

instance (Unbox v, Measured v a, Show a) => Show (FingerTree v a) where
        {-# INLINE showsPrec #-}
	showsPrec p xs = showParen (p > 10) $
		showString "fromList " . shows (toList xs)

--data Split t a = Split t a t
type Split t a = (# t, a, t #)
mkSplit :: t -> a -> t -> Split t a
mkSplit a b c = (# a, b, c #)
  
----------------------------------------------------------------------------------------------------
--                                         Some cheap typeclasses                                 --
----------------------------------------------------------------------------------------------------
instance Foldable Digit where
	foldMap f (One a) = f a
	foldMap f (Two a b) = f a `mappend` f b
	foldMap f (Three a b c) = f a `mappend` f b `mappend` f c
	foldMap f (Four a b c d) = f a `mappend` f b `mappend` f c `mappend` f d
        {-# INLINE foldMap #-}
--        {-# INLINABLE foldMap #-}


instance Unbox v => Foldable (Node v) where
        foldMap f node = case unMk1 node of
           Node2 _ a b -> f a `mappend` f b
           Node3 _ a b c -> f a `mappend` f b `mappend` f c
--        {-# INLINABLE foldMap #-}
        {-# INLINE foldMap #-}

class Monoid v => MaybeGroup v where
    -- | If subtract is supported:
    --
    -- > trySubtract a b c = a - b
    --
    -- otherwise:
    --
    -- > trySubtract a b c = c
    trySubtract :: v -> v -> v -> v

-- | Things that can be measured.
class (MaybeGroup v) => Measured v a | a -> v where
	measure :: a -> v

{-
instance Measured v a => Measured v (Digit a) where
    measure (One a) = measure a
    measure (Two a b) = measure a `mappend`
    {-# INLINABLE measure #-}
--    {-# INLINE measure #-}
-}

instance (MaybeGroup v, Unbox v) => Measured v (Node v a) where
    measure node = case unMk1 node of
        Node2 v _ _ -> v
        Node3 v _ _ _ -> v
    {-# INLINABLE measure #-}
--    {-# INLINE measure #-}

----------------------------------------------------------------------------------------------------
--                                         A big 'let' declaration                                --
----------------------------------------------------------------------------------------------------

data BigDict v a =
  BigDict{
     emptyD :: FingerTree v a,
     singletonD :: a -> FingerTree v a,
     consD :: a -> FingerTree v a -> FingerTree v a,
     snocD :: FingerTree v a -> a -> FingerTree v a,
     viewlD :: FingerTree v a -> ViewL (FingerTree v) a,
     viewrD :: FingerTree v a -> ViewR (FingerTree v) a,
     appendD :: FingerTree v a -> FingerTree v a -> FingerTree v a,
     splitD :: forall d. SplitPred d v => d -> FingerTree v a -> (FingerTree v a, a, FingerTree v a)
    }

class SplitPred d v | d -> v where
  checkPred :: d -> v -> Bool
  -- incrPred :: d -> v -> d

newtype MeasuredD v a = MeasuredD { measureD :: a -> v}

{-# INLINABLE empty #-}
empty :: Unbox v => FingerTree v a
empty = mk1 Empty

{-# INLINABLE singleton #-}
singleton :: Unbox v => a -> FingerTree v a
singleton a = mk1 (Single a)

--{-# INLINE empty #-}
--empty = emptyD dict
-- {-# INLINABLE singleton #-}
--singleton = singletonD dict

{-# INLINABLE (<|) #-}
(<|) = consD dict
{-# INLINABLE (|>) #-}
(|>) = snocD dict
{-# INLINABLE (><) #-}
(><) = appendD dict
{-# INLINABLE viewr #-}
viewr = viewrD dict
{-# INLINABLE viewl #-}
viewl = viewlD dict
{-# INLINE split #-}
split = splitD dict

-- this dictionary gives us scoped type variables!
{-# INLINE dict #-}
dict :: forall v a. (Unbox v, Measured v a) => BigDict v a
dict = BigDict{..} where
  ------------------------------------------------------------------------------------------
  --                                         Smart constructors                           --
  ------------------------------------------------------------------------------------------
  node2        ::  forall b. Measured v b => b -> b -> Node v b
  node2 a b    =   mk1 $ Node2 (myMeasure a `mappend` myMeasure b) a b
  {-# SPECIALISE node2 :: a -> a -> Node v a #-}
  {-# SPECIALISE node2 :: Node v b -> Node v b -> Node v (Node v b) #-}

  node3        ::  forall b. Measured v b => b -> b -> b -> Node v b
  node3 a b c  =   mk1 $ Node3 (myMeasure a `mappend` myMeasure b `mappend` myMeasure c) a b c
  {-# SPECIALISE node3 :: a -> a -> a -> Node v a #-}
  {-# SPECIALISE node3 :: Node v b -> Node v b -> Node v b -> Node v (Node v b) #-}

  nodeToDigit :: forall b. Node v b -> Digit b
  nodeToDigit node = case unMk1 node of
    Node2 _ a b -> Two a b
    Node3 _ a b c -> Three a b c

  myMeasure :: forall b. Measured v b => b -> v
  myMeasure a = {- inline -} measure a
  {-# SPECIALISE myMeasure :: a -> v #-}
  {-# SPECIALISE myMeasure :: Node v b -> v #-}

  measureDigit :: forall b. Measured v b => Digit b -> v
  measureDigit (One a) = myMeasure a
  measureDigit (Two a b) = myMeasure a `mappend` myMeasure b
  measureDigit (Three a b c) = myMeasure a `mappend` myMeasure b `mappend` myMeasure c
  measureDigit (Four a b c d) = myMeasure a `mappend` myMeasure b `mappend` myMeasure c `mappend` myMeasure d
  {-# SPECIALISE measureDigit :: Digit a -> v #-}
  {-# SPECIALISE measureDigit :: Digit (Node v b) -> v = measureDigit' #-}

  {-# NOINLINE myMeasure' #-}
  myMeasure' :: forall b. Measured v b => b -> v
  myMeasure' a = myMeasure a

  measureDigit' :: forall b. Digit (Node v b) -> v
  measureDigit' (One a) = myMeasure' a
  measureDigit' (Two a b) = myMeasure' a `mappend` myMeasure' b
  measureDigit' (Three a b c) = myMeasure' a `mappend` myMeasure' b `mappend` myMeasure' c
  measureDigit' (Four a b c d) = myMeasure' a `mappend` myMeasure' b `mappend` myMeasure' c `mappend` myMeasure' d


  measureTree :: forall b. Measured v b => FingerTree v b -> v
  measureTree t = case unMk1 t of
     Empty -> mempty
     Single x -> myMeasure x
     Deep v _ _ _ -> v
  {-# SPECIALISE measureTree :: FingerTree v a -> v #-}
  {-# SPECIALISE measureTree :: FingerTree v (Node v b) -> v #-}

  deep ::  forall b. Measured v b => Digit b -> FingerTree v (Node v b) -> Digit b -> FingerTree v b
  deep pr m sf = mk1 $ Deep ((measureDigit pr `mappendVal` m) `mappend` measureDigit sf) pr m sf
  {-# SPECIALISE deep :: Digit a -> FingerTree v (Node v a) -> Digit a -> FingerTree v a #-}
  {-# SPECIALISE deep :: Digit (Node v c) -> FingerTree v (Node v (Node v c)) -> Digit (Node v c) -> FingerTree v (Node v c) #-}

  empty' :: forall b. FingerTree v b
  empty' = mk1 Empty

  mappendVal :: forall b. Measured v b => v -> FingerTree v b -> v
  mappendVal v t = v `seq` case unMk1 t of
      Empty -> v
      _ -> v `mappend` measureTree t
--  {-# SPECIALISE mappendVal :: v -> FingerTree v a -> v #-}
--  {-# SPECIALISE mappendVal :: v -> FingerTree v (Node v b) -> v #-}
  {-# INLINE mappendVal #-}

  ------------------------------------------------------------------------------------------
  --                                    Empty and singleton                               --
  ------------------------------------------------------------------------------------------
  -- | /O(1)/. The empty sequence.
  emptyD :: FingerTree v a
  emptyD = empty'

  -- | /O(1)/. A singleton sequence.
  singletonD :: a -> FingerTree v a
  singletonD = mk1 . Single

  ------------------------------------------------------------------------------------------
  --                                         Cons                                         --
  ------------------------------------------------------------------------------------------
  -- | /O(1)/. Add an element to the left end of a sequence.
  -- Mnemonic: a triangle with the single element at the pointy end.
  consD :: forall b. Measured v b => b -> FingerTree v b -> FingerTree v b
  consD a t = case unMk1 t of
        Empty -> mk1 $ Single a
        Single b -> deep (One a) empty' (One b)
        Deep v (Four b c d e) m sf -> m `seq`
            (mk1 $ Deep (myMeasure a `mappend` v) (Two a b) (consD (node3 c d e) m) sf)
        Deep v pr m sf -> mk1 $ Deep (myMeasure a `mappend` v) (consDigit a pr) m sf
  {-# SPECIALISE consD :: a -> FingerTree v a -> FingerTree v a #-}
  {-# SPECIALISE consD :: Node v b -> FingerTree v (Node v b) -> FingerTree v (Node v b) #-}

  consDigit :: forall b. b -> Digit b -> Digit b
  consDigit a (One b) = Two a b
  consDigit a (Two b c) = Three a b c
  consDigit a (Three b c d) = Four a b c d

  ------------------------------------------------------------------------------------------
  --                                         Snoc                                         --
  ------------------------------------------------------------------------------------------
  -- | /O(1)/. Add an element to the right end of a sequence.
  -- Mnemonic: a triangle with the single element at the pointy end.
  snocD :: forall b. Measured v b => FingerTree v b -> b -> FingerTree v b
  snocD t l = case unMk1 t of
        Empty -> mk1 $ Single l
        Single a -> deep (One a) empty' (One l)
        Deep v pr m (Four a b c d) -> m `seq`
           (mk1 $  Deep (v `mappend` myMeasure l) pr (snocD m (node3 a b c)) (Two d l))
        Deep v pr m sf -> mk1 $ Deep (v `mappend` myMeasure l) pr m (snocDigit sf l)
  {-# SPECIALISE snocD :: FingerTree v a -> a -> FingerTree v a #-}
  {-# SPECIALISE snocD :: FingerTree v (Node v b) -> Node v b -> FingerTree v (Node v b) #-}

  snocDigit :: forall b. Digit b -> b -> Digit b
  snocDigit (One a) b = Two a b
  snocDigit (Two a b) c = Three a b c
  snocDigit (Three a b c) d = Four a b c d

  ------------------------------------------------------------------------------------------
  --                                         viewl                                        --
  ------------------------------------------------------------------------------------------
  -- | /O(1)/. Analyse the left end of a sequence.
  viewlD :: forall b. Measured v b => FingerTree v b -> ViewL (FingerTree v) b
  viewlD f = case unMk1 f of
    Empty -> EmptyL
    Single x -> x :< empty'
    Deep v pr m sf -> case viewlDigit pr of
       Left x -> x :< rotL m sf
       Right (x, pr') -> x :< mk1 (Deep (trySubtract v (myMeasure x) (measureDigit pr' `mappend` measureTree m `mappend` measureDigit sf)) pr' m sf)
  {-# SPECIALISE viewlD :: FingerTree v a -> ViewL (FingerTree v) a #-}
  {-# SPECIALISE viewlD :: FingerTree v (Node v b) -> ViewL (FingerTree v) (Node v b) #-}

  rotL :: forall b. Measured v b => FingerTree v (Node v b) -> Digit b -> FingerTree v b
  rotL m sf      =   case viewlD m of
	EmptyL  ->  digitToTree sf
	node :< m' ->  case unMk1 node of
            Node2 _ a b -> mk1 $ Deep (measureTree m `mappend` measureDigit sf) (Two a b) m' sf
            Node3 _ a b c -> mk1 $ Deep (measureTree m `mappend` measureDigit sf) (Three a b c) m' sf
  {-# SPECIALISE NOINLINE rotL :: FingerTree v (Node v a) -> Digit a -> FingerTree v a #-}
  {-# SPECIALISE NOINLINE rotL :: FingerTree v (Node v (Node v b)) -> Digit (Node v b) -> FingerTree v (Node v b) #-}

  viewlDigit :: forall b. Digit b -> Either b (b, Digit b)
  viewlDigit (One a) = Left a
  viewlDigit (Two a b) = Right (a, One b)
  viewlDigit (Three a b c) = Right (a, Two b c)
  viewlDigit (Four a b c d) = Right (a, Three b c d)

  digitToTree :: forall b. (Measured v b) => Digit b -> FingerTree v b
  digitToTree (One a) = mk1 $ Single a
  digitToTree (Two a b) = deep (One a) empty' (One b)
  digitToTree (Three a b c) = deep (Two a b) empty' (One c)
  digitToTree (Four a b c d) = deep (Two a b) empty' (Two c d)
  {-# SPECIALISE digitToTree :: Digit a -> FingerTree v a #-}
  {-# SPECIALISE digitToTree :: Digit (Node v b) -> FingerTree v (Node v b) #-}

  ------------------------------------------------------------------------------------------
  --                                         viewr                                        --
  ------------------------------------------------------------------------------------------
  -- | /O(1)/. Analyse the right end of a sequence.
  viewrD :: forall b. Measured v b => FingerTree v b -> ViewR (FingerTree v) b
  viewrD f = case unMk1 f of
      Empty -> EmptyR
      Single x -> empty' :> x
      Deep v pr m sf -> case viewrDigit sf of
          Left x -> rotR pr m :> x
          Right (sf', x) -> mk1 (Deep (trySubtract v (myMeasure x) (measureDigit pr `mappend` measureTree m `mappend` measureDigit sf')) pr m sf') :> x
  {-# SPECIALISE viewrD :: FingerTree v a -> ViewR (FingerTree v) a #-}
  {-# SPECIALISE viewrD :: FingerTree v (Node v b) -> ViewR (FingerTree v) (Node v b) #-}

  rotR :: forall b. Measured v b => Digit b -> FingerTree v (Node v b) -> FingerTree v b
  rotR pr m = case viewrD m of
      EmptyR	->  digitToTree pr
      m' :> node -> case unMk1 node of
          Node2 _ a b -> mk1 $ Deep (measureDigit pr `mappend` measureTree m) pr m' (Two a b)
          Node3 _ a b c -> mk1 $ Deep (measureDigit pr `mappend` measureTree m) pr m' (Three a b c)
  {-# SPECIALISE rotR :: Digit a -> FingerTree v (Node v a) -> FingerTree v a #-}
  {-# SPECIALISE rotR :: Digit (Node v b) -> FingerTree v (Node v (Node v b)) -> FingerTree v (Node v b) #-}

  viewrDigit :: forall b. Digit b -> Either b (Digit b, b)
  viewrDigit (One a) = Left a
  viewrDigit (Two a b) = Right (One a, b)
  viewrDigit (Three a b c) = Right (Two a b, c)
  viewrDigit (Four a b c d) = Right (Three a b c, d)

  ------------------------------------------------------------------------------------------
  --                                              (><)                                    --
  ------------------------------------------------------------------------------------------
  infixl 5 `snocD`
  infixr 5 `consD`
  -- | /O(log(min(n1,n2)))/. Concatenate two sequences.
  appendD :: FingerTree v a -> FingerTree v a -> FingerTree v a
  appendD =  appendTree0

  appendTree0 :: FingerTree v a -> FingerTree v a -> FingerTree v a
  appendTree0 l r = case unMk1 l of
      Empty -> r
      Single x -> x `consD` r -- assume that the "r=Empty" check will be done by 'consD'
      Deep _ pr1 m1 sf1 -> case unMk1 r of
          Empty -> l
          Single x -> l `snocD` x
          Deep _ pr2 m2 sf2 -> deep pr1 (addDigits0 m1 sf1 pr2 m2) sf2

  addDigits0 :: FingerTree v (Node v a) -> Digit a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
  addDigits0 m1 (One a) (One b) m2 =
	appendTree1 m1 (node2 a b) m2
  addDigits0 m1 (One a) (Two b c) m2 =
	appendTree1 m1 (node3 a b c) m2
  addDigits0 m1 (One a) (Three b c d) m2 =
	appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits0 m1 (One a) (Four b c d e) m2 =
	appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits0 m1 (Two a b) (One c) m2 =
	appendTree1 m1 (node3 a b c) m2
  addDigits0 m1 (Two a b) (Two c d) m2 =
	appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits0 m1 (Two a b) (Three c d e) m2 =
	appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits0 m1 (Two a b) (Four c d e f) m2 =
	appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits0 m1 (Three a b c) (One d) m2 =
	appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits0 m1 (Three a b c) (Two d e) m2 =
	appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits0 m1 (Three a b c) (Three d e f) m2 =
	appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits0 m1 (Three a b c) (Four d e f g) m2 =
	appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits0 m1 (Four a b c d) (One e) m2 =
	appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits0 m1 (Four a b c d) (Two e f) m2 =
	appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits0 m1 (Four a b c d) (Three e f g) m2 =
	appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits0 m1 (Four a b c d) (Four e f g h) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2

  appendTree1 :: forall b. FingerTree v (Node v b) -> Node v b -> FingerTree v (Node v b) -> FingerTree v (Node v b)
  appendTree1 l a r = case unMk1 l of
      Empty -> a `consD` r
      Single x -> x `consD` a `consD` r
      Deep _ pr1 m1 sf1 -> case unMk1 r of
          Empty -> l `snocD` a
          Single x -> l `snocD` a `snocD` x
          Deep _ pr2 m2 sf2 -> deep pr1 (addDigits1 m1 sf1 a pr2 m2) sf2

  addDigits1 :: forall b. FingerTree v (Node v (Node v b)) -> Digit (Node v b) -> Node v b -> Digit (Node v b) -> FingerTree v (Node v (Node v b)) -> FingerTree v (Node v (Node v b))
  addDigits1 m1 (One a) b (One c) m2 =
	appendTree1 m1 (node3 a b c) m2
  addDigits1 m1 (One a) b (Two c d) m2 =
	appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits1 m1 (One a) b (Three c d e) m2 =
	appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits1 m1 (One a) b (Four c d e f) m2 =
	appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits1 m1 (Two a b) c (One d) m2 =
	appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits1 m1 (Two a b) c (Two d e) m2 =
	appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits1 m1 (Two a b) c (Three d e f) m2 =
	appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits1 m1 (Two a b) c (Four d e f g) m2 =
	appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits1 m1 (Three a b c) d (One e) m2 =
	appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits1 m1 (Three a b c) d (Two e f) m2 =
	appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits1 m1 (Three a b c) d (Three e f g) m2 =
	appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits1 m1 (Three a b c) d (Four e f g h) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits1 m1 (Four a b c d) e (One f) m2 =
	appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits1 m1 (Four a b c d) e (Two f g) m2 =
	appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits1 m1 (Four a b c d) e (Three f g h) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits1 m1 (Four a b c d) e (Four f g h i) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2

  appendTree2 :: forall b. FingerTree v (Node v b) -> Node v b -> Node v b -> FingerTree v (Node v b) -> FingerTree v (Node v b)
  appendTree2 l a b r = case unMk1 l of
      Empty -> a `consD` b `consD` r
      Single x -> x `consD` a `consD` b `consD` r
      Deep _ pr1 m1 sf1 -> case unMk1 r of
          Empty -> l `snocD` a `snocD` b
          Single x -> l `snocD` a `snocD` b `snocD` x
          Deep _ pr2 m2 sf2 -> deep pr1 (addDigits2 m1 sf1 a b pr2 m2) sf2

  addDigits2 :: forall b. FingerTree v (Node v (Node v b)) -> Digit (Node v b) -> Node v b -> Node v b -> Digit (Node v b) -> FingerTree v (Node v (Node v b)) -> FingerTree v (Node v (Node v b))
  addDigits2 m1 (One a) b c (One d) m2 =
	appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits2 m1 (One a) b c (Two d e) m2 =
	appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits2 m1 (One a) b c (Three d e f) m2 =
	appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits2 m1 (One a) b c (Four d e f g) m2 =
	appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits2 m1 (Two a b) c d (One e) m2 =
	appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits2 m1 (Two a b) c d (Two e f) m2 =
	appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits2 m1 (Two a b) c d (Three e f g) m2 =
	appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits2 m1 (Two a b) c d (Four e f g h) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits2 m1 (Three a b c) d e (One f) m2 =
	appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits2 m1 (Three a b c) d e (Two f g) m2 =
	appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits2 m1 (Three a b c) d e (Three f g h) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits2 m1 (Three a b c) d e (Four f g h i) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits2 m1 (Four a b c d) e f (One g) m2 =
	appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits2 m1 (Four a b c d) e f (Two g h) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits2 m1 (Four a b c d) e f (Three g h i) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits2 m1 (Four a b c d) e f (Four g h i j) m2 =
	appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2

  appendTree3 :: forall b. FingerTree v (Node v b) -> Node v b -> Node v b -> Node v b -> FingerTree v (Node v b) -> FingerTree v (Node v b)
  appendTree3 l a b c r = case unMk1 l of
      Empty -> a `consD` b `consD` c `consD` r
      Single x -> x `consD` a `consD` b `consD` c `consD` r
      Deep _ pr1 m1 sf1 -> case unMk1 r of
          Empty -> l `snocD` a `snocD` b `snocD` c
          Single x -> l `snocD` a `snocD` b `snocD` c `snocD` x
          Deep _ pr2 m2 sf2 -> deep pr1 (addDigits3 m1 sf1 a b c pr2 m2) sf2

  addDigits3 :: forall b. FingerTree v (Node v (Node v b)) -> Digit (Node v b) -> Node v b -> Node v b -> Node v b -> Digit (Node v b) -> FingerTree v (Node v (Node v b)) -> FingerTree v (Node v (Node v b))
  addDigits3 m1 (One a) b c d (One e) m2 =
	appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits3 m1 (One a) b c d (Two e f) m2 =
	appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits3 m1 (One a) b c d (Three e f g) m2 =
	appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits3 m1 (One a) b c d (Four e f g h) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits3 m1 (Two a b) c d e (One f) m2 =
	appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits3 m1 (Two a b) c d e (Two f g) m2 =
	appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits3 m1 (Two a b) c d e (Three f g h) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits3 m1 (Two a b) c d e (Four f g h i) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits3 m1 (Three a b c) d e f (One g) m2 =
	appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits3 m1 (Three a b c) d e f (Two g h) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits3 m1 (Three a b c) d e f (Three g h i) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits3 m1 (Three a b c) d e f (Four g h i j) m2 =
	appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits3 m1 (Four a b c d) e f g (One h) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits3 m1 (Four a b c d) e f g (Two h i) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits3 m1 (Four a b c d) e f g (Three h i j) m2 =
	appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits3 m1 (Four a b c d) e f g (Four h i j k) m2 =
	appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2

  appendTree4 :: forall b. FingerTree v (Node v b) -> Node v b -> Node v b -> Node v b -> Node v b -> FingerTree v (Node v b) -> FingerTree v (Node v b)
  appendTree4 l a b c d r = case unMk1 l of
      Empty -> a `consD` b `consD` c `consD` d `consD` r
      Single x -> x `consD` a `consD` b `consD` c `consD` d `consD` r
      Deep _ pr1 m1 sf1 -> case unMk1 r of
          Empty -> l `snocD` a `snocD` b `snocD` c `snocD` d
          Single x -> l `snocD` a `snocD` b `snocD` c `snocD` d `snocD` x
          Deep _ pr2 m2 sf2 -> deep pr1 (addDigits4 m1 sf1 a b c d pr2 m2) sf2

  addDigits4 :: forall b. FingerTree v (Node v (Node v b)) -> Digit (Node v b) -> Node v b -> Node v b -> Node v b -> Node v b -> Digit (Node v b) -> FingerTree v (Node v (Node v b)) -> FingerTree v (Node v (Node v b))
  addDigits4 m1 (One a) b c d e (One f) m2 =
	appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits4 m1 (One a) b c d e (Two f g) m2 =
	appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits4 m1 (One a) b c d e (Three f g h) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits4 m1 (One a) b c d e (Four f g h i) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits4 m1 (Two a b) c d e f (One g) m2 =
	appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits4 m1 (Two a b) c d e f (Two g h) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits4 m1 (Two a b) c d e f (Three g h i) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits4 m1 (Two a b) c d e f (Four g h i j) m2 =
	appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits4 m1 (Three a b c) d e f g (One h) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits4 m1 (Three a b c) d e f g (Two h i) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits4 m1 (Three a b c) d e f g (Three h i j) m2 =
	appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits4 m1 (Three a b c) d e f g (Four h i j k) m2 =
	appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
  addDigits4 m1 (Four a b c d) e f g h (One i) m2 =
	appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits4 m1 (Four a b c d) e f g h (Two i j) m2 =
	appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits4 m1 (Four a b c d) e f g h (Three i j k) m2 =
	appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
  addDigits4 m1 (Four a b c d) e f g h (Four i j k l) m2 =
	appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node3 j k l) m2
  
  ------------------------------------------------------------------------------------------
  --                                         Splitting                                    --
  ------------------------------------------------------------------------------------------
  splitError :: forall b. b
  splitError = error "splitTree of empty tree (possible violation of monoid invariant?)"
  
  -- | /O(log(min(i,n-i)))/. Split a sequence at a point where the predicate
  -- on the accumulated measure changes from 'False' to 'True'. Also focuses on the element at which the change occurred.
  {-# INLINE splitD #-}
  splitD :: forall d. SplitPred d v => d -> FingerTree v a -> (FingerTree v a, a, FingerTree v a)
  splitD d t = case unMk1 t of
      Empty -> error "empty" -- Nothing -- (empty, empty)
      _ | p (measureTree t) -> case splitTree mempty t of (# l, x, r #) -> (l, x, r)
      _ | otherwise -> error "not found" -- (t, empty)
     where

    p :: v -> Bool
    p x = checkPred d x

    -- we manually CPR this call, because GHC apparently doesn't want to
    splitTree :: forall b. Measured v b => v -> FingerTree v b -> Split (FingerTree v b) b
    splitTree i tree = case unMk1 tree of
        Empty -> i `seq` mkSplit splitError splitError splitError
        Single x -> i `seq` mkSplit empty x empty
        Deep _ pr m sf 
          | p vpr ->  case splitDigit i pr of
                         (# l, x, r #) -> mkSplit (maybe empty digitToTree l) x (deepL r m sf)
          | p vm ->  case splitTree vpr m of
                       (# ml, xs, mr #) -> case splitNode (vpr `mappend` measureTree ml) xs of
                         (# l, x, r #) -> mkSplit (deepR pr  ml l) x (deepL r mr sf)
                           where 
          | otherwise -> case splitDigit vm sf of
                            (# l, x, r #) -> mkSplit (deepR pr  m  l) x (maybe empty digitToTree r)
         where 
           vpr =  i    `mappend`  measureDigit' pr
           vm =  vpr  `mappend` measureTree m
    {-# SPECIALIZE splitTree :: v -> FingerTree v a -> Split (FingerTree v a) a #-}
    {-# SPECIALIZE splitTree :: v -> FingerTree v (Node v b) -> Split (FingerTree v (Node v b)) (Node v b) #-}
  
    splitNode :: forall b. Measured v b => v -> Node v b -> Split (Maybe (Digit b)) b
    splitNode i node = case unMk1 node of
      Node2 _ a b 
        | p va       -> mkSplit Nothing a (Just (One b))
        | otherwise  -> mkSplit (Just (One a)) b Nothing
       where	va	= i `mappend` myMeasure a
      Node3 _ a b c
        | p va	-> mkSplit Nothing a (Just (Two b c))
        | p vab	-> mkSplit (Just (One a)) b (Just (One c))
        | otherwise	-> mkSplit (Just (Two a b)) c Nothing
       where va  = i `mappend` myMeasure a
             vab = va `mappend` myMeasure b
    {-# SPECIALISE splitNode :: v -> Node v a -> Split (Maybe (Digit a)) a #-}
    {-# SPECIALISE splitNode :: v -> Node v (Node v b) -> Split (Maybe (Digit (Node v b))) (Node v b) #-}
    
    splitDigit :: forall b. Measured v b => v -> Digit b -> Split (Maybe (Digit b)) b
    splitDigit i (One a) = i `seq` mkSplit Nothing a Nothing
    splitDigit i (Two a b)
      | p va	= mkSplit Nothing a (Just (One b))
      | otherwise	= mkSplit (Just (One a)) b Nothing
      where	va	= i `mappend` myMeasure a
    splitDigit i (Three a b c)
      | p va	= mkSplit Nothing a (Just (Two b c))
      | p vab	= mkSplit (Just (One a)) b (Just (One c))
      | otherwise	= mkSplit (Just (Two a b)) c Nothing
      where va	= i `mappend` myMeasure a
            vab	= va `mappend` myMeasure b
    splitDigit i (Four a b c d)
      | p va	= mkSplit Nothing a (Just (Three b c d))
      | p vab	= mkSplit (Just (One a)) b (Just (Two c d))
      | p vabc	= mkSplit (Just (Two a b)) c (Just (One d))
      | otherwise	= mkSplit (Just (Three a b c)) d Nothing
      where va	= i `mappend` myMeasure a
            vab	= va `mappend` myMeasure b
            vabc	= vab `mappend` myMeasure c
    {-# SPECIALISE splitDigit :: v -> Digit a -> Split (Maybe (Digit a)) a #-}
    {-# SPECIALISE splitDigit :: v -> Digit (Node v b) -> Split (Maybe (Digit (Node v b))) (Node v b) #-}

  deepL :: forall b. Measured v b => Maybe (Digit b) -> FingerTree v (Node v b) -> Digit b -> FingerTree v b
  deepL Nothing m sf	=   rotL m sf
  deepL (Just pr) m sf	=   deep pr m sf
  {-# SPECIALISE deepL :: Maybe (Digit a) -> FingerTree v (Node v a) -> Digit a -> FingerTree v a #-}
  {-# SPECIALISE deepL :: Maybe (Digit (Node v b)) -> FingerTree v (Node v (Node v b)) -> Digit (Node v b) -> FingerTree v (Node v b) #-}
  
  deepR :: forall b. Measured v b => Digit b -> FingerTree v (Node v b) -> Maybe (Digit b) -> FingerTree v b
  deepR pr m Nothing	=   rotR pr m
  deepR pr m (Just sf)	=   deep pr m sf
  {-# SPECIALISE deepR :: Digit a -> FingerTree v (Node v a) -> Maybe (Digit a) -> FingerTree v a #-}
  {-# SPECIALISE deepR :: Digit (Node v b) -> FingerTree v (Node v (Node v b)) -> Maybe (Digit (Node v b)) -> FingerTree v (Node v b) #-}
  

------------------
-- Transformations
------------------
{-
-- | /O(n)/. The reverse of a sequence.
reverse :: (Unbox v, Measured v a) => FingerTree v a -> FingerTree v a
reverse = reverseTree id
{-# INLINABLE reverse #-}

reverseTree :: (Unbox v1, Unbox v2, Measured v2 a2) => (a1 -> a2) -> FingerTree v1 a1 -> FingerTree v2 a2
reverseTree _ (unMk1 -> Empty) = mk1 Empty
reverseTree f (unMk1 -> Single x) = mk1 $ Single (f x)
reverseTree f (unMk1 -> Deep _ pr m sf) =
	deep (reverseDigit f sf) (reverseTree (reverseNode f) m) (reverseDigit f pr)
{-# INLINABLE reverseTree #-}

reverseNode :: (Unbox v1, Unbox v2, Measured v2 a2) => (a1 -> a2) -> Node v1 a1 -> Node v2 a2
reverseNode f (unMk1 -> Node2 _ a b) = node2 (f b) (f a)
reverseNode f (unMk1 -> Node3 _ a b c) = node3 (f c) (f b) (f a)
{-# INLINABLE reverseNode #-}

reverseDigit :: (a -> b) -> Digit a -> Digit b
reverseDigit f (One a) = One (f a)
reverseDigit f (Two a b) = Two (f b) (f a)
reverseDigit f (Three a b c) = Three (f c) (f b) (f a)
reverseDigit f (Four a b c d) = Four (f d) (f c) (f b) (f a)
{-# INLINABLE reverseDigit #-}
-}


{-
-- | Like 'fmap', but with a more constrained type.
fmap' :: (Unbox v1, Unbox v2, Measured v1 a1, Measured v2 a2) =>
     (a1 -> a2) -> FingerTree' v1 a1 -> FingerTree' v2 a2
fmap' = mapTree
{-# INLINABLE fmap' #-}

mapTree :: (Unbox v1, Unbox v2, Measured v2 a2) =>
	(a1 -> a2) -> FingerTree' v1 a1 -> FingerTree' v2 a2
mapTree _ (unMk1 -> Empty) = mk1 Empty
mapTree f (unMk1 -> Single x) = mk1 $ Single (f x)
mapTree f (unMk1 -> Deep _ pr m sf) =
	deep (mapDigit f pr) (mapTree (mapNode f) m) (mapDigit f sf)
{-# INLINABLE mapTree #-}

mapNode :: (Unbox v1, Unbox v2, Measured v2 a2) =>
	(a1 -> a2) -> Node v1 a1 -> Node v2 a2
mapNode f (unMk1 -> Node2 _ a b) = node2 (f a) (f b)
mapNode f (unMk1 -> Node3 _ a b c) = node3 (f a) (f b) (f c)
{-# INLINABLE mapNode #-}

mapDigit :: (a -> b) -> Digit a -> Digit b
mapDigit f (One a) = One (f a)
mapDigit f (Two a b) = Two (f a) (f b)
mapDigit f (Three a b c) = Three (f a) (f b) (f c)
mapDigit f (Four a b c d) = Four (f a) (f b) (f c) (f d)
{-# INLINABLE mapDigit #-}

-- | Map all elements of the tree with a function that also takes the
-- measure of the prefix of the tree to the left of the element.
fmapWithPos :: (Unbox v1, Unbox v2, Measured v1 a1, Measured v2 a2) =>
	(v1 -> a1 -> a2) -> FingerTree' v1 a1 -> FingerTree' v2 a2
fmapWithPos f = mapWPTree f mempty
{-# INLINABLE fmapWithPos #-}

mapWPTree :: (Unbox v1, Unbox v2, Measured v1 a1, Measured v2 a2) =>
	(v1 -> a1 -> a2) -> v1 -> FingerTree' v1 a1 -> FingerTree' v2 a2
mapWPTree _ _ (unMk1 -> Empty) = mk1 Empty
mapWPTree f v (unMk1 -> Single x) = mk1 $ Single (f v x)
mapWPTree f v (unMk1 -> Deep _ pr m sf) =
	deep (mapWPDigit f v pr)
		(mapWPTree (mapWPNode f) vpr m)
		(mapWPDigit f vm sf)
  where	vpr	=  v    `mappend`  measure pr
	vm	=  vpr  `mappendVal` m
{-# INLINABLE mapWPTree #-}

mapWPNode :: (Unbox v1, Unbox v2, Measured v1 a1, Measured v2 a2) =>
	(v1 -> a1 -> a2) -> v1 -> Node v1 a1 -> Node v2 a2
mapWPNode f v (unMk1 -> Node2 _ a b) = node2 (f v a) (f va b)
  where	va	= v `mappend` measure a
mapWPNode f v (unMk1 -> Node3 _ a b c) = node3 (f v a) (f va b) (f vab c)
  where	va	= v `mappend` measure a
	vab	= va `mappend` measure b
{-# INLINABLE mapWPNode #-}

mapWPDigit :: (Measured v a) => (v -> a -> b) -> v -> Digit a -> Digit b
mapWPDigit f v (One a) = One (f v a)
mapWPDigit f v (Two a b) = Two (f v a) (f va b)
  where	va	= v `mappend` measure a
mapWPDigit f v (Three a b c) = Three (f v a) (f va b) (f vab c)
  where	va	= v `mappend` measure a
	vab	= va `mappend` measure b
mapWPDigit f v (Four a b c d) = Four (f v a) (f va b) (f vab c) (f vabc d)
  where	va	= v `mappend` measure a
	vab	= va `mappend` measure b
        vabc	= vab `mappend` measure c
{-# INLINABLE mapWPDigit #-}

-- | Like 'fmap', but safe only if the function preserves the measure.
unsafeFmap :: Unbox v => (a -> b) -> FingerTree' v a -> FingerTree' v b
unsafeFmap _ (unMk1 -> Empty) = mk1 Empty
unsafeFmap f (unMk1 -> Single x) = mk1 $ Single (f x)
unsafeFmap f (unMk1 -> Deep v pr m sf) =
	mk1 $ Deep v (mapDigit f pr) (unsafeFmap (unsafeFmapNode f) m) (mapDigit f sf)
{-# INLINABLE unsafeFmap #-}

unsafeFmapNode :: Unbox v => (a -> b) -> Node v a -> Node v b
unsafeFmapNode f (unMk1 -> Node2 v a b) = mk1 $ Node2 v (f a) (f b)
unsafeFmapNode f (unMk1 -> Node3 v a b c) = mk1 $ Node3 v (f a) (f b) (f c)
{-# INLINABLE unsafeFmapNode #-}

-- | Like 'traverse', but with a more constrained type.
traverse' :: (Unbox v1, Unbox v2, Measured v1 a1, Measured v2 a2, Applicative f) =>
	(a1 -> f a2) -> FingerTree' v1 a1 -> f (FingerTree' v2 a2)
traverse' = traverseTree
{-# INLINABLE traverse' #-}

traverseTree :: (Unbox v1, Unbox v2, Measured v2 a2, Applicative f) =>
	(a1 -> f a2) -> FingerTree' v1 a1 -> f (FingerTree' v2 a2)
traverseTree _ (unMk1 -> Empty) = pure (mk1 Empty)
traverseTree f (unMk1 -> Single x) = (mk1 . Single) <$> f x
traverseTree f (unMk1 -> Deep _ pr m sf) =
	deep <$> traverseDigit f pr <*> traverseTree (traverseNode f) m <*> traverseDigit f sf
{-# INLINABLE traverseTree #-}

traverseNode :: (Unbox v1, Unbox v2, Measured v2 a2, Applicative f) =>
	(a1 -> f a2) -> Node v1 a1 -> f (Node v2 a2)
traverseNode f (unMk1 -> Node2 _ a b) = node2 <$> f a <*> f b
traverseNode f (unMk1 -> Node3 _ a b c) = node3 <$> f a <*> f b <*> f c
{-# INLINABLE traverseNode #-}

traverseDigit :: (Applicative f) => (a -> f b) -> Digit a -> f (Digit b)
traverseDigit f (One a) = One <$> f a
traverseDigit f (Two a b) = Two <$> f a <*> f b
traverseDigit f (Three a b c) = Three <$> f a <*> f b <*> f c
traverseDigit f (Four a b c d) = Four <$> f a <*> f b <*> f c <*> f d
{-# INLINABLE traverseDigit #-}

-- | Traverse the tree with a function that also takes the
-- measure of the prefix of the tree to the left of the element.
traverseWithPos :: (Unbox v1, Unbox v2, Measured v1 a1, Measured v2 a2, Applicative f) =>
	(v1 -> a1 -> f a2) -> FingerTree' v1 a1 -> f (FingerTree' v2 a2)
traverseWithPos f = traverseWPTree f mempty
{-# INLINABLE traverseWithPos #-}

traverseWPTree :: (Unbox v1, Unbox v2, Measured v1 a1, Measured v2 a2, Applicative f) =>
	(v1 -> a1 -> f a2) -> v1 -> FingerTree' v1 a1 -> f (FingerTree' v2 a2)
traverseWPTree _ _ (unMk1 -> Empty) = pure (mk1 Empty)
traverseWPTree f v (unMk1 -> Single x) = (mk1 . Single) <$> f v x
traverseWPTree f v (unMk1 -> Deep _ pr m sf) =
	deep <$> traverseWPDigit f v pr <*> traverseWPTree (traverseWPNode f) vpr m <*> traverseWPDigit f vm sf
  where	vpr	=  v    `mappend`  measure pr
	vm	=  vpr  `mappendVal` m
{-# INLINABLE traverseWPTree #-}

traverseWPNode :: (Unbox v1, Unbox v2, Measured v1 a1, Measured v2 a2, Applicative f) =>
	(v1 -> a1 -> f a2) -> v1 -> Node v1 a1 -> f (Node v2 a2)
traverseWPNode f v (unMk1 -> Node2 _ a b) = node2 <$> f v a <*> f va b
  where	va	= v `mappend` measure a
traverseWPNode f v (unMk1 -> Node3 _ a b c) = node3 <$> f v a <*> f va b <*> f vab c
  where	va	= v `mappend` measure a
	vab	= va `mappend` measure b
{-# INLINABLE traverseWPNode #-}

traverseWPDigit :: (Measured v a, Applicative f) =>
	(v -> a -> f b) -> v -> Digit a -> f (Digit b)
traverseWPDigit f v (One a) = One <$> f v a
traverseWPDigit f v (Two a b) = Two <$> f v a <*> f va b
  where	va	= v `mappend` measure a
traverseWPDigit f v (Three a b c) = Three <$> f v a <*> f va b <*> f vab c
  where	va	= v `mappend` measure a
	vab	= va `mappend` measure b
traverseWPDigit f v (Four a b c d) = Four <$> f v a <*> f va b <*> f vab c <*> f vabc d
  where	va	= v `mappend` measure a
	vab	= va `mappend` measure b
        vabc	= vab `mappend` measure c
{-# INLINABLE traverseWPDigit #-}

-- | Like 'traverse', but safe only if the function preserves the measure.
unsafeTraverse :: (Unbox v, Applicative f) =>
	(a -> f b) -> FingerTree' v a -> f (FingerTree' v b)
unsafeTraverse _ (unMk1 -> Empty) = pure (mk1 Empty)
unsafeTraverse f (unMk1 -> Single x) = (mk1 . Single)  <$> f x
unsafeTraverse f (unMk1 -> Deep v pr m sf) =
	(\a b c -> mk1 $ Deep v a b c) <$> traverseDigit f pr <*> unsafeTraverse (unsafeTraverseNode f) m <*> traverseDigit f sf
{-# INLINABLE unsafeTraverse #-}

unsafeTraverseNode :: (Unbox v, Applicative f) =>
	(a -> f b) -> Node v a -> f (Node v b)
unsafeTraverseNode f (unMk1 -> Node2 v a b) = (\a b -> mk1 $ Node2 v a b) <$> f a <*> f b
unsafeTraverseNode f (unMk1 -> Node3 v a b c) = (\a b c -> mk1 $ Node3 v a b c) <$> f a <*> f b <*> f c
{-# INLINABLE unsafeTraverseNode #-}
-}


{-
-- | /O(n)/. Create a sequence from a finite list of elements.
fromList :: (Unbox v, Measured v a) => [a] -> FingerTree v a 
fromList = foldr (<|) empty
{-# INLINABLE fromList #-}
-}