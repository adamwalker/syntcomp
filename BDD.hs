{-# LANGUAGE RecordWildCards #-}
module BDD where

import Control.Monad.ST
import Control.Monad.ST.Unsafe

import qualified Cudd.Imperative as Cudd
import Cudd.Imperative (DDManager, DDNode)
import Cudd.Reorder

--BDD operations
data Ops s a = Ops {
    bAnd           :: a -> a -> ST s a,
    bOr            :: a -> a -> ST s a,
    lEq            :: a -> a -> ST s Bool,
    neg            :: a -> a,
    vectorCompose  :: a -> [a] -> ST s a,
    newVar         :: ST s a,
    computeCube    :: [a] -> ST s a,
    computeCube2   :: [a] -> [Bool] -> ST s a,
    getSize        :: ST s Int,
    ithVar         :: Int -> ST s a,
    bforall        :: a -> a -> ST s a,
    bexists        :: a -> a -> ST s a,
    deref          :: a -> ST s (),
    ref            :: a -> ST s (),
    btrue          :: a,
    bfalse         :: a,
    andAbstract    :: a -> a -> a -> ST s a,
    getIdx         :: a -> ST s Int,
    largestCube    :: a -> ST s (a, Int),
    makePrime      :: a -> a -> ST s a,
    supportIndices :: a -> ST s [Int],
    printMinterm   :: a -> ST s ()
}

constructOps :: DDManager s u -> Ops s (DDNode s u)
constructOps m = Ops {..}
    where
    bAnd              = Cudd.bAnd m
    bOr               = Cudd.bOr  m
    lEq               = Cudd.lEq  m
    neg               = Cudd.bNot
    vectorCompose     = Cudd.vectorCompose m
    newVar            = Cudd.newVar m
    computeCube       = Cudd.nodesToCube m
    computeCube2      = Cudd.computeCube m
    getSize           = Cudd.readSize m
    ithVar            = Cudd.ithVar m
    bforall           = flip $ Cudd.bForall m
    bexists           = flip $ Cudd.bExists m
    deref             = Cudd.deref m
    ref               = Cudd.ref
    btrue             = Cudd.bOne m
    bfalse            = Cudd.bZero m
    andAbstract c x y = Cudd.andAbstract m x y c
    getIdx            = Cudd.readIndex
    largestCube       = Cudd.largestCube m
    makePrime         = Cudd.makePrime m
    supportIndices    = Cudd.supportIndices m
    printMinterm      = Cudd.printMinterm m

bddSynopsis :: (Show a, Eq a) => Ops s a -> a -> ST s ()
bddSynopsis Ops{..} x 
    | x == btrue  = unsafeIOToST $ putStrLn "True"
    | x == bfalse = unsafeIOToST $ putStrLn "False"
    | otherwise   = unsafeIOToST $ print x

