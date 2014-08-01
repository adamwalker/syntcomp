{-# LANGUAGE OverloadedStrings, RecordWildCards, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

import Control.Applicative
import qualified  Data.Text.IO as T
import Data.Map.Strict (Map)
import qualified  Data.Map.Strict as Map
import Control.Monad.ST.Strict
import Control.Monad
import Data.List
import Data.Tuple.All
import Data.Bits
import Control.Monad.ST.Unsafe
import System.Directory
import System.IO
import System.CPUTime
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import qualified Data.Traversable as T
import Control.Monad.Trans.Either
import Control.Monad.Trans

import Options.Applicative as O
import Safe
import Data.Attoparsec.Text as P

import qualified Cudd.Imperative as Cudd
import Cudd.Imperative (STDdManager, DDNode)
import Cudd.Reorder

--Parsing
data Header = Header {
    m :: Int,
    i :: Int,
    l :: Int,
    o :: Int,
    a :: Int
} deriving (Show)

data InputType  = Cont | UCont deriving (Show)
data SymbolType = Is InputType | Ls | Os deriving (Show)

data Symbol = Symbol {
    typ :: SymbolType,
    idx :: Int,
    str :: String
} deriving (Show)

data AAG = AAG {
    header   :: Header,
    inputs   :: [Int],
    latches  :: [(Int, Int)],
    outputs  :: [Int],
    andGates :: [(Int, Int, Int)],
    symbols  :: [Symbol]
} deriving (Show)

ws  = skipSpace
eol = endOfLine

header' = Header <$  string "aag" 
                 <*  ws
                 <*> decimal
                 <*  ws
                 <*> decimal
                 <*  ws
                 <*> decimal
                 <*  ws
                 <*> decimal
                 <*  ws
                 <*> decimal
                 <*  eol
input   = decimal <* eol
latch   = (,) <$> decimal <*  ws <*> decimal <* eol
output  = decimal <* eol
andGate = (,,) <$> decimal <*  ws <*> decimal <*  ws <*> decimal <* eol
symbol  = iSymbol <|> lSymbol <|> oSymbol
    where
    iSymbol = constructISymbol <$ char 'i' <*> decimal <* ws <*> isCont <*> manyTill anyChar endOfLine
        where 
        isCont = P.option UCont (Cont <$ string "controllable") 
        constructISymbol idx cont name = Symbol (Is cont) idx name
    lSymbol = Symbol <$> (Ls <$ char 'l') <*> decimal <* ws <*> manyTill anyChar endOfLine
    oSymbol = Symbol <$> (Os <$ char 'o') <*> decimal <* ws <*> manyTill anyChar endOfLine

aag = do
    header@Header{..} <- header' 
    inputs   <- replicateM i input
    latches  <- replicateM l latch
    outputs  <- replicateM o output
    andGates <- replicateM a andGate
    symbols  <- many symbol
    return $ AAG {..}

--BDD operations
data Ops s a = Ops {
    bAnd          :: a -> a -> ST s a,
    bOr           :: a -> a -> ST s a,
    lEq           :: a -> a -> ST s Bool,
    neg           :: a -> a,
    vectorCompose :: a -> [a] -> ST s a,
    newVar        :: ST s a,
    computeCube   :: [a] -> ST s a,
    computeCube2  :: [a] -> [Bool] -> ST s a,
    getSize       :: ST s Int,
    ithVar        :: Int -> ST s a,
    bforall       :: a -> a -> ST s a,
    bexists       :: a -> a -> ST s a,
    deref         :: a -> ST s (),
    ref           :: a -> ST s (),
    btrue         :: a,
    bfalse        :: a
}

constructOps :: STDdManager s u -> Ops s (DDNode s u)
constructOps m = Ops {..}
    where
    bAnd          = Cudd.band m
    bOr           = Cudd.bor  m
    lEq           = Cudd.leq  m
    neg           = Cudd.bnot
    vectorCompose = Cudd.vectorCompose m
    newVar        = Cudd.newVar m
    computeCube   = Cudd.nodesToCube m
    computeCube2  = Cudd.computeCube m
    getSize       = Cudd.readSize m
    ithVar        = Cudd.bvar m
    bforall       = flip $ Cudd.bforall m
    bexists       = flip $ Cudd.bexists m
    deref         = Cudd.deref m
    ref           = Cudd.ref
    btrue         = Cudd.bone m
    bfalse        = Cudd.bzero m

bddSynopsis :: (Show a, Eq a) => Ops s a -> a -> ST s ()
bddSynopsis Ops{..} x 
    | x == btrue  = unsafeIOToST $ putStrLn "True"
    | x == bfalse = unsafeIOToST $ putStrLn "False"
    | otherwise   = unsafeIOToST $ print x

--Compiling the AIG
makeAndMap :: [(Int, Int, Int)] -> Map Int (Int, Int)
makeAndMap = Map.fromList . map func
    where func (out, x, y) = (out, (x, y))

doAndGates :: Ops s a -> Map Int (Int, Int) -> Map Int a -> Int -> ST s (Map Int a, a)
doAndGates ops@Ops{..} andGateInputs accum andGate = 
    case Map.lookup andGate accum of
        Just x  -> return (accum, x)
        Nothing -> do
            let varIdx   =  clearBit andGate 0
                (x, y)   =  fromJustNote "doAndGates" $ Map.lookup varIdx andGateInputs
            (accum', x)  <- doAndGates ops andGateInputs accum x
            (accum'', y) <- doAndGates ops andGateInputs accum' y
            res          <- bAnd x y
            let finalMap =  Map.insert varIdx res (Map.insert (varIdx + 1) (neg res) accum'')
            return (finalMap, fromJustNote "doAndGates2" $ Map.lookup andGate finalMap) 

mapAccumLM :: Monad m => (acc -> x -> m (acc, y)) -> acc -> [x] -> m (acc, [y])
mapAccumLM _ s []     = return (s, [])
mapAccumLM f s (x:xs) = do
    (s1, x')  <- f s x
    (s2, xs') <- mapAccumLM f s1 xs
    return    (s2, x' : xs')

--Synthesis
data SynthState a = SynthState {
    cInputCube :: a,
    uInputCube :: a,
    safeRegion :: a,
    trel       :: [a],
    initState  :: a
} deriving (Functor, Foldable, Traversable)

substitutionArray :: Ops s a -> Map Int Int -> Map Int a -> ST s [a]
substitutionArray Ops{..} latches andGates = do
    sz <- getSize
    --unsafeIOToST $ print sz
    mapM func [0..(sz-1)]
    where 
    func idx = case Map.lookup (idx * 2 + 2) latches of
        Nothing    -> ithVar idx
        Just input -> return $ fromJustNote ("substitutionArray: " ++ show input) $ Map.lookup input andGates

compile :: Ops s a -> [Int] -> [Int] -> [(Int, Int)] -> [(Int, Int, Int)] -> Int -> ST s (SynthState a)
compile ops@Ops{..} controllableInputs uncontrollableInputs latches ands safeIndex = do
    let andGates = map sel1 ands
        andMap   = makeAndMap ands
    --create an entry for each controllable input 
    cInputVars <- sequence $ replicate (length controllableInputs) newVar
    cInputCube <- computeCube cInputVars

    --create an entry for each uncontrollable input
    uInputVars <- sequence $ replicate (length uncontrollableInputs) newVar
    uInputCube <- computeCube uInputVars

    --create an entry for each latch 
    latchVars  <- sequence $ replicate (length latches) newVar

    ref btrue
    ref bfalse

    --create the symbol table
    let func idx var = [(idx, var), (idx + 1, neg var)]
        tf   = Map.fromList $ [(0, bfalse), (1, btrue)]
        mpCI = Map.fromList $ concat $ zipWith func controllableInputs cInputVars
        mpUI = Map.fromList $ concat $ zipWith func uncontrollableInputs uInputVars
        mpL  = Map.fromList $ concat $ zipWith func (map fst latches) latchVars
        im   = Map.unions [tf, mpCI, mpUI, mpL]

    --compile the and gates
    stab     <- fmap fst $ mapAccumLM (doAndGates ops andMap) im andGates 

    --get the safety condition
    let sr   = fromJustNote "compile" $ Map.lookup safeIndex stab
    
    --construct the initial state
    initState <- computeCube2 latchVars (replicate (length latchVars) False)

    --construct the transition relation
    let latchMap = Map.fromList latches
    trel <- substitutionArray ops latchMap stab

    mapM ref trel
    ref sr
    let func k v = when (even k) (deref v)
    Map.traverseWithKey func stab

    return $ SynthState cInputCube uInputCube (neg sr) trel initState

safeCpre :: (Show a, Eq a) => Bool -> Ops s a -> SynthState a -> a -> ST s a
safeCpre quiet ops@Ops{..} SynthState{..} s = do
    when (not quiet) $ unsafeIOToST $ print "*"
    scu' <- vectorCompose s trel

    scu <- bAnd safeRegion scu'
    deref scu'

    su  <- bexists cInputCube scu
    deref scu
    s   <- bforall uInputCube su
    deref su
    return s

fixedPoint :: Eq a => Ops s a -> a -> a -> (a -> ST s a) -> ST s Bool
fixedPoint ops@Ops{..} init start func = do
    res <- func start
    deref start
    win <- init `lEq` res
    case win of
        False -> deref res >> return False
        True  -> 
            case (res == start) of
                True  -> deref res >> return True
                False -> fixedPoint ops init res func 

solveSafety :: (Eq a, Show a) => Bool -> Ops s a -> SynthState a -> a -> a -> ST s Bool
solveSafety quiet ops@Ops{..} ss init safeRegion = do
    ref btrue
    fixedPoint ops init btrue $ safeCpre quiet ops ss 

setupManager :: Bool -> STDdManager s u -> ST s ()
setupManager quiet m = void $ do
    cuddAutodynEnable m CuddReorderGroupSift
    when (not quiet) $ void $ do
        regStdPreReordHook m
        regStdPostReordHook m
        cuddEnableReorderingReporting m

categorizeInputs :: [Symbol] -> [Int] -> ([Int], [Int])
categorizeInputs symbols inputs = (cont, inputs \\ cont)
    where
    cont                     = map (inputs !!) theSet
    theSet                   = map idx $ filter (isControllable . typ) symbols
    isControllable (Is Cont) = True
    isControllable _         = False

doIt :: Options -> IO (Either String Bool)
doIt (Options {..}) = runEitherT $ do
    contents    <- lift $ T.readFile filename
    aag@AAG{..} <- hoistEither $ parseOnly aag contents
    lift $ do
        let (cInputs, uInputs) = categorizeInputs symbols inputs
        stToIO $ Cudd.withManagerDefaults $ \m -> do
            setupManager quiet m
            let ops = constructOps m
            ss@SynthState{..} <- compile ops cInputs uInputs latches andGates (head outputs)
            res <- solveSafety quiet ops ss initState safeRegion
            T.mapM (deref ops) ss
            Cudd.quit m
            return res

run :: Options -> IO ()
run g = do
    res <- doIt g 
    case res of
        Left err    -> putStrLn $ "Error: " ++ err
        Right True  -> putStrLn "REALIZABLE"
        Right False -> putStrLn "UNREALIZABLE"

data Options = Options {
    quiet    :: Bool,
    filename :: String
}

main = execParser opts >>= run
    where
    opts   = info (helper <*> parser) (fullDesc <> progDesc "Solve the game specified in INPUT" <> O.header "Simple BDD solver")
    parser = Options <$> flag False True (long "quiet" <> short 'q' <> help "Be quiet")
                     <*> argument O.str (metavar "INPUT")
