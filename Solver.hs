{-# LANGUAGE OverloadedStrings, RecordWildCards, DeriveFunctor, DeriveFoldable, DeriveTraversable, RankNTypes #-}

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
import Cudd.Imperative (DDManager, DDNode)
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
    bXNor         :: a -> a -> ST s a,
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
    bfalse        :: a,
    andAbstract   :: a -> a -> a -> ST s a,
    setVarMap     :: [a] -> [a] -> ST s (),
    varMap        :: a -> ST s a
}

constructOps :: Options -> DDManager s u -> Ops s (DDNode s u)
constructOps Options{..} m = Ops {..}
    where
    bAnd              = Cudd.bAnd m
    bOr               = Cudd.bOr  m
    bXNor             = Cudd.bXnor m
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
    deref             = if noDeref then (const $ return ()) else Cudd.deref m
    ref               = Cudd.ref
    btrue             = Cudd.bOne m
    bfalse            = Cudd.bZero m
    andAbstract c x y = Cudd.andAbstract m x y c
    setVarMap         = Cudd.setVarMap m
    varMap            = Cudd.varMap m

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
data SynthState s a = SynthState {
    cInputCube :: a,
    uInputCube :: a,
    safeRegion :: a,
    subNext    :: a -> ST s a,
    initState  :: a
} 

substitutionArray :: Ops s a -> Map Int Int -> Map Int a -> ST s [a]
substitutionArray Ops{..} latches andGates = do
    sz <- getSize
    --unsafeIOToST $ print sz
    mapM func [0..(sz-1)]
    where 
    func idx = case Map.lookup (idx * 2 + 2) latches of
        Nothing    -> ithVar idx
        Just input -> return $ fromJustNote ("substitutionArray: " ++ show input) $ Map.lookup input andGates

compile :: Ops s a -> [Int] -> [Int] -> [(Int, Int)] -> [(Int, Int, Int)] -> Int -> ST s (SynthState s a)
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

    let subNext s = vectorCompose s trel

    return $ SynthState cInputCube uInputCube (neg sr) subNext initState

conj :: Ops s a -> [a] -> ST s a
conj Ops{..} xs = do
    ref btrue
    foldM func btrue xs
    where
    func accum y = do
        res <- bAnd accum y
        deref accum
        return res

compileMonolithic :: Ops s a -> [Int] -> [Int] -> [(Int, Int)] -> [(Int, Int, Int)] -> Int -> ST s (SynthState s a)
compileMonolithic ops@Ops{..} controllableInputs uncontrollableInputs latches ands safeIndex = do
    let andGates = map sel1 ands
        andMap   = makeAndMap ands
    --create an entry for each controllable input 
    cInputVars <- sequence $ replicate (length controllableInputs) newVar
    cInputCube <- computeCube cInputVars

    --create an entry for each uncontrollable input
    uInputVars <- sequence $ replicate (length uncontrollableInputs) newVar
    uInputCube <- computeCube uInputVars

    --create an entry for each latch 
    latchVars  <- sequence $ replicate (length latches) ((,) <$> newVar <*> newVar)

    ref btrue
    ref bfalse

    --create the symbol table
    let func idx var = [(idx, var), (idx + 1, neg var)]
        tf   = Map.fromList $ [(0, bfalse), (1, btrue)]
        mpCI = Map.fromList $ concat $ zipWith func controllableInputs cInputVars
        mpUI = Map.fromList $ concat $ zipWith func uncontrollableInputs uInputVars
        mpL  = Map.fromList $ concat $ zipWith func (map fst latches) (map fst latchVars)
        im   = Map.unions [tf, mpCI, mpUI, mpL]

    --compile the and gates
    stab     <- fmap fst $ mapAccumLM (doAndGates ops andMap) im andGates 

    --get the safety condition
    let sr   = fromJustNote "compile" $ Map.lookup safeIndex stab
    
    --construct the initial state
    initState <- computeCube2 (map fst latchVars) (replicate (length latchVars) False)

    --set the variable map
    setVarMap (map fst latchVars) (map snd latchVars)

    --calculate the next cube
    nextCube <- computeCube (map snd latchVars)

    ref sr
    --let func k v = when (even k) (deref v)
    --Map.traverseWithKey func stab

    --construct the transition relation
    let func (latchIndex, latchAssign) (latchCurrentNode, latchNextNode) = do
            let assignedTo = fromJustNote "compileMonolithic" $ Map.lookup latchAssign stab
            bXNor latchNextNode assignedTo

    trel <- zipWithM func latches latchVars
    trans <- conj ops trel
    mapM deref trel

    let subNext s = do
            s' <- varMap s 
            c  <- bOr (neg trans) s'
            deref s'
            r  <- bforall nextCube c
            deref c
            return r

    return $ SynthState cInputCube uInputCube (neg sr) subNext initState

safeCpre :: (Show a, Eq a) => Options -> Ops s a -> SynthState s a -> a -> ST s a
safeCpre Options{..} ops@Ops{..} SynthState{..} s = do
    when (not quiet) $ unsafeIOToST $ print "*"
    scu' <- subNext s

    scu <- if noSimult then do
            var <- bAnd safeRegion scu'
            deref scu'
            scu <- bexists cInputCube var
            deref var
            return scu
        else do
            scu <- andAbstract cInputCube safeRegion scu'
            deref scu'
            return scu

    s   <- bforall uInputCube scu
    deref scu
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

fixedPointNoEarly :: Eq a => Ops s a -> a -> a -> (a -> ST s a) -> ST s Bool
fixedPointNoEarly ops@Ops{..} init start func = do
    res <- f start
    win <- init `lEq` res
    deref res
    return win
    where 
    f start = do
        res <- func start
        deref start
        case res == start of
            True  -> return res
            False -> f res

solveSafety :: (Eq a, Show a) => Options -> Ops s a -> SynthState s a -> a -> a -> ST s Bool
solveSafety options@Options{..} ops@Ops{..} ss init safeRegion = do
    ref btrue
    if noEarly then (fixedPointNoEarly ops init btrue $ safeCpre options ops ss) else (fixedPoint ops init btrue $ safeCpre options ops ss)

setupManager :: Options -> DDManager s u -> ST s ()
setupManager Options{..} m = void $ do
    unless noReord $ cuddAutodynEnable m CuddReorderGroupSift
    unless quiet   $ void $ do
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
doIt o@Options{..} = runEitherT $ do
    contents    <- lift $ T.readFile filename
    aag@AAG{..} <- hoistEither $ parseOnly aag contents
    lift $ do
        let (cInputs, uInputs) = categorizeInputs symbols inputs
        stToIO $ Cudd.withManagerDefaults $ \m -> do
            setupManager o m
            let ops = constructOps o m
            ss@SynthState{..} <- (if noPart then compileMonolithic else compile) ops cInputs uInputs latches andGates (head outputs)
            res <- solveSafety o ops ss initState safeRegion
            --T.mapM (deref ops) ss
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
    noReord  :: Bool,
    noDeref  :: Bool,
    noSimult :: Bool,
    noEarly  :: Bool,
    noPart   :: Bool,
    filename :: String
}

main = execParser opts >>= run
    where
    opts   = info (helper <*> parser) (fullDesc <> progDesc "Solve the game specified in INPUT" <> O.header "Simple BDD solver")
    parser = Options <$> flag False True (long "quiet"              <> short 'q' <> help "Be quiet")
                     <*> flag False True (long "noreord"            <> short 'r' <> help "Disable reordering")
                     <*> flag False True (long "noderef"            <> short 'd' <> help "Disable dereferencing")
                     <*> flag False True (long "nosimult"           <> short 's' <> help "Disable simultaneous conjunction and quantification")
                     <*> flag False True (long "noearlytermination" <> short 't' <> help "Disable early termination")
                     <*> flag False True (long "noPartitioned"      <> short 'p' <> help "Disable conjunctive partitioning of transition relations")
                     <*> argument O.str (metavar "INPUT")

