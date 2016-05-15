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
import Control.Arrow
import Control.Monad.Trans.State

import Options.Applicative as O
import Safe
import Data.Attoparsec.Text as P

import qualified Cudd.Imperative as Cudd
import Cudd.Imperative (DDManager, DDNode)
import Cudd.Reorder

import AAG
import BDD

--Compiling the AIG
data VarInfo 
    = CInput
    | UInput
    | Latch Int
    | And Int Int

--Takes a list of state and untracked vars in winning partition
promoteUntracked :: Bool -> Ops s a -> Map Int VarInfo -> [Int] -> StateT (SynthStateDynamic a) (ST s) ()
promoteUntracked quiet ops@Ops{..} varInfoMap bddIndices' = do
    ss@SynthStateDynamic{..} <- get

    --Update the state map
    let bddIndices = filter (flip Map.member revMap) bddIndices'
    when (not quiet) $ lift $ unsafeIOToST $ putStrLn $ "Promoting: " ++ show bddIndices
    let aigIndices =  map (fromJustNote "promoteUntracked" . flip Map.lookup revMap) bddIndices
    res <- mapM (compile ops  varInfoMap) aigIndices 
    ss@SynthStateDynamic{..} <- get
    let stateMap'  =  Map.union stateMap $ Map.fromList $ zip bddIndices res

    --Remove the vars from the untracked cube
    vars           <- lift $ mapM ithVar bddIndices
    cb             <- lift $ computeCube vars
    untrackedCube' <- lift $ bexists cb untrackedCube
    lift $ deref cb
    lift $ deref untrackedCube

    --Update the revMap
    let revMap'    =  Map.filterWithKey (\k v -> notElem k bddIndices) revMap

    --Update the initial state
    conj           <- lift $ computeCube2 vars (replicate (length vars) False)
    initialState'  <- lift $ bAnd conj initialState
    lift $ deref initialState
    lift $ deref conj
    
    --Update the state
    put ss{stateMap = stateMap', initialState = initialState', revMap = revMap', untrackedCube = untrackedCube'}
    return ()

iff :: Bool -> a -> a -> a
iff True  x y = x
iff False x y = y

--The lazy compilation function
compile :: Ops s a -> Map Int VarInfo -> Int -> StateT (SynthStateDynamic a) (ST s) a
compile ops@Ops{..} varInfoMap idx = do
    ss@SynthStateDynamic{..} <- get
    let thisIdx              =  idx `quot` 2
    case Map.lookup idx theMap of
        Just x  -> return x
        Nothing -> do
            case Map.lookup (2 * thisIdx) varInfoMap of
                Nothing          -> lift (unsafeIOToST (putStrLn "error")) >> (return $ error $ "doAndGates: index does not exist: " ++ show (2 * thisIdx))
                Just CInput      -> do
                    res         <- lift $ newVar
                    cInputCube' <- lift $ bAnd cInputCube res
                    lift $ deref cInputCube
                    let theMap' =  Map.insert (2 * thisIdx) res (Map.insert (2 * thisIdx + 1) (neg res) theMap)
                    put ss{theMap = theMap', cInputCube = cInputCube'}
                    return $ iff (even idx) res (neg res)
                Just UInput      -> do
                    res         <- lift $ newVar
                    uInputCube' <- lift $ bAnd uInputCube res
                    lift $ deref uInputCube
                    let theMap' =  Map.insert (2 * thisIdx) res (Map.insert (2 * thisIdx + 1) (neg res) theMap)
                    put ss{theMap = theMap', uInputCube = uInputCube'}
                    return $ iff (even idx) res (neg res)
                Just (Latch updIdx) -> do
                    ss@SynthStateDynamic{..} <- get
                    --Create a new untracked var
                    res                      <- lift newVar
                    let theMap'              =  Map.insert (2 * thisIdx) res $ Map.insert (2 * thisIdx + 1) (neg res) theMap
                    --Update the reverse map
                    idxOfRes                 <- lift $ getIdx res
                    let revMap'              =  Map.insert idxOfRes updIdx revMap
                    --Update the untracked cube
                    untrackedCube'           <- lift $ bAnd untrackedCube res
                    lift $ deref untrackedCube
                    --Update the state
                    put ss{theMap = theMap', revMap = revMap', untrackedCube = untrackedCube'}
                    return $ iff (even idx) res (neg res)
                Just (And x y)   -> do
                    x   <- compile ops varInfoMap x
                    y   <- compile ops varInfoMap y
                    ss@SynthStateDynamic{..} <- get
                    res <- lift $ bAnd x y
                    let theMap' = Map.insert (2 * thisIdx) res (Map.insert (2 * thisIdx + 1) (neg res) theMap)
                    put ss{theMap = theMap'}
                    return $ iff (even idx) res (neg res)

--Synthesis
data SynthStateDynamic a = SynthStateDynamic {
    --Map from AIGER indices to bdds that have been compiled already
    theMap        :: Map Int a,
    --Map from untracked BDD indices to update function AIGER indices
    revMap        :: Map Int Int,
    --Map from state BDD indices to update functions
    stateMap      :: Map Int a,
    untrackedCube :: a,
    cInputCube    :: a,
    uInputCube    :: a,
    initialState  :: a
} deriving (Functor, Foldable, Traversable)

initialDyn :: Ops s a -> SynthStateDynamic a
initialDyn Ops{..} = SynthStateDynamic {..}
    where
    theMap        = Map.fromList [(0, bfalse), (1, btrue)]
    revMap        = Map.empty
    stateMap      = Map.empty
    untrackedCube = btrue
    cInputCube    = btrue
    uInputCube    = btrue
    initialState  = btrue

dumpState :: StateT (SynthStateDynamic a) (ST s) ()
dumpState = do
    SynthStateDynamic{..} <- get
    lift $ unsafeIOToST $ do
        putStrLn "revMap"
        print $ Map.keys revMap 
        putStrLn "stateMap"
        print $ Map.keys stateMap

substitutionArray :: Ops s a -> SynthStateDynamic a -> ST s [a]
substitutionArray Ops{..} SynthStateDynamic{..} = do
    sz <- getSize
    mapM func [0..(sz-1)]
    where 
    func idx = case Map.lookup idx stateMap of
        Nothing    -> ithVar idx
        Just input -> return input

makeMap :: [Int] -> [Int] -> [(Int, Int)] -> [(Int, Int, Int)] -> Map Int VarInfo
makeMap controllableInputs uncontrollableInputs latches ands = Map.unions [cInputMap, uInputMap, latchMap, andMap]
    where
    cInputMap = Map.fromList $ zip controllableInputs   (repeat CInput)
    uInputMap = Map.fromList $ zip uncontrollableInputs (repeat UInput)
    latchMap  = Map.fromList $ map (id *** Latch) latches
    andMap    = Map.fromList $ map (\(x, y, z) -> (x, And y z)) ands

--Leaves untracked vars in place
safeCpre' :: (Show a, Eq a) => Bool -> Ops s a -> SynthStateDynamic a -> [a] -> a -> a -> ST s a
safeCpre' quiet ops@Ops{..} ssd@SynthStateDynamic{..} trel safeRegion s = do
    when (not quiet) $ unsafeIOToST $ print "*"
    scu' <- vectorCompose s trel

    scu <- andAbstract cInputCube (neg safeRegion) scu'
    deref scu'

    s   <- bforall uInputCube scu
    deref scu
    return s

safeCpre :: (Show a, Eq a) => Bool -> Ops s a -> SynthStateDynamic a -> [a] -> a -> a -> ST s a
safeCpre quiet ops@Ops{..} ssd@SynthStateDynamic{..} trel safeRegion s = do
    su  <- safeCpre' quiet ops ssd trel safeRegion s
    res <- bexists untrackedCube su
    deref su
    return res

safeCpreUnderApprox :: (Show a, Eq a) => Bool -> Ops s a -> SynthStateDynamic a -> [a] -> a -> a -> ST s a
safeCpreUnderApprox quiet ops@Ops{..} ssd@SynthStateDynamic{..} trel safeRegion s = do
    su  <- safeCpre' quiet ops ssd trel safeRegion s
    res <- bforall untrackedCube su
    deref su
    return res

fixedPoint :: Eq a => Ops s a -> a -> a -> (a -> ST s a) -> ST s (Maybe a)
fixedPoint ops@Ops{..} initialState start func = do
    res <- func start
    deref start
    win <- initialState `lEq` res
    case win of
        False -> deref res >> return Nothing
        True  -> case (res == start) of
            True  -> return $ Just res
            False -> fixedPoint ops initialState res func 

fixedPointNoEarly :: Eq a => Ops s a -> a -> a -> (a -> ST s a) -> ST s (Maybe a)
fixedPointNoEarly ops@Ops{..} init start func = do
    res <- f start
    win <- init `lEq` res
    case win of
        False -> deref res >> return Nothing
        True  -> return $ Just res
    where 
    f start = do
        res <- func start
        deref start
        case res == start of
            True  -> return res
            False -> f res

pickUntrackedToPromote :: (Eq a) => Ops s a -> a -> ST s (Maybe [Int])
pickUntrackedToPromote Ops{..} x = do
    if x == bfalse then
        return Nothing
    else do
        (lc, _) <- largestCube x
        prime   <- makePrime lc x
        deref lc
        si      <- supportIndices prime
        deref prime
        return $ Just si

solveSafety :: (Eq a, Show a) => Map Int VarInfo -> Options -> Ops s a -> a -> StateT (SynthStateDynamic a) (ST s) Bool
solveSafety varInfoMap options@Options{..} ops@Ops{..} safeRegion = do
    lift $ ref btrue
    ssd  <- get
    func btrue
    where
    func mayWin = do
        ssd@SynthStateDynamic{..} <- get
        trel                      <- lift $ substitutionArray ops ssd
        mayWin'                   <- lift $ if noEarly then fixedPointNoEarly ops initialState mayWin (safeCpre quiet ops ssd trel safeRegion) 
                                                       else fixedPoint        ops initialState mayWin (safeCpre quiet ops ssd trel safeRegion)
        case mayWin' of
            Nothing      -> return False
            Just mayWin' -> do

                let doPromotion = do
                        toPromote <- lift $ do
                            winSU     <- safeCpre' quiet ops ssd trel safeRegion mayWin'
                            mayLose   <- bAnd mayWin' (neg winSU)
                            deref winSU
                            toPromote <- pickUntrackedToPromote ops mayLose
                            deref mayLose
                            return toPromote
                        case toPromote of
                            Just xs -> do
                                promoteUntracked quiet ops varInfoMap xs 
                                func mayWin'
                            Nothing -> return True

                if computeWinUnderApprox then do
                    lift $ ref mayWin'
                    mustWin <- lift $ if noEarlyUnder then fixedPointNoEarly ops initialState mayWin' (safeCpreUnderApprox quiet ops ssd trel safeRegion)
                                                      else fixedPoint        ops initialState mayWin' (safeCpreUnderApprox quiet ops ssd trel safeRegion)
                    case mustWin of 
                        Nothing  -> doPromotion
                        Just win -> lift $ deref win >> return True

                else doPromotion

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
            let ops        = constructOps m
                varInfoMap = makeMap cInputs uInputs latches andGates
            (res, state) <- flip runStateT (initialDyn ops) $ do
                safeRegion <- compile ops  varInfoMap (head outputs)
                solveSafety varInfoMap o ops safeRegion
            unsafeIOToST $ when (not quiet) $ putStrLn $ "Number of untracked vars at termination: " ++ show (length (Map.keys (revMap state)))
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
    quiet                 :: Bool,
    noReord               :: Bool,
    noEarly               :: Bool,
    computeWinUnderApprox :: Bool,
    noEarlyUnder          :: Bool,
    filename              :: String
}

main = execParser opts >>= run
    where
    opts   = info (helper <*> parser) (fullDesc <> progDesc "Solve the game specified in INPUT" <> O.header "Simple BDD solver")
    parser = Options <$> flag False True (long "quiet"       <> short 'q' <> help "Be quiet")
                     <*> flag False True (long "noreord"     <> short 'n' <> help "Disable reordering")
                     <*> flag False True (long "noearly"     <> short 'e' <> help "Disable early termination")
                     <*> flag False True (long "underapprox" <> short 'u' <> help "Compute an under approximation of the winning set and terminate early with WIN if it still contains the initial set")
                     <*> flag False True (long "earlyunder"  <> short 't' <> help "Terminate early when computing the under approx winning set")
                     <*> argument O.str (metavar "INPUT")

