import Control.Concurrent.Async
import Options.Applicative as O
import Data.Monoid
import Data.Either

import qualified SimpleBDDSolver.AbsSolver as AS
import qualified SimpleBDDSolver.Solver    as S

run fName = do
    let sOptions  = S.Options  True False False fName
        asOptions = AS.Options True False False False False fName

    res <- either id id <$> race (S.doIt sOptions) (AS.doIt asOptions)
    case res of
        Left err    -> putStrLn $ "Error: " ++ err
        Right True  -> putStrLn "REALIZABLE"
        Right False -> putStrLn "UNREALIZABLE"

main = execParser opts >>= run
    where
    opts   = info (helper <*> parser) (fullDesc <> progDesc "Solve the game specified in INPUT" <> O.header "Simple BDD solver")
    parser = argument O.str (metavar "INPUT")
