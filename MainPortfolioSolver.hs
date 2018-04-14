import Control.Concurrent.Async
import Options.Applicative as O
import Data.Monoid
import Data.Either

import qualified SimpleBDDSolver.AbsSolver as AS
import qualified SimpleBDDSolver.Solver    as S

data Portfolio
    = P1
    | P2
    | P3

run (fName, portfolio) = do

    res <- case portfolio of
        P1 -> do
            let sOptions  = S.Options  True False False fName
                asOptions = AS.Options True False False False False fName

            either id id <$> race (S.doIt sOptions) (AS.doIt asOptions)

        P2 -> do
            let sOptions  = S.Options  True False False fName
                asOptions = AS.Options True False False True False fName

            either id id <$> race (S.doIt sOptions) (AS.doIt asOptions)

        P3 -> do
            let sOptions   = S.Options  True False False fName
                asOptions  = AS.Options True False False False False fName
                asOptions2 = AS.Options True False False True  False fName

            either id (either id id) <$> race (S.doIt sOptions) (race (AS.doIt asOptions) (AS.doIt asOptions2))

    case res of
        Left err    -> putStrLn $ "Error: " ++ err
        Right True  -> putStrLn "REALIZABLE"
        Right False -> putStrLn "UNREALIZABLE"

main = execParser opts >>= run
    where
    opts           = info (helper <*> parser) (fullDesc <> progDesc "Solve the game specified in INPUT" <> O.header "Simple BDD solver")
    parser         = (,) <$> argument O.str (metavar "INPUT") <*> parsePortfolio
    parsePortfolio 
        =   flag' P1 (short '1' <> long "p1" <> help "Run portfolio 1")
        <|> flag' P2 (short '2' <> long "p2" <> help "Run portfolio 2")
        <|> flag' P3 (short '3' <> long "p3" <> help "Run portfolio 3")
