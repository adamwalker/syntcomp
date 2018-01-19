import Data.Monoid 

import Options.Applicative as O
import SimpleBDDSolver.Solver

main = execParser opts >>= run
    where
    opts   = info (helper <*> parser) (fullDesc <> progDesc "Solve the game specified in INPUT" <> O.header "Simple BDD solver")
    parser = Options <$> flag False True (long "quiet"   <> short 'q' <> help "Be quiet")
                     <*> flag False True (long "noreord" <> short 'n' <> help "Disable reordering")
                     <*> flag False True (long "noearly" <> short 'e' <> help "Disable early termination")
                     <*> argument O.str (metavar "INPUT")
