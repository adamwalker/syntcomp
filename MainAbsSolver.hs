import Data.Monoid

import Options.Applicative as O
import SimpleBDDSolver.AbsSolver

main = execParser opts >>= run
    where
    opts   = info (helper <*> parser) (fullDesc <> progDesc "Solve the game specified in INPUT" <> O.header "Simple BDD solver")
    parser = Options <$> flag False True (long "quiet"       <> short 'q' <> help "Be quiet")
                     <*> flag False True (long "noreord"     <> short 'n' <> help "Disable reordering")
                     <*> flag False True (long "noearly"     <> short 'e' <> help "Disable early termination")
                     <*> flag False True (long "underapprox" <> short 'u' <> help "Compute an under approximation of the winning set and terminate early with WIN if it still contains the initial set")
                     <*> flag False True (long "earlyunder"  <> short 't' <> help "Terminate early when computing the under approx winning set")
                     <*> argument O.str (metavar "INPUT")

