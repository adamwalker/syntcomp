{-# LANGUAGE RecordWildCards, OverloadedStrings #-}

module SimpleBDDSolver.AAG where

import Control.Monad
import Control.Applicative

import Data.Attoparsec.Text as P

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
    return AAG {..}

