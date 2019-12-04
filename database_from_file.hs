-- Takes a filepath as input.
-- The file must contain a list of strings (one string per line)
-- Outputs the complexity of each string and the list of minimal programs for that sequence

import Lot(min_progs_absolute_L)
import BinaryLot(min_progs_absolute_B)
import BinaryChunkLot(min_progs_absolute_C)
import System.IO
import System.Process
import Control.Concurrent
import System.Environment (getArgs)

run mpa arg = do
              content <- readFile arg;
              let linesOfFiles = lines content;
              putStrLn (concat [((mpa x) ++ "\n") | x <- (linesOfFiles)]);

main =  do {
  args <- getArgs;
  case args of
    [] -> error "Must supply a file of sequences and LoT type (\"octagon\",\"binary\", \"chunk\")"

    [arg] -> run min_progs_absolute_L arg
    [arg, "octagon"] -> run min_progs_absolute_L arg
    [arg, "binary"] -> run min_progs_absolute_B arg
    [arg,"chunk"] -> run min_progs_absolute_C arg

    _ -> error "Too many arguments"
  }
