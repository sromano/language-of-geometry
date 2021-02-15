module BinaryChunkLot(min_progs_absolute_C, complexity_C) where
import Data.Char(digitToInt,intToDigit)
import Data.Maybe(fromJust,isJust)
import Data.List(find,sortBy)
import Data.List(elemIndex)
import Data.Ord(comparing)
import Dict(emptyDict,add,addMany)
import Auxiliary(substring,substrings,interleave,split,prefixes,powerset,chunks,substringChunks,splitInChunks)
import Data.List(permutations)


atomic_instrucion_size = 2

data Instr = P0                   |  -- +0
             B                    |  -- B-axis reflection
             Prog :^: Int         |  -- [...]^.. Plain repetition
             Prog :*: (Int,Instr) |  -- [...]^..<..> Repetition with Goto - Type I
             Prog :+: (Int,Instr) |  -- [...]^..{..} Repetition with Goto - Type II
             PR Prog                 -- Prefixes (not used)
             deriving (Eq, Read)

type Prog      = [Instr]
atomic_progs   = [[P0],[B]]
axes           = [B]


-- Instruction size
i_size P0 = atomic_instrucion_size
i_size B  = atomic_instrucion_size


-- Program size
size []                  = 0
size (i:xs)              | any (==[i]) atomic_progs = (i_size i)  + (size xs)
size ((p :^: m):xs)      = (fromIntegral (1+floor (logBase 10 (fromIntegral m)))) + (size p) + (size xs)
size ((PR p):xs)         = 1 + (size p) + (size xs)
size ((p :*: (m,i)):xs)  = (fromIntegral (1+floor (logBase 10 (fromIntegral m)))) + (size p) + (i_size i) + (size xs)
size ((p :+: (m,i)):xs)  = (fromIntegral (1+floor (logBase 10 (fromIntegral m)))) + (size p) + (i_size i) + (size xs)


-- This is how a program is shown on screen. It differs from the actual algebraic type.
instance Show Instr where
    show P0            = "+0"
    show B             = "B"
    show (p :^: m)     = (show p) ++  "^" ++ (show m)
    show (PR p)        = "Pref" ++ (show p)
    show (p :*: (m,i)) = (show p) ++ "^" ++ (show m) ++ "<" ++ (show i) ++ ">"
    show (p :+: (m,i)) = (show p) ++ "^" ++ (show m) ++ "{" ++ (show i) ++ "}"


-- SEMANTICS OF ATOMIC PROGRAMS
-- functions for instructions
f P0  n = n
f B  n = ((1-n)  `mod` 8)

-- inverse functions for instructions
inv P0  n = n
inv B  n = f B n


-- Nesting: maximum number of loop's nesting in a program.
nesting :: Prog -> Int
nesting []                  = 0
nesting (i:xs) | any (==[i]) atomic_progs = nesting xs
nesting ((p :^: m):xs)            = max (1+(nesting p)) (nesting xs)
nesting ((p :+: (m,i)):xs)            = max (1+(nesting p)) (nesting xs)
nesting ((p :*: (m,i)):xs)            = max (1+(nesting p)) (nesting xs)


-- SEMANTICS OF ARBITRARY PROGRAMS: Execution of a program on a given input
exe :: Prog -> Int -> String
exe []                 n = ""
exe (i:xs)             n | any (==[i]) atomic_progs = show (f i n) ++ exe xs (f i n)
exe ((p :^: 1):xs)     n = (exe p n) ++ exe xs (digitToInt (last ep))
                           where ep = (exe p n)
exe ((p :^: m):xs)     n = ep ++ exe ((p :^: (m-1)):xs) (digitToInt (last ep))
                           where ep = (exe p n)
exe ((PR p):xs)        n = pref ++ exe xs (digitToInt (last pref))
                           where pref = concat [take ((length ep)-i) ep | i <- [0..((length ep)-1)]]
                                 ep   = (exe p n)
exe ((p :+: (m,i)):xs) n | any (==[i]) atomic_progs = z ++ exe xs (digitToInt (last z))
                                                       where z = concat [exe p k | k <- (take m (iterate (f i) n))]
exe ((p :*: (m,i)):xs) n | any (==[i]) atomic_progs = ep ++ z ++ exe xs (digitToInt (last z))
                                                       where ep = (exe p n)
                                                             z  = apply ep i (m-1)


-- KOLMOGOROV COMPLEXITY
-- Given a list of programs ps, obtain the shortest ones
shortest_prog ps = rmDup [q | q <- ps, size q == len]
                   where len = minimum [size q | q <- ps]

-- Given a string x and an initial point n, obtain the list of all minimal programs describing x from n.
-- It uses a dictionary with key (string s, starting point n) and value [list of minimal programs computing s from n]
min_prog x n = fromJust ((min_prog' ("0":"1":substringChunks x) emptyDict) (x,n))

-- Given a list of strings and a dictionary dict, it adds to dict all entries (y,n)->[shortest programs computing y from n]
-- for any y in the list of trings and any possible value for n from 0 to 1
min_prog' []     dict = dict
min_prog' (y:ys) dict = min_prog' ys new_dict
                        where new_dict = addMany [((y,n) , (min_prog'' y n dict)) | n <- [0..1]] dict

-- It gives the shortest programs describing y at n (needs dictionary dict to do it as dynamic programming)
min_prog'' y n dict | length y == 1 = shortest_prog [q | q <- atomic_progs, (exe q n) == y]
                    | otherwise     = shortest_prog (rmDup (a ++ b ++ c ++ d))
                                      where a = min_prog_concat y n dict
                                            b = min_prog_repeat y n dict
                                            c = min_prog_C      y n dict
                                            d = min_prog_D      y n dict


min_prog_concat y n dict = [p1++p2 | (z1,z2) <- (splitInChunks y), p1 <- fromJust (dict (z1, n)), p2 <- fromJust (dict (z2, digitToInt (last z1)))]

min_prog_repeat y n dict = [[p:^: ((length y) `div` d)] | d <- [1..(length y)-1], isJust (dict ((take d y),n)), d == 1 || elem (take d y) (map fst (splitInChunks y)), p <- fromJust (dict ((take d y),n)), (length y) `mod` d == 0, y == (exe [p:^: ((length y) `div` d)] n)]

min_prog_C y n dict =[[p :*: (((length y) `div` d), i)] | d <- [1..(length y)-1], [i] <- atomic_progs, isJust (dict ((take d y),n)), d == 1 || elem (take d y) (map fst (splitInChunks y)), p <- (fromJust (dict ((take d y),n))), (length y) `mod` d == 0, y == (exe [p :*: (((length y) `div` d), i)] n) ]

min_prog_D y n dict =[[p :+: (((length y) `div` d), i)] | d <- [1..(length y)-1], [i] <- atomic_progs, isJust (dict ((take d y),n)), d == 1 || elem (take d y) (map fst (splitInChunks y)), p <- (fromJust (dict ((take d y),n))), (length y) `mod` d == 0, y == (exe [p :+: (((length y) `div` d), i)] n) ]

--
---- It gives either empty or a singleton list consisting of the minimum prefix-like program describing y from n
--min_prog_pref y n dict = if (null l) then [] else [head l]
--                         where l   = [q z | z <- (prefixes y), y == (exe (q z) n)]
--                               q z = [PR (fromJust (dict (z,n)))]






min_progs_absolute_C = min_progs_absolute''''

-- Given a string x:xs, outputs: string; Kolmogorov complexity of x:xs ; list of minimal programs describing x:xs
min_progs_absolute (x:xs) = (x:xs) ++ " ; complexity = " ++ (show len) ++ " \n " ++ concat [(show q) ++ " \n " | q <- ps]
                            where len = size (ps !! 0)
                                  ps  = min_prog (x:xs) (digitToInt x)
                                  ns  = [(nesting q) | q <- ps]


-- Same as before, with other format
min_progs_absolute' (x:xs) = "K(" ++ (x:xs) ++ ") = " ++ (show len) ++ "\nMinimal program(s) starting at " ++ (show x) ++ ":\n" ++ concat ["   " ++ (show q) ++ "\n" | q <- ps]
                             where len = size (ps !! 0)
                                   ps  = min_prog (x:xs) (digitToInt x)


-- Outputs the Kolmogorov complexity of a given string x:xs, and the number of minimal programs describing x:xs
complexity_C (x:xs) = (x:xs) ++ " ; " ++ (show len) ++ " ; " ++ (show (length ps))
                            where len = size (ps !! 0)
                                  ps  = min_prog (x:xs) (digitToInt x)


-- To be used in database creation
min_progs_absolute'' (x:xs) = (x:xs) ++ " ; " ++ (show len)
                            where len = size (ps !! 0)
                                  ps  = min_prog (x:xs) (digitToInt x)


-- Given a string x:xs, outputs: string; Kolmogorov complexity of x:xs ; list of minimal programs describing x:xs with nesting
min_progs_absolute''' (x:xs) = (x:xs) ++ " ; " ++ (show len) ++ " ; " ++ concat [(show q) ++ " " ++ (show (nesting q)) ++ " ; " | q <- ps]
                            where len = size (ps !! 0)
                                  ps  = min_prog (x:xs) (digitToInt x)


-- Given a string x:xs, outputs: string; Kolmogorov complexity of x:xs ; min nesting among all minimal programs ; ; max nesting among all minimal programs ; list of minimal programs describing x:xs
min_progs_absolute'''' (x:xs) = (x:xs) ++ " ; " ++ (show len) ++ " ; " ++ (show (minimum ns)) ++ " ; " ++ (show (maximum ns)) ++ " \n " ++ concat [(show q) ++ " \n " | q <- ps]
                              where len = size (ps !! 0)
                                    ps  = min_prog (x:xs) (digitToInt x)
                                    ns  = [(nesting q) | q <- ps]





parse [] = ""
parse (' ':xs)     = parse xs
parse ('[':xs)     = "["  ++ parse xs
parse (']':xs)     = "]"  ++ parse xs
parse (',':xs)     = ","  ++ parse xs
parse ('+':'0':xs) = "P0" ++ parse xs
parse ('B':xs)     = "B"  ++ parse xs
parse ('^':xs)     = parse_rep xs ""
parse ('>':xs)     = ")" ++ (parse xs)
parse ('}':xs)     = ")" ++ (parse xs)

parse_rep ('<':xs) acum = " :*: (" ++ acum ++ "," ++ (parse xs)
parse_rep ('{':xs) acum = " :+: (" ++ acum ++ "," ++ (parse xs)

parse_rep (',':xs) acum = " :^: " ++ acum ++ "," ++ (parse xs)
parse_rep (']':xs) acum = " :^: " ++ acum ++ "]" ++ (parse xs)
parse_rep (x:xs) acum = parse_rep xs (acum ++ [x])

exe' :: String -> Int -> String
exe' s n = s ++ "(" ++ (show n) ++ ") = " ++ (exe p n) ++ "\nsize(" ++ s ++ ") = " ++ (show (size p))
           where p = (read (parse s))::Prog

rmDup [] = []
rmDup (x:xs) = x : rmDup (filter (\y -> not(x == y)) xs)


apply x i 0 = []
apply x i m = y ++ apply y i (m-1)
              where y = [intToDigit (f i (digitToInt c)) | c <- x]

-- size []              = 0
-- size (i:xs)          | any (==[i]) atomic_progs = (i_size i)  + (size xs)
-- size ((p :^: m):xs  )  = (1+floor (logBase 10 (fromIntegral m))) + (size p) + (size xs)
-- size ((PR p):xs)     = 1 + (size p) + (size xs)
-- size ((p :*: (m,i)):xs)  = (1+floor (logBase 10 (fromIntegral m))) + (size p) + (i_size i) + (size xs)
-- size ((p :+: (m,i)):xs)  = (1+floor (logBase 10 (fromIntegral m))) + (size p) + (i_size i) + (size xs)

writeAllDict dict []     = []
writeAllDict dict ((x,n):xs) = (x,size ((fromJust (dict (x,n)))!!0)) : (writeAllDict dict xs)

sortByLength :: [[a]] -> [[a]]
sortByLength xs = sortBy (comparing length) xs


subs_of_length l = concat (map (\x -> permutations x) (filter (\x -> length x == l) (powerset ['0','1','2','3','4','5','6','7'])))
subs_starting_in_zero_of_length l = map (\x -> "0"++x) (concat (map (\x -> permutations x) (filter (\x -> length x == (l-1)) (powerset ['1','2','3','4','5','6','7']))))

subs_of_length_up_to_eight_starting_in_zero = (subs_starting_in_zero_of_length 1) ++ (subs_starting_in_zero_of_length 2) ++ (subs_starting_in_zero_of_length 3) ++ (subs_starting_in_zero_of_length 4) ++ (subs_starting_in_zero_of_length 5) ++ (subs_starting_in_zero_of_length 6) ++ (subs_starting_in_zero_of_length 7) ++ (subs_starting_in_zero_of_length 8)
