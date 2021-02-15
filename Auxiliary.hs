module Auxiliary(substring,substrings,interleave,split,prefixes,powerset,allStringsOfLengthEightStartingInZero,allstrings,chunks,substringChunks,splitInChunks) where

import Data.List (sortBy)
import Data.Function (on)

substring :: [a] -> Int -> Int -> [a]
substring x i j = drop i (take (j+1) x)

substrings :: Eq a => [a] -> [[a]]
substrings x = removeDuplicates [substring x i (i+l) | l <- [0..(length x)-1], i <- [0..(length x)-1-l]]

substringChunks :: Eq a => [a] -> [[a]]
substringChunks y = sortBy (compare `on` length) $ removeDuplicates $ y : (foldr (\(a,b) xs-> (a:b:xs++substringChunks a++substringChunks b)) [] (splitInChunks y))

splitInChunks :: Eq a => [a] -> [([a], [a])]
splitInChunks y | (length $ chunks y ) == 1 = []
                | otherwise = [ splitChunkAt y n | n <- [1..(length $ chunks y)-1]]
                              where splitChunkAt y n = (concat $ take n $ chunks y, concat $ drop n $ chunks y)


chunks :: (Eq a) => [a] -> [[a]]
chunks [] = []
chunks (x:xs) = (x : takeWhile (==x) xs) : chunks (dropWhile (==x) xs)

removeDuplicates :: Eq a => [a] -> [a]
removeDuplicates []     = []
removeDuplicates (x:xs) | any (==x) xs = removeDuplicates xs
                        | otherwise    = x:removeDuplicates xs

interleave :: [t] -> [t] -> [t]
interleave []     []     = []
interleave (x:xs) (y:ys) = x:y:(interleave xs ys)


split :: [a] -> [([a],[a])]
split x = [(splitAt i x) | i <- [1..((length x)-1)]]

prefixes :: [a] -> [[a]]
prefixes x = [take i x | i <- [1..(length x)-1]]

powerset :: [t] -> [[t]]
powerset [] = [[]]
powerset (x:xs) = powerset xs ++ map (x:) (powerset xs)

allstrings :: (Eq t, Num t) => t -> [[Char]]
allstrings 0 = [""]
allstrings n = concat [(map ((++) x) (allstrings (n-1)))  | x <- ["0","1","2","3","4","5","6","7"] ]

allStringsOfLengthEightStartingInZero :: [[Char]]
allStringsOfLengthEightStartingInZero = map ("0" ++) (allstrings 7)
