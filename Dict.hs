module Dict(emptyDict,add,addMany) where
import Data.List
import qualified Data.Map as Map

emptyDict = const Nothing

add :: Eq a => a -> b -> (a -> Maybe b) -> (a -> Maybe b)
add key val dict = \k -> if k == key
                         then Just val
                         else dict k

addMany :: Eq a => [(a, b)] -> (a -> Maybe b) -> a -> Maybe b
addMany []         dict = dict
addMany ((a,b):xs) dict = add a b (addMany xs dict)
