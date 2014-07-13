module Prelude where

data Bool = True | False

not b = case b of
    True -> False
    False -> True

infixr 2 ||

(||) :: Bool -> Bool -> Bool
(||) True y = True
(||) False y = y

infixr 3 &&

(&&) :: Bool -> Bool -> Bool
(&&) x y = case x of
    True -> y
    False -> False

data Maybe a = Just a | Nothing

maybe :: b -> (a -> b) -> Maybe a -> b
maybe def f m = case m of
    Just x -> f x
    Nothing -> def


data Either a b = Left a | Right b

either :: (a -> c) -> (b -> c) -> Either a b -> c
either l r e = case e of
    Left x -> l x
    Right x -> r x

id x = x


infix 4 ==, /=

class Eq a where
    (==) :: a -> a -> Bool
    (==) x y = not (x /= y)
    (/=) :: a -> a -> Bool
    (/=) x y = not (x == y)

instance Eq Bool where
    (==) True True = True
    (==) False False = True
    (==) x y = False

    (/=) x y = not (x == y)

instance Eq Int where
    (==) x y = primIntEQ x y
    (/=) x y = not (x == y)

instance Eq Double where
    (==) x y = primDoubleEQ x y
    (/=) x y = not (x == y)

instance Eq a => Eq [a] where
    (==) (x:xs) (y:ys) = (x == y) && (xs == ys)
    (==) [] [] = True
    (==) x y = False

    (/=) xs ys = not (xs == ys)

instance Eq a => Eq (Maybe a) where
    (==) x y = case x of
        Just l -> case y of
            Just r -> l == r
            Nothing -> False
        Nothing -> case y of
            Just r -> False
            Nothing -> True

    (/=) x y = not (x == y)

infixl 6 +, -
infixl 7 *

class Num a where
    (+) :: a -> a -> a
    (-) :: a -> a -> a
    (*) :: a -> a -> a
    fromInteger :: Int -> a

instance Num Int where
    (+) x y = primIntAdd x y
    (-) x y = primIntSubtract x y
    (*) x y = primIntMultiply x y
    fromInteger x = x

instance Num Double where
    (+) x y = primDoubleAdd x y
    (-) x y = primDoubleSubtract x y
    (*) x y = primDoubleMultiply x y
    fromInteger x = primIntToDouble x

infixl 7 /

class Fractional a where
    (/) :: a -> a -> a
    fromRational :: Double -> a

instance Fractional Double where
    (/) x y = primDoubleDivide x y
    fromRational x = x

infixl 7 `div`, `rem`

class Integral a where
    div :: a -> a -> a
    rem :: a -> a -> a
    toInteger :: a -> Int

instance Integral Int where
    div x y = primIntDivide x y
    rem x y = primIntRemainder x y
    toInteger x = x

data Ordering = LT | EQ | GT

infix 1 <, >, <=, >=

class Eq a => Ord a where
    compare :: a -> a -> Ordering
    (<) :: a -> a -> Bool
    (>) :: a -> a -> Bool
    (<=) :: a -> a -> Bool
    (>=) :: a -> a -> Bool
    min :: a -> a -> a
    max :: a -> a -> a

instance Ord Int where
    compare x y = case primIntLT x y of
        True -> LT
        False -> case primIntEQ x y of
            True -> EQ
            False -> GT
    (<) x y = case compare x y of
        LT -> True
        EQ -> False
        GT -> False
    (>) x y = case compare x y of
        LT -> False
        EQ -> False
        GT -> True
    (<=) x y = case compare x y of
        LT -> True
        EQ -> True
        GT -> False
    (>=) x y = case compare x y of
        LT -> False
        EQ -> True
        GT -> True
    min x y = case x < y of
        True -> x
        False -> y
    max x y = case x > y of
        True -> x
        False -> y

instance Ord Double where
    compare x y = case primDoubleLT x y of
        True -> LT
        False -> case primDoubleEQ x y of
            True -> EQ
            False -> GT
    (<) x y = case compare x y of
        LT -> True
        EQ -> False
        GT -> False
    (>) x y = case compare x y of
        LT -> False
        EQ -> False
        GT -> True
    (<=) x y = case compare x y of
        LT -> True
        EQ -> True
        GT -> False
    (>=) x y = case compare x y of
        LT -> False
        EQ -> True
        GT -> True
    min x y = case x < y of
        True -> x
        False -> y
    max x y = case x > y of
        True -> x
        False -> y

instance Ord Bool where
    compare False True = LT
    compare True False = GT
    compare _ _ = EQ
    
    (<) x y = case compare x y of
        LT -> True
        EQ -> False
        GT -> False
    (>) x y = case compare x y of
        LT -> False
        EQ -> False
        GT -> True
    (<=) x y = case compare x y of
        LT -> True
        EQ -> True
        GT -> False
    (>=) x y = case compare x y of
        LT -> False
        EQ -> True
        GT -> True
    min x y = case x < y of
        True -> x
        False -> y
    max x y = case x > y of
        True -> x
        False -> y

class Functor f where
    fmap :: (a -> b) -> f a -> f b

instance Functor Maybe where
    fmap f x = case x of
        Just y -> Just (f y)
        Nothing -> Nothing

instance Functor [] where
    fmap = map

infixl 1 >>, >>=

class Monad m where
    (>>=) :: m a -> (a -> m b) -> m b
    return :: a -> m a
    fail :: [Char] -> m a

(>>) :: Monad m => m a -> m b -> m b
(>>) x y = x >>= \_ -> y

instance Monad Maybe where
    (>>=) x f = case x of
        Just y -> f y
        Nothing -> Nothing
    return x = Just x
    fail x = error x

instance Monad [] where
    (>>=) xs f = concat (map f xs)
    return x = [x]
    fail x = error x

class Enum a where
    succ :: a -> a
    pred :: a -> a
    enumFrom :: a -> [a]
    enumFromThen :: a -> a -> [a]
    enumFromTo :: a -> a -> [a]
    enumFromThenTo :: a -> a -> a -> [a]

instance Enum Int where
    succ x = x + 1
    pred x = x - 1
    enumFrom x =
        let
            xs = x : enumFrom (x + 1)
        in xs
    enumFromThen n step = n : enumFromThen (n + step) step
    enumFromTo start stop = case start <= stop of
        True -> start : enumFromTo (start + 1) stop
        False -> []
    enumFromThenTo start step stop = case start <= stop of
        True -> start : enumFromThenTo (start + step) step stop
        False -> []

instance Enum Double where
    succ x = x + 1
    pred x = x - 1
    enumFrom x =
        let
            xs = x : enumFrom (x + 1)
        in xs
    enumFromThen n step = n : enumFromThen (n + step) step
    enumFromTo start stop = case start <= stop of
        True -> start : enumFromTo (start + 1) stop
        False -> []
    enumFromThenTo start step stop = case start <= stop of
        True -> start : enumFromThenTo (start + step) step stop
        False -> []

otherwise :: Bool
otherwise = True

fst :: (a, b) -> a
fst x = case x of
    (y, _) -> y

    
snd :: (a, b) -> b
snd x = case x of
    (_, y) -> y

curry :: ((a, b) -> c) -> a -> b -> c
curry f x y = f (x, y)

uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry f x = case x of
    (y, z) -> f y z

const :: a -> b -> a
const x _ = x

infixr 9 .

(.) :: (b -> c) -> (a -> b) -> (a -> c)
(.) f g x = f (g x)

infixr 0 $, $!, `seq`

($) :: (a -> b) -> a -> b
($) f x = f x

until :: (a -> Bool) -> (a -> a) -> a -> a
until p f x
    | p x = x
    | otherwise = until p f (f x)

map :: (a -> b) -> [a] -> [b]
map f (y:ys) = f y : map f ys
map f [] = []

foldl :: (b -> a -> b) -> b -> [a] -> b
foldl f x (y:ys) = foldl f (f x y) ys
foldl f x [] = x

undefined :: a
undefined = error "undefined"

head :: [a] -> a
head xs = case xs of
    y:ys -> y
    [] -> error "head called on empty list"

last :: [a] -> a
last xs = case xs of
    y:ys -> case ys of
        _:zs -> last ys
        [] -> y
    [] -> error "last called on empty list"

tail :: [a] -> [a]
tail xs = case xs of
    y:ys -> ys
    [] -> error "tail called on empty list"

init :: [a] -> [a]
init xs = case xs of
    y:ys -> case ys of
        _:zs -> y : init ys
        [] -> []
    [] -> error "init called on empty list"

sum :: Num a => [a] -> a
sum xs = case xs of
    y:ys -> y + sum ys
    [] -> 0

infixl 9 !!

(!!) :: [a] -> Int -> a
(!!) xs n = case xs of
    y:ys -> case n of
        0 -> y
        _ -> ys !! (n-1)
    [] -> error "(!!) index to large"

reverse_ :: [a] -> [a] -> [a]
reverse_ xs ys = case xs of
    z:zs -> reverse_ zs (z : ys)
    [] -> ys

reverse :: [a] -> [a]
reverse xs = reverse_ xs []

infixr 5 ++

(++) :: [a] -> [a] -> [a]
(++) xs ys = case xs of
    x2:xs2 -> x2 : (xs2 ++ ys)
    [] -> ys

filter :: (a -> Bool) -> [a] -> [a]
filter p xs = case xs of
    y:ys -> case p y of
        True -> y : filter p ys
        False -> filter p ys
    [] -> []

null :: [a] -> Bool
null xs = case xs of
    y:ys -> False
    [] -> True

length :: [a] -> Int
length xs = case xs of
    _:ys -> 1 + length ys
    [] -> 0

concat :: [[a]] -> [a]
concat xs = case xs of
    y:ys -> y ++ concat ys
    [] -> []


class Show a where
    show :: a -> [Char]

instance Show Bool where
    show x = case x of
        True -> "True"
        False -> "False"

instance (Show a, Show b) => Show (a, b) where
    show x = case x of
        (y, z) -> "(" ++ show y ++ ", " ++ show z ++ ")"

instance Show a => Show (Maybe a) where
    show x = case x of
        Just y -> "Just (" ++ show y ++ ")"
        Nothing -> "Nothing"

data RealWorld = RealWorld

data IO a = IO

instance Monad IO where
    (>>=) x f = io_bind x f
    return = io_return
    fail x = error x


