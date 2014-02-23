
data Bool = True | False

not b = case b of
    True -> False
    False -> True

(||) :: Bool -> Bool -> Bool
(||) x y = case x of
    True -> True
    False -> y

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

class Eq a where
    (==) :: a -> a -> Bool
    (/=) :: a -> a -> Bool

instance Eq Bool where
    (==) x y = case x of
        True ->
            case y of
                True -> True
                False -> False
        False ->
            case y of
                True -> False
                False -> True

    (/=) x y = not (x == y)

instance Eq Int where
    (==) x y = primIntEQ x y
    (/=) x y = not (x == y)

instance Eq a => Eq [a] where
    (==) xs ys = case xs of
        : x2 xs2 -> case ys of
            : y2 ys2 -> (x2 == y2) && (xs2 == ys2)
            [] -> False
        [] -> case ys of
            : y2 ys2 -> False
            [] -> True
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

class Fractional a where
    (/) :: a -> a -> a
    fromRational :: Double -> a

instance Fractional Double where
    (/) x y = primDoubleDivide x y
    fromRational x = x

class Integral a where
    div :: a -> a -> a
    rem :: a -> a -> a
    toInteger :: a -> Int

instance Integral Int where
    div x y = primIntDivide x y
    rem x y = primIntRemainder x y
    toInteger x = x

data Ordering = LT | EQ | GT

class Ord a where
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

class Functor f where
    fmap :: (a -> b) -> f a -> f b

instance Functor Maybe where
    fmap f x = case x of
        Just y -> Just (f y)
        Nothing -> Nothing

instance Functor [] where
    fmap = map

otherwise :: Bool
otherwise = True


(.) :: (b -> c) -> (a -> b) -> (a -> c)
(.) f g x = f (g x)

($) :: (a -> b) -> a -> b
($) f x = f x

map :: (a -> b) -> [a] -> [b]
map f xs = case xs of
    : y ys -> f y : map f ys
    [] -> []

foldl :: (b -> a -> b) -> b -> [a] -> b
foldl f x xs = case xs of
    : y ys -> foldl f (f x y) ys
    [] -> x

undefined :: a
undefined = undefined

head :: [a] -> a
head xs = case xs of
    : y ys -> y
    [] -> undefined

tail :: [a] -> [a]
tail xs = case xs of
    : y ys -> ys
    [] -> undefined

sum :: Num a => [a] -> a
sum xs = case xs of
    : y ys -> y + sum ys
    [] -> 0
