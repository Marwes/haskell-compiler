
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

class Num a where
    (+) :: a -> a -> a
    (-) :: a -> a -> a
    (*) :: a -> a -> a

instance Num Int where
    (+) x y = primIntAdd x y
    (-) x y = primIntSubtract x y
    (*) x y = primIntMultiply x y

instance Num Double where
    (+) x y = primDoubleAdd x y
    (-) x y = primDoubleSubtract x y
    (*) x y = primDoubleMultiply x y

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
