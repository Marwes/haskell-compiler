module Test where
import Prelude


test :: IO Int
test = do
    let y = primIntAdd 0 2 * 4
    putStrLn "test"
    return y

main :: Int
main = sum [1, 2, 3]


