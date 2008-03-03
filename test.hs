main = putStrLn "Hello, World!"

-- main = do { cs <- getContents ; print $ length $ lines cs }

firstNLines n cs = unlines $ take n $ lines cs

-- main = print $ 5 + 2 * 5
rmain = print $ tail [1,2,3]
-- main = tail [1,2,3]

tail [1,2,3]
print [1,2,3,4]

fib 0 = 0
fib 1 = 1
fib n = fib (n-1) + fib (n-2)

