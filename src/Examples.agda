{-# OPTIONS --rewriting #-}

module Examples where

-- Sequential
import Examples.Id
-- import Examples.Gcd
-- import Examples.Queue
import Examples.Sorting.Sequential

-- Parallel
import Examples.TreeSum
import Examples.Exp2
-- import Examples.Sorting.Parallel
import Examples.Scan

-- Amortized Analysis via Coinduction
import Examples.Amortized

-- Effectful
import Examples.Decalf
