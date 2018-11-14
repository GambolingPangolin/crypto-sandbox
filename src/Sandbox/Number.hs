-- |
-- Module: Sandbox.Number
--
-- Numerical algorithms, for fun!

{-# LANGUAGE BangPatterns #-}

module Sandbox.Number where

import           Data.Bits

-- | Given n and x find (u, v) such that u * x + v * n = gcd x n `mod` n
euclideanConj :: Integer -> Integer -> (Integer, Integer)
euclideanConj x n
  | x > n = go (1,0) (0,1)
  | otherwise = go (0,1) (1,0)
  where
    go (!u1, !v1) (!u2, !v2) =
      -- (u1 * x + v1 * n) = u * (u2 * x + v2 * n) + v
      let (u, v) = a `quotRem` b in
      if v > 0
        -- go b v
        then go (u2, v2) (u1 - u * u2, v1 - u * v2)
        else (u2, v2)
      where
        a = u1 * x + v1 * n
        b = u2 * x + v2 * n


-- | modular exponentiation in O(log e) multiplications
expBySquaring :: Integer -> Integer -> Integer -> Integer
expBySquaring !b !e !m
  | e == 0 = 1
  | e == 1 = b `mod` m
  -- e = 2 * k + 1 => b ^ e = b * (b^2)^k
  | e `mod` 2 == 1
  = let r = b * expBySquaring (b * b `mod` m) (e `shiftR` 1) m in r `mod` m
  -- e = 2 * k => b ^ e = (b^2) ^ k
  | otherwise
  = let r = expBySquaring (b * b `mod` m) (e `shiftR` 1) m in r `mod` m
