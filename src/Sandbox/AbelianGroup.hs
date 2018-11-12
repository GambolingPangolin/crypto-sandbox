-- |
-- Module: Sandbox.AbelianGroup
--

module Sandbox.AbelianGroup where


infixl 7 .*
infixl 6 .+, .-

class AbelianGroup g where
  -- | The additive identity
  zeroG :: g

  -- | A commutative, associative binary operation
  (.+) :: g -> g -> g

  -- | Direct implementation of repeated addition
  (.*) :: Integral a => a -> g -> g

  -- | Additive inverse
  negateG :: g -> g

(.-) :: AbelianGroup g => g -> g -> g
x .- y = x .+ (negateG y)
