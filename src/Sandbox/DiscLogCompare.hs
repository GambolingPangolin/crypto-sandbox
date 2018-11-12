-- |
-- Module: Sandbox.DiscLogCompare
--
--
-- Comparison of discrete logs in different groups
-- ====
--
-- Let A = <G> and B = <H> be two cyclic groups and X ∈ A, Y ∈ B.  A prover
-- wishes to convince a verifier that she knows an x ∈ Z such that X = x G and
-- Y = x H in zero knowledge.
--
-- This module implements a scheme proposed by Andrew Poelstra for achieving
-- this.  In order for the challenge to be meaningful, the verifier must supply
-- additional group points G' and H' for which the prover cannot solve DLP.

{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}

module Sandbox.DiscLogCompare where

import           Control.Monad.Random
import           Data.Bits
import           Sandbox.AbelianGroup

-- ~~~~~~~~~~~~~~~~ --
-- "Reasonable" API --
-- ~~~~~~~~~~~~~~~~ --

type Prover g1 g2 m = Integer -> m (Proof g1 g2)

withProvingContext :: forall m g1 g2 r. (MonadRandom m, AbelianGroup g1, AbelianGroup g2)
  => Parameters g1
  -> Parameters g2
  -> (Prover g1 g2 m -> m r)
  -> m r
withProvingContext p1 p2 k = k prover
  where
    prover x =
      let bs = binary x
          rawParams = forM bs $ \b -> (b,) <$> (replicateM 6 $ getRandomR (0, _))
      in
      prove p1 p2 _ <$> rawParams


-- ~~~~~~~~~~~~~ --
-- Preliminaries --
-- ~~~~~~~~~~~~~ --

data Parameters g = Parameters { basePoint :: g, pedersenPoint :: g }

type Hash g1 g2 = (g1, g2, g1, g2) -> Integer

newtype Nonce = Nonce Integer

-- | Pedersen commitment with explicit nonce
commitWith :: AbelianGroup g
  => Parameters g
  -> Integer
  -- ^ value
  -> Nonce
  -- ^ nonce
  -> g
commitWith Parameters{..} x (Nonce r) =
  r .* basePoint .+ x .* pedersenPoint


-- | Compute the little endian encoding of an integer
binary :: Integer -> [Bool]
binary x
  | x < 0
  = error "Negative number!"
  | x == 0
  = []
  | otherwise
  = (1 .&. x == 1) : binary (x `shiftR` 1)


-- | Produce nonces having the property that $ sum_i {2^i * r_i} == 0 $
schemeNonces :: MonadRandom m => Int -> m [Nonce]
schemeNonces k = do
  rs <- replicateM (k-1) $ getRandomR (0, _)
  let r0 = -2 * f rs
      f []     = 0
      f (x:xs) = x + 2 * f xs
  return $ Nonce <$> (r0 : rs)


-- | Compute A and A' from the proof
impliedBlinds :: (AbelianGroup g1, AbelianGroup g2)
  => Proof g1 g2
  -> (g1, g2)
impliedBlinds (Proof bs)  = (f (commitment1 <$> bs), f (commitment2 <$> bs))
  where
    -- f [x0, x1, ..., xn] = x0 + 2 * x1 + ... + 2^n * xn
    f xs = g 0 xs
    g _ []     = zeroG
    g i (b:bs) = (2^i) .* b .+ g (i+1) bs


-- ~~~~~~~~~~~~~~~~~~ --
-- Proof construction --
-- ~~~~~~~~~~~~~~~~~~ --

-- | Proof data asserting that the commitments, though in different groups are
-- commitments to the same bit
data BitProof g1 g2
  = BitProof
  { commitment1 :: g1
  , commitment2 :: g2
  , sigE0       :: Integer
  , bitProofA0  :: Integer
  , bitProofA1  :: Integer
  , bitProofB0  :: Integer
  , bitProofB1  :: Integer
  }

-- | Proof data for the assertion that two commitments commit to the same
-- value, despite being in different groups
newtype Proof g1 g2 = Proof [BitProof g1 g2]

-- | The construction requires 4 random parameters
newtype IV = IV (Integer, Integer, Integer, Integer)

-- | Generate a proof that two commitments over different groups commit to the same bit
proveBit :: (AbelianGroup g1, AbelianGroup g2)
  => Parameters g1
  -> Parameters g2
  -> Hash g1 g2
  -> IV
  -> Nonce
  -> Nonce
  -> Bool
  -> BitProof g1 g2
proveBit p1 p2 hash (IV (j,k,a,b)) nr@(Nonce r) ns@(Nonce s) bit = if bit then proof1 else proof0
  where

    -- parameters
    g = basePoint p1
    g' = pedersenPoint p1
    h = basePoint p2
    h' = pedersenPoint p2

    -- commitments
    x = if bit then 1 else 0
    gi = commitWith p1 x nr
    hi = commitWith p2 x ns

    -- We know a discrete log for exactly one of the following:
    -- - x * G + y * g        ... b = 0
    -- - x * G + y * (g - G') ... b = 1
    --
    -- This will determine what we rewrite

    proof0 = BitProof gi hi e0 a (j + r * e1) b (k + s * e1)
      where
        e0 = hash (gi, hi, j .* g, k .* h)
        e1 = hash (gi, hi, a .* g .- e0 .* (gi .- g'), b .* h .- e0 .* (hi .- h'))
    proof1 = BitProof gi hi e0 (j + r * e0) a (k + s * e0) b
      where
        e1 = hash (gi, hi, j .* g, k .* h)
        e0 = hash (gi, hi, a .* g .- e1 .* gi, b .* h .- e1 .* hi)


-- | Prove: ∃ a. A == a * G && A' == a * G'
prove :: (AbelianGroup g1, AbelianGroup g2)
  => Parameters g1
  -> Parameters g2
  -> Hash g1 g2
  -> [(Bool, [Integer])]
  -> Proof g1 g2
prove p1 p2 hash xs = Proof $ f <$> xs
  where
    f (bit, vs) =
      let [j,k,a,b,r,s] = vs in
      proveBit p1 p2 hash (IV (j, k, a, b)) (Nonce r) (Nonce s) bit

-- | Verify: ∃ a. A == a * G && A' == a * G'
verify :: (AbelianGroup g1, AbelianGroup g2)
  => Parameters g1
  -> Parameters g2
  -> Hash g1 g2
  -> Proof g1 g2
  -> Bool
verify p1 p2 hash (Proof bs) = all (verifyBit p1 p2 hash) bs

-- | Verify: ∃a ∈ {0,1}. A = Com(a) && A' = Com'(a)
verifyBit :: (AbelianGroup g1, AbelianGroup g2)
  => Parameters g1
  -> Parameters g2
  -> Hash g1 g2
  -> BitProof g1 g2
  -> Bool
verifyBit p1 p2 hash BitProof{..} = sigE0 == e0
  where
    g = basePoint p1
    g' = pedersenPoint p1
    h = basePoint p2
    h' = basePoint p2

    gi = commitment1
    hi = commitment2
    a0 = bitProofA0
    a1 = bitProofA1
    b0 = bitProofB0
    b1 = bitProofB1

    e1 = hash (gi, hi, a0 .* g .- sigE0 .* gi, b0 .* h .- sigE0 .* hi)
    e0 = hash (gi, hi, a1 .* g .- e1 .* (gi .- g'), b1 .* h .- e1 .* (hi .- h'))

