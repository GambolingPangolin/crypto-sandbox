-- |
-- Module: Sandbox.Paillier
--
-- An implementation of the Paillier cryptosystem

{-# LANGUAGE RecordWildCards #-}

module Sandbox.Paillier where

import           Crypto.Number.Generate
import           Crypto.Number.ModArithmetic
import           Crypto.Number.Prime
import           Crypto.Random
import           Data.Function
import           Sandbox.Number

-- ~~~~~ --
-- Model --
-- ~~~~~ --

data PrivateKey = PrivateKey { λ :: Integer, μ :: Integer }
  deriving Show
data PublicKey = PublicKey { n :: Integer, g :: Integer }
  deriving Show

newtype Ciphertext = Ciphertext Integer
  deriving Show

data PaillierKit m a
  = PaillierKit
  { encrypt :: a -> m Ciphertext
  , decrypt :: PrivateKey -> Ciphertext -> Integer
  , add     :: Ciphertext -> Ciphertext -> Ciphertext
  , scale   :: Integer -> Ciphertext -> Ciphertext
  }


-- ~~~~~~~~ --
-- Main API --
-- ~~~~~~~~ --

-- | Generate an INSECURE Paillier key pair
newKeyPair :: MonadRandom m => Int -> m (PrivateKey, PublicKey)
newKeyPair bw =
  generatePrime bw >>= \p ->
  generatePrime bw >>= \q ->
    if gcd (p*q) ((p-1)*(q-1)) /= 1
      then newKeyPair bw
      else return $ keyPair p q


-- | Apply the decription algorithm
paillierDecrypt :: PrivateKey -> PublicKey -> Ciphertext -> Integer
paillierDecrypt PrivateKey{..} PublicKey{..} (Ciphertext x) =
  let l = paillierL n (expSafe x λ (n^2)) in (l * μ) `mod` n

{-# INLINE paillierDecrypt #-}

-- | Deterministic form of the encryption algorithm
paillierEncrypt :: Integral a => PublicKey -> Integer -> a -> Ciphertext
paillierEncrypt PublicKey{..} r msg =
  Ciphertext $ (expSafe g (toInteger msg) (n^2) * expSafe r n (n^2)) `mod` n^2

{-# INLINE paillierEncrypt #-}


-- | Provides a scope with an embedded public key in which encryption; and
-- addition of ciphertexts is supported
withPaillier :: (MonadRandom m, Integral msg) => PublicKey -> (PaillierKit m msg -> m r) -> m r
withPaillier pub@PublicKey{..} k = k $ PaillierKit e d a s
  where
    e msg = sampleNonce n & fmap (\r -> paillierEncrypt pub r msg)
    d sk c = paillierDecrypt sk pub c
    (Ciphertext x) `a` (Ciphertext y) = Ciphertext $ x * y `mod` n^2
    k `s` (Ciphertext x) = Ciphertext $ expSafe x k (n^2)


-- ~~~~~~~~~ --
-- Tool belt --
-- ~~~~~~~~~ --

paillierL :: Integer -> Integer -> Integer
paillierL n x = (x - 1) `quot` n

{-# INLINE paillierL #-}

-- | Sample an encryption nonce
sampleNonce :: MonadRandom m => Integer -> m Integer
sampleNonce n =
  generateMax (n-1) >>= \r' ->
  let r = r' + 1 in
  if gcd r n == 1
    then return r
    else sampleNonce n

-- | Create a keypair given two input primes
keyPair :: Integer -> Integer -> (PrivateKey, PublicKey)
keyPair p q = (PrivateKey λ μ, PublicKey n g)
  where
    n = p * q
    g = n + 1
    λ = lcm (p-1) (q-1)
    μ = let u = fst $ l `euclideanConj` n in u `mod` n
    l = paillierL n $ expSafe g λ (n^2)

