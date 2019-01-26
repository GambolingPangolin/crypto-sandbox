-- |
-- Module: Sandbox.DiscreetLogContracts
--
-- An implementation of https://adiabat.github.io/dlc.pdf

{-# LANGUAGE RecordWildCards #-}

module Sandbox.DiscreetLogContracts () where


import           Crypto.ECC.Edwards25519 as Ed25519
import           Crypto.Error            as CE
import           Crypto.Hash             as Hash
import           Data.ByteArray          as BA
import           Data.ByteString         as BS
import           Data.Vector             as Vector
import           Data.Word               as W


newtype Alice a = A a
newtype Bob a = B a


data Script
    = Sig Point
    | Or Script Script
    | TimeLock Word32 Script
    deriving Eq


newtype Output = Output (Script, Word32)


data ContractParams
    = ContractParams
    { oracleKey       :: Point
    , contractNonce   :: Point
    , contractOptions :: Vector ByteString
    } deriving Eq


hash256 :: ByteString -> ByteString
hash256 = BA.convert . hashWith SHA3_256


-- | Generate the secret that the contract participants will use to choose a
-- branch
oracleChoice :: Scalar -> Scalar -> ContractParams -> Int -> Maybe Scalar
oracleChoice pk r ContractParams{..} i = decision' <$> contractOptions Vector.!? i

    where

    decision' x =
        let h = throwCryptoError . scalarDecodeLong . hash256 $ pointEncode contractNonce <> x in
        r `scalarAdd` (h `scalarMul` pk)


-- | Calculate the offsets to use when setting up the contracts
contractPoints :: ContractParams -> Vector Point
contractPoints ContractParams{..} = f <$> contractOptions

    where

    f x =
        let r = pointEncode contractNonce
            h = throwCryptoError . scalarDecodeLong . hash256 $ r <> x
        in contractNonce `pointAdd` ( h `pointMul` oracleKey )


-- | Each outcome corresponds to a transaction that Alice and Bob sign
contractBranch :: (Alice Point, Word32) -> (Bob Point, Word32) -> Point -> [Output]
contractBranch (A pka, qa) (B pkb, qb) s = [ Output (scriptA, qa), Output (scriptB, qb) ]

    where

    scriptA = TimeLock 36 (Sig pkb) `Or` Sig (pka `pointAdd` s)
    scriptB = TimeLock 36 (Sig pka) `Or` Sig (pkb `pointAdd` s)


discreetLogContract :: Alice Point -> Bob Point -> ContractParams -> Vector (Word32, Word32) -> Vector [Output]
discreetLogContract a b params payouts = Vector.zipWith branch payouts $ contractPoints params

    where

    branch (qa, qb) = contractBranch (a, qa) (b, qb)
