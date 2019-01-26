-- |
-- Module: Sandbox.DiscreetLogContracts
--
-- An implementation of https://adiabat.github.io/dlc.pdf

{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Sandbox.DiscreetLogContracts where


import           Control.Arrow
import           Crypto.ECC.Edwards25519 as Ed25519
import           Crypto.Error            as CE
import           Crypto.Hash             as Hash
import           Data.ByteArray          as BA
import           Data.ByteString         as BS
import           Data.ByteString.Char8   as BS8
import           Data.List               as List
import           Data.Vector             as Vector
import           Data.Word               as W


-- ~~~~~~~~~~~~~~~~~~~ --
-- Data models & setup --
-- ~~~~~~~~~~~~~~~~~~~ --


newtype Alice a = A a
newtype Bob a = B a


data Signature
    = Signature
    { pubKey  :: Point
    , message :: ByteString
    , valueR  :: Point
    , valueS  :: Scalar
    } deriving (Eq, Show)


newtype Value = Value Word32
    deriving (Eq, Ord, Show)


newtype Index = Index Word32
    deriving (Eq, Ord, Show)


data Script
    = Sig Point
    | Or Script Script
    | And Script Script
    | TimeLock Word32 Script
    deriving (Eq, Show)


newtype Output = Output (Script, Value)
    deriving (Eq, Show)


data Transaction = Transaction { txInputs :: [ (Output, Index, [Signature]) ], txOutputs :: [ Output ] }
    deriving (Eq, Show)


data ContractParams
    = ContractParams
    { oracleKey       :: Point
    , contractNonce   :: Point
    , contractOptions :: Vector ByteString
    } deriving Eq


hash256 :: ByteString -> ByteString
hash256 = BA.convert . hashWith SHA3_256


scalarHash = throwCryptoError . scalarDecodeLong . hash256

signature ::
       Scalar
    -- ^ private signing key
    -> Scalar
    -- ^ nonce
    -> ByteString
    -- ^ message
    -> Signature
signature priv r msg = Signature (toPoint priv) msg vR s

    where

    vR = toPoint r
    h = scalarHash $ pointEncode vR <> msg
    s = r `scalarAdd` (h `scalarMul` priv)


isValidSignature :: Signature -> Bool
isValidSignature Signature{..} = toPoint valueS == valueR `pointAdd` (h `pointMul` pubKey)

    where

    h = scalarHash $ pointEncode valueR <> message


outputSignature ::
       Scalar
    -- ^ private signing key
    -> Scalar
    -- ^ nonce
    -> Output
    -> Index
    -> Signature
outputSignature priv r (Output (script, value)) index =
    signature priv r $ BS8.pack $ show (script, index)


-- | Check whether a list of signatures satisfies some branch of the script
runScript :: Script -> Index -> [Signature] -> Bool
runScript script index sigs = go script

    where

    go = \case
        Sig pub ->
            let f sig =
                    isValidSignature sig &&
                    pubKey sig == pub &&
                    message sig == BS8.pack (show (script, index))
            in
            List.any f sigs
        TimeLock _ branch   -> go branch
        And branchL branchR -> go branchL && go branchR
        Or branchL branchR  -> go branchL || go branchR


isValidTransaction :: Transaction -> Bool
isValidTransaction Transaction{..} = balanced && List.all signed txInputs

    where

    inputValue (Output (_, Value v), _, _) = v
    outputValue (Output (_, Value v)) = v

    balanced = List.sum (inputValue <$> txInputs) == List.sum (outputValue <$> txOutputs)

    signed (Output (script, _), index, sigs) = runScript script index sigs


-- ~~~~~~~~~~~~~~~~~~~~~~ --
-- Discreet log contracts --
-- ~~~~~~~~~~~~~~~~~~~~~~ --


-- | Generate the secret that the contract participants will use to choose a
-- branch
oracleChoice ::
       Scalar
    -- ^ oracle private key
    -> Scalar
    -- ^ contract private nonce
    -> ContractParams
    -> Int
    -- ^ outcome index
    -> Maybe Scalar
oracleChoice pk r ContractParams{..} i = decision' <$> contractOptions Vector.!? i

    where

    decision' x =
        let h = scalarHash $ pointEncode contractNonce <> x in
        r `scalarAdd` (h `scalarMul` pk)


-- | Calculate the offsets to use when setting up the contracts
contractPoints :: ContractParams -> Vector Point
contractPoints ContractParams{..} = f <$> contractOptions

    where

    f x =
        let h = scalarHash $ pointEncode contractNonce <> x in
        contractNonce `pointAdd` ( h `pointMul` oracleKey )


-- | Each outcome corresponds to a transaction that Alice and Bob sign
contractBranch :: (Alice Point, Value) -> (Bob Point, Value) -> Point -> (Alice Output, Bob Output)
contractBranch (A pka, qa) (B pkb, qb) s = (A $ Output (scriptA, qa), B $ Output (scriptB, qb))

    where

    scriptA = TimeLock 36 (Sig pkb) `Or` Sig (pka `pointAdd` s)
    scriptB = TimeLock 36 (Sig pka) `Or` Sig (pkb `pointAdd` s)


discreetLogContract :: Alice Point -> Bob Point -> ContractParams -> Vector (Value, Value) -> Vector (Alice Output, Bob Output)
discreetLogContract a b params payouts = Vector.zipWith branch payouts $ contractPoints params

    where

    branch (qa, qb) = contractBranch (a, qa) (b, qb)


-- ~~~~~~~~~~~~~~~~~~~~~ --
-- Example contract flow --
-- ~~~~~~~~~~~~~~~~~~~~~ --


example =
    -- Oracle setup
    scalarGenerate >>= \oraclePrivKey ->
    scalarGenerate >>= \nonceVal ->

    -- Alice and bob setup
    scalarGenerate >>= \alicePrivKey ->
    scalarGenerate >>= \bobPrivKey ->

    let params =
            ContractParams
            { oracleKey = toPoint oraclePrivKey
            , contractNonce = toPoint nonceVal
            , contractOptions = Vector.fromList ["option 1", "option 2", "option 3"]
            }

        alicePub = A $ toPoint alicePrivKey
        bobPub = B $ toPoint bobPrivKey

        payouts = Vector.fromList $ (Value *** Value) <$> [ (0, 5), (2, 3), (5, 0) ]

        contract = discreetLogContract alicePub bobPub params payouts
    in

    Vector.mapM_ print (contractOptions params) >>

    -- Choose the option
    read <$> Prelude.getLine >>= \(i :: Int) ->

    -- Generate additional random signing values
    scalarGenerate >>= \aNonce1 ->
    scalarGenerate >>= \aNonce2 ->

    scalarGenerate >>= \bNonce1 ->
    scalarGenerate >>= \bNonce2 ->


    let sharedOutput =
            let A a = alicePub; B b = bobPub in
            Output (Sig a `And` Sig b, Value 5)

        ms = oracleChoice oraclePrivKey nonceVal params i
        mc = contract Vector.!? i

        ix0 = Index 0
        ix1 = Index 1

        -- Transaction spending the shared output
        tx1 (A oa, B ob) = Transaction
            [ (sharedOutput, ix0, [ outputSignature alicePrivKey aNonce1 sharedOutput ix0, outputSignature bobPrivKey bNonce1 sharedOutput ix0]) ]
            [ oa, ob ]

        -- Transaction spending Alice's share
        tx2 s (A oa@(Output (_, v)), _) =
            let A a = alicePub
                scr = Sig a
            in
            Transaction [ (oa, ix1, [ outputSignature (alicePrivKey `scalarAdd` s) aNonce2 oa ix1]) ] [ Output (scr, v) ]

        -- Transaction spending Bob's share
        tx3 s (_, B ob@(Output (_, v))) =
            let B b = bobPub
                scr = Sig b
            in
            Transaction [ (ob, ix1, [ outputSignature (bobPrivKey `scalarAdd` s) bNonce2 ob ix1]) ] [ Output (scr, v) ]

    in

    print (tx1 <$> mc) >>
    print (isValidTransaction . tx1 <$> mc) >>

    print (tx2 <$> ms <*> mc) >>
    print (fmap isValidTransaction $ tx2 <$> ms <*> mc) >>

    print (tx3 <$> ms <*> mc) >>
    print (fmap isValidTransaction $ tx3 <$> ms <*> mc)

