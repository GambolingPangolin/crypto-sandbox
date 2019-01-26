crypto-sandbox
====

It looks like this is going to be where I gain a toe hold on implementing cryptography.

Paillier cryptosystem
----

```haskell
{-# LANGUAGE RecordWildCards #-}

import Sandbox.Paillier

main :: IO ()
main = newKeyPair 128 >>= \(sk, pk) ->
  withPaillier pk $ \PaillierKit{..} -> do
    let msg1 = 12345
        msg2 = 67890

    -- Encryption
    e1 <- encrypt msg1
    e2 <- encrypt msg2
    print e1

    -- Decryption
    print $ decrypt sk e1

    -- Additive homomorphism
    let e3 = e1 `add` e2
    print $ msg1 + msg2
    print $ decrypt sk e3

    -- Scalar multiplication
    let e4 = 21 `scale` e2
    print $ 21 * msg2
    print $ decrypt sk e4
```

Discreet log contracts
----

[Discreet log contracts][dcl] is a system by which an "oracle" can sign one of 
many messages and other users can use this signature to unlock transaction 
outputs.  See `example` in `src/Sandbox/DiscreetLogContracts.hs` for a worked 
discreet log contract flow.

[dcl]: https://adiabat.github.io/dlc.pdf
