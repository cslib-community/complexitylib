# Homomorphic encryption: models, parameters, and endpoints

The library's FHE statements combine three obligations: distributional encryption security, circuit-level correctness with explicit noise control, and native efficiency of encoded operations. GSW arithmetic alone is not the endpoint: the current snapshot contains the decision-LWE-to-leveled and LWE-plus-circular-security-to-full theorems in [Complexity/Crypto/Computational/Homomorphic/GSW/FullyHomomorphic.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Homomorphic/GSW/FullyHomomorphic.lean) [complexitylib][complexitylib].

## Base scheme and concrete assumptions

`LWE.publicMatrixLaw` draws independent uniform `B` and secret `t`, plus independent error entries, and reveals `[B*t+e | B]`. `DecisionLWE` compares the complete row-major binary encoding with the identically shaped uniform matrix against uniform classical strict-PPT distinguishers. This is the exact parameter-family hypothesis used in the reductions; it does not assert worst-case lattice hardness or quantum security.

[abstracts/ComplexityAbstracts/GSWSecurityAbstract.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/GSWSecurityAbstract.lean) exposes the fresh bit-encryption endpoint. Its security parameter `λ` gives `n = λ+1`, binary modulus width `w = 16 + 8*clog₂(λ+1)`, and sample count `m = (n+1)*w + 2λ`. The centered-binomial error distribution and full serialization are explicit. Key generation and encryption have native certificates, and encryption is a total operation on raw public-key words. The theorem gives the staged chosen-message IND-CPA security of this specified family from its decision-LWE assumption; it is not a generic claim that all bounded-noise GSW choices are secure.

The formalization follows the approximate-eigenvector construction of Gentry, Sahai and Waters. The primary ePrint metadata confirms the original construction's matrix-based perspective; the detailed correspondence and parameter adaptations here are grounded in the Lean definitions and their docstrings [gsw13][gsw13].

## Correctness, circuits, and encoding

The implementation separates matrix/gadget algebra, decryption and noise estimates, serialization, circuit evaluation and machine certificates. [Complexity/Crypto/Computational/Homomorphic/GSW/DecryptionCircuit.lean](../../Complexity/Crypto/Computational/Homomorphic/GSW/DecryptionCircuit.lean) constructs the decryption circuit, while [Complexity/Crypto/Computational/Homomorphic/GSW/DecryptionCircuit/PolyTime.lean](../../Complexity/Crypto/Computational/Homomorphic/GSW/DecryptionCircuit/PolyTime.lean) certifies uniform construction. The scheme uses finite De Morgan circuits, with input/gate references and a charged encoding; circuit description and complete input-ciphertext list belong to the evaluator's input size.

[Scheme.Correct and Scheme.FixedWidth](../../Complexity/Crypto/Computational/Homomorphic/Basic.lean) state fresh-input correctness and fixed secret/ciphertext lengths. Correctness holds on supported honest keys and pointwise supported fresh encryptions; inputs may repeat ciphertexts or share randomness. [DecryptionCircuits](../../Complexity/Crypto/Computational/Homomorphic/Refresh.lean) requires agreement with decryption on **all raw words of the declared lengths**, including earlier evaluation outputs. Native efficiency is stated separately through `IsPPTOn` and `ComputableInPolyTime` certificates for the encoded operations.

The base correctness contract concerns fresh inputs. The constructed fixed-key scheme has the stronger [FixedKey.evaluate_spec](../../Complexity/Crypto/Computational/Homomorphic/FixedKey/Correctness.lean): inputs may be well-sized ciphertexts from prior evaluations under the same key, and evaluation preserves their plaintext semantics and output width. This does not assert circuit privacy.

## The bootstrappable depth family

The family used for bootstrapping differs from the earlier fresh-security example. In [Complexity/Crypto/Computational/Homomorphic/GSW/DepthParameters.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Homomorphic/GSW/DepthParameters.lean), put `t = 1+clog₂(λ+2)`, `w = 16384*t²`, `n = η = λ+1`, `N = (n+1)*w`, `m = N+2λ`, and `L = 512*t`. The checked noise inequality is

`4*m*η*(N+1)^L < 2^w`.

It leaves enough noise budget for the constructed augmented decryption circuits. The modulus is represented in binary; its value is quasi-polynomial in `λ`, while the encoded widths and supplied parameter schedules have the needed polynomial-time certificates. The concrete constants are formalization parameters, not asserted to be practical cryptographic choices.

The exported [Complexity/Crypto/Computational/Homomorphic/GSW/DepthParameters/Scheme.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Homomorphic/GSW/DepthParameters/Scheme.lean) supplies the base scheme witness. Generic `Homomorphic/KeyChain`, `Layered`, `Leveled` and `FixedKey` modules carry the bootstrapping construction and security reductions. Gentry's bootstrapping paradigm is the mathematical source; the local statement explicitly distinguishes fresh-key chains from a fixed key encrypted under itself [gentry09][gentry09].

## Leveled versus full endpoints

| Endpoint | Hypotheses | What the statement supplies | Important quantifier |
|---|---|---|---|
| [exists_leveled_of_decisionLWE](../../Complexity/Crypto/Computational/Homomorphic/GSW/FullyHomomorphic.lean) | Exact depth-family decision LWE | A constructed `Leveled.scheme` covering every polynomially bounded depth family, with compact ciphertexts, correctness, native efficiency and IND-CPA | One uniformly generated decryption-circuit family and fixed polynomial widths are chosen before the depth family |
| [fullyHomomorphic_of_decisionLWE_of_circularSecure](../../Complexity/Crypto/Computational/Homomorphic/GSW/FullyHomomorphic.lean) | The same LWE plus separate `Encryption.CircularSecure` | The constructed `FixedKey.scheme`, permitting all finite circuits, with native efficiency, compactness, correctness and IND-CPA | One self-loop key is used for every circuit; key generation has no depth parameter |

The leveled theorem chooses an efficiently computable budget dominating the requested polynomially bounded depth family. The separate [Leveled.schemeFamily_spec](../../Complexity/Crypto/Computational/Homomorphic/Leveled/Bootstrapping.lean) supplies joint polynomial runtime in unary security parameter and depth. The constructions themselves are explicit in [Leveled.Basic](../../Complexity/Crypto/Computational/Homomorphic/Leveled/Basic.lean) and [FixedKey.Basic](../../Complexity/Crypto/Computational/Homomorphic/FixedKey/Basic.lean): the former uses a chain of keys, while the latter reuses one key and encryptions of its own secret bits.

The library also proves quantitative reduction bounds in `GSW/FullyHomomorphic.lean` and [Leveled.ExactSecurity](../../Complexity/Crypto/Computational/Homomorphic/Leveled/ExactSecurity.lean). The former uses power-of-two `dyadicSize` sampling. The latter removes that rounding: each key-chain hop has loss `(2 * budget n) * capacity n`, while the unified `exactLeveledAdversary` has loss `3 * (2 * budget n) * capacity n`. Its strict-PPT modular counterpart has an explicit statistical error bound. `exists_leveledAdversary_overhead` supplies polynomial artifact-length bounds and component evaluator witnesses; polynomial boundedness of its composite coin-budget expressions alone does not identify them with the reduction's execution cost.

[Leveled.CoinTape](../../Complexity/Crypto/Computational/Homomorphic/Leveled/CoinTape.lean) makes that execution connection for the modular link reduction's choice stage. Supply a key evaluator whose output on `keyCoins` uniform bits has the original key-generation law. `eval_modLinkAdversary_choose_eq_map_coins` then realizes the original choice using exactly `2 * indexCoins + depth * keyCoins` bits: two selector blocks followed by separate blocks for the generated keys. The selector remains binary decoding modulo the range, including its non-power-of-two bias and zero-range behavior. `exists_modLinkAdversary_choose_coin_evaluator` obtains a polynomial component budget and a native polynomial-time replay certificate directly from strict-PPT key generation. [Checked replay examples](../../ComplexityTests/Crypto/LeveledCoinTape.lean) inspect saved contexts, independent key seeds, modular bias and rejection. The guessing stage's composite execution bound and Gentry's literal loss and multiplicative runtime comparison remain separate obligations; see [#2572](https://github.com/cslib-community/complexitylib/issues/2572).

## Review path and remaining boundaries

Start with the scheme contracts in `Homomorphic/Basic.lean`, then read `Refresh.lean` for the refresh algorithm and its decryption-preservation proof. Next check `GSW/DepthParameters/Scheme.lean` for the concrete bootstrappability premises. Follow `Leveled/Bootstrapping.lean` or `FixedKey/Bootstrapping.lean` to the generic construction, then `GSW/FullyHomomorphic.lean` for the final instantiation. Each property has separate correctness, security or runtime dependencies that can be reviewed in turn.

Existing clients include [GSWNative](../../ComplexityTests/Crypto/GSWNative.lean), [GSWDepthParameters](../../ComplexityTests/Crypto/GSWDepthParameters.lean), and [GSWFullyHomomorphic](../../ComplexityTests/Crypto/GSWFullyHomomorphic.lean). The last checks concrete widths and applies the endpoints to NAND evaluation and shared decryption across depth budgets. The decision-LWE and circular-security premises remain hypotheses in these tests.

These endpoints do not prove a worst-case lattice reduction, hardness for this exact noise family, or circuit privacy. Reviewing the endpoint assembly does not replace reviewing its supporting matrix/noise arithmetic, native certificates and security reductions.

[complexitylib]: ../sources.md#complexitylib
[gentry09]: ../sources.md#gentry09
[gsw13]: ../sources.md#gsw13
