# Homomorphic encryption: models, parameters, and endpoints

The library's FHE statements combine three obligations: distributional encryption security, circuit-level correctness with explicit noise control, and native efficiency of encoded operations. GSW arithmetic alone is not the endpoint: the current snapshot contains the decision-LWE-to-leveled and LWE-plus-circular-security-to-full theorems in [Complexity/Crypto/Computational/Homomorphic/GSW/FullyHomomorphic.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Homomorphic/GSW/FullyHomomorphic.lean) [complexitylib][complexitylib].

## Base scheme and concrete assumptions

`LWE.publicMatrixLaw` draws independent uniform `B` and secret `t`, plus independent error entries, and reveals `[B*t+e | B]`. `DecisionLWE` compares the complete row-major binary encoding with the identically shaped uniform matrix against uniform classical strict-PPT distinguishers. This is the exact parameter-family hypothesis used in the reductions; it does not assert worst-case lattice hardness or quantum security.

[abstracts/ComplexityAbstracts/GSWSecurityAbstract.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/GSWSecurityAbstract.lean) exposes the fresh bit-encryption endpoint. Its security parameter `λ` gives `n = λ+1`, binary modulus width `w = 16 + 8*clog₂(λ+1)`, and sample count `m = (n+1)*w + 2λ`. The centered-binomial error distribution and full serialization are explicit. Key generation and encryption have native certificates, and encryption is a total operation on raw public-key words. The theorem gives the staged chosen-message IND-CPA security of this specified family from its decision-LWE assumption; it is not a generic claim that all bounded-noise GSW choices are secure.

The formalization follows the approximate-eigenvector construction of Gentry, Sahai and Waters. The primary ePrint metadata confirms the original construction's matrix-based perspective; the detailed correspondence and parameter adaptations here are grounded in the Lean definitions and their docstrings [gsw13][gsw13].

## Correctness, circuits, and encoding

The implementation separates matrix/gadget algebra, decryption and noise estimates, serialization, circuit evaluation and machine certificates. [Complexity/Crypto/Computational/Homomorphic/GSW/DecryptionCircuit.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Homomorphic/GSW/DecryptionCircuit.lean) constructs the decryption circuit, while [Complexity/Crypto/Computational/Homomorphic/GSW/DecryptionCircuit/PolyTime.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Homomorphic/GSW/DecryptionCircuit/PolyTime.lean) certifies uniform construction. The abstract uses ordinary finite De Morgan circuits, with input/gate references and a charged encoding; circuit description and complete input-ciphertext list belong to the evaluator's input size.

[Homomorphic](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/GSWFHEAbstract.lean#L324) requires correctness on supported fresh encryptions of all circuit inputs and on supported honest keys. It includes exact fresh decryption. `FixedWidths` makes secret/ciphertext lengths independent of the evaluated circuit's size and depth. `DecryptsWith` states decryption-circuit agreement for **all raw words of the declared lengths**, not just honest ciphertexts. `Native` requires keygen, encryption, decryption and evaluation certificates on raw encoded inputs.

This is a fresh-input, single evaluation contract. It does not assert that an already evaluated ciphertext may be fed back as an arbitrary fresh input for unlimited further evaluation, nor does it assert circuit privacy. These limits are explicit in the selected abstract.

## The bootstrappable depth family

The family used for bootstrapping differs from the earlier fresh-security example. In [Complexity/Crypto/Computational/Homomorphic/GSW/DepthParameters.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Homomorphic/GSW/DepthParameters.lean), put `t = 1+clog₂(λ+2)`, `w = 16384*t²`, `n = η = λ+1`, `N = (n+1)*w`, `m = N+2λ`, and `L = 512*t`. The checked noise inequality is

`4*m*η*(N+1)^L < 2^w`.

It leaves enough noise budget for the constructed augmented decryption circuits. The modulus is represented in binary; its value is quasi-polynomial in `λ`, while the encoded widths and supplied parameter schedules have the needed polynomial-time certificates. The concrete constants are formalization parameters, not asserted to be practical cryptographic choices.

The exported [Complexity/Crypto/Computational/Homomorphic/GSW/DepthParameters/Scheme.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Homomorphic/GSW/DepthParameters/Scheme.lean) supplies the base scheme witness. Generic `Homomorphic/KeyChain`, `Layered`, `Leveled` and `FixedKey` modules carry the bootstrapping construction and security reductions. Gentry's bootstrapping paradigm is the mathematical source; the local statement explicitly distinguishes fresh-key chains from a fixed key encrypted under itself [gentry09][gentry09].

## Leveled versus full endpoints

| Endpoint | Hypotheses | What the statement supplies | Important quantifier |
|---|---|---|---|
| [leveled](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/GSWFHEAbstract.lean#L479) | Exact depth-family decision LWE | A depth-indexed family, compact ciphertexts, fresh-input homomorphic correctness and native efficiency | One uniformly constructible decryption-circuit family; `NativeInDepth` uses a single polynomial jointly in unary `λ` and depth |
| [fullyHomomorphic](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/GSWFHEAbstract.lean#L526) | The same LWE plus separate `CircularSecure` | Fixed-key all-circuit scheme with native efficiency, compactness, correctness and chosen-message security | Key generation's complete self-loop law is stated; circular security is not silently derived from LWE |

The leveled theorem proves security at each fixed depth and for every unary-polynomial-time computable depth budget. Its fresh key/encryption marginal is tied to the concrete GSW operations. The rest of its joint key-chain law and evaluation implementation are existential in the human-facing theorem, with explicit witnesses in the bridge. The full theorem specifies the exact self-encryption key law and GSW encryption/decryption; its evaluator remains existential with a supplied implementation witness.

The library also proves quantitative reduction bounds. The abstract intentionally emphasizes asymptotic security and exact functionality rather than exposing the full concrete reduction loss. It should not be cited as a proof of Gentry's exact adversary-runtime comparison without that additional statement.

## Evidence and remaining boundaries

The author inspected the two selected GSW abstracts, their bridge structure, the native PPT definition, LWE law, depth parameters and exported bootstrapping endpoints. Existing tests include [ComplexityTests/Crypto/GSWNative.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/Crypto/GSWNative.lean), [ComplexityTests/Crypto/GSWDepthParameters.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/Crypto/GSWDepthParameters.lean), and [ComplexityTests/Crypto/GSWFullyHomomorphic.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/Crypto/GSWFullyHomomorphic.lean); no new compilation was performed. The supporting matrix/noise arithmetic and every internal reduction were not audited line by line.

There is no claimed worst-case lattice reduction, established hardness for this exact noise family, multi-hop ciphertext-closure theorem, or circuit-privacy theorem. The absence of those claims is an honest endpoint boundary, not a defect discovered by this survey.

[complexitylib]: ../sources.md#complexitylib
[gentry09]: ../sources.md#gentry09
[gsw13]: ../sources.md#gsw13
