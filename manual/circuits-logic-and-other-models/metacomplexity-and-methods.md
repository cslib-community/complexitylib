# Metacomplexity and general lower-bound methods

Metacomplexity treats a function's representation or truth table as input and asks about the cost of computing that function. Complexitylib separates total tables, partial tables, sample constraints and promise gaps. Its general lower-bound interfaces then connect concrete circuits to covers, approximation schemes and cryptographic distinguishers. [complexitylib][complexitylib]

## MCSP variants and encodings

| Variant | Instance and acceptance |
|---|---|
| [Instance](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/MCSP/Basic.lean#L97) | Arity n, table of exactly `2^n` bits, threshold s; some De Morgan circuit of at most s gates computes the table. |
| [Instance](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/MCSP/Partial.lean#L91) | Table entries are optional booleans; a circuit must agree at every defined position. |
| [Instance](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/MCSP/Succinct.lean#L64) | Finite set of input/output samples; one circuit must satisfy all sample constraints. |
| [GapMCSP](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/MCSP/Basic.lean#L270) | Promise separates complexity at most a lower threshold from complexity above an upper threshold. |

“Succinct” here means a sample-set specification, not an arbitrary circuit encoding of a longer truth table. Partial MCSP supplies both the default all-operation count and a binary AND/OR-only cost measure. The library also distinguishes unary and binary threshold encodings. A theorem stated in function arity n may become a qualitatively different bound when expressed in truth-table length `N=2^n`.

The [partial-MCSP abstract](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/PartialMCSPAbstract.lean) states NP membership and ETH-conditional hardness at the `2^o(n log n)` scale, equivalently `N^o(log log N)`. It preserves the different cost/threshold conventions. At this snapshot the library also contains a separate [native fixed-width SAT counting endpoint](../machines-and-classes/native-counting.md) deriving the negation of ETH. Consequently the historical ETH-conditional implication remains a valid formal theorem, but its premise is false within the combined development. That chapter gives the native encodings, quantitative contract, manuscript mapping and review limits; this interaction affects how the conditional result may be applied and is not a proof inconsistency.

## Hardness magnification

The [magnification abstract](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/MagnificationAbstract.lean) gives decision, no-oracle and size-only specializations. Under `NP subset P/poly`, there is a constant c such that every threshold function s and every arity n admit a decision circuit for the corresponding MCSP slice of size at most `2^n c (n+s(n)+1)^c`; a polynomial threshold yields `2^n c(n+1)^c` after changing c. Contrapositive lower bounds therefore imply `NP` is not contained in P/poly and, through the native containment bridge, `P != NP`.

The [implementation](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/MCSP/Magnification.lean) explicitly maps this version to the cited McKay–Murray–Williams lemma/theorem and explains its stronger lower-bound premise and restricted scope. It uses fixed-threshold witness certificates, binary subcube merging and a polynomial-hierarchy collapse. It should not be cited as every search, oracle or fine quantitative formulation of magnification in the literature.

## Hardness versus randomness

[IsAverageCaseHard](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Circuit/Boolean/HardnessAmplification.lean#L58) says that every Boolean function of De Morgan circuit complexity at most s agrees with a target function on at most a `1/2 + 1/s` fraction of uniformly distributed inputs. Both the gate bound and agreement bound are non-strict. This is a nonuniform circuit predicate, distinct from hardness against uniform probabilistic heuristics. XOR amplification and the Nisan–Wigderson generator use it as an intermediate interface.

The [average-case endpoint](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Classes/BPP/Derandomization.lean#L302) assumes a binary language in native E and a positive natural c such that its n-bit slice satisfies this predicate at size `2^(n/c)` at all sufficiently large lengths, with natural-number division. It proves `P enc = BPP enc` for every supplied instance encoding. The native deterministic decider computes a Nisan–Wigderson generator and enumerates its short seeds. The result credits Nisan and Wigderson. [nisanwigderson94][nisanwigderson94]

The [worst-case endpoint](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Classes/BPP/WorstCaseHardness.lean#L80) assumes instead a native E language and a real `gamma > 0` whose slices require at least `2^(gamma*n)` De Morgan gates at **all sufficiently large lengths**. It derives the same native class equality through Reed–Muller/Hadamard encoding and local list decoding. The endpoint is credited to Impagliazzo and Wigderson, while the source identifies the Sudan–Trevisan–Vadhan proof route. These declarations assume their circuit lower bounds; an infinitely-often hardness hypothesis and simulation variant are not formalized here. [impagliazzowigderson97][impagliazzowigderson97] [sudantrevisanvadhan01][sudantrevisanvadhan01]

The [machine endpoint account](../machines-and-classes/endpoints-and-hierarchies.md#hardness-versus-randomness) states the uniform class side and the literature-check scope. Here the inspected evidence is the circuit-hardness definition, the final theorem statements and their direct native bridge, not an independent reconstruction of the hardness amplification or generator proof.

## Natural proofs and cryptographic assumptions

[NaturalProof.IsLarge](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Circuit/Boolean/NaturalProof.lean#L147) separates largeness, constructivity and usefulness. A property is a family of sets of Boolean functions. Constructivity concerns deciding from a full truth table; polynomial in that input length is exponential in the function's arity. Usefulness excludes every easy language's slices eventually. Largeness is a quantitative density condition.

The Razborov–Rudich barrier is stated through concrete circuit distinguishers: a property excluding a small-circuit keyed family distinguishes its truth tables from uniform random function tables with advantage equal to the property's density. An exponentially secure keyed family prevents a P/poly-natural useful property. A [generator-to-barrier bridge](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Circuit/Boolean/NaturalProof/Generator.lean) uses the GGM construction and its circuit-size analysis. Security is an explicit hypothesis and belongs to the cryptographic model in the [programs section](../programs-crypto-and-probability/index.md), not an unconditional result.

## Lower-bound interfaces beyond one theorem

[Atom](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Circuit/Fusion/Basic.lean#L60) represents a gate together with argument values as an atom and a finite collection of invariant failures as a cover. The central inequality `coverComplexity_le_ecomplexityFrom` lets a combinatorial cover lower bound imply a weighted source-relative circuit lower bound. This factors semantic lower-bound arguments away from a particular syntax traversal.

[SemifilterWitness](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Circuit/Fusion/Semifilter.lean#L127) specializes the argument to monotone truth-valued maps on subsets that preserve the empty and full set. These maps need not preserve intersections, so they are not filters in the usual algebraic sense. Pair covers connect their witness failures to AND complexity, including the conondeterministic model in which both input polarities and OR gates are free.

[Scheme](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Circuit/Approximation.lean#L55) compares exact and approximate interpretations of the same circuit program. A correctness relation can be one-sided; each gate has a finite exception set with bounded cardinality. The approximate value is correct outside the union of gate exceptions, giving a failure bound by total charged cost. A shared gate is charged once even if its output has many uses. This reusable statement supports the monotone approximation method rather than reproving the same union argument for every lower bound.

These are mathematical proof interfaces, not automatically encoded certificates or proof-search procedures. Other reusable measures in the query and formula layers—sensitivity, certificate complexity, degree, Khrapchenko edge counts—play a similar role while using different objects and costs.

## Known Limitations

The conditional statements, truth-table scales and source-specific quantitative scope were inspected, but the complete magnification and cryptographic reduction proofs were not independently reconstructed in this worker pass. Distinguish a valid conditional theorem, a conventional open assumption, and a premise that this same library proves false elsewhere.

[complexitylib]: ../sources.md#complexitylib
[impagliazzowigderson97]: ../sources.md#impagliazzowigderson97
[nisanwigderson94]: ../sources.md#nisanwigderson94
[sudantrevisanvadhan01]: ../sources.md#sudantrevisanvadhan01
