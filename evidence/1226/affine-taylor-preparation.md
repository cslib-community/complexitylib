# Paused affine/Taylor slice preparation

Worker: review_560. Paused on the coordinator's new dispatch before any Lean source implementation or build. Reviewed supplier #1236 remains unchanged at `0826c8ba7d1694885ac4343873dff875b62984bc` and is queued. This branch saves design notes only; it is not a mathematical result or a new PR.

Durable proposed contract: https://github.com/cslib-community/complexitylib/issues/1226#issuecomment-6430623796 . Latest claims were checked: no overlap with Jetski's Hermite, parity or replacement-form slices. Existing package/build outputs are untouched; no new worktree/package copy or seeder invocation.

## Remaining implementation

Derive zero constant coefficients directly from scalar Taylor differences; implement the affine row input and full factor product; prove the diagonal map equals the scalar shifted product, then connect coefficient sums to the landed assignment-dependent Möbius identity. Keep any CommRing, full captured baselines, dependent factor variable types and empty cases. Add concrete multi-factor/nonzero-node/characteristic-two controls, then focused validation, coordinated broad checks and outside exact-head source/API review. No quotient-preservation, Hermite reconstruction, native/runtime or ETH claim.

## Inspected APIs

- `MvPolynomial.totalDegree_coeff_eval₂_le` and `totalDegree_coeff_X_mul_map_le` from reviewed #1236.
- `Cslib.BitString.sum_eval_eq_restricted_subsets` from landed #1232.
- `Polynomial.taylor`, `taylor_coeff_zero`, `taylorAlgHom`, `map_taylor`, `finsetSum_coeff`, `coeff_map`.
- `MvPolynomial.eval₂Hom`, `map_eval₂Hom` / `hom_eval₂`, ordinary finite map-sum/product laws.

## Proposed contract (not implemented)

Active bounded §3.4 slice (review_560), before edits: actual affine/Taylor substitutions and their full factor product, equations (3.7)–(3.10), printed/PDF p24 of pinned OpenAI2026ETH (7ef5c0cc; PDF hash unchanged). Reuse current #1236 worktree/cache in a clean child branch, preserving approved 0826c8ba7. No overlap with confluent Hermite reconstruction, parity amplification or replacement-form construction.

Exact proposed contract: any CommRing A, finite coordinate type ι, finite factor set s : Finset F, dependent factor-variable types κ(f), arbitrary factors Φ_f:MvPolynomial κ(f) A, and supplied scalar rows P_fvi:A[T]. For arbitrary node t:A and original Boolean assignment x, define each input as C(C(sum_i P_fvi(t)*bitVal(x_i))) + sum_i C(X_i)*map C(taylor t P_fvi - C(P_fvi(t))). Define G_x as the product over ALL f in s of the corresponding eval₂ Φ_f. Derive—not assume—the zero constant coefficient of every scalar Taylor correction, then prove totalDegree((G_x).coeff j)<=j from #1236. No prepackaged affine/zero-correction result is an unexplained hypothesis.

Define H(T)=sum_x product_f Φ_f(sum_i P_fvi(T)*bitVal(x_i)). Prove diagonal evaluation of G_x equals the corresponding scalar Taylor factor product, so taylor t H = sum_x map(eval_x)G_x. Then for j<=q obtain the actual coefficient identity [z^j]H(t+z)=sum_{E,|E|<=q}sum_{U⊆E}(-1)^(|E|-|U|)sum_{x|E=1}eval(1_U)((G_x).coeff j) using landed #1232. The polynomial inside the restricted sum stays indexed by the ORIGINAL x. This handles assignment-dependent baselines, empty factor/coordinate sets, q=0 and arbitrary characteristic; it does not assert efficient enumeration, truncation/quotient coefficient preservation, interpolation or any native/runtime/ETH result.

Proposed deliverable: one AffineTaylor source/test slice, estimated ~300–700 lines, split/report if it approaches1500. Reuse scalar Polynomial.taylor/taylorAlgHom, coefficient/eval/map APIs, current coefficient-degree closure and Boolean Möbius theorem; no second polynomial framework or global automation registrations. Meaningful controls: nonzero node and nonconstant rows, multiple factors with mixed signs, captured baseline dependence, empty sets, characteristic-two cancellation, and the common-q bound. Focused <=2 threads only; broad lease requested later. Parent #1236 is queued; no new PR/queue action until its disposition and concrete validation.

