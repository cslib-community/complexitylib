/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger, Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger, Anton Kovsharov
-/

-- upstream: local-only (formal abstract library)

import Complexity.Computability.Complexity.FineGrained.CountingNativeEndpoint
import Complexity.Computability.Complexity.FineGrained.CountingNativeModelCount

/-! # Bridge for exact subexponential counting and the ETH refutation

Transfer the unconditional native counting endpoint to the abstract. Its list-of-list CNF
representation, Boolean evaluation, model count, encoding combinators, fine-grained
classes and interpolation scale are definitionally equal to the definitions displayed in
`SubexponentialSATAbstract.lean`. Thus these transfers require no semantic weakening,
additional hypothesis or alternative machine notion. The abstract does not import the native
definitions into its statement surface, and this bridge does not import the abstract.

## Construction provenance

`Cslib.Complexity.CountingNativeEndpoint.exists_declaredCounter` composes uniform disjoint
counting sparsification, the normalized sparse CNF leaf counter and Anton Kovsharov's concrete
bounded-incidence evaluator with its exactness and independent native time/workspace
certificates. Its witnesses are uniform for each width. The external validity guard retains the
original clause width, even though the construction uses `max 2 k` internally. The proof uses
one inner support normalization and one outer declared-variable correction, accounting for
every unused declared variable and all small or zero sizes.
`Cslib.Complexity.CountingNativeEndpoint.exists_modelCounter` restates it on the plain formula by
dense relabeling, with all resource charges referring to `encCNF φ`.

The native endpoint's dense-relabeling argument supplies the decision consequences for formulas
with arbitrary natural labels and the occurring-variable parameter. Its SAT exponent and
ETH/SETH results are transferred directly here. No branch-certificate or exactness premise
remains in any of the four complexity theorems.

The argument follows OpenAI's *The Exponential Time Hypothesis is False*, revised 25 October
2026, Sections 3–6, Proposition 6.4 (pp. 43–44), and Appendices A–B [OpenAI2026ETH], pinned to
`openai/math@7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`. It establishes the interpolation-scale
bound, not the sharper Theorem 1.1 / Appendix D bound. The native port is the joint work recorded
in #1226, including Samuel Schlesinger, Anton Kovsharov, Erik Demaine and the contributing
Codex, Claude and Jetski workers; the machine and encoding foundations include Christian
Reitwiessner's contributions. These transfer proofs reuse that development.
-/

namespace ComplexityAbstracts.SubexponentialSATBridge

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-- The bounded-width model counter on the abstract's underlying list representation. -/
theorem exact_count (k : ℕ) :
    ∃ (count : List (List (ℕ × Bool)) → ℕ) (A e b : ℕ),
      (∀ φ : List (List (ℕ × Bool)), (∀ clause ∈ φ, clause.length ≤ k) →
        count φ = CNF.modelCount φ) ∧
      ComputableInO count encCNF encNat
        (fun φ => ⌈(2 : ℝ) ^ ((A : ℝ) * SubexponentialSAT.interpolationScale (CNF.numVars φ))⌉₊ *
          ((encCNF φ).length + 1) ^ e)
        (fun φ => ((encCNF φ).length + 1) ^ b) :=
  CountingNativeEndpoint.exists_modelCounter k

/-- The exact length of the CNF encoding: one bit per clause, plus `10 + 8 · Nat.size v` bits for
each literal occurrence with variable `v`. -/
theorem length_encCNF (φ : List (List (ℕ × Bool))) :
    (encCNF φ).length = φ.length + (φ.flatten.map fun l => 10 + 8 * Nat.size l.1).sum := by
  have hc (c : List (ℕ × Bool)) : 2 * (encList (encPair encNat encBool) c).length =
      (c.map fun l => 10 + 8 * Nat.size l.1).sum := by
    induction c with
    | nil => rfl
    | cons l c ih =>
      have hl : (encPair encNat encBool l).length = 2 * Nat.size l.1 + 2 := by
        rw [length_encPair, encNat_apply, Nat.size_eq_bits_len]; rfl
      rw [encList_cons, List.length_append, length_frame, hl, List.map_cons, List.sum_cons, ← ih]
      ring
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    change (encList _ (c :: φ)).length = _
    change (encList _ φ).length = _ at ih
    rw [encList_cons, List.length_append, length_frame, ih, List.flatten_cons, List.map_append,
      List.sum_append, ← hc c, List.length_cons]
    ring

/-- The native counter refutes the library's Exponential Time Hypothesis. -/
theorem not_eth : ¬ETH := CountingNativeEndpoint.not_ETH

/-- The native counter refutes the library's Strong Exponential Time Hypothesis. -/
theorem not_seth : ¬SETH := CountingNativeEndpoint.not_SETH

/-- Every fixed-width SAT exponent is zero in the native fine-grained classes. -/
theorem satExponent_eq_zero : ∀ k, satExponent k = 0 :=
  CountingNativeEndpoint.satExponent_eq_zero

end ComplexityAbstracts.SubexponentialSATBridge
