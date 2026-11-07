/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.LocallyDecodable.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Locally decodable codes are smooth

Katz and Trevisan [KatzTrevisan2000] observed that a local decoder can be made smooth: a
`(q, δ, ε)` local decoder whose queries do not depend on the received word yields a `(q, q / δ, ε)`
smooth decoder (see also [KerenidisDeWolf2004]). The decoder reads at most `q` positions in
expectation, so at most `δ |P|` positions are *heavy*, read more than `q / (δ |P|)` times in
expectation (`Code.card_heavyPositions_le`). The smooth decoder runs the local decoder but answers
the queries to heavy positions itself, from a fixed word `z`, without reading them (`Code.mask`).
Run on the codeword `C x`, it behaves as the local decoder run on the word that agrees with `z`
on the heavy positions and with `C x` elsewhere, which differs from
`C x` on at most `δ |P|` positions, so it still outputs each bit with probability `1 / 2 + ε`; and
it reads no heavy position, while it reads every other position as often as the local decoder,
whose reads do not depend on the word, does against `z`.

The hypothesis that the reads are oblivious (`Code.HasObliviousReads`) holds for every
non-adaptive decoder (`Code.hasObliviousReads_nonadaptive`) and for every decoder making a single
query, adaptive or not (`Code.hasObliviousReads_of_isQueryBounded_one`). Smoothness is measured
here by expected reads, which bounds the probability of reading a position; smoothing adaptive
decoders that make several queries is not covered here.

## Main definitions

* `Cslib.Code.mask`: answer the queries to some positions from a fixed word.
* `Cslib.Code.heavyPositions`: the positions read more often than a threshold.

## Main results

* `Cslib.Code.isSmoothDecoder_mask_heavyPositions`: **local decoders with oblivious reads become
  smooth** after masking their heavy positions [KatzTrevisan2000].
* `Cslib.Code.IsLocalDecoder.isSmoothCode`: a locally decodable code with an oblivious-read
  decoder is smooth.
* `Cslib.Code.IsLocalDecoder.isSmoothCode_of_one`: every one-query locally decodable code is
  smooth.

## References

* [J. Katz, L. Trevisan, *On the efficiency of local decoding procedures for error-correcting
  codes*][KatzTrevisan2000]
* [I. Kerenidis, R. de Wolf, *Exponential lower bound for 2-query locally decodable codes via a
  quantum argument*][KerenidisDeWolf2004]
-/

public section

open scoped ENNReal

namespace Cslib.Code

open OracleComp ProbOracleComp

variable {ι P Γ α : Type} [DecidableEq P]

/-- Answer a query to the position `j` from `z` if `j ∈ H`, and query it otherwise. -/
private noncomputable def maskAnswer (H : Finset P) (z : P → Γ) (j : P) :
    ProbOracleComp (fun _ : P => Γ) Γ :=
  if j ∈ H then pure (z j) else ProbOracleComp.query j

/-- Answer a query to a position of `H` from the word `z`, and pass every other call through. -/
private noncomputable def maskHandler (H : Finset P) (z : P → Γ) :
    (q : ℕ ⊕ P) → ProbOracleComp (fun _ : P => Γ) (probOracleSpec (fun _ : P => Γ) q) :=
  sumHandler (fun n => OracleComp.query (spec := probOracleSpec fun _ : P => Γ) (.inl n))
    (maskAnswer H z)

/-- Run `program`, answering its queries to the positions of `H` from the word `z` instead of
querying them. -/
noncomputable def mask (H : Finset P) (z : P → Γ) (program : ProbOracleComp (fun _ : P => Γ) α) :
    ProbOracleComp (fun _ : P => Γ) α :=
  interpret (maskHandler H z) program

/-- The word that agrees with `z` on `H` and with `y` elsewhere. -/
def splice (H : Finset P) (z y : P → Γ) : P → Γ := fun j => if j ∈ H then z j else y j

section Mask

variable (H : Finset P) (z : P → Γ)

/-- Masking makes no more queries. -/
theorem isQueryBounded_mask {program : ProbOracleComp (fun _ : P => Γ) α} {q : ℕ}
    (hq : program.IsQueryBounded q) : (mask H z program).IsQueryBounded q := by
  refine hq.interpret fun q' => ?_
  cases q' with
  | inl n => exact IsCostBounded.query (Sum.inl n)
  | inr j =>
    change IsCostBounded _ (maskAnswer H z j) 1
    rw [maskAnswer]
    split_ifs
    · exact (IsCostBounded.pure _ 0).mono (Nat.zero_le _)
    · exact IsQueryBounded.query j

private theorem evalWith_maskHandler (y : P → Γ) :
    (fun q' => evalWith (wordOracle y) (maskHandler H z q')) = wordOracle (splice H z y) := by
  funext q'
  cases q' with
  | inl n => exact evalWith_query _ _
  | inr j =>
    change evalWith (wordOracle y) (maskAnswer H z j) = PMF.pure (splice H z y j)
    rw [maskAnswer]
    by_cases hj : j ∈ H
    · rw [ite_eq_left hj, evalWith_pure, splice, ite_eq_left hj]
    · rw [ite_eq_right hj, splice, ite_eq_right hj, ← decodeLaw_eq, decodeLaw_query]

private theorem expectedCost_maskHandler (y : P → Γ) (j : P) (q' : ℕ ⊕ P) :
    expectedCost (wordOracle y) (readCost j) (maskHandler H z q') =
      if j ∈ H then 0 else readCost j q' := by
  cases q' with
  | inl n =>
    change expectedCost (wordOracle y) (readCost j) (OracleComp.query (.inl n)) = _
    rw [expectedCost_query, readCost_inl, ite_self]
  | inr j' =>
    change expectedCost (wordOracle y) (readCost j) (maskAnswer H z j') = _
    rw [readCost_inr, maskAnswer]
    by_cases hj' : j' ∈ H
    · rw [ite_eq_left hj', expectedCost_pure]
      by_cases hj : j ∈ H
      · rw [ite_eq_left hj]
      · rw [ite_eq_right hj, ite_eq_right fun h : j' = j => hj (h ▸ hj')]
    · rw [ite_eq_right hj', ProbOracleComp.query, expectedCost_query, readCost_inr]
      by_cases hj : j ∈ H
      · rw [ite_eq_left hj, ite_eq_right fun h : j' = j => hj' (h ▸ hj)]
      · rw [ite_eq_right hj]

/-- The masked program run against `y` is the program run against `y` spliced with `z` on `H`. -/
theorem decodeLaw_mask (program : ProbOracleComp (fun _ : P => Γ) α) (y : P → Γ) :
    decodeLaw (mask H z program) y = decodeLaw program (splice H z y) := by
  rw [decodeLaw_eq, decodeLaw_eq, mask, evalWith_interpret, evalWith_maskHandler]

/-- The masked program reads no position of `H`, and reads every other position as often as the
program run against the spliced word. -/
theorem expectedReads_mask (program : ProbOracleComp (fun _ : P => Γ) α) (y : P → Γ) (j : P) :
    expectedReads (mask H z program) y j =
      if j ∈ H then 0 else expectedReads program (splice H z y) j := by
  rw [expectedReads_eq, mask, expectedCost_interpret, evalWith_maskHandler]
  by_cases hj : j ∈ H
  · have hcost : (fun q' => expectedCost (wordOracle y) (readCost j) (maskHandler H z q')) = 0 := by
      funext q'
      rw [expectedCost_maskHandler, ite_eq_left hj, Pi.zero_apply]
    rw [hcost, expectedCost_zero, ite_eq_left hj]
  · have hcost : (fun q' => expectedCost (wordOracle y) (readCost j) (maskHandler H z q')) =
        readCost j := by
      funext q'
      rw [expectedCost_maskHandler, ite_eq_right hj]
    rw [hcost, ite_eq_right hj, expectedReads_eq]

/-- The spliced word differs from `y` only on `H`. -/
theorem hammingDist_splice_le [Fintype P] [DecidableEq Γ] (y : P → Γ) :
    hammingDist (splice H z y) y ≤ H.card := by
  refine Finset.card_le_card fun j hj => ?_
  rw [Finset.mem_filter] at hj
  by_contra hjH
  exact hj.2 (by rw [splice, ite_eq_right hjH])

end Mask

/-! ### Heavy positions -/

section Heavy

variable [Fintype P]

/-- The positions that `program`, run against `z`, reads more than `c / |P|` times in
expectation. -/
noncomputable def heavyPositions (program : ProbOracleComp (fun _ : P => Γ) α) (z : P → Γ)
    (c : ℝ) : Finset P :=
  {j | c / (Fintype.card P : ℝ) < (expectedReads program z j).toReal}

/-- **Few positions are heavy**: a program making at most `q` queries reads more than
`q / (δ |P|)` times in expectation at most `δ |P|` positions. -/
theorem card_heavyPositions_le {program : ProbOracleComp (fun _ : P => Γ) α} {q : ℕ}
    (hq : program.IsQueryBounded q) (z : P → Γ) {δ : ℝ} (hδ : 0 < δ) :
    ((heavyPositions program z (q / δ)).card : ℝ) ≤ δ * Fintype.card P := by
  set H := heavyPositions program z (q / δ)
  have hHn : (H.card : ℝ) ≤ Fintype.card P := by exact_mod_cast Finset.card_le_univ H
  set n : ℝ := (Fintype.card P : ℝ)
  set w : P → ℝ := fun j => (expectedReads program z j).toReal
  have hsum : ∑ j, w j ≤ q := by
    have h := sum_expectedReads_le hq z
    have h' := ENNReal.toReal_mono (ENNReal.natCast_ne_top q) h
    rwa [ENNReal.toReal_sum fun j _ => expectedReads_ne_top hq z j, ENNReal.toReal_natCast] at h'
  have hsumH : ∑ j ∈ H, w j ≤ q :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H)
      fun _ _ _ => ENNReal.toReal_nonneg).trans hsum
  by_contra hcon
  rw [not_le] at hcon
  have hn : 0 < n := by nlinarith
  have hne : H.Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast (mul_nonneg hδ.le hn.le).trans_lt hcon
  have hlt : ∑ _j ∈ H, (q / δ / n) < ∑ j ∈ H, w j :=
    Finset.sum_lt_sum_of_nonempty hne fun j hj => (Finset.mem_filter.mp hj).2
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  have hq0 : (0 : ℝ) < q := by
    have : (0 : ℝ) ≤ q / δ / n := div_nonneg (div_nonneg (Nat.cast_nonneg _) hδ.le) hn.le
    nlinarith
  have : (q : ℝ) ≤ H.card * (q / δ / n) := by
    rw [show (H.card : ℝ) * (q / δ / n) = q * (H.card / (δ * n)) by field_simp]
    have : 1 ≤ (H.card : ℝ) / (δ * n) := by
      rw [le_div_iff₀ (mul_pos hδ hn)]
      linarith
    nlinarith
  linarith

end Heavy

/-! ### Smoothing -/

section Smoothing

variable [Fintype P] [DecidableEq Γ]

/-- **Katz–Trevisan smoothing** [KatzTrevisan2000]: a `(q, δ, ε)` local decoder whose
reads do not depend on the received word becomes a `(q, q / δ, ε)` smooth decoder when the queries
to its heavy positions are answered from a fixed word `z` instead. -/
theorem isSmoothDecoder_mask_heavyPositions {C : (ι → Bool) → P → Γ} {q : ℕ} {δ ε : ℝ}
    {A : LocalDecoder ι P Γ} (hA : IsLocalDecoder C q δ ε A) (hobl : ∀ i, HasObliviousReads (A i))
    (hδ : 0 < δ) (z : P → Γ) :
    IsSmoothDecoder C q (q / δ) ε fun i => mask (heavyPositions (A i) z (q / δ)) z (A i) where
  isQueryBounded i := isQueryBounded_mask _ _ (hA.isQueryBounded i)
  correct x i := by
    rw [decodeLaw_mask]
    refine hA.correct x _ i ?_
    exact (Nat.cast_le.mpr (hammingDist_splice_le _ z (C x))).trans
      (card_heavyPositions_le (hA.isQueryBounded i) z hδ)
  smooth x i j := by
    rw [expectedReads_mask]
    split_ifs with hj
    · rw [ENNReal.toReal_zero]
      exact div_nonneg (div_nonneg (Nat.cast_nonneg _) hδ.le) (Nat.cast_nonneg _)
    · rw [(hobl i).expectedReads_eq _ z]
      simpa [heavyPositions] using hj

/-- A locally decodable code with an oblivious-read decoder is smooth. -/
theorem IsLocalDecoder.isSmoothCode {C : (ι → Bool) → P → Γ} {q : ℕ} {δ ε : ℝ}
    {A : LocalDecoder ι P Γ} (hA : IsLocalDecoder C q δ ε A) (hobl : ∀ i, HasObliviousReads (A i))
    (hδ : 0 < δ) : IsSmoothCode C q (q / δ) ε :=
  (isSmoothDecoder_mask_heavyPositions hA hobl hδ (C fun _ => false)).isSmoothCode

end Smoothing

/-! ### Decoders making one query -/

section OneQuery

/-- A program making no query reads no position. -/
theorem expectedReads_eq_zero_of_isQueryBounded_zero {program : ProbOracleComp (fun _ : P => Γ) α}
    (hq : program.IsQueryBounded 0) (y : P → Γ) (j : P) : expectedReads program y j = 0 := by
  rw [expectedReads_eq]
  exact expectedCost_eq_zero_of_isCostBounded _ _ hq fun q' hq' => by
    cases q' with
    | inl n => exact readCost_inl j n
    | inr j' => simp at hq'

omit [DecidableEq P] in
/-- A program making no query has the same output law against every word. -/
theorem decodeLaw_eq_of_isQueryBounded_zero {program : ProbOracleComp (fun _ : P => Γ) α}
    (hq : program.IsQueryBounded 0) (y y' : P → Γ) :
    decodeLaw program y = decodeLaw program y' := by
  induction program using OracleComp.induction with
  | pure a => rw [decodeLaw_pure, decodeLaw_pure]
  | query_bind q' cont ih =>
    obtain ⟨hle, hcont⟩ := IsCostBounded.liftBind_iff.mp hq
    cases q' with
    | inl n =>
      rw [decodeLaw_bind, decodeLaw_bind, decodeLaw_query_inl, decodeLaw_query_inl]
      exact congrArg _ (funext fun a => ih a ((hcont a).mono (by omega)))
    | inr j => simp at hle

/-- **A decoder making one query has oblivious reads**: the position it reads is chosen before it
reads anything. -/
theorem hasObliviousReads_of_isQueryBounded_one {program : ProbOracleComp (fun _ : P => Γ) α}
    (hq : program.IsQueryBounded 1) : HasObliviousReads program := by
  refine hasObliviousReads_iff.mpr fun y y' j => ?_
  suffices h : ∀ n ≤ 1, program.IsQueryBounded n →
      expectedReads program y j = expectedReads program y' j from h 1 le_rfl hq
  clear hq
  intro n hn hqn
  induction program using OracleComp.induction generalizing n with
  | pure a => rw [expectedReads_pure, expectedReads_pure]
  | query_bind q' cont ih =>
    obtain ⟨hle, hcont⟩ := IsCostBounded.liftBind_iff.mp hqn
    rw [expectedReads_query_bind, expectedReads_query_bind]
    cases q' with
    | inl m =>
      congr 1
      exact tsum_congr fun a => congrArg _ (ih a n hn ((hcont a).mono (by simp)))
    | inr j' =>
      have h0 (a : Γ) : ProbOracleComp.IsQueryBounded (cont a) 0 := by
        have h := (hcont a).mono (m := 0) (by simp only [Sum.elim_inr] at hle ⊢; omega)
        exact h
      simp only [expectedReads_eq_zero_of_isQueryBounded_zero (h0 _), mul_zero]

end OneQuery

section Smoothing

variable [Fintype P] [DecidableEq Γ]

/-- **One-query locally decodable codes are smooth** [KatzTrevisan2000]: a
`(1, δ, ε)` local decoder, adaptive or not, yields a `(1, 1 / δ, ε)` smooth decoder. -/
theorem IsLocalDecoder.isSmoothCode_of_one {C : (ι → Bool) → P → Γ} {δ ε : ℝ}
    {A : LocalDecoder ι P Γ} (hA : IsLocalDecoder C 1 δ ε A) (hδ : 0 < δ) :
    IsSmoothCode C 1 (1 / δ) ε := by
  simpa using hA.isSmoothCode (fun i => hasObliviousReads_of_isQueryBounded_one
    (hA.isQueryBounded i)) hδ

end Smoothing

end Cslib.Code
