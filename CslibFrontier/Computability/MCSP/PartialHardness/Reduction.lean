/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BPP
public import CslibFrontier.Computability.Complexity.Classes.RP
public import CslibFrontier.Computability.MCSP.PartialHardness.Seeded
import CslibFrontier.Computability.Complexity.Problems.CMMSA.Size
import CslibFrontier.Computability.MCSP.PartialHardness.Completeness
import CslibFrontier.Computability.MCSP.PartialHardness.EvaluatorPolyTime
import CslibFrontier.Computability.MCSP.PartialHardness.Soundness

/-!
# Partial MCSP is `NP`-hard under randomized reductions

Hirahara's theorem [Hirahara2022, Theorem I.2]: every `NP` problem reduces to partial MCSP by a
polynomial-time randomized reduction with one-sided error. The reduction maps yes-instances to
yes-instances always and no-instances to no-instances with probability at least `2/3`.

The proof composes the `NP`-hardness of `GapCMMSA Δ g 1` (`exists_hard_params`) with a randomized
reduction from `GapCMMSA Δ g 1` to partial MCSP, `rpReducible_GapCMMSA_PartialMCSP`. That reduction
reads the functions of the variables of a CMMSA instance `I` from the random string
(`seededFunctions`) at the scale `λ = λ₀ (|I| + 1)²` and outputs the partial truth table
`toInstance I Δ k λ P f`.

* **Completeness** (`exists_toInstance_mem_PartialMCSP`): on a yes-instance, every choice of the
  functions gives a yes-instance of partial MCSP.
* **Soundness** (`three_mul_card_toInstance_mem_PartialMCSP_le`): on a no-instance, at most a third
  of the choices do.
* **Polynomial time** (`computableInPolyTime_toInstance`): the output is computed from the instance
  and the tables read from the random string.

## Main results

* `Cslib.PartialMCSP.rpReducible_GapCMMSA_PartialMCSP`: the randomized reduction from `GapCMMSA`.
* `Cslib.PartialMCSP.rpHard`: every `NP` problem reduces to partial MCSP, with the threshold in
  unary (`PartialMCSP.enc`).
* `Cslib.PartialMCSP.rpHard_encBinary`: the same with the threshold in binary.
* `Cslib.PartialMCSP.NP_subset_BPP_of_mem_BPP`, `NP_subset_coRP_of_mem_coRP`: if partial MCSP is in
  `BPP` (resp. `coRP`), then so is every `NP` problem.

The statement is the "In particular" clause of [Hirahara2022, Theorem I.2]; the construction and
its analysis are the library's own (issue #4362, route B). The inapproximability and average-case
forms of the theorem are not formalized.

## References

* [S. Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*][Hirahara2022]
-/

public section

namespace Cslib.PartialMCSP

open Cslib.Complexity Cslib.Complexity.PromiseProblem Cslib.PartialMCSP.FromCMMSA
  Turing.MultiTapeTM Finset

/-- **`GapCMMSA` reduces to partial MCSP** by a polynomial-time randomized reduction with one-sided
error, for an odd `k`, a bias `δ₀ ≤ 1/2` with `(1 - 2 δ₀)^k ≤ 1/(2 Δ²)` and a gap `g` large enough
for the soundness count. This is a library result (issue #4362, route B). -/
theorem rpReducible_GapCMMSA_PartialMCSP {Δ k P : ℕ} (hP : 0 < P) (hk : Odd k) {δ₀ g : ℝ}
    (hδ₀ : 0 ≤ δ₀) (hδ₀' : δ₀ ≤ 1 / 2) (hkδ : (1 - 2 * δ₀) ^ k ≤ 1 / (2 * Δ ^ 2))
    (hg : 8 * (1 + 2 / P) * Real.log 2 < g * (Real.log 2 - Real.binEntropy δ₀)) :
    RPReducible CMMSAInstance.encoding enc (GapCMMSA Δ g 1) (ofSet PartialMCSP) := by
  obtain ⟨lam₁, hyes⟩ := exists_toInstance_mem_PartialMCSP Δ k P hP
  obtain ⟨lam₂, hno⟩ := three_mul_card_toInstance_mem_PartialMCSP_le Δ k P hP hk hδ₀ hδ₀' hkδ hg
  have hfst := ComputableInPolyTime.fst CMMSAInstance.encoding encBits
  refine rpReducible_of_seeded (max lam₁ lam₂)
    (fun I f => toInstance I Δ k (lamOf (max lam₁ lam₂) I) P f)
    (computableInPolyTime_toInstance Δ k P hfst (computableInPolyTime_lamOf _ hfst)
      (computableInPolyTime_seededTables _ hfst (ComputableInPolyTime.snd _ _))
      fun p => isVarTable_seededTables _ p.1 p.2)
    (fun I hI f => hyes g 1 I hI _ ((Nat.mul_le_mul_right _ (le_max_left _ _)).trans
      (mul_sq_le_lamOf (CMMSAInstance.length_formulas_le I))) f)
    fun I hI => ?_
  have h := hno I hI _ (CMMSAInstance.length_formulas_le I) (CMMSAInstance.length_weights_le I)
    (fun w hw => CMMSAInstance.le_of_mem_weights I hw) (lamOf (max lam₁ lam₂) I)
    ((Nat.mul_le_mul_right _ (le_max_right lam₁ lam₂)).trans (mul_sq_le_lamOf le_rfl))
  convert h using 3
  ext f
  classical
  rw [Finset.mem_filter, Finset.mem_filter]
  simp [ofSet]

/-- **Partial MCSP is `NP`-hard under randomized reductions** [Hirahara2022, Theorem I.2,
p. 971]: every problem in `NP` reduces to partial MCSP, with the threshold in unary, by a
polynomial-time randomized reduction with one-sided error. -/
theorem rpHard {α : Type} {encA : α ↪ List Bool} :
    ∀ A ∈ NP encA, RPReducible encA enc (ofSet A) (ofSet PartialMCSP) := by
  intro A hA
  obtain ⟨Δ, k, δ₀, g, hk, hδ₀, hδ₀', hkδ, hg, hNP⟩ := exists_hard_params
  refine (hNP encA A hA).trans_rpReducible
    (rpReducible_GapCMMSA_PartialMCSP one_pos hk hδ₀ hδ₀' hkδ ?_)
  norm_num
  linarith

/-- **Partial MCSP is `NP`-hard under randomized reductions**, with the threshold in binary
(`PartialMCSP.encBinary`) [Hirahara2022, Theorem I.2, p. 971]. -/
theorem rpHard_encBinary {α : Type} {encA : α ↪ List Bool} :
    ∀ A ∈ NP encA, RPReducible encA encBinary (ofSet A) (ofSet PartialMCSP) :=
  fun A hA => (rpHard A hA).trans_polyTimeReducible
    ⟨id, computableInPolyTime_id_enc_encBinary, fun _ h => h, fun _ h => h⟩

/-- **If partial MCSP is in `BPP`, then `NP ⊆ BPP`.** A conditional consequence of `rpHard`
[Hirahara2022, Theorem I.2, p. 971]. -/
theorem NP_subset_BPP_of_mem_BPP {α : Type} {encA : α ↪ List Bool}
    (h : PartialMCSP ∈ BPP enc) : NP encA ⊆ BPP encA :=
  NP_subset_BPP_of_forall_rpReducible rpHard (ofSet_mem_PromiseBPP.mpr h)

/-- **If partial MCSP is in `coRP`, then `NP ⊆ coRP`.** A conditional consequence of `rpHard`, whose
reduction has one-sided error [Hirahara2022, Theorem I.2, p. 971]. -/
theorem NP_subset_coRP_of_mem_coRP {α : Type} {encA : α ↪ List Bool}
    (h : PartialMCSP ∈ coRP enc) : NP encA ⊆ coRP encA :=
  NP_subset_coRP_of_forall_rpReducible rpHard (ofSet_mem_PromiseCoRP.mpr h)

end Cslib.PartialMCSP
