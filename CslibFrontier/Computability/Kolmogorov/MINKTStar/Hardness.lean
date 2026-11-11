/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BPP
public import CslibFrontier.Computability.Complexity.Classes.RP
public import CslibFrontier.Computability.Kolmogorov.MINKTStar.Generator.PolyTime
public import CslibFrontier.Computability.MCSP.PartialHardness.Seeded
import CslibFrontier.Computability.Complexity.Problems.CMMSA.Size
import CslibFrontier.Computability.Kolmogorov.MINKTStar.TruthTable
import CslibFrontier.Computability.Kolmogorov.TimeBounded.Counting
import CslibFrontier.Computability.MCSP.PartialHardness.EvaluatorPolyTime
import CslibFrontier.Computability.MCSP.PartialHardness.Soundness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# `MINKT*` is `NP`-hard under randomized reductions

A special case of [Hirahara2022, Theorem I.2] ("In particular", p. 971), in the library's
one-sided many-one form: every `NP` problem reduces to `MINKT*` by a polynomial-time randomized
reduction with one-sided error. The reduction maps yes-instances to yes-instances always and
no-instances to no-instances with probability at least `2/3`.

The proof composes the `NP`-hardness of `GapCMMSA Δ g 1` (`exists_hard_params`) with a randomized
reduction from `GapCMMSA Δ g 1` to `MINKT*`, `rpReducible_GapCMMSA_MINKTStar`. That reduction
reads the functions of the variables of a CMMSA instance `I` from the random string
(`seededFunctions`) at the scale `λ = λ₀ (|I| + 1)²` and outputs the partial truth table of the
CMMSA construction as a `MINKT*` instance (`toMINKTStar`), with size threshold
`s = sizeBound Δ I λ + c` and step budget `pG s`.

* **Completeness** (`exists_toMINKTStar_mem`): on a yes-instance, every choice of the functions
  gives a yes-instance, because the generator prints a consistent table from a short witness.
* **Soundness** (`exists_three_mul_card_toMINKTStar_mem_le`): on a no-instance, at most a third of
  the choices do, for every step budget. A yes-instance of `MINKT*` gives a Boolean function that
  agrees with the table and whose truth table has time-bounded complexity at most `s`; there are
  fewer than `2 ^ (s + 1)` such functions, and the union bound of the partial MCSP soundness
  count (`exists_three_mul_card_le_of_card_le_two_pow`) applies to them.

## Main results

* `Cslib.Kolmogorov.MINKTStar.exists_three_mul_card_toMINKTStar_mem_le`: the soundness count.
* `Cslib.Kolmogorov.MINKTStar.rpReducible_GapCMMSA_MINKTStar`: the randomized reduction from
  `GapCMMSA`.
* `Cslib.Kolmogorov.MINKTStar.rpHard`: every `NP` problem reduces to `MINKT*`, with the step budget
  and the size threshold in unary (`MINKTStar.enc`).
* `Cslib.Kolmogorov.MINKTStar.NP_subset_BPP_of_mem_BPP`, `NP_subset_coRP_of_mem_coRP`: if `MINKT*`
  is in `BPP` (resp. `coRP`), then so is every `NP` problem.

The statement is the `MINKT*` case of the "In particular" clause of [Hirahara2022, Theorem I.2];
the construction and its analysis are the library's own (route B, as for partial MCSP in issue
#4362). The library's time-bounded complexity counts the steps of the described machine under the
universal machine, where footnote 6 of the source uses a KT-style measure; the soundness count
holds for every step budget, and the completeness needs only some polynomial budget, so the
argument should transfer to that measure, which the library does not formalize. The `(log N)^ε`
inapproximability and the distributional forms of the theorem are not formalized.

## References

* [S. Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*][Hirahara2022]
-/

public section

namespace Cslib.Kolmogorov.MINKTStar

open Cslib.Complexity Cslib.Complexity.PromiseProblem Cslib.PartialMCSP.FromCMMSA
  Turing.MultiTapeTM Finset

open Classical in
/-- **Soundness of the `MINKT*` table.** For an odd `k`, a bias `δ₀ ≤ 1/2` with
`(1 - 2 δ₀)^k ≤ 1/(2 Δ²)`, a gap with `6 log 2 < g (log 2 - H(δ₀))` and every constant `c`, there is
`λ₀ ≥ 1` such that, for every no-instance `I` of `GapCMMSA Δ g 1`, every `λ ≥ λ₀ (|I| + 1)` and
every step budget `t`, the `MINKT*` instance of the CMMSA table with size threshold
`sizeBound Δ I λ + c` is a yes-instance for at most a third of the choices of the functions.

The constant 6 comes from the framing of the witness encoding in `sizeBound`, at most
`(4 θ + 2) λ ≤ 6 θ λ` for `θ ≥ 1`; it does not affect `rpHard`, whose gap is free. This is a library
result (issue #4447). -/
theorem exists_three_mul_card_toMINKTStar_mem_le (Δ k : ℕ) (hk : Odd k) {δ₀ g : ℝ}
    (hδ₀ : 0 ≤ δ₀) (hδ₀' : δ₀ ≤ 1 / 2) (hkδ : (1 - 2 * δ₀) ^ k ≤ 1 / (2 * Δ ^ 2))
    (hg : 6 * Real.log 2 < g * (Real.log 2 - Real.binEntropy δ₀)) (c : ℕ) :
    ∃ lam₀ : ℕ, 1 ≤ lam₀ ∧ ∀ I ∈ (GapCMMSA Δ g 1).no,
      ∀ lam, lam₀ * ((CMMSAInstance.encoding I).length + 1) ≤ lam → ∀ t : ℕ,
        3 * #{f : VarFunctions I lam |
            toMINKTStar I Δ k lam f t (GenWitness.sizeBound Δ I lam + c) ∈ MINKTStar} ≤
          Fintype.card (VarFunctions I lam) := by
  obtain ⟨lam₀, hlam₀, h⟩ := exists_three_mul_card_le_of_card_le_two_pow Δ k hk hδ₀ hδ₀' hkδ 6
    (4 * Δ + 4 + c) (by exact_mod_cast hg)
  refine ⟨lam₀, hlam₀, fun I hI lam hlam t => ?_⟩
  obtain ⟨hwf, -, -⟩ := mem_no_GapCMMSA_one.1 hI
  have hθ : 1 ≤ I.threshold := hwf.threshold_pos
  set N := (CMMSAInstance.encoding I).length
  set s := GenWitness.sizeBound Δ I lam + c
  let F := Finset.univ.filter fun h : BooleanFunction (inputLength I Δ k lam) =>
    timeBoundedAt t (List.ofFn fun i => h ((BitString.equivFin _).symm i)) ≤ s
  have hF : #F ≤ 2 ^ (6 * I.threshold * lam + (4 * Δ + 4 + c) * (N + 1)) := by
    refine (card_filter_timeBoundedAt_truthTable_le_lt _ t s).le.trans
      (Nat.pow_le_pow_right two_pos ?_)
    have hθlam : lam ≤ I.threshold * lam := Nat.le_mul_of_pos_left _ hθ
    simp only [s, GenWitness.sizeBound]
    nlinarith
  refine h I hI N (CMMSAInstance.length_formulas_le I) (CMMSAInstance.length_weights_le I)
    (fun w hw => CMMSAInstance.le_of_mem_weights I hw) lam hlam F hF _ fun f hf => ?_
  obtain ⟨h', hagree, hK⟩ := mk_ofFn_mem_iff_exists_booleanFunction.1 hf
  refine ⟨h', Finset.mem_filter.2 ⟨Finset.mem_univ _, hK⟩, fun x b hx => ?_⟩
  simpa using hagree (BitString.equivFin _ x) b (by simpa using hx)

/-- **`GapCMMSA` reduces to `MINKT*`** by a polynomial-time randomized reduction with one-sided
error, for an odd `k`, a bias `δ₀ ≤ 1/2` with `(1 - 2 δ₀)^k ≤ 1/(2 Δ²)` and a gap with
`6 log 2 < g (log 2 - H(δ₀))`.

The order of choices avoids a circularity. The polynomial `pG` and the constant `c` of the
completeness (`exists_toMINKTStar_mem`) are fixed first: the generator reads `λ` from its witness,
so they do not depend on `λ₀`. The soundness count then gives `λ₀` for this `c`, and holds for
every step budget, so the budget `pG (sizeBound Δ I λ + c)` is admissible. The completeness holds
for every `λ ≥ 1`, so `rpReducible_of_seeded` applies with this `λ₀` alone. This is a library result
(issue #4447). -/
theorem rpReducible_GapCMMSA_MINKTStar {Δ k : ℕ} (hk : Odd k) {δ₀ g : ℝ}
    (hδ₀ : 0 ≤ δ₀) (hδ₀' : δ₀ ≤ 1 / 2) (hkδ : (1 - 2 * δ₀) ^ k ≤ 1 / (2 * Δ ^ 2))
    (hg : 6 * Real.log 2 < g * (Real.log 2 - Real.binEntropy δ₀)) :
    RPReducible CMMSAInstance.encoding enc (GapCMMSA Δ g 1) (ofSet MINKTStar) := by
  obtain ⟨pG, c, -, hyes⟩ := exists_toMINKTStar_mem Δ k
  obtain ⟨lam₀, hlam₀, hno⟩ :=
    exists_three_mul_card_toMINKTStar_mem_le Δ k hk hδ₀ hδ₀' hkδ hg c
  have hfst := ComputableInPolyTime.fst CMMSAInstance.encoding encBits
  have hL := computableInPolyTime_lamOf lam₀ hfst
  have hs := ComputableInPolyTime.unary_add' (GenWitness.computableInPolyTime_sizeBound Δ hfst hL)
    (ComputableInPolyTime.const c)
  refine rpReducible_of_seeded lam₀
    (fun I f => toMINKTStar I Δ k (lamOf lam₀ I) f
      (pG.eval (GenWitness.sizeBound Δ I (lamOf lam₀ I) + c))
      (GenWitness.sizeBound Δ I (lamOf lam₀ I) + c))
    (computableInPolyTime_toMINKTStar Δ k hfst hL
      (computableInPolyTime_seededTables _ hfst (ComputableInPolyTime.snd _ _))
      (fun p => isVarTable_seededTables _ p.1 p.2) ((ComputableInPolyTime.unary_eval pG).comp hs)
      hs)
    (fun I hI f => hyes g 1 I hI _ (one_le_lamOf hlam₀ I) f) fun I hI => ?_
  have hlam : lam₀ * ((CMMSAInstance.encoding I).length + 1) ≤ lamOf lam₀ I :=
    (Nat.mul_le_mul_left _ (Nat.le_self_pow two_ne_zero _)).trans (mul_sq_le_lamOf le_rfl)
  convert hno I hI _ hlam (pG.eval (GenWitness.sizeBound Δ I (lamOf lam₀ I) + c)) using 3
  ext f
  classical
  rw [Finset.mem_filter, Finset.mem_filter]
  simp [ofSet]

/-- **`MINKT*` is `NP`-hard under randomized reductions** [Hirahara2022, Theorem I.2, "In
particular", p. 971]: every `NP` problem reduces to `MINKT*`, with the step budget and the size
threshold in unary (`MINKTStar.enc`), by a polynomial-time randomized many-one reduction with
one-sided error. Yes maps to yes always, and no maps to no with probability at least `2/3`.

The library's variants of the source's statement: the time-bounded complexity counts the steps of
the described machine under the universal machine (`timeBoundedAt`), where footnote 6 of the source
uses a KT-style measure; the reductions are one-sided and many-one, a special case of the source's
randomized polynomial-time reductions; and the proof is the library's own (route B). The
`(log N)^ε` inapproximability and the distributional forms of Theorem I.2 are not claimed. -/
theorem rpHard {α : Type} {encA : α ↪ List Bool} :
    ∀ A ∈ NP encA, RPReducible encA enc (ofSet A) (ofSet MINKTStar) := by
  intro A hA
  obtain ⟨Δ, k, δ₀, g, hk, hδ₀, hδ₀', hkδ, hg, hNP⟩ := exists_hard_params
  exact (hNP encA A hA).trans_rpReducible
    (rpReducible_GapCMMSA_MINKTStar hk hδ₀ hδ₀' hkδ (by linarith [Real.log_pos one_lt_two]))

/-- **If `MINKT*` is in `BPP`, then `NP ⊆ BPP`.** A conditional consequence of `rpHard`
[Hirahara2022, Theorem I.2, "In particular", p. 971]. -/
theorem NP_subset_BPP_of_mem_BPP {α : Type} {encA : α ↪ List Bool}
    (h : MINKTStar ∈ BPP enc) : NP encA ⊆ BPP encA :=
  NP_subset_BPP_of_forall_rpReducible rpHard (ofSet_mem_PromiseBPP.mpr h)

/-- **If `MINKT*` is in `coRP`, then `NP ⊆ coRP`.** A conditional consequence of `rpHard`, whose
reduction has one-sided error [Hirahara2022, Theorem I.2, "In particular", p. 971]. -/
theorem NP_subset_coRP_of_mem_coRP {α : Type} {encA : α ↪ List Bool}
    (h : MINKTStar ∈ coRP enc) : NP encA ⊆ coRP encA :=
  NP_subset_coRP_of_forall_rpReducible rpHard (ofSet_mem_PromiseCoRP.mpr h)

end Cslib.Kolmogorov.MINKTStar
