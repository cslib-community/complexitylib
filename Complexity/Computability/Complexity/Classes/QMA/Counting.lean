/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.QMA
public import Complexity.Computability.Complexity.Classes.PP
public import Complexity.Computability.Circuit.Quantum.AcceptOperator
import Complexity.Computability.Complexity.Classes.BQP.Counting
import Complexity.Computability.Complexity.Classes.PP.Characterization
import Complexity.Computability.Complexity.Classes.SharpP.Aggregation
import Complexity.Computability.Complexity.Classes.SharpP.Products
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Foundations.Data.BitString.Block
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Tactic.PolyTime

/-!
# `QMA ⊆ PP`

For a quantum verifier with `m` witness qubits and `h` Hadamard gates, the trace of the `d`-th
power of its acceptance operator `Q_x` is the integer `traceGap x d` divided by `2^{hd}`
(`Cslib.Quantum.UniformVerifierFamily.re_trace_acceptOp_pow`). That integer is a sum over closed
paths of `d` steps through the `2^m` basis witnesses of products of pair gaps, so for `d`
computed in polynomial time it is a `GapP` function of the instance
(`Cslib.Complexity.traceGap_mem_GapP`). Since `Q_x` is positive, its largest eigenvalue `λ` is the
maximum acceptance probability and `λ^d ≤ tr(Q_x^d) ≤ 2^m λ^d`. With completeness `c` and soundness
`s < c`, a power `d` linear in `m` separates the two cases: for naturals `B, D` with
`s ≤ B / D` and `(B + 1) / D ≤ c` and `d = B (m + 1)`,

* on yes-instances, `tr(Q_x^d) ≥ c^d ≥ ((B + 1) / D)^d`;
* on no-instances, `tr(Q_x^d) ≤ 2^m s^d ≤ 2^m (B / D)^d ≤ ((B + 1) / D)^d / 2`, by Bernoulli's
  inequality `(B + 1)^B ≥ 2 B^B`.

So the `GapP` function `2 D^d traceGap - ((B + 1) 2^h)^d` is positive on yes-instances and not on
no-instances, which places the promise problem in `PP` (`Cslib.Complexity.mem_PP_iff_exists_GapP`).
This gives `QMA(c, s) ⊆ PP` for all constants `s < c`
(`Cslib.Complexity.PromiseQMA_subset_promiseClass_PP`), with no error reduction, and `QMA ⊆ PP`
(`Cslib.Complexity.QMA_subset_PP`).

`QMA ⊆ PP` was noted without proof by Kitaev and Watrous [Kitaev, Watrous][KitaevWatrous2000] and
proved by Vyalyi [Vyalyi][Vyalyi2003], who showed the stronger `QMA ⊆ A₀PP`; see
[Marriott, Watrous][MarriottWatrous2005], Section 1. The argument here follows the proof of
Theorem 3.4 of [Marriott, Watrous][MarriottWatrous2005]: the acceptance operator is positive, its
quadratic form is the acceptance probability, and its entries are `GapP` functions over a power of
two. Marriott and Watrous first reduce the error below `2^{-m-2}` without lengthening the witness
and then compare `tr(Q_x)` with `1/2`. Their strong error reduction is not formalized here, so this
file compares `tr(Q_x^d)` for `d` linear in `m` instead. The path sums are those of Fortnow and
Rogers [Fortnow, Rogers][FortnowRogers1999], Lemma 3.2, as in `Cslib.Complexity.BQP_subset_AWPP`.

## Main results

* `Cslib.Complexity.traceGap_mem_GapP`: the trace gap of a verifier is a `GapP` function.
* `Cslib.Complexity.PromiseQMA_subset_promiseClass_PP`: `QMA(c, s) ⊆ PP` for constants `s < c`.
* `Cslib.Complexity.QMA_subset_PP`: `QMA ⊆ PP`.

## References

* [A. Kitaev, J. Watrous, *Parallelization, amplification, and exponential time simulation of
  quantum interactive proof systems*][KitaevWatrous2000]
* [M. Vyalyi, *QMA = PP implies that PP contains PH*][Vyalyi2003]
* [C. Marriott, J. Watrous, *Quantum Arthur–Merlin games*][MarriottWatrous2005]
* [L. Fortnow, J. Rogers, *Complexity limitations on quantum computation*][FortnowRogers1999]
-/

public section

namespace Cslib.Complexity

open Quantum Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- **The trace gap of a verifier is a `GapP` function** of the instance, for a power computed in
polynomial time. Reindexing the closed paths through the basis witnesses as words of `(d + 1) m`
bits, each step is the pair gap of two registers cut out of the word in polynomial time. -/
theorem traceGap_mem_GapP (V : UniformVerifierFamily) {d : α → ℕ}
    (hd : ComputableInPolyTime d enc encUnary) :
    (fun a => V.traceGap (enc a) (d a)) ∈ GapP enc := by
  have hgates := V.computableInPolyTime_gates
  have hwidth := V.computableInPolyTime_width
  have hwit := V.computableInPolyTime_witnessLength
  let m : α → ℕ := fun a => V.witnessLength (enc a).length
  have hm : ComputableInPolyTime m enc encUnary := by dsimp only [m]; fun_prop
  -- the register holding the instance and the `i`-th block of the path `w`
  let reg : (α × List Bool) × ℕ → List Bool := fun x =>
    enc x.1.1 ++ BitString.listBlock (m x.1.1) x.1.2 x.2 ++
      List.replicate (V.width (enc x.1.1).length - ((enc x.1.1).length + m x.1.1)) false
  have hreg : ComputableInPolyTime reg (encPair (encPair enc encBits) encUnary) encBits := by
    dsimp only [reg, BitString.listBlock]
    fun_prop
  let gs : (α × List Bool) × ℕ → List GateCode := fun x => V.gates (enc x.1.1).length
  have hgs : ComputableInPolyTime gs (encPair (encPair enc encBits) encUnary)
      (encList encGateCode) := by dsimp only [gs]; fun_prop
  let reg' : (α × List Bool) × ℕ → List Bool := fun x => reg (x.1, x.2 + 1)
  have hreg' : ComputableInPolyTime reg' (encPair (encPair enc encBits) encUnary) encBits :=
    hreg.comp (by fun_prop)
  have hprod := GapP.prod_range_mem (onesPairGap_zero_mem_GapP hgs hreg hreg')
    (r := fun x : α × List Bool => d x.1) (by fun_prop)
  let closed : α × List Bool → Bool := fun x =>
    decide (BitString.listBlock (m x.1) x.2 0 = BitString.listBlock (m x.1) x.2 (d x.1))
  have hclosed : ComputableInPolyTime closed (encPair enc encBits) encBool := by
    dsimp only [closed, BitString.listBlock]
    fun_prop
  have hsum := GapP.sum_bits_mem (GapP.ite_mem hclosed hprod GapP.zero_mem)
    (r := fun a => (d a + 1) * m a) (by fun_prop)
  convert hsum using 2 with a
  rw [UniformVerifierFamily.traceGap]
  refine (Fintype.sum_equiv BitString.blocksEquiv _ _ fun w => ?_).symm
  have hblock (i : ℕ) (hi : i < d a + 1) :
      BitString.listBlock (m a) (List.ofFn w) i = List.ofFn (BitString.block w ⟨i, hi⟩) :=
    BitString.listBlock_ofFn w ⟨i, hi⟩
  have hlen (u : Fin (m a) → Bool) : (enc a ++ List.ofFn u).length ≤ V.width (enc a).length := by
    rw [List.length_append, List.length_ofFn]
    exact V.add_witnessLength_le _
  rw [BitString.blocksEquiv_apply]
  refine if_congr ?_ ?_ rfl
  · change decide (_ = _) = true ↔ _
    rw [decide_eq_true_iff, hblock 0 (by omega), hblock (d a) (by omega), List.ofFn_inj]
    exact Iff.rfl
  · rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    dsimp only [gs, reg, reg']
    rw [hblock i (Nat.lt_succ_of_lt i.2), hblock (i + 1) (Nat.succ_lt_succ i.2),
      ofFn_inputState (hlen _), ofFn_inputState (hlen _)]
    simp only [List.length_append, List.length_ofFn]
    rfl

/-- Naturals `B ≥ 1` and `D ≥ 1` with `s D ≤ B` and `B + 1 < c D`, for `0 ≤ s < c`. -/
private theorem exists_threshold {c s : ℝ} (hs : 0 ≤ s) (hcs : s < c) :
    ∃ B D : ℕ, 1 ≤ B ∧ 0 < D ∧ s * D ≤ B ∧ (B + 1 : ℝ) < c * D := by
  obtain ⟨D, hD⟩ := exists_nat_gt (2 / (c - s))
  have hcs' : 0 < c - s := sub_pos.mpr hcs
  have hD2 : 2 < (c - s) * D := by
    rwa [div_lt_iff₀ hcs', mul_comm] at hD
  have hDpos : (0 : ℝ) < D := by nlinarith
  refine ⟨⌊s * D⌋₊ + 1, D, by omega, by exact_mod_cast hDpos, ?_, ?_⟩
  · push_cast
    exact (Nat.lt_floor_add_one _).le
  · push_cast
    have := Nat.floor_le (mul_nonneg hs hDpos.le)
    linarith

/-- **Bernoulli**: `2^{m+1} B^{B (m+1)} ≤ (B + 1)^{B (m+1)}` for `B ≥ 1`. -/
private theorem two_pow_mul_pow_le {B : ℕ} (hB : 1 ≤ B) (m : ℕ) :
    (2 : ℝ) ^ (m + 1) * (B : ℝ) ^ (B * (m + 1)) ≤ ((B : ℝ) + 1) ^ (B * (m + 1)) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have h1 : 2 * (B : ℝ) ^ B ≤ ((B : ℝ) + 1) ^ B := by
    have := one_add_mul_le_pow (a := (1 / B : ℝ)) (by linarith [one_div_pos.mpr hBpos]) B
    rwa [mul_one_div_cancel hBpos.ne', one_add_one_eq_two, one_add_div hBpos.ne', div_pow,
      le_div_iff₀ (by positivity)] at this
  rw [pow_mul, pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) h1 _

/-- `QMA(c, s) ⊆ PP` for `0 ≤ s < c`. -/
private theorem PromiseQMA_subset_promiseClass_PP_of_nonneg {c s : ℝ} (hs : 0 ≤ s) (hcs : s < c) :
    PromiseQMA (fun _ => c) (fun _ => s) enc ⊆ promiseClass (PP enc) := by
  rintro Q ⟨V, hV⟩
  obtain ⟨B, D, hB, hD, hsB, hBc⟩ := exists_threshold hs hcs
  have hgates := V.computableInPolyTime_gates
  have hwit := V.computableInPolyTime_witnessLength
  let m : α → ℕ := fun a => V.witnessLength (enc a).length
  let h : α → ℕ := fun a => hadamardCount (V.gates (enc a).length)
  let J : α → ℕ := fun a => B * (m a + 1)
  have hh : ComputableInPolyTime h enc encUnary := by
    simp only [h, hadamardCount_eq_countP]
    fun_prop
  have hJ : ComputableInPolyTime J enc encUnary := by dsimp only [J, m]; fun_prop
  -- the separating gap function
  let G : α → ℤ := fun a =>
    2 * (D : ℤ) ^ J a * V.traceGap (enc a) (J a) - (((B : ℤ) + 1) * 2 ^ h a) ^ J a
  have hG : G ∈ GapP enc := by
    have hT := traceGap_mem_GapP V hJ
    have hD' : (fun a => (D : ℤ) ^ J a) ∈ GapP enc :=
      GapP.pow_mem_polyTime (g := fun _ => (D : ℤ))
        (mem_GapP_of_polyTime (ComputableInPolyTime.const _)) hJ
    have hX : (fun a => ((B : ℤ) + 1) * 2 ^ h a) ∈ GapP enc :=
      mem_GapP_of_polyTime (by fun_prop)
    exact GapP.sub_mem'
      (GapP.mul_mem (GapP.mul_mem (mem_GapP_of_polyTime (ComputableInPolyTime.const 2)) hD') hT)
      (GapP.pow_mem_polyTime hX hJ)
  refine ⟨{a | 0 < G a}, (mem_PP_iff_exists_GapP).2 ⟨G, hG, fun _ => Iff.rfl⟩, fun a ha => ?_,
    Set.disjoint_left.2 fun a ha hno => ?_⟩
  all_goals
    have hGr : (G a : ℝ) = 2 * (D : ℝ) ^ J a * V.traceGap (enc a) (J a) -
        ((B : ℝ) + 1) ^ J a * 2 ^ (h a * J a) := by
      simp only [G]
      push_cast
      rw [mul_pow, ← pow_mul]
    have hX : (0 : ℝ) < 2 ^ (h a * J a) := by positivity
    have hDJ : (0 : ℝ) < (D : ℝ) ^ J a := by positivity
  · -- yes-instances: `((B + 1) / D)^J < c^J ≤ tr(Q^J)`
    have hJpos : J a ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    have hT := V.pow_mul_le_traceGap (enc a) (hs.trans hcs.le) ((hV a).1 ha) (J a)
    have hlt : ((B : ℝ) + 1) ^ J a < (c * D) ^ J a :=
      pow_lt_pow_left₀ hBc (by positivity) hJpos
    rw [mul_pow] at hlt
    have : (0 : ℝ) < G a := by
      rw [hGr, sub_pos]
      calc ((B : ℝ) + 1) ^ J a * 2 ^ (h a * J a)
          < c ^ J a * (D : ℝ) ^ J a * 2 ^ (h a * J a) := mul_lt_mul_of_pos_right hlt hX
        _ = (D : ℝ) ^ J a * (c ^ J a * 2 ^ (h a * J a)) := by ring
        _ ≤ (D : ℝ) ^ J a * V.traceGap (enc a) (J a) := mul_le_mul_of_nonneg_left hT hDJ.le
        _ ≤ 2 * (D : ℝ) ^ J a * V.traceGap (enc a) (J a) := by
          have : (0 : ℝ) ≤ (D : ℝ) ^ J a * V.traceGap (enc a) (J a) :=
            mul_nonneg hDJ.le ((mul_nonneg (pow_nonneg (hs.trans hcs.le) _) hX.le).trans hT)
          linarith
    exact_mod_cast this
  · -- no-instances: `tr(Q^J) ≤ 2^m s^J ≤ ((B + 1) / D)^J / 2`
    have hT := V.traceGap_le (enc a) ((hV a).2 hno) (J a)
    have hsD : (s * D) ^ J a ≤ (B : ℝ) ^ J a := pow_le_pow_left₀ (by positivity) hsB _
    have hbern := two_pow_mul_pow_le hB (m a)
    have : (G a : ℝ) ≤ 0 := by
      rw [hGr, sub_nonpos]
      calc 2 * (D : ℝ) ^ J a * V.traceGap (enc a) (J a)
          ≤ 2 * (D : ℝ) ^ J a * (2 ^ m a * s ^ J a * 2 ^ (h a * J a)) :=
            mul_le_mul_of_nonneg_left hT (by positivity)
        _ = 2 ^ (m a + 1) * (s * D) ^ J a * 2 ^ (h a * J a) := by ring
        _ ≤ 2 ^ (m a + 1) * (B : ℝ) ^ J a * 2 ^ (h a * J a) := by gcongr
        _ ≤ ((B : ℝ) + 1) ^ J a * 2 ^ (h a * J a) := by gcongr
    exact absurd (show (0 : ℝ) < G a by exact_mod_cast ha) (not_lt.2 this)

/-- **`QMA(c, s) ⊆ PP`** for all constants `s < c`: every promise problem with a quantum verifier of
completeness `c` and soundness `s` is separated by a problem in `PP`. The trace of a power of the
acceptance operator separates the two cases without error reduction (compare
[Marriott, Watrous][MarriottWatrous2005], proof of Theorem 3.4). -/
theorem PromiseQMA_subset_promiseClass_PP {c s : ℝ} (hcs : s < c) :
    PromiseQMA (fun _ => c) (fun _ => s) enc ⊆ promiseClass (PP enc) := by
  rcases le_or_gt 0 s with hs | hs
  · exact PromiseQMA_subset_promiseClass_PP_of_nonneg hs hcs
  rcases lt_or_ge 0 c with hc | hc
  · exact (PromiseQMA_mono (fun _ => le_rfl) (fun _ => hs.le)).trans
      (PromiseQMA_subset_promiseClass_PP_of_nonneg le_rfl hc)
  -- with negative soundness there are no no-instances
  rintro Q ⟨V, hV⟩
  refine ⟨Set.univ, (mem_PP_iff_exists_GapP).2 ⟨1, GapP.one_mem, fun _ => by simp⟩,
    Set.subset_univ _, Set.disjoint_left.2 fun a _ hno => ?_⟩
  have := (hV a).2 hno (ket 0) (norm_ket _)
  linarith [V.acceptProb_nonneg (enc a) (ket 0)]

/-- **`QMA ⊆ PP`** [Kitaev, Watrous][KitaevWatrous2000]; [Vyalyi][Vyalyi2003];
[Marriott, Watrous][MarriottWatrous2005], Theorem 3.4. -/
theorem QMA_subset_PP : QMA enc ⊆ PP enc := fun A hA =>
  ofSet_mem_promiseClass.mp
    (PromiseQMA_subset_promiseClass_PP (by norm_num) hA)

end Cslib.Complexity
