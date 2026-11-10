/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.Cut
public import Mathlib.Analysis.Real.Sqrt
import CslibFrontier.Computability.Circuit.Frontier.IncidenceComponents
import CslibFrontier.Foundations.Combinatorics.HypergraphCut
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Threshold lower bounds from bounded direct input support

The bounds in this module restrict the number of original input coordinates read by each
gate. Internal predecessor fan-in, circuit depth, and real coefficient magnitudes remain
unrestricted. High-incidence input coordinates can be fixed before applying a random cut.

If both Boolean fibers are `K`-rectangle-free with `K ≤ 2 ^ k`, a program with `q`
input-reading gates and at most `d` original inputs per gate satisfies, for every natural `T`,
`n ≤ (2 * (1 - 2⁻ᵈ) + d / (T + 1)) * q + 2 * k + (T + 1) * √(2 * n)`.
For support at most three, an incidence-graph layout sharpens this to
`2 * n < (3 + 6 / (T + 1)) * q + max 3 T * Nat.log 2 (n + q) + 6 * k + 1`.
The support restriction concerns aggregated coefficients, so repeated wires and cancellation
are handled by the existing native circuit semantics.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.inputDegree`: the number of input-reading gates
  that have a nonzero effective coefficient on a given original input.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.sum_inputDegree`: incidence double counting.
* `Cslib.Circuits.Boolean.WeightedThreshold.exists_fixed_inputs_of_inputSupport_card_le`:
  fixing coordinates of degree above `T` costs at most `d * q / (T + 1)` coordinates.
* `Cslib.Circuits.Boolean.WeightedThreshold.le_inputGates_of_bounded_incidence`:
  the finite lower bound after fixing an arbitrary set of high-incidence inputs.
* `Cslib.Circuits.Boolean.WeightedThreshold.le_inputGates_of_inputSupport_card_le`,
  `Cslib.Circuits.Boolean.WeightedThreshold.circuit_le_of_inputSupport_card_le`:
  the finite support bound for programs and circuits.
* `Cslib.Circuits.Boolean.WeightedThreshold.two_mul_lt_inputGates_of_inputSupport_card_le_three`,
  `Cslib.Circuits.Boolean.WeightedThreshold.circuit_two_mul_lt_of_inputSupport_card_le_three`:
  the stronger finite incidence bound when each gate reads at most three original inputs.

## References

The lower-bound refinement combines the existing fixed-coordinate rectangle
lemma from [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*]
[Schlesinger2026Algebraic] with a random partition of the direct input supports.
The support-three refinement uses the existing cycle-rank layout bound on the incidence graph
and the hereditary obstruction to two disjoint coordinate sets with large deficits.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset

variable {n g : ℕ}

/-- The number of gates reading an original input with nonzero effective coefficient. -/
noncomputable def inputDegree (p : Program signature n g) (i : Fin n) : ℕ :=
  open scoped Classical in
  (univ.filter fun gate : inputGates p => i ∈ inputSupport p gate.val).card

/-- Counting direct input incidences either by input or by gate gives the same total. -/
theorem sum_inputDegree (p : Program signature n g) :
    ∑ i, inputDegree p i = ∑ gate : inputGates p, (inputSupport p gate.val).card := by
  classical
  simp only [inputDegree, card_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro gate _
  rw [← card_filter]
  simp [inputSupport]

/-- Fixing high-incidence coordinates leaves degree at most `T`; their number times `T + 1`
is at most the total direct input incidence bound. -/
theorem exists_fixed_inputs_of_inputSupport_card_le (p : Program signature n g)
    {d : ℕ} (hd : ∀ gate, (inputSupport p gate).card ≤ d) (T : ℕ) :
    ∃ F : Finset (Fin n), (∀ i, i ∉ F → inputDegree p i ≤ T) ∧
      (T + 1) * F.card ≤ d * (inputGates p).card := by
  classical
  let F := univ.filter fun i => T < inputDegree p i
  refine ⟨F, ?_, ?_⟩
  · intro i hi
    simpa [F] using hi
  · calc
      (T + 1) * F.card = ∑ _i ∈ F, (T + 1) := by simp [mul_comm]
      _ ≤ ∑ i ∈ F, inputDegree p i := sum_le_sum fun i hi =>
        (mem_filter.mp hi).2
      _ ≤ ∑ i, inputDegree p i := sum_le_sum_of_subset_of_nonneg (subset_univ _)
        (fun _ _ _ => Nat.zero_le _)
      _ = ∑ gate : inputGates p, (inputSupport p gate.val).card := sum_inputDegree p
      _ ≤ ∑ _gate : inputGates p, d := sum_le_sum fun gate _ => hd gate.val
      _ = d * (inputGates p).card := by simp [mul_comm]

private noncomputable def residualSupport (p : Program signature n g)
    (F : Finset (Fin n)) (gate : Fin g) : Finset ↥Fᶜ :=
  open scoped Classical in
  (inputSupport p gate).subtype (fun i => i ∈ Fᶜ)

private theorem mem_residualSupport (p : Program signature n g) (F : Finset (Fin n))
    (gate : Fin g) (i : ↥Fᶜ) :
    i ∈ residualSupport p F gate ↔ i.val ∈ inputSupport p gate := by
  classical
  simp [residualSupport]

private theorem card_residualSupport_le (p : Program signature n g) (F : Finset (Fin n))
    (gate : Fin g) :
    (residualSupport p F gate).card ≤ (inputSupport p gate).card := by
  classical
  rw [residualSupport, card_subtype]
  exact card_filter_le _ _

private theorem card_filter_inputGates (p : Program signature n g) (P : Fin g → Prop)
    [DecidablePred P] (hP : ∀ gate, P gate → gate ∈ inputGates p) :
    (univ.filter fun gate : inputGates p => P gate.val).card = (univ.filter P).card := by
  classical
  rw [← card_image_of_injective _ Subtype.val_injective]
  congr 1
  ext gate
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact hj
  · intro hgate
    exact ⟨⟨gate, hP gate hgate⟩, hgate, rfl⟩

private theorem cut_deficit_lt_of_rectangleFree (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction n} {K k : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) (hK : K ≤ 2 ^ k)
    (U A B : Finset (Fin n)) :
    U.card - A.card < (univ.filter fun j => ¬ inputSupport p j ∩ U ⊆ A).card + k ∨
      Uᶜ.card - B.card < (univ.filter fun j => ¬ inputSupport p j ∩ Uᶜ ⊆ B).card + k := by
  classical
  by_contra h
  push Not at h
  obtain ⟨P, Q, v, hv, hP, hQ⟩ := exists_rectangle_of_cut_with_fixed p U A B
  have hPK := le_card_of_pow_le hP h.1 hK
  have hQK := le_card_of_pow_le hQ h.2 hK
  have hmono : ∀ x ∈ P, ∀ y ∈ Q, f (glue U x y) = readout v := by
    intro x hx y hy
    rw [← hreadout, hv x hx y hy]
  rcases card_lt_or_card_lt_of_rectangleFree hf U P Q (readout v) hmono with h | h <;> omega

private theorem disjoint_deficit_lt (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction n} {K k : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) (hK : K ≤ 2 ^ k)
    (U V : Finset (Fin n)) (hUV : Disjoint U V) :
    U.card < (univ.filter fun j => ¬ Disjoint (inputSupport p j) U).card + k ∨
      V.card < (univ.filter fun j => ¬ Disjoint (inputSupport p j) V).card + k := by
  classical
  have hV : V ⊆ Uᶜ := subset_compl_iff_disjoint_right.mpr hUV.symm
  have hcard : Uᶜ.card - (Uᶜ \ V).card = V.card := by
    rw [card_sdiff_of_subset hV]
    have := card_le_card hV
    omega
  have hleft (j : Fin g) :
      inputSupport p j ∩ U ⊆ ∅ ↔ Disjoint (inputSupport p j) U := by
    constructor
    · intro h
      rw [disjoint_left]
      intro i hi hiU
      simpa using h (mem_inter.mpr ⟨hi, hiU⟩)
    · intro h i hi
      exact False.elim (disjoint_left.mp h (mem_inter.mp hi).1 (mem_inter.mp hi).2)
  have hright (j : Fin g) :
      inputSupport p j ∩ Uᶜ ⊆ Uᶜ \ V ↔ Disjoint (inputSupport p j) V := by
    constructor
    · intro h
      rw [disjoint_left]
      intro i hi hiV
      exact (mem_sdiff.mp (h (mem_inter.mpr ⟨hi, hV hiV⟩))).2 hiV
    · intro h i hi
      exact mem_sdiff.mpr ⟨(mem_inter.mp hi).2,
        fun hiV => disjoint_left.mp h (mem_inter.mp hi).1 hiV⟩
  have h := cut_deficit_lt_of_rectangleFree p readout hreadout hf hK U ∅ (Uᶜ \ V)
  simpa only [card_empty, Nat.sub_zero, hcard, hleft, hright] using h

private theorem residual_disjoint_deficit_lt (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction n} {K k : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) (hK : K ≤ 2 ^ k)
    (F : Finset (Fin n)) (U V : Finset ↥Fᶜ) (hUV : Disjoint U V) :
    U.card < (univ.filter fun gate : inputGates p =>
      ¬ Disjoint (residualSupport p F gate.val) U).card + k ∨
      V.card < (univ.filter fun gate : inputGates p =>
        ¬ Disjoint (residualSupport p F gate.val) V).card + k := by
  classical
  have himage : Disjoint (U.image Subtype.val) (V.image Subtype.val) := by
    rw [disjoint_left]
    intro i hiU hiV
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hiU
    obtain ⟨v, hv, hvu⟩ := mem_image.mp hiV
    have hvu' : v = u := Subtype.ext hvu
    exact disjoint_left.mp hUV hu (hvu' ▸ hv)
  have htouch (W : Finset ↥Fᶜ) :
      (univ.filter fun j => ¬ Disjoint (inputSupport p j) (W.image Subtype.val)).card =
        (univ.filter fun gate : inputGates p =>
          ¬ Disjoint (residualSupport p F gate.val) W).card := by
    have heq (j : Fin g) :
        ¬ Disjoint (inputSupport p j) (W.image Subtype.val) ↔
          ¬ Disjoint (residualSupport p F j) W := by
      rw [not_disjoint_iff, not_disjoint_iff]
      constructor
      · rintro ⟨i, hi, hiW⟩
        obtain ⟨w, hw, rfl⟩ := mem_image.mp hiW
        exact ⟨w, (mem_residualSupport p F j w).mpr hi, hw⟩
      · rintro ⟨w, hw, hwW⟩
        exact ⟨w.val, (mem_residualSupport p F j w).mp hw,
          mem_image.mpr ⟨w, hwW, rfl⟩⟩
    simp_rw [heq]
    apply (card_filter_inputGates p _ ?_).symm
    intro j hj
    obtain ⟨i, hi, _⟩ := not_disjoint_iff.mp hj
    exact (mem_inputGates_iff_inputSupport_nonempty p j).mpr
      ⟨i.val, (mem_residualSupport p F j i).mp hi⟩
  have h := disjoint_deficit_lt p readout hreadout hf hK
    (U.image Subtype.val) (V.image Subtype.val) himage
  simpa only [card_image_of_injective _ Subtype.val_injective, htouch] using h

private theorem residual_deficit_lt (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction n} {K k : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) (hK : K ≤ 2 ^ k)
    (F : Finset (Fin n)) (U : Finset ↥Fᶜ) :
    (U.card : ℝ) - (univ.filter fun gate : inputGates p =>
      ¬ Disjoint (residualSupport p F gate.val) U).card < k ∨
      (Uᶜ.card : ℝ) - (univ.filter fun gate : inputGates p =>
        ¬ Disjoint (residualSupport p F gate.val) Uᶜ).card < k := by
  rcases residual_disjoint_deficit_lt p readout hreadout hf hK F U Uᶜ disjoint_compl_right
    with h | h
  · have h' := (Nat.cast_lt (α := ℝ)).mpr h
    push_cast at h'
    exact Or.inl (by linarith)
  · have h' := (Nat.cast_lt (α := ℝ)).mpr h
    push_cast at h'
    exact Or.inr (by linarith)

/-- After fixing `F`, bounded incidence gives a support-sensitive lower bound. Only effective
coefficients on original input coordinates are counted. -/
theorem le_inputGates_of_bounded_incidence (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction n} {K k : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K)
    {d : ℕ} (hd : ∀ gate, (inputSupport p gate).card ≤ d)
    (F : Finset (Fin n)) (D : ℕ)
    (hD : ∀ i, i ∉ F → inputDegree p i ≤ D) (hK : K ≤ 2 ^ k) :
    (n : ℝ) ≤ 2 * (1 - (1 / 2 : ℝ) ^ d) * (inputGates p).card + F.card +
      2 * k + (D + 1 : ℝ) * Real.sqrt (2 * n) := by
  classical
  have h := Cslib.HypergraphCut.card_le_of_deficit
    (fun gate : inputGates p => residualSupport p F gate.val)
    (fun gate => (card_residualSupport_le p F gate.val).trans (hd gate.val))
    (fun i => by
      simpa only [mem_residualSupport, inputDegree] using
        hD i.val (mem_compl.mp i.property))
    (residual_deficit_lt p readout hreadout hf hK F)
  have hcard : Fintype.card ↥Fᶜ + F.card = n := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using card_compl_add_card F
  have hcardR : (Fintype.card ↥Fᶜ : ℝ) + F.card = n := by exact_mod_cast hcard
  have hle : (Fintype.card ↥Fᶜ : ℝ) ≤ n := by
    linarith [show (0 : ℝ) ≤ F.card by positivity]
  have hroot : 2 * Real.sqrt (Fintype.card ↥Fᶜ / 2) ≤ Real.sqrt (2 * (n : ℝ)) := by
    have hleft := Real.sq_sqrt (show 0 ≤ (Fintype.card ↥Fᶜ : ℝ) / 2 by positivity)
    have hright := Real.sq_sqrt (show 0 ≤ 2 * (n : ℝ) by positivity)
    nlinarith [Real.sqrt_nonneg ((Fintype.card ↥Fᶜ : ℝ) / 2),
      Real.sqrt_nonneg (2 * (n : ℝ))]
  have hmul := mul_le_mul_of_nonneg_left hroot (show (0 : ℝ) ≤ D + 1 by positivity)
  rw [Fintype.card_coe (inputGates p)] at h
  nlinarith

/-- A weighted threshold program whose gates each read at most `d` original inputs satisfies
`n ≤ (2 (1 - 2⁻ᵈ) + d / (T + 1)) q + 2 k + (T + 1) √(2 n)` for every `T`, where `q` is
the number of input-reading gates and both output fibers are `K`-rectangle-free with `K ≤ 2^k`.
There is no restriction on internal predecessor fan-in or real coefficient magnitudes. -/
theorem le_inputGates_of_inputSupport_card_le (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction n} {K k : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K)
    {d : ℕ} (hd : ∀ gate, (inputSupport p gate).card ≤ d)
    (T : ℕ) (hK : K ≤ 2 ^ k) :
    (n : ℝ) ≤ (2 * (1 - (1 / 2 : ℝ) ^ d) + (d : ℝ) / (T + 1)) *
      (inputGates p).card + 2 * k + (T + 1 : ℝ) * Real.sqrt (2 * n) := by
  classical
  obtain ⟨F, hdegree, hF⟩ := exists_fixed_inputs_of_inputSupport_card_le p hd T
  have h := le_inputGates_of_bounded_incidence p readout hreadout hf hd F T hdegree hK
  have hFR : (F.card : ℝ) ≤ (d : ℝ) / (T + 1) * (inputGates p).card := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < T + 1)]
    have h' : ((T + 1 : ℕ) : ℝ) * F.card ≤ (d : ℝ) * (inputGates p).card :=
      by exact_mod_cast hF
    push_cast at h'
    nlinarith
  nlinarith

/-- The support-sensitive bound for a native single-output threshold circuit whose output
selects a gate. -/
theorem circuit_le_of_inputSupport_card_le (c : Circuit signature n 1)
    (houtput : ∃ gate, c.outputs 0 = .gate gate) {f : Cslib.BooleanFunction n} {K k : ℕ}
    (hcomputes : ∀ x, c.eval interpretation x 0 = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K)
    {d : ℕ} (hd : ∀ gate, (inputSupport c.program gate).card ≤ d)
    (T : ℕ) (hK : K ≤ 2 ^ k) :
    (n : ℝ) ≤ (2 * (1 - (1 / 2 : ℝ) ^ d) + (d : ℝ) / (T + 1)) *
      (inputGates c.program).card + 2 * k + (T + 1 : ℝ) * Real.sqrt (2 * n) := by
  obtain ⟨gate, hgate⟩ := houtput
  apply le_inputGates_of_inputSupport_card_le c.program (fun z => z gate) ?_ hf hd T hK
  simpa only [Circuit.eval_of_output_eq_gate hgate] using hcomputes

/-- If every gate reads at most three original inputs, the incidence layout gives
`2 n < (3 + 6 / (T + 1)) q + max 3 T * log₂(n + q) + 6 k + 1` for every natural `T`.
Here `log₂` is `Nat.log 2`, `q` counts input-reading gates, and both fibers are
`K`-rectangle-free with `K ≤ 2 ^ k`. Internal predecessor fan-in and depth are unrestricted. -/
theorem two_mul_lt_inputGates_of_inputSupport_card_le_three (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction n} {K k : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K)
    (hsupport : ∀ gate, (inputSupport p gate).card ≤ 3)
    (T : ℕ) (hK : K ≤ 2 ^ k) :
    (2 * n : ℝ) < (3 + 6 / (T + 1 : ℝ)) * (inputGates p).card +
      (max 3 T : ℕ) * (Nat.log 2 (n + (inputGates p).card) : ℝ) + 6 * k + 1 := by
  classical
  obtain ⟨F, hdegree, hF⟩ := exists_fixed_inputs_of_inputSupport_card_le p hsupport T
  have h := Frontier.Incidence.two_mul_card_lt_of_disjoint
    (fun gate : inputGates p => residualSupport p F gate.val)
    (fun gate => (card_residualSupport_le p F gate.val).trans (hsupport gate.val))
    (fun i => by
      simpa only [mem_residualSupport, inputDegree] using
        hdegree i.val (mem_compl.mp i.property))
    (residual_disjoint_deficit_lt p readout hreadout hf hK F)
  have hcard : Fintype.card ↥Fᶜ + F.card = n := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using card_compl_add_card F
  have hle : Fintype.card ↥Fᶜ ≤ n := by omega
  rw [Fintype.card_coe (inputGates p)] at h
  have hlog := Nat.mul_le_mul_left (max 3 T)
    (Nat.log_mono_right (b := 2) (Nat.add_le_add_right hle (inputGates p).card))
  have hnat : 2 * Fintype.card ↥Fᶜ < 3 * (inputGates p).card +
      max 3 T * Nat.log 2 (n + (inputGates p).card) + 6 * k + 1 := by omega
  have hR : (2 : ℝ) * Fintype.card ↥Fᶜ < 3 * (inputGates p).card +
      (max 3 T : ℕ) * (Nat.log 2 (n + (inputGates p).card) : ℝ) + 6 * k + 1 :=
    by exact_mod_cast hnat
  have hcardR : (Fintype.card ↥Fᶜ : ℝ) + F.card = n := by exact_mod_cast hcard
  have hFR : (F.card : ℝ) ≤ (3 : ℝ) / (T + 1) * (inputGates p).card := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < T + 1)]
    have h' : ((T + 1 : ℕ) : ℝ) * F.card ≤ (3 : ℝ) * (inputGates p).card :=
      by exact_mod_cast hF
    push_cast at h'
    nlinarith
  have hcoeff : (6 : ℝ) / (T + 1) = 2 * (3 / (T + 1)) := by ring
  rw [hcoeff]
  nlinarith

/-- The incidence lower bound for a native single-output threshold circuit whose output
selects a gate, assuming each gate reads at most three original inputs. -/
theorem circuit_two_mul_lt_of_inputSupport_card_le_three (c : Circuit signature n 1)
    (houtput : ∃ gate, c.outputs 0 = .gate gate) {f : Cslib.BooleanFunction n} {K k : ℕ}
    (hcomputes : ∀ x, c.eval interpretation x 0 = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K)
    (hsupport : ∀ gate, (inputSupport c.program gate).card ≤ 3)
    (T : ℕ) (hK : K ≤ 2 ^ k) :
    (2 * n : ℝ) < (3 + 6 / (T + 1 : ℝ)) * (inputGates c.program).card +
      (max 3 T : ℕ) * (Nat.log 2 (n + (inputGates c.program).card) : ℝ) + 6 * k + 1 := by
  obtain ⟨gate, hgate⟩ := houtput
  apply two_mul_lt_inputGates_of_inputSupport_card_le_three
    c.program (fun z => z gate) ?_ hf hsupport T hK
  simpa only [Circuit.eval_of_output_eq_gate hgate] using hcomputes

end Cslib.Circuits.Boolean.WeightedThreshold
