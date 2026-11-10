/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORSparsification
public import CslibFrontier.Computability.Complexity.FineGrained.SparsificationFamilyResources
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.StreamingFlatMap
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Charged sparse-family generation

The actual collector is followed by a streaming digit reduction. Each callback sees one CNF,
not the entire family. The collector's fixed quadratic round factor admits rate slack chosen
before selecting thresholds. This proves the time refinement in
[WangLvShenZhang2027], Theorem 2 (PDF pp. 12–13), with the explicit zero-variable width convention
of `Sparsification.exists_parameters`. The source polynomial may depend on the requested rate.

## Main results

* `Sparsification.instances_quadratic_rounds`: the assembled native generator, with polynomial
  factors only in the original encoded formula.
* `Sparsification.source_generation`: the exact family-size and native source-rate endpoint.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.Sparsification
open Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM Cslib.GenericRAM

/-- Stream the checked digit reduction over the actual generated leaves. All preprocessing,
state copies, callback buffers and materialized input/output contribute to this bound. -/
theorem instances_quadratic_rounds {α M : ℕ} (hα : 1 ≤ α) (hM : Sparsify.LeafBound 3 α M) :
    ∃ Q : ℕ → ℕ, Cslib.PolynomiallyBounded Q ∧ Monotone Q ∧
      ComputableInO (instances α M) encCNF (encList encInstance)
        (fun φ => (Sparsify.rounds M φ + 1) ^ 2 * Q (encCNF φ).length)
        (fun φ => (Sparsify.rounds M φ + 1) ^ 2 * Q (encCNF φ).length) := by
  obtain ⟨Q, hQ, hmQ, hc⟩ := Sparsify.Family.collect_quadratic_rounds (by omega) hα le_rfl hM
  have he : ComputableInPolyTime (fun q : Unit × CNF ℕ => [threeSATToAddXNOR q.2])
      (encPair encUnit encCNF) (encList encInstance) := by fun_prop
  obtain ⟨P, hP, hmP, hs⟩ := ComputableInO.flatMap_stream he
  have prepare := (ComputableInO.const (encIn := encList encCNF) (encMid := encUnit) ()).prod
    (ComputableInO.of_eq (encIn := encList encCNF) (encMid := encList encCNF) fun _ => rfl)
  have machine := ((hs.comp prepare).comp hc).of_enc_eq (g := instances α M)
    (encC := encList encInstance)
    (fun φ => by simp only [Function.comp_apply, instances, List.map_eq_flatMap])
  let size := fun φ : CNF ℕ => (encCNF φ).length
  let nb := Sparsify.nodeBound 3 α
  have hnb : PolyBounded size nb := Sparsify.Family.nodeBound_poly 3 α
  have hPQ : PolyBounded size (fun φ => Q (size φ)) :=
    PolyBounded.of_polynomiallyBounded size hQ
  have hPP : PolyBounded size (fun φ => P (nb φ + 1)) :=
    (PolyBounded.of_polynomiallyBounded id hP).comp (hnb.add (.const 1))
  obtain ⟨R, hR, hmR, hle⟩ := exists_mono_poly
    (hPQ.add ((hnb.mul (.const 2)).add (.const 1)) |>.add hPP |>.add (.const 1))
  refine ⟨R, hR, hmR, machine.mono 10 (fun φ => ?_) (fun φ => ?_)⟩ <;>
  · let rows := Sparsify.Family.collect 3 α 3 M φ
    have hrow : ∀ ψ ∈ rows, (encCNF ψ).length ≤ nb φ :=
      fun ψ hψ => Sparsify.Family.mem_collect_wire_le (by omega) hα le_rfl hM hψ
    have hwidth : streamRecordLength encCNF rows ≤ nb φ := listMax_le hrow
    have hwire : (encList encCNF rows).length ≤ Sparsify.rounds M φ * (2 * nb φ + 1) :=
      Sparsify.Family.prefix_output (by omega) hα le_rfl hM φ (Sparsify.rounds M φ)
    have hpop : rows.length ≤ Sparsify.rounds M φ := by
      have hl := (Sparsify.Family.collect_length_le (by omega) hα le_rfl hM φ).trans
        (hM φ.numVars)
      exact hl.trans (Nat.pow_le_pow_right (by omega) (by
        simp only [CNF.length_distinctVars]; omega))
    have hPwidth : P (streamFilterWidth encUnit encCNF ((), rows)) ≤ P (nb φ + 1) :=
      hmP (by simpa only [streamFilterWidth, encUnit_apply, List.length_nil, zero_add] using
        Nat.add_le_add_right hwidth 1)
    have hh := hle φ
    have hm := Nat.mul_le_mul (Nat.add_le_add_right hpop 1) hPwidth
    have hr : 1 ≤ Sparsify.rounds M φ + 1 := by omega
    have hr2 : Sparsify.rounds M φ + 1 ≤ (Sparsify.rounds M φ + 1) ^ 2 :=
      by simpa only [pow_two] using Nat.le_mul_self (Sparsify.rounds M φ + 1)
    have hR : 1 ≤ R (size φ) := by omega
    have hp0 := Nat.mul_le_mul_left ((Sparsify.rounds M φ + 1) ^ 2)
      (show Q (size φ) ≤ R (size φ) by omega)
    have hp1 := Nat.mul_le_mul_left (Sparsify.rounds M φ + 1)
      (show P (nb φ + 1) ≤ R (size φ) by omega)
    have hw0 := Nat.mul_le_mul_left (Sparsify.rounds M φ)
      (show 2 * nb φ + 1 ≤ R (size φ) by omega)
    have hrR := Nat.mul_le_mul_right (R (size φ)) hr2
    simp only [length_encPair, encUnit_apply, List.length_nil] at *
    dsimp only [rows, size] at *
    nlinarith

/-- Theorem 2's source rate for the actual materialized family generator. Thresholds and the
finite machine are fixed for each positive rate. Family size is exact; time and charged space
include all materialization and are `O(ceil(2^(η v)) * Q(L))` for a polynomial `Q` in the original
encoded formula length. The width-zero qualification is inherited from `exists_parameters`. -/
theorem source_generation {η : ℝ} (hη : 0 < η) :
    ∃ α M C : ℕ, 0 < M ∧ 1 ≤ α ∧ Sparsify.LeafBound 3 α M ∧
      ∃ Q : ℕ → ℕ, Cslib.PolynomiallyBounded Q ∧ Monotone Q ∧
        ComputableInO (instances α M) encCNF (encList encInstance)
          (fun φ => ⌈(2 : ℝ) ^ (η * φ.numVars)⌉₊ * Q (encCNF φ).length)
          (fun φ => ⌈(2 : ℝ) ^ (η * φ.numVars)⌉₊ * Q (encCNF φ).length) ∧
        ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) →
          ((instances α M φ).length : ℝ) ≤ 2 ^ (η * φ.numVars) ∧
          (φ.Satisfiable ↔ ∃ x ∈ instances α M φ, x ∈ Decision) ∧
          ∀ x ∈ instances α M φ,
            x.1 ≤ C * (φ.numVars + 1) ∧ (1 ≤ φ.numVars → x.1 ≤ C * φ.numVars) := by
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / η)
  have hMr : (0 : ℝ) < M := lt_trans (by positivity) hM
  have hMpos : 0 < M := by exact_mod_cast hMr
  have hrate : 2 / (M : ℝ) ≤ η := by
    rw [div_le_iff₀ hMr]
    have ht := (div_lt_iff₀ hη).mp hM
    nlinarith
  obtain ⟨α, C, hα, hLB, hspec⟩ := exists_parameters hη hMpos
  obtain ⟨Q, hQ, hmQ, machine⟩ := instances_quadratic_rounds hα hLB
  refine ⟨α, M, C, hMpos, hα, hLB, Q, hQ, hmQ, ?_, hspec⟩
  have hrounds (φ : CNF ℕ) : (Sparsify.rounds M φ + 1) ^ 2 ≤
      25 * ⌈(2 : ℝ) ^ (η * φ.numVars)⌉₊ := by
    have hr := Sparsify.rounds_add_one_le M φ
    have hpow : (Sparsify.rounds M φ + 1) ^ 2 ≤ 25 * (2 ^ (φ.numVars / M)) ^ 2 := by
      nlinarith [Nat.mul_self_le_mul_self hr]
    have hexp : ((φ.numVars / M * 2 : ℕ) : ℝ) ≤ η * φ.numVars := by
      calc ((φ.numVars / M * 2 : ℕ) : ℝ) = 2 * ((φ.numVars / M : ℕ) : ℝ) := by
              push_cast; ring
        _ ≤ 2 * ((φ.numVars : ℝ) / M) :=
          mul_le_mul_of_nonneg_left Nat.cast_div_le (by norm_num)
        _ = (2 / (M : ℝ)) * φ.numVars := by ring
        _ ≤ η * φ.numVars := mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg _)
    have hreal : (((2 ^ (φ.numVars / M)) ^ 2 : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (η * φ.numVars) := by
      calc (((2 ^ (φ.numVars / M)) ^ 2 : ℕ) : ℝ) =
            (2 : ℝ) ^ ((φ.numVars / M * 2 : ℕ) : ℝ) := by
              simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast] using
                (pow_mul (2 : ℝ) (φ.numVars / M) 2).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hceil : (2 ^ (φ.numVars / M)) ^ 2 ≤ ⌈(2 : ℝ) ^ (η * φ.numVars)⌉₊ := by
      exact_mod_cast hreal.trans (Nat.le_ceil _)
    exact hpow.trans (Nat.mul_le_mul_left 25 hceil)
  exact machine.mono 25 (fun φ => by
    have h := Nat.mul_le_mul_right (Q (encCNF φ).length) (hrounds φ)
    nlinarith) (fun φ => by
    have h := Nat.mul_le_mul_right (Q (encCNF φ).length) (hrounds φ)
    nlinarith)

end Cslib.Cryptanalysis.AddXNOR.Sparsification
