/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORNPComplete
public import CslibFrontier.Computability.Complexity.FineGrained.SparsificationFamily
import CslibFrontier.Logics.Propositional.ClauseSet.Sparsification

/-!
# The materialized sparse 3-SAT reduction

Theorem 2, second clause of [WangLvShenZhang2027], pp. 12–13, asks for every positive `η` a
subexponential-time disjunction of at most `2 ^ (η v)` balanced instances of width at most
`Cη * v`. Here the actual collector is composed with the existing carry-free reduction. The
family size and linear width are proved with constants independent of the input, and a native
machine generates the family without a satisfiability oracle. Multiplicities are charged.

The generic certificate in this module charges a polynomial of the whole materialized state.
The refined implementation in `AddXNORSparsificationResources` uses polynomial branching on
only the stack and a streaming digit map; `Sparsification.source_generation` proves the source
`O*(2^(η v))` generation time. The generic certificate remains available for arbitrary parameters.
The chosen constant is `13 * (1 + Sparsify.occBound 3 α) + 16`.
The width bound is `Cη * (v + 1)` for all inputs and `Cη * v` when `v ≥ 1`. This zero-variable
qualification is necessary for this target encoding, whose yes-instances have width at least two.
No zero-variable yes-input can have a correct disjunctive reduction to width-zero instances.

## Main definitions

* `Sparsification.instances`: the actual list of balanced Add/XNOR instances.
* `Sparsification.certificate`: the composed native generator with charged output.

## Main results

* `Sparsification.correct`: original 3-CNF satisfiability is the disjunction of the returned
  answers.
* `Sparsification.exists_parameters`: exact exponential family size and linear width, with one
  input-independent choice of constants, for every positive real rate and positive round divisor.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.Sparsification

open Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM Cslib.GenericRAM
open ClauseSet.Sparsification (base)

/-- Generate sparse leaves and apply the checked, balanced 3-SAT reduction to every occurrence. -/
@[expose] def instances (α M : ℕ) (φ : CNF ℕ) : List (ℕ × List ℕ) :=
  (Sparsify.Family.collect 3 α 3 M φ).map threeSATToAddXNOR

/-- Native generation, including normalization, branching, materialization and reduction of every
leaf. Actual copied state and output costs remain in the certificate; no source-rate claim. -/
noncomputable def certificate (α M : ℕ) :
    NativeCertificate (instances α M) encCNF (encList encInstance) :=
  (NativeCertificate.ofPolyTime (show ComputableInPolyTime (List.map threeSATToAddXNOR)
    (encList encCNF) (encList encInstance) by fun_prop)).comp
      (Sparsify.Family.certificate 3 α 3 M)

/-- The actual returned disjunction decides the original valid 3-CNF, without semantic answers as
input to the generator. -/
theorem correct {α M : ℕ} (hα : 1 ≤ α) (hM : Sparsify.LeafBound 3 α M)
    {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ 3) :
    φ.Satisfiable ↔ ∃ x ∈ instances α M φ, x ∈ Decision := by
  rw [Sparsify.Family.satisfiable_iff (by omega) hα le_rfl hM hφ]
  constructor
  · rintro ⟨ψ, hψ, hsat⟩
    refine ⟨threeSATToAddXNOR ψ, List.mem_map.mpr ⟨ψ, hψ, rfl⟩,
      (threeSATToAddXNOR_mem_iff ψ).mpr ?_⟩
    exact ⟨(Sparsify.Family.collect_properties (by omega) hα le_rfl hM hφ hψ).1, hsat⟩
  · rintro ⟨x, hx, hxD⟩
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hx
    exact ⟨ψ, hψ, ((threeSATToAddXNOR_mem_iff ψ).mp hxD).2⟩

/-- Every generated occurrence is balanced and fitting, including no-instances. -/
theorem instances_shape (α M : ℕ) (φ : CNF ℕ) {x : ℕ × List ℕ}
    (hx : x ∈ instances α M φ) :
    2 ≤ x.1 ∧ x.2.length = x.1 ∧ ∀ a ∈ x.2, a < 2 ^ x.1 := by
  obtain ⟨ψ, -, rfl⟩ := List.mem_map.mp hx
  exact toAddXNOR_shape (ThreeSAT.toSubsetSum ψ)

/-- A width-zero disjunction cannot represent a yes-input in this balanced target language. -/
theorem zero_width_disjunction_rejects (xs : List (ℕ × List ℕ))
    (hzero : ∀ x ∈ xs, x.1 ≤ 0) : ¬ ∃ x ∈ xs, x ∈ Decision := by
  rintro ⟨x, hx, hD⟩
  have := hzero x hx
  have := hD.1
  omega

/-- A rate and a positive round divisor select fixed thresholds and one linear-width constant.
The family-size inequality is exact (no hidden multiplicative constant); the same returned list
has the original disjunctive semantics. The unconditional generic certificate is above; the
source-rate implementation is `source_generation` in `AddXNORSparsificationResources`. -/
theorem exists_parameters {η : ℝ} (hη : 0 < η) {M : ℕ} (hM : 0 < M) :
    ∃ α C : ℕ, 1 ≤ α ∧ Sparsify.LeafBound 3 α M ∧
      ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) →
        ((instances α M φ).length : ℝ) ≤ 2 ^ (η * φ.numVars) ∧
        (φ.Satisfiable ↔ ∃ x ∈ instances α M φ, x ∈ Decision) ∧
        ∀ x ∈ instances α M φ,
          x.1 ≤ C * (φ.numVars + 1) ∧ (1 ≤ φ.numVars → x.1 ≤ C * φ.numVars) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨α, hα, hcount⟩ := ClauseSet.Sparsification.exists_sum_choose_le
    (k := 3) (by omega) (ε := min η (1 / M)) (lt_min hη (by positivity))
  have hLB : Sparsify.LeafBound 3 α M := Sparsify.leafBound_of_real hM fun N =>
    (hcount N).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)))
  refine ⟨α, 13 * (1 + Sparsify.occBound 3 α) + 16, hα, hLB, fun φ hφ => ⟨?_,
    correct hα hLB hφ, ?_⟩⟩
  · have hc := Sparsify.Family.collect_length_le (by omega) hα le_rfl hLB φ
    have hc' : ((instances α M φ).length : ℝ) ≤
        (∑ j ∈ Finset.range ((3 - 1) * φ.numVars / α + 1),
          (φ.numVars * (3 * base 3 α ^ (2 * 3))).choose j : ℕ) := by
      exact_mod_cast (show (instances α M φ).length ≤ _ by
        simpa only [instances, List.length_map] using hc)
    rw [Nat.cast_sum] at hc'
    exact hc'.trans ((hcount φ.numVars).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))))
  · intro x hx
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hx
    obtain ⟨-, hlen, hvars⟩ :=
      Sparsify.Family.collect_properties (by omega) hα le_rfl hLB hφ hψ
    have hw := threeSATToAddXNOR_width_le ψ
    rw [CNF.length_distinctVars] at hw
    constructor
    · nlinarith
    · intro hv
      nlinarith

end Cslib.Cryptanalysis.AddXNOR.Sparsification
