/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.HintDecoding
public import CslibFrontier.Foundations.Data.Code.SelfCorrection

/-!
# Circuits for the arithmetic of Reed–Muller decoding

The decoders `Cslib.Code.lineListDecode` and the self-correction by interpolation and majority
trees query an oracle at computed points and combine the answers arithmetically. This module
counts the arithmetic over the full binary basis of the field, where every operation on at most
two field elements is one gate; the oracle queries are accounted for separately.

* The first nonzero entry of a vector of `m` available entries costs `4 * m + 2` gates
  (`Cslib.Circuits.Synthesis.full_firstNonzero`).
* The points `x + t • v`, for all `t ∈ F`, of the line through `x` and a fixed point `z`
  parametrized as in `Cslib.Code.lineListDecode`, together with the hint position, cost
  `(q + 5) * m + 2` gates (`Cslib.Circuits.Synthesis.full_linePoints`).
* A combination with fixed weights of `N` available values costs `2 * N + 1` gates
  (`Cslib.Circuits.Synthesis.full_weightedSum`).
* A majority tree over `3 ^ L` available values costs at most `2 * 3 ^ L - 2` gates
  (`Cslib.Circuits.Synthesis.full_majTree`): four gates for each majority of three, computed as
  `c + [a = b] * (a - c)`.

## Main results

* `Cslib.Circuits.Synthesis.full_firstNonzero`, `Cslib.Circuits.Synthesis.full_linePoints`,
  `Cslib.Circuits.Synthesis.full_weightedSum`, `Cslib.Circuits.Synthesis.full_majTree`.

## References

* [M. Sudan, L. Trevisan, S. Vadhan, *Pseudorandom generators without the XOR lemma*]
  [SudanTrevisanVadhan2001]
-/

public section

namespace Cslib.Circuits.Synthesis

open Finset Cslib.LinearAlgebra Cslib.Code

variable {F : Type*} [Field F] [DecidableEq F] {N : ℕ} {s : Set ((Fin N → F) → F)}

/-- **The first nonzero entry** of a vector of `m` available functions costs `4 * m + 2` gates. -/
theorem full_firstNonzero {m : ℕ} (u : Fin m → (Fin N → F) → F) (hu : ∀ i, u i ∈ s) :
    Synthesis (fullInterpretation (k := 2)) s {fun x => firstNonzero fun i => u i x}
      (4 * m + 2) := by
  have h₁ := full_firstFlags (s := s) u hu
  have h₂ := full_dot (s := s ∪ Set.range fun i x => firstFlags (fun j => u j x) i) univ
    (fun i x => firstFlags (fun j => u j x) i) u
    (fun i _ => Set.mem_union_right _ ⟨i, rfl⟩) (fun i _ => Set.mem_union_left _ (hu i))
  refine (h₁.trans h₂).mono Set.Subset.rfl (Set.singleton_subset_iff.2 rfl) ?_
  simp only [card_univ, Fintype.card_fin]
  omega

/-- **The points of a line by a circuit.** Given the coordinates of `x` as available functions
and a fixed point `z`, the hint position `firstNonzero (z - x)` and the coordinates of all points
`x + t • (firstNonzero (z - x))⁻¹ • (z - x)`, `t ∈ F`, of the line through `x` and `z` cost
`(q + 5) * m + 2` gates of the full binary basis. -/
theorem full_linePoints [Fintype F] {m : ℕ} (x : Fin m → (Fin N → F) → F) (hx : ∀ i, x i ∈ s)
    (z : Fin m → F) :
    Synthesis (fullInterpretation (k := 2)) s
      (Set.range fun o : Option (F × Fin m) => fun v => match o with
        | none => firstNonzero (z - fun i => x i v)
        | some (t, i) => ((fun i => x i v) + t • (firstNonzero (z - fun i => x i v))⁻¹ •
            (z - fun i => x i v)) i)
      ((Fintype.card F + 5) * m + 2) := by
  -- the differences
  have h₁ := family (I := fullInterpretation (k := 2)) (s := s) (fun i v => z i - x i v)
    (fun _ => 1) (fun i => full_unary (fun a => z i - a) (hx i))
  set s₁ := s ∪ Set.range fun i v => z i - x i v
  -- the hint position
  have h₂ := full_firstNonzero (s := s₁) (fun i v => z i - x i v) fun i =>
    Set.mem_union_right _ ⟨i, rfl⟩
  set s₂ := s₁ ∪ {fun v => firstNonzero fun i => z i - x i v}
  -- the points
  have h₃ := family (I := fullInterpretation (k := 2)) (s := s₂)
    (fun ti : F × Fin m => fun v => x ti.2 v + ti.1 * ((firstNonzero fun i => z i - x i v)⁻¹ *
      (z ti.2 - x ti.2 v))) (fun _ => 1)
    (fun ti => full_binary_mem (fun a c => a + ti.1 * (c⁻¹ * (z ti.2 - a)))
      (Set.mem_union_left _ (Set.mem_union_left _ (hx ti.2))) (Set.mem_union_right _ rfl))
  refine (h₁.comp (h₂.comp h₃)).mono Set.Subset.rfl ?_ ?_
  · rintro _ ⟨o, rfl⟩
    rcases o with _ | ⟨t, i⟩
    · exact Set.mem_union_right _ (Set.mem_union_left _ rfl)
    · refine Set.mem_union_right _ (Set.mem_union_right _ ⟨(t, i), funext fun v => ?_⟩)
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rfl
  · simp only [sum_const, card_univ, Fintype.card_fin, Fintype.card_prod, smul_eq_mul, mul_one]
    nlinarith

omit [DecidableEq F] in
/-- **A combination with fixed weights** of `N'` available functions costs `2 * N' + 1` gates. -/
theorem full_weightedSum {ι : Type*} [Fintype ι] (c : ι → F) (f : ι → (Fin N → F) → F)
    (hf : ∀ i, f i ∈ s) :
    Synthesis (fullInterpretation (k := 2)) s {fun x => ∑ i, c i * f i x}
      (2 * Fintype.card ι + 1) := by
  classical
  have hmul := biUnion (I := fullInterpretation (k := 2)) (s := s) univ
    (fun i => {fun x => c i * f i x}) (fun _ => 1) (fun i _ => full_unary (fun a => c i * a) (hf i))
  have hsum := full_sum (s := s ∪ ⋃ i ∈ (univ : Finset ι), {fun x => c i * f i x}) univ
    (fun i x => c i * f i x) (fun i hi => Set.mem_union_right _ (Set.mem_biUnion hi rfl))
  refine (hmul.trans hsum).mono Set.Subset.rfl Set.Subset.rfl ?_
  simp only [sum_const, card_univ, smul_eq_mul, mul_one]
  omega

/-- A majority of three available functions costs four gates. -/
private theorem full_maj3 {a b c : (Fin N → F) → F} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    Synthesis (fullInterpretation (k := 2)) s {fun x => maj3 (a x) (b x) (c x)} 4 := by
  have h₁ := full_binary_mem (s := s) (fun u v => if u = v then (1 : F) else 0) ha hb
  have h₂ := full_binary_mem (s := s ∪ {fun x => if a x = b x then (1 : F) else 0})
    (· - ·) (Set.mem_union_left _ ha) (Set.mem_union_left _ hc)
  set s₂ := (s ∪ {fun x => if a x = b x then (1 : F) else 0}) ∪ {fun x => a x - c x}
  have h₃ := full_binary_mem (s := s₂) (· * ·) (Set.mem_union_left _ (Set.mem_union_right _ rfl))
    (Set.mem_union_right _ rfl)
  have h₄ := full_binary_mem (s := s₂ ∪ {fun x => (if a x = b x then (1 : F) else 0) *
    (a x - c x)}) (fun u v => u + v)
    (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ hc)))
    (Set.mem_union_right _ rfl)
  refine (h₁.trans (h₂.trans (h₃.trans h₄))).mono Set.Subset.rfl
    (Set.singleton_subset_iff.2 (funext fun x => ?_)) le_rfl
  simp only [maj3]
  split_ifs with h
  · rw [h]
    ring
  · ring

/-- **A majority tree by a circuit.** A majority tree over `3 ^ L` available functions costs at
most `2 * 3 ^ L - 2` gates of the full binary basis. -/
theorem full_majTree (L : ℕ) (f : Fin (3 ^ L) → (Fin N → F) → F) (hf : ∀ k, f k ∈ s) :
    Synthesis (fullInterpretation (k := 2)) s {fun x => majTree L fun k => f k x}
      (2 * 3 ^ L - 2) := by
  induction L generalizing s with
  | zero =>
    exact (of_mem (hf _)).mono Set.Subset.rfl Set.Subset.rfl (by omega)
  | succ L ih =>
    have h₀ := ih (s := s) (fun k => f (tripleEquiv L (0, k))) fun k => hf _
    have h₁ := ih (s := s) (fun k => f (tripleEquiv L (1, k))) fun k => hf _
    have h₂ := ih (s := s) (fun k => f (tripleEquiv L (2, k))) fun k => hf _
    have h₃ := full_maj3 (s := s ∪ ({fun x => majTree L fun k => f (tripleEquiv L (0, k)) x} ∪
        ({fun x => majTree L fun k => f (tripleEquiv L (1, k)) x} ∪
          {fun x => majTree L fun k => f (tripleEquiv L (2, k)) x})))
      (Set.mem_union_right _ (Set.mem_union_left _ rfl))
      (Set.mem_union_right _ (Set.mem_union_right _ (Set.mem_union_left _ rfl)))
      (Set.mem_union_right _ (Set.mem_union_right _ (Set.mem_union_right _ rfl)))
    refine ((h₀.union (h₁.union h₂)).trans h₃).mono Set.Subset.rfl
      (Set.singleton_subset_iff.2 rfl) ?_
    rw [pow_succ]
    have : 1 ≤ 3 ^ L := Nat.one_le_pow _ _ (by decide)
    omega

end Cslib.Circuits.Synthesis
