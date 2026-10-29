/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.PH
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
import Complexity.Computability.Complexity.Classes.PH.Projection
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Collapses of the polynomial hierarchy

If `Πₖ ⊆ Σₖ` for some `k ≥ 1`, for problems with any encoding of their instances, then the
polynomial hierarchy collapses to its level `k`: `PH = Σₖ`
(`Cslib.Complexity.PH_eq_SigmaP_of_PiP_subset_SigmaP`) [Arora and Barak, Theorem 5.4][AroraBarak09],
[Stockmeyer][Stockmeyer1976]. Consequently `NP = coNP` collapses the hierarchy to `NP`
(`Cslib.Complexity.PH_eq_NP_of_coNP_subset_NP`) and `P = NP` collapses it to `P`
(`Cslib.Complexity.PH_eq_P_of_NP_subset_P`).

The collapse goes one level at a time (`Cslib.Complexity.SigmaP_succ_subset_SigmaP`). A problem
`A` in `Σₖ₊₁` is the projection of a problem `B` in `Πₖ` on pairs `(a, w₁)` of an instance and a
first certificate (`Cslib.Complexity.exists_mem_PiP_of_mem_SigmaP_succ`). Then `B` is in `Σₖ`, and
the existential quantifier over `w₁` merges with the first quantifier of `B`, whose block lengths
are polynomials in the length of the encoded pair `(a, w₁)`, hence in the length of `enc a`.

## Main results

* `Cslib.Complexity.SigmaP_succ_subset_SigmaP`: one level of the collapse.
* `Cslib.Complexity.PH_eq_SigmaP_of_PiP_subset_SigmaP`: `Πₖ ⊆ Σₖ` collapses `PH` to `Σₖ`.
* `Cslib.Complexity.PH_eq_NP_of_coNP_subset_NP`: `NP = coNP` collapses `PH` to `NP`.
* `Cslib.Complexity.PH_eq_P_of_NP_subset_P`: `P = NP` collapses `PH` to `P`.
* `Cslib.Complexity.PH_eq_SigmaP_of_SigmaP_succ_subset_SigmaP`: `Σₖ₊₁ ⊆ Σₖ` collapses `PH` to
  `Σₖ`, for every `k`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [L. Stockmeyer, *The polynomial-time hierarchy*][Stockmeyer1976]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-! ### One level of the collapse -/

variable {α : Type} {enc : α ↪ List Bool}

/-- A word of length `a + b` is a word of length `a` followed by one of length `b`. -/
private theorem exists_length_add_iff {a b : ℕ} {P : List Bool → Prop} :
    (∃ w : List Bool, w.length = a + b ∧ P w) ↔
      ∃ u : List Bool, u.length = a ∧ ∃ v : List Bool, v.length = b ∧ P (u ++ v) := by
  constructor
  · rintro ⟨w, hw, hP⟩
    refine ⟨w.take a, by simp [hw], w.drop a, by simp [hw], by rwa [List.take_append_drop]⟩
  · rintro ⟨u, hu, v, hv, hP⟩
    exact ⟨u ++ v, by simp [hu, hv], hP⟩

/-- **One level of the collapse.** If `Πₖ ⊆ Σₖ` for problems on pairs of an instance and a word,
for some `k ≥ 1`, then `Σₖ₊₁ ⊆ Σₖ`: the pairs `(a, w₁)` from which the last `k` quantifiers
accept form a problem in `Πₖ`, hence in `Σₖ`, and the quantifier over `w₁` merges with its first
quantifier. -/
theorem SigmaP_succ_subset_SigmaP {k : ℕ} (hk : 1 ≤ k)
    (h : PiP k (encPair enc encBits) ⊆ SigmaP k (encPair enc encBits)) :
    SigmaP (k + 1) enc ⊆ SigmaP k enc := by
  intro A hA
  -- the pairs of an instance and a first certificate from which the last `k` quantifiers accept
  obtain ⟨p, B, hB, hA⟩ := exists_mem_PiP_of_mem_SigmaP_succ hA
  obtain ⟨rs, V', hrs, hV', hB'⟩ := h hB
  obtain ⟨r, rs, rfl⟩ := List.exists_cons_of_length_eq_add_one
    (show rs.length = (k - 1) + 1 by omega)
  -- the length of the encoded pair of an instance and a first certificate
  let L : Polynomial ℕ := 2 * Polynomial.X + 1 + p
  have hL (a : α) (w : List Bool) (hw : w.length = p.eval (enc a).length) :
      (encPair enc encBits (a, w)).length = L.eval (enc a).length := by
    simp only [length_encPair, encBits_apply, hw, L, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  refine ⟨(p + r.comp L) :: rs.map (·.comp L),
    fun x => V' ((x.1, x.2.take (p.eval (enc x.1).length)), x.2.drop (p.eval (enc x.1).length)),
    by simp only [List.length_cons, List.length_map]; omega, ?_, fun a => ?_⟩
  · have hn : ComputableInPolyTime (fun x : α × List Bool => p.eval (enc x.1).length)
        (encPair enc encBits) encUnary :=
      ((ComputableInPolyTime.unary_eval p).comp
        (ComputableInPolyTime.encoding_length enc)).comp (.fst _ _)
    exact hV'.comp (((ComputableInPolyTime.fst _ _).prod
      (ComputableInPolyTime.bitsTakeWithInput (.snd _ _) hn)).prod
        (ComputableInPolyTime.bitsDropWithInput (.snd _ _) hn))
  · rw [hA a]
    simp only [List.map_cons, alternation_true_cons, Polynomial.eval_add, Polynomial.eval_comp,
      List.map_map, Function.comp_def]
    rw [exists_length_add_iff]
    refine exists_congr fun w => and_congr_right fun hw => ?_
    have hmem := hB' (a, w)
    simp only [List.map_cons, alternation_true_cons, hL a w hw] at hmem
    rw [hmem]
    refine exists_congr fun v => and_congr_right fun hv => alternation_congr fun u => ?_
    simp [hw, List.append_assoc]

/-! ### The collapses -/

/-- **`Πₖ ⊆ Σₖ` collapses the polynomial hierarchy to `Σₖ`**, for `k ≥ 1`
[Arora and Barak, Theorem 5.4][AroraBarak09]: if `Πₖ ⊆ Σₖ` for problems with any encoding of their
instances, then `PH = Σₖ`. -/
theorem PH_eq_SigmaP_of_PiP_subset_SigmaP {k : ℕ} (hk : 1 ≤ k)
    (h : ∀ {β : Type} (encB : β ↪ List Bool), PiP k encB ⊆ SigmaP k encB) :
    PH enc = SigmaP k enc := by
  -- every level from `k` on is within `Σₖ`, for every encoding
  have hlevel (j : ℕ) :
      ∀ {β : Type} (encB : β ↪ List Bool), SigmaP (k + j) encB ⊆ SigmaP k encB := by
    induction j with
    | zero => intro β encB; exact le_rfl
    | succ j ih =>
      intro β encB
      refine (SigmaP_succ_subset_SigmaP (k := k + j) (by omega) fun A hA => ?_).trans
        (ih encB)
      -- `Πₖ₊ⱼ` is the complement of `Σₖ₊ⱼ ⊆ Σₖ`, within `Πₖ ⊆ Σₖ ⊆ Σₖ₊ⱼ`
      have hc : Aᶜ ∈ SigmaP k _ := ih _ (compl_mem_SigmaP_of_mem_PiP hA)
      have := h _ (by simpa using compl_mem_PiP_of_mem_SigmaP hc)
      exact SigmaP_mono (Nat.le_add_right k j) this
  refine Set.Subset.antisymm (Set.iUnion_subset fun j => ?_) (SigmaP_subset_PH k)
  rcases le_total j k with hj | hj
  · exact SigmaP_mono hj
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
    exact hlevel i enc

/-- **`NP = coNP` collapses the polynomial hierarchy to `NP`** [Arora and Barak, Theorem 5.4]
[AroraBarak09]. -/
theorem PH_eq_NP_of_coNP_subset_NP (h : ∀ {β : Type} (encB : β ↪ List Bool), coNP encB ⊆ NP encB) :
    PH enc = NP enc := by
  rw [← SigmaP_one]
  exact PH_eq_SigmaP_of_PiP_subset_SigmaP le_rfl fun encB => by
    rw [PiP_one_eq_coNP, SigmaP_one]
    exact h encB

/-- **`P = NP` collapses the polynomial hierarchy to `P`** [Arora and Barak, Theorem 5.4]
[AroraBarak09]: then `coNP ⊆ NP`, since `P` is closed under complement. -/
theorem PH_eq_P_of_NP_subset_P (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ P encB) :
    PH enc = P enc := by
  have hNP : ∀ {β : Type} (encB : β ↪ List Bool), NP encB = P encB := fun encB =>
    (h encB).antisymm (SigmaP_one ▸ SigmaP_zero ▸ SigmaP_mono (Nat.zero_le 1))
  rw [PH_eq_NP_of_coNP_subset_NP fun encB A hA => ?_, hNP]
  obtain ⟨f, hf, hfA⟩ := h encB hA
  rw [hNP]
  exact ⟨fun a => !f a, (ComputableInPolyTime.bool_not.comp hf), fun a => by
    simpa using (hfA a).not⟩

/-- **`Σₖ₊₁ ⊆ Σₖ` collapses the polynomial hierarchy to `Σₖ`**, for every `k`: then
`Πₖ ⊆ Σₖ₊₁ ⊆ Σₖ`, and for `k = 0` the hypothesis is `NP ⊆ P`. -/
theorem PH_eq_SigmaP_of_SigmaP_succ_subset_SigmaP {k : ℕ}
    (h : ∀ {β : Type} (encB : β ↪ List Bool), SigmaP (k + 1) encB ⊆ SigmaP k encB) :
    PH enc = SigmaP k enc := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [SigmaP_zero]
    exact PH_eq_P_of_NP_subset_P fun encB => by
      simpa only [zero_add, SigmaP_one, SigmaP_zero] using h encB
  · exact PH_eq_SigmaP_of_PiP_subset_SigmaP hk fun encB =>
      (PiP_subset_SigmaP_succ k).trans (h encB)

end Cslib.Complexity
