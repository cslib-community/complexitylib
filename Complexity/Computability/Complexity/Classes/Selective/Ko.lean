/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Selective
public import Complexity.Computability.Circuit.Boolean.PPoly
import Complexity.Computability.Circuit.Boolean.Advice
import Complexity.Computability.Circuit.Boolean.PolynomialTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Foundations.Data.Finset.Tournament
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Finite.List

/-!
# P-selective sets have polynomial advice: Ko's theorem

Every P-selective set is in `P/poly` [Ko1983]; see also
[Hemaspaandra and Torenvliet, Chapter 1][HemaspaandraTorenvliet2003]. Given a selector `f` for
`A`, relate `x` to `y` when `f` picks `x` from `x` and `y`, in one of the two orders; then
`x ∈ A` whenever `y ∈ A`. The relation is total, so on the members of `A` of encoded length `n`
it is a tournament. There are at most `2 ^ n` such members, so at most `n + 1` of them dominate:
every member of length `n` is related to one of them
(`Finset.exists_dominating_subset_of_card_lt_two_pow`). Hence an instance of length `n` is in
`A` exactly when it is related to one of them (`Cslib.Complexity.IsSelector.exists_advice`).

The advice for length `n` is that list of at most `n + 1` instances, each of encoded length `n`;
with the list encoding `Turing.MultiTapeTM.encList` it takes at most `(n + 1) * (2 * n + 1)` bits,
so `O(n ^ 2)` bits, which is Ko's `P/quadratic` bound
(`Cslib.Complexity.PSel.exists_advice_polyTime`). With this advice, a polynomial-time machine
decides `A` by running the selector against each advice instance. This is the library's `P/poly`
advice convention (`Cslib.Circuits.Boolean.PPoly.of_advice`), so every P-selective set is in
`PPolyOn` (`Cslib.Complexity.PSel_subset_PPolyOn`).

## Main results

* `Cslib.Complexity.IsSelector.exists_advice`: for each length `n`, at most `n + 1` members of
  `A` of length `n` decide membership in `A` at length `n` through the selector.
* `Cslib.Complexity.PSel.exists_advice_polyTime`: a P-selective set is decided in polynomial time
  with advice of at most `(n + 1) * (2 * n + 1)` bits at length `n`.
* `Cslib.Complexity.PSel_subset_PPolyOn`: **Ko's theorem**, P-selective sets are in `P/poly`.

## References

* [K.-I. Ko, *On self-reducibility and weak P-selectivity*][Ko1983]
* [L. A. Hemaspaandra and L. Torenvliet, *Theory of Semi-Feasible Algorithms*,
  Chapter 1][HemaspaandraTorenvliet2003]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- At most `2 ^ n` instances have encodings of length `n`. -/
private theorem card_le_two_pow_of_length_eq {α : Type*} (enc : α ↪ List Bool) (n : ℕ)
    (T : Finset α) (hT : ∀ x ∈ T, (enc x).length = n) : T.card ≤ 2 ^ n := by
  classical
  have h := Finset.card_le_card_of_injOn (s := T) (t := (Finset.univ : Finset (Fin n → Bool)))
    (fun x i => (enc x).getD i false)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) (fun x hx y hy hxy => by
      refine enc.injective (List.ext_getElem ((hT x hx).trans (hT y hy).symm) fun i hi hi' => ?_)
      have := congrFun hxy ⟨i, (hT x hx) ▸ hi⟩
      simpa [List.getD_eq_getElem?_getD, hi, hi'] using this)
  simpa using h

/-- **Ko's advice for a selector.** If `f` is a selector for `A`, then for each length `n` some
list of at most `n + 1` members of `A`, each of encoded length `n`, decides membership in `A` at
length `n`: an instance `x` of length `n` is in `A` exactly when `f` picks `x` from `x` and some
`y` in the list, in one of the two orders. -/
theorem IsSelector.exists_advice {α : Type*} {A : Set α} {f : α → α → α} (hf : IsSelector A f)
    (enc : α ↪ List Bool) :
    ∃ adv : ℕ → List α, ∀ n, (adv n).length ≤ n + 1 ∧
      (∀ y ∈ adv n, y ∈ A ∧ (enc y).length = n) ∧
      ∀ x, (enc x).length = n → (x ∈ A ↔ ∃ y ∈ adv n, f x y = x ∨ f y x = x) := by
  classical
  have key (n : ℕ) : ∃ S : Finset α, S.card ≤ n + 1 ∧ (∀ y ∈ S, y ∈ A ∧ (enc y).length = n) ∧
      ∀ x, (enc x).length = n → (x ∈ A ↔ ∃ y ∈ S, f x y = x ∨ f y x = x) := by
    let T : Finset α :=
      (((List.finite_length_eq Bool n).preimage_embedding enc).inter_of_left A).toFinset
    have hT (x : α) : x ∈ T ↔ (enc x).length = n ∧ x ∈ A := by
      simp only [T, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_ofPred_eq]
    have hcard : T.card < 2 ^ (n + 1) := by
      have := card_le_two_pow_of_length_eq enc n T fun x hx => ((hT x).1 hx).1
      rw [pow_succ]
      have : 0 < 2 ^ n := by positivity
      omega
    obtain ⟨S, hST, hScard, hS⟩ := Finset.exists_dominating_subset_of_card_lt_two_pow
      (fun x y => f x y = x ∨ f y x = x) (n + 1) T (fun x _ y _ => by
        rcases hf.eq_or_eq x y with h | h
        · exact .inl (.inl h)
        · exact .inr (.inr h)) hcard
    refine ⟨S, hScard, fun y hy => ((hT y).1 (hST hy)).symm, fun x hx => ⟨fun hxA => ?_, ?_⟩⟩
    · exact hS x ((hT x).2 ⟨hx, hxA⟩)
    · rintro ⟨y, hy, h⟩
      exact hf.mem_of_mem_of_eq ((hT y).1 (hST hy)).2 h
  choose S hScard hSA hS using key
  refine ⟨fun n => (S n).toList, fun n => ⟨by simpa using hScard n, fun y hy => hSA n y
    (Finset.mem_toList.1 hy), fun x hx => (hS n x hx).trans ?_⟩⟩
  simp only [Finset.mem_toList]

/-- **P-selective sets are in `P/quadratic`.** A P-selective set is decided by a polynomial-time
function `D` of the advice and the instance, with advice `adv n` for the instances of encoded
length `n` taking at most `(n + 1) * (2 * n + 1)` bits: at most `n + 1` instances of length `n`
in the list encoding. -/
theorem PSel.exists_advice_polyTime {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ PSel enc) :
    ∃ D : List α × α → Bool, ComputableInPolyTime D (encPair (encList enc) enc) encBool ∧
      ∃ adv : ℕ → List α, (∀ n, (encList enc (adv n)).length ≤ (n + 1) * (2 * n + 1)) ∧
        ∀ a, a ∈ A ↔ D (adv (enc a).length, a) = true := by
  classical
  obtain ⟨f, hf, hsel⟩ := hA
  obtain ⟨adv, hadv⟩ := hsel.exists_advice enc
  refine ⟨fun p => p.1.any fun y => decide (f p.2 y = p.2 ∨ f y p.2 = p.2), ?_, adv,
    fun n => ?_, fun a => ?_⟩
  · have hx : ComputableInPolyTime (fun q : (List α × α) × α => q.1.2)
        (encPair (encPair (encList enc) enc) enc) enc :=
      (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)
    have hy : ComputableInPolyTime (fun q : (List α × α) × α => q.2)
        (encPair (encPair (encList enc) enc) enc) enc := ComputableInPolyTime.snd _ _
    exact ComputableInPolyTime.anyWithInput (ComputableInPolyTime.fst _ _)
      (ComputableInPolyTime.decide_or
        (.of_tidy (ComputableTidilyInPolyTime.decide_eq' (hf.comp (hx.prod hy)).tidy hx.tidy))
        (.of_tidy (ComputableTidilyInPolyTime.decide_eq' (hf.comp (hy.prod hx)).tidy hx.tidy)))
  · rw [length_encList]
    have h := List.sum_le_length_nsmul ((adv n).map fun a => 2 * (enc a).length + 1)
      (2 * n + 1) (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        rw [((hadv n).2.1 y hy).2])
    rw [List.length_map, smul_eq_mul] at h
    exact h.trans (Nat.mul_le_mul_right _ (hadv n).1)
  · rw [(hadv _).2.2 a rfl, List.any_eq_true]
    simp only [decide_eq_true_eq]

open Circuits.Boolean in
/-- **Ko's theorem.** Every P-selective set is in `P/poly` [Ko1983]. -/
theorem PSel_subset_PPolyOn {α : Type} {enc : α ↪ List Bool} : PSel enc ⊆ PPolyOn enc := by
  intro A hA
  obtain ⟨D, hD, adv, hadv, hA⟩ := PSel.exists_advice_polyTime hA
  obtain ⟨M, hM, hDM⟩ := PPoly.exists_of_polyTime hD
  let w : ℕ → List Bool := fun n => encList enc (adv n)
  have hw : PolynomiallyBounded fun n => (w n).length :=
    PolynomiallyBounded.mono_of_le (g := fun n => (n + 1) * (2 * n + 1)) (by fun_prop) hadv
  refine ⟨{x : List Bool | frame (w x.length) ++ x ∈ M}, PPoly.of_advice hM w hw
    (fun _ => Iff.rfl), fun a => ?_⟩
  change a ∈ A ↔ frame (w (enc a).length) ++ enc a ∈ M
  rw [hA, hDM (adv (enc a).length, a), encPair_apply]

end Cslib.Complexity
