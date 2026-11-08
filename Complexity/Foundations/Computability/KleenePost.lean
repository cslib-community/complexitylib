/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Computability/TuringDegree.lean`)

public import Complexity.Foundations.Computability.RecursiveInCode
public import Mathlib.Algebra.Notation.Indicator

/-!
# The Kleene–Post theorem: incomparable Turing degrees

Kleene and Post showed that the Turing degrees are not linearly ordered: there are sets `A` and
`B` of natural numbers with `A ≰ᵀ B` and `B ≰ᵀ A`. This file proves it by the finite extension
method. Two finite binary strings `σ` and `τ` are built in stages. At stage `2e + 1` the string
`σ` is extended by one bit so that the oracle code `e` relative to any extension of `τ` cannot
compute the characteristic function of `A` at the position of the new bit. Either some extension
of `τ` makes the computation converge, in which case `τ` is extended to it and the bit is chosen
to disagree with the output, or no extension does, in which case the computation diverges for
every oracle extending `τ`. Stage `2e + 2` is symmetric. The stage-bounded evaluator
`Nat.RecursiveIn.Code.evaln` turns the first alternative into a statement about finite strings,
and its soundness and completeness (the use principle) carry the conclusion to the limit sets.

This proves the incomparability statement of Kleene–Post. The construction is noncomputable here:
it decides by classical choice whether some extension forces convergence. The bound
`A, B ≤ᵀ ∅′` from the source, which says that this question is a `Σ₁` question answered by the
halting problem, is not formalized in this file.

## Main results

* `Nat.RecursiveIn.kleene_post`: there are sets `A B : Set ℕ` whose characteristic functions are
  Turing incomparable.
* `TuringDegree.exists_incomparable`: the Turing degrees are not linearly ordered.

## References

* [S. C. Kleene and E. L. Post, *The upper semi-lattice of degrees of recursive
  unsolvability*][KleenePost1954]
* [R. I. Soare, *Recursively Enumerable Sets and Degrees*][Soare1987]
-/

public section

open Encodable Denumerable
open scoped Computability

namespace Nat.RecursiveIn

namespace KleenePost

open Code

/-- A finite binary string, read as a finite oracle prefix with values in `{0, 1}`. -/
private def bits (σ : List Bool) : List ℕ := σ.map Bool.toNat

/-- Some extension of the finite string `τ` makes the code `c` converge on `x` at some stage.
The witness packs the extension, the stage and the output. -/
private def Halts (c : Code) (τ : List Bool) (x : ℕ) : Prop :=
  ∃ p : List Bool × ℕ × ℕ, τ <+: p.1 ∧ p.2.2 ∈ evaln (bits p.1) p.2.1 c x

open Classical in
/-- One finite-extension step against the code `c`: extend `σ` by one bit at position
`σ.length`, and extend `τ` to force convergence of `c` at that position when possible. -/
private noncomputable def step (c : Code) (σ τ : List Bool) : List Bool × List Bool :=
  if h : Halts c τ σ.length then
    (σ ++ [decide ((Classical.choose h).2.2 = 0)], (Classical.choose h).1)
  else
    (σ ++ [false], τ)

private theorem step_fst (c : Code) (σ τ : List Bool) : ∃ b, (step c σ τ).1 = σ ++ [b] := by
  unfold step
  split_ifs with h
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

private theorem step_snd (c : Code) (σ τ : List Bool) : τ <+: (step c σ τ).2 := by
  unfold step
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact List.prefix_refl τ

/-- The finite string `σ` is an initial segment of the `Bool` sequence `a`. -/
private def Agrees (σ : List Bool) (a : ℕ → Bool) : Prop := ∀ i (h : i < σ.length), σ[i] = a i

/-- The diagonalization step: if `a` extends the first output of `step c σ τ` and `b` extends the
second, then `c` relative to `b` does not compute `a`. -/
private theorem step_spec {c : Code} {σ τ : List Bool} {a b : ℕ → Bool}
    (hσ : Agrees (step c σ τ).1 a) (hτ : Agrees (step c σ τ).2 b) :
    eval (fun n => (b n).toNat : ℕ → ℕ) c ≠ (fun n => (a n).toNat : ℕ → ℕ) := by
  intro heq
  have hx : (a σ.length).toNat ∈ eval (fun n => (b n).toNat : ℕ → ℕ) c σ.length := by
    rw [heq, PFun.coe_val]; exact Part.mem_some _
  by_cases h : Halts c τ σ.length
  · simp only [step, h, ↓reduceDIte] at hσ hτ
    have hspec := Classical.choose_spec h
    generalize Classical.choose h = p at hspec hσ hτ
    have hv : p.2.2 ∈ eval (fun n => (b n).toNat : ℕ → ℕ) c σ.length := by
      refine evaln_sound (fun i hi => ?_) hspec.2
      have hi' : i < p.1.length := by simpa [bits] using hi
      simp only [bits, List.getElem_map, hτ i hi', PFun.coe_val]
      exact Part.mem_some _
    have hax : a σ.length = decide (p.2.2 = 0) := by
      have := hσ σ.length (by simp)
      simp only [List.getElem_concat_length] at this
      exact this.symm
    have := Part.mem_unique hv hx
    rw [hax] at this
    by_cases h0 : p.2.2 = 0 <;> simp [h0] at this
  · simp only [step, h, ↓reduceDIte] at hσ hτ
    obtain ⟨N, k, hk⟩ := evaln_complete.1 hx
    apply h
    let M := max N τ.length
    refine ⟨((List.range M).map b, k, (a σ.length).toNat), ?_, ?_⟩
    · rw [List.prefix_iff_eq_take]
      refine List.ext_getElem (by simp; omega) fun i h₁ h₂ => ?_
      simp [hτ i h₁]
    · have hbits : bits ((List.range M).map b) = prefixOf (fun n => (b n).toNat) M := by
        simp [bits, prefixOf, Function.comp_def]
      rw [hbits]
      exact evaln_mono (prefixOf_prefix _ (le_max_left _ _)) le_rfl hk

/-- The finite-extension construction. Stage `2e + 1` extends the first string against code `e`,
and stage `2e + 2` extends the second string against code `e`. -/
private noncomputable def stage : ℕ → List Bool × List Bool
  | 0 => ([], [])
  | s + 1 =>
    if s % 2 = 0 then step (ofNat Code (s / 2)) (stage s).1 (stage s).2
    else (step (ofNat Code (s / 2)) (stage s).2 (stage s).1).swap

private theorem stage_succ_prefix (s : ℕ) :
    (stage s).1 <+: (stage (s + 1)).1 ∧ (stage s).2 <+: (stage (s + 1)).2 := by
  simp only [stage]
  split_ifs with h
  · obtain ⟨b, hb⟩ := step_fst (ofNat Code (s / 2)) (stage s).1 (stage s).2
    exact ⟨hb ▸ List.prefix_append _ _, step_snd _ _ _⟩
  · obtain ⟨b, hb⟩ := step_fst (ofNat Code (s / 2)) (stage s).2 (stage s).1
    exact ⟨step_snd _ _ _, by simp only [Prod.snd_swap, hb]; exact List.prefix_append _ _⟩

private theorem stage_prefix {s t : ℕ} (h : s ≤ t) :
    (stage s).1 <+: (stage t).1 ∧ (stage s).2 <+: (stage t).2 := by
  induction h with
  | refl => exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | step _ ih =>
    exact ⟨ih.1.trans (stage_succ_prefix _).1, ih.2.trans (stage_succ_prefix _).2⟩

private theorem length_stage (s : ℕ) :
    (s + 1) / 2 ≤ (stage s).1.length ∧ s / 2 ≤ (stage s).2.length := by
  induction s with
  | zero => simp
  | succ s ih =>
    simp only [stage]
    split_ifs with h
    · obtain ⟨b, hb⟩ := step_fst (ofNat Code (s / 2)) (stage s).1 (stage s).2
      have := (step_snd (ofNat Code (s / 2)) (stage s).1 (stage s).2).length_le
      rw [hb, List.length_append]
      simp only [List.length_singleton]
      omega
    · obtain ⟨b, hb⟩ := step_fst (ofNat Code (s / 2)) (stage s).2 (stage s).1
      have := (step_snd (ofNat Code (s / 2)) (stage s).2 (stage s).1).length_le
      simp only [Prod.fst_swap, Prod.snd_swap, hb, List.length_append, List.length_singleton]
      omega

/-- The first limit sequence: its value at `n` is fixed by stage `2 * n + 2`. -/
private noncomputable def limA (n : ℕ) : Bool := (stage (2 * n + 2)).1.getD n false

/-- The second limit sequence: its value at `n` is fixed by stage `2 * n + 2`. -/
private noncomputable def limB (n : ℕ) : Bool := (stage (2 * n + 2)).2.getD n false

private theorem agrees_limA (s : ℕ) : Agrees (stage s).1 limA := by
  intro i hi
  have hi' : i < (stage (2 * i + 2)).1.length := by
    have := (length_stage (2 * i + 2)).1; omega
  have h₁ := (stage_prefix (le_max_left s (2 * i + 2))).1
  have h₂ := (stage_prefix (le_max_right s (2 * i + 2))).1
  rw [limA, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some,
    h₁.getElem hi, h₂.getElem hi']

private theorem agrees_limB (s : ℕ) : Agrees (stage s).2 limB := by
  intro i hi
  have hi' : i < (stage (2 * i + 2)).2.length := by
    have := (length_stage (2 * i + 2)).2; omega
  have h₁ := (stage_prefix (le_max_left s (2 * i + 2))).2
  have h₂ := (stage_prefix (le_max_right s (2 * i + 2))).2
  rw [limB, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some,
    h₁.getElem hi, h₂.getElem hi']

private theorem not_limA_le_limB :
    ¬(fun n => (limA n).toNat : ℕ → ℕ) ≤ᵀ (fun n => (limB n).toNat : ℕ → ℕ) := by
  intro h
  obtain ⟨c, hc⟩ := turingReducible_iff_exists_code.1 h
  have hs : stage (2 * encode c + 1) =
      step c (stage (2 * encode c)).1 (stage (2 * encode c)).2 := by
    simp [stage]
  refine step_spec (c := c) (σ := (stage (2 * encode c)).1) (τ := (stage (2 * encode c)).2)
    ?_ ?_ hc
  · rw [← hs]; exact agrees_limA _
  · rw [← hs]; exact agrees_limB _

private theorem not_limB_le_limA :
    ¬(fun n => (limB n).toNat : ℕ → ℕ) ≤ᵀ (fun n => (limA n).toNat : ℕ → ℕ) := by
  intro h
  obtain ⟨c, hc⟩ := turingReducible_iff_exists_code.1 h
  have hs : stage (2 * encode c + 2) =
      (step c (stage (2 * encode c + 1)).2 (stage (2 * encode c + 1)).1).swap := by
    rw [stage]
    simp only [show ¬((2 * encode c + 1) % 2 = 0) by omega, ↓reduceIte,
      show (2 * encode c + 1) / 2 = encode c by omega, ofNat_encode]
  refine step_spec (c := c) (σ := (stage (2 * encode c + 1)).2)
    (τ := (stage (2 * encode c + 1)).1) ?_ ?_ hc
  · have := agrees_limB (2 * encode c + 2)
    rwa [hs, Prod.snd_swap] at this
  · have := agrees_limA (2 * encode c + 2)
    rwa [hs, Prod.fst_swap] at this

private theorem indicator_eq (a : ℕ → Bool) :
    ({n | a n = true} : Set ℕ).indicator 1 = fun n => (a n).toNat := by
  funext n
  cases h : a n <;> simp [Set.indicator, h]

end KleenePost

open KleenePost in
/-- **Kleene–Post theorem** (incomparability part): there are sets `A` and `B` of natural numbers
whose characteristic functions are Turing incomparable, `A ≰ᵀ B` and `B ≰ᵀ A`. The sets are built
by finite extension; the bound `A, B ≤ᵀ ∅′` of the source is not part of this statement. -/
theorem kleene_post :
    ∃ A B : Set ℕ, ¬(A.indicator 1 : ℕ → ℕ) ≤ᵀ (B.indicator 1 : ℕ → ℕ) ∧
      ¬(B.indicator 1 : ℕ → ℕ) ≤ᵀ (A.indicator 1 : ℕ → ℕ) :=
  ⟨{n | limA n = true}, {n | limB n = true}, by
    rw [indicator_eq, indicator_eq]; exact ⟨not_limA_le_limB, not_limB_le_limA⟩⟩

end Nat.RecursiveIn

/-- The Turing degrees are not linearly ordered: some two degrees are incomparable. -/
theorem TuringDegree.exists_incomparable : ∃ d₁ d₂ : TuringDegree, ¬d₁ ≤ d₂ ∧ ¬d₂ ≤ d₁ := by
  obtain ⟨A, B, h₁, h₂⟩ := Nat.RecursiveIn.kleene_post
  exact ⟨toAntisymmetrization _ (A.indicator 1 : ℕ → ℕ),
    toAntisymmetrization _ (B.indicator 1 : ℕ → ℕ), h₁, h₂⟩
