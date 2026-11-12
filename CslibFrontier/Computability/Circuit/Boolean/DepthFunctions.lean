/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Formula
public import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Counting the functions of shallow formulas

Formulas of bounded `binaryCost` depth are infinitely many, since negations and constants are free.
The functions they compute are few. `depthFunctions n t` is a finset of functions containing the
function of every formula of depth at most `t`, together with its negation
(`eval_mem_depthFunctions`). It has at most `(4n + 4)^{2^t} / 2` elements
(`two_mul_card_depthFunctions_le`). At depth `0` the functions are the `2n` literals and the two
constants. One more level adds an AND or an OR of two earlier functions, and negations are absorbed
by De Morgan's laws.

This is the count of [ChukhinKulikovMihajlinSmal2026], proof of Lemma 6.3 (printed p. 16; PDF
p. 17): "there are at most `2^{2^t} (2n + 2)^{2^t} = 2^{2^t log₂(4n + 4)}` formulas of depth at
most `t`". The count here is of computed functions rather than padded formulas, which is what
union bounds over formulas need.

## Main definitions

* `Cslib.Circuits.Boolean.depthFunctions`: candidate functions of formulas of depth at most `t`.

## Main results

* `Cslib.Circuits.Boolean.eval_mem_depthFunctions`: every shallow formula computes one of them.
* `Cslib.Circuits.Boolean.two_mul_card_depthFunctions_le`: there are few of them.
-/

public section

namespace Cslib.Circuits.Boolean

open Formula

/-- Functions of formulas of `binaryCost` depth at most `t`, closed under negation: literals and
constants at depth `0`, then ANDs and ORs of two earlier functions. -/
noncomputable def depthFunctions (n : ℕ) : ℕ → Finset (BitString n → Bool)
  | 0 => (Finset.univ.image fun (p : Fin n × Bool) (x : BitString n) => x p.1 == p.2) ∪
      Finset.univ.image fun (b : Bool) (_ : BitString n) => b
  | t + 1 => (Finset.univ.image fun (b : Bool) => b).biUnion fun b =>
      ((depthFunctions n t) ×ˢ (depthFunctions n t)).image fun p (x : BitString n) =>
        if b then p.1 x && p.2 x else p.1 x || p.2 x

variable {n : ℕ}

private theorem and_mem {t : ℕ} {f g : BitString n → Bool} (hf : f ∈ depthFunctions n t)
    (hg : g ∈ depthFunctions n t) : (fun x => f x && g x) ∈ depthFunctions n (t + 1) := by
  simp only [depthFunctions, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
  exact ⟨true, ⟨true, Finset.mem_univ _, rfl⟩, (f, g), ⟨hf, hg⟩, by simp⟩

private theorem or_mem {t : ℕ} {f g : BitString n → Bool} (hf : f ∈ depthFunctions n t)
    (hg : g ∈ depthFunctions n t) : (fun x => f x || g x) ∈ depthFunctions n (t + 1) := by
  simp only [depthFunctions, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
  exact ⟨false, ⟨false, Finset.mem_univ _, rfl⟩, (f, g), ⟨hf, hg⟩, by simp⟩

/-- An AND (`b = true`) or OR (`b = false`) of two candidates and their negations is a candidate
one level up, and so is its negation, by De Morgan's laws. -/
private theorem gate_mem {t : ℕ} {f g : BitString n → Bool} (b : Bool)
    (hf : f ∈ depthFunctions n t ∧ (fun x => !f x) ∈ depthFunctions n t)
    (hg : g ∈ depthFunctions n t ∧ (fun x => !g x) ∈ depthFunctions n t) :
    (fun x => if b then f x && g x else f x || g x) ∈ depthFunctions n (t + 1) ∧
      (fun x => !(if b then f x && g x else f x || g x)) ∈ depthFunctions n (t + 1) := by
  cases b
  · exact ⟨by simpa using or_mem hf.1 hg.1, by simpa [Bool.not_or] using and_mem hf.2 hg.2⟩
  · exact ⟨by simpa using and_mem hf.1 hg.1, by simpa [Bool.not_and] using or_mem hf.2 hg.2⟩

/-- The candidate functions grow with the depth. -/
theorem depthFunctions_mono {s t : ℕ} (h : s ≤ t) : depthFunctions n s ⊆ depthFunctions n t := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact fun f hf => by simpa using and_mem (ih hf) (ih hf)

/-- **Every formula of depth at most `t` computes a candidate function, and so does its
negation.** -/
theorem eval_mem_depthFunctions (F : Formula signature n) {t : ℕ}
    (hF : F.depthWith binaryCost ≤ t) :
    F.eval interpretation ∈ depthFunctions n t ∧
      (fun x => !F.eval interpretation x) ∈ depthFunctions n t := by
  induction F generalizing t with
  | input i =>
    have h0 (b : Bool) : (fun x : BitString n => x i == b) ∈ depthFunctions n 0 :=
      Finset.mem_union_left _ (Finset.mem_image.2 ⟨(i, b), Finset.mem_univ _, rfl⟩)
    have e₁ : (Formula.input i : Formula signature n).eval interpretation =
        fun x => x i == true := funext fun x => by simp
    have e₂ : (fun x => !(Formula.input i : Formula signature n).eval interpretation x) =
        fun x => x i == false := funext fun x => by cases h : x i <;> simp [h]
    rw [e₂, e₁]
    exact ⟨depthFunctions_mono (Nat.zero_le t) (h0 true),
      depthFunctions_mono (Nat.zero_le t) (h0 false)⟩
  | gate op args ih =>
    cases op with
    | const c =>
      have h0 (b : Bool) : (fun _ : BitString n => b) ∈ depthFunctions n 0 :=
        Finset.mem_union_right _ (Finset.mem_image.2 ⟨b, Finset.mem_univ _, rfl⟩)
      have e₁ : (Formula.gate (Op.const c) args).eval interpretation = fun _ => c := rfl
      have e₂ : (fun x => !(Formula.gate (Op.const c) args).eval interpretation x) =
          fun _ => !c := rfl
      rw [e₂, e₁]
      exact ⟨depthFunctions_mono (Nat.zero_le t) (h0 c),
        depthFunctions_mono (Nat.zero_le t) (h0 (!c))⟩
    | not =>
      have h := ih 0 (t := t) (by simpa using hF)
      have e₁ : (Formula.gate Op.not args).eval interpretation =
          fun x => !(args 0).eval interpretation x := rfl
      have e₂ : (fun x => !(Formula.gate Op.not args).eval interpretation x) =
          (args 0).eval interpretation := funext fun x => by
        change (!!(args 0).eval interpretation x) = _
        simp
      rw [e₂, e₁]
      exact ⟨h.2, h.1⟩
    | and =>
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by simp at hF; omega⟩
      exact gate_mem true (ih 0 (by simp at hF; omega)) (ih 1 (by simp at hF; omega))
    | or =>
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by simp at hF; omega⟩
      exact gate_mem false (ih 0 (by simp at hF; omega)) (ih 1 (by simp at hF; omega))

/-- **The count.** There are at most `(4n + 4)^{2^t} / 2` candidate functions of depth `t`. -/
theorem two_mul_card_depthFunctions_le (t : ℕ) :
    2 * (depthFunctions n t).card ≤ (4 * n + 4) ^ 2 ^ t := by
  induction t with
  | zero =>
    have h₁ := Finset.card_union_le
      (Finset.univ.image fun (p : Fin n × Bool) (x : BitString n) => x p.1 == p.2)
      (Finset.univ.image fun (b : Bool) (_ : BitString n) => b)
    have h₂ := Finset.card_image_le (s := (Finset.univ : Finset (Fin n × Bool)))
      (f := fun p (x : BitString n) => x p.1 == p.2)
    have h₃ := Finset.card_image_le (s := (Finset.univ : Finset Bool))
      (f := fun b (_ : BitString n) => b)
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at h₂ h₃
    change 2 * ((Finset.univ.image fun (p : Fin n × Bool) (x : BitString n) => x p.1 == p.2) ∪
      Finset.univ.image fun (b : Bool) (_ : BitString n) => b).card ≤ (4 * n + 4) ^ 2 ^ 0
    simp only [pow_zero, pow_one]
    omega
  | succ t ih =>
    have h : (depthFunctions n (t + 1)).card ≤ 2 * (depthFunctions n t).card ^ 2 := by
      refine Finset.card_biUnion_le.trans ?_
      refine (Finset.sum_le_sum fun b _ => Finset.card_image_le.trans
        (Finset.card_product _ _).le).trans ?_
      calc ∑ _b ∈ Finset.univ.image fun (b : Bool) => b,
            (depthFunctions n t).card * (depthFunctions n t).card
          ≤ ∑ _b : Bool, (depthFunctions n t).card * (depthFunctions n t).card :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ = 2 * (depthFunctions n t).card ^ 2 := by simp [sq]
    calc 2 * (depthFunctions n (t + 1)).card ≤ (2 * (depthFunctions n t).card) ^ 2 := by
          nlinarith
      _ ≤ ((4 * n + 4) ^ 2 ^ t) ^ 2 := Nat.pow_le_pow_left ih 2
      _ = (4 * n + 4) ^ 2 ^ (t + 1) := by rw [← pow_mul, pow_succ]

end Cslib.Circuits.Boolean
