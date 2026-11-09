/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORStripping

/-!
# Forced four-operation Add/XNOR guards

The four-bit guard in [WangLvShenZhang2027], Lemma 5 and the soundness
argument of Theorem 1 (PDF pp. 9–11). Normalization removes the complement
caused by the parity of XNOR operations. The guard theorem below evaluates
actual word operations, rather than assuming a table of normalized transitions.

## Main definitions

* `normalize`: complement the actual state for odd XNOR parity.
* `fourSteps`: the four unrestricted operations on alternating operands.

## Main results

* `four_bit_guard`: the exact two accepted patterns of Lemma 5.
* `guard_forces_pattern`: forcing at an arbitrary field, with arbitrary high
  and low state bits and a later chain whose low operands are zero.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR

/-- Remove the complement introduced by an odd number of XNOR operations. -/
@[expose] def normalize {m : ℕ} (parity : Bool) (s : BitVec m) : BitVec m :=
  if parity then ~~~s else s

/-- The guard gadget, retaining all four independent operator choices. -/
@[expose] def fourSteps {m : ℕ} (b c d e : Bool) (u v : BitVec m) :
    List (Bool × BitVec m) := [(b, u), (c, v), (d, u), (e, v)]

/-- Lemma 5: only the all-add and all-XNOR patterns restore the normalized
four-bit field to one. This is a kernel computation of all sixteen cases. -/
theorem four_bit_guard (b c d e : Bool) :
    normalize (xnorParity (fourSteps b c d e 3#4 13#4))
      (eval (fourSteps b c d e 3#4 13#4) 1#4) = 1#4 ↔
    (b = false ∧ c = false ∧ d = false ∧ e = false) ∨
    (b = true ∧ c = true ∧ d = true ∧ e = true) := by
  cases b <;> cases c <;> cases d <;> cases e <;> decide

/-- Both accepted patterns have even XNOR parity. -/
theorem fourSteps_parity_of_uniform {m : ℕ} (b : Bool) (u v : BitVec m) :
    xnorParity (fourSteps b b b b u v) = false := by
  cases b <;> rfl

/-- Four additions add twice the sum of the alternating operands. -/
theorem fourSteps_add {m : ℕ} (s u v : BitVec m) :
    eval (fourSteps false false false false u v) s = s + (u + v) + (u + v) := by
  simp only [fourSteps, eval, step, Bool.false_eq_true, ↓reduceIte]
  simp only [BitVec.add_assoc]

/-- Four XNORs on alternating operands are exactly the identity. -/
theorem fourSteps_xnor {m : ℕ} (s u v : BitVec m) :
    eval (fourSteps true true true true u v) s = s := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [fourSteps, eval, step, ↓reduceIte, BitVec.getLsbD_not, hi,
    decide_true, Bool.true_and, BitVec.getLsbD_xor]
  cases s.getLsbD i <;> cases u.getLsbD i <;> cases v.getLsbD i <;> rfl

/-- Normalization commutes with every downward projection. -/
theorem normalize_project {m p : ℕ} (hp : p ≤ m) (b : Bool) (s : BitVec m) :
    (normalize b s).setWidth p = normalize b (s.setWidth p) := by
  cases b <;> simp [normalize, BitVec.setWidth_not, hp]

private theorem eval_zero_operands {m : ℕ} (xs : List (Bool × BitVec m))
    (h : ∀ x ∈ xs, x.2 = 0) (s : BitVec m) :
    eval xs s = normalize (xnorParity xs) s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨b, a⟩
    have ha : a = 0 := h (b, a) (by simp)
    have ht : ∀ x ∈ xs, x.2 = 0 := fun x hx => h x (by simp [hx])
    simp only [eval, ih ht, xnorParity, ha]
    cases b <;> cases xnorParity xs <;> simp [normalize, step]

/-- Operands with zero low fields preserve the normalized low state. The
incoming XNOR parity is arbitrary; this is the nonrepair argument in the
hardness reduction. -/
theorem normalized_low_invariant {m p : ℕ} (hp : p ≤ m)
    (xs : List (Bool × BitVec m)) (h : ∀ x ∈ xs, x.2.setWidth p = 0)
    (s : BitVec m) (parity : Bool) :
    (normalize (parity ^^ xnorParity xs) (eval xs s)).setWidth p =
      (normalize parity s).setWidth p := by
  rw [normalize_project hp, eval_project hp]
  have hz : ∀ x ∈ project p xs, x.2 = 0 := by
    intro x hx
    obtain ⟨⟨b, a⟩, ha, rfl⟩ := List.mem_map.1 hx
    exact h (b, a) ha
  have he := eval_zero_operands (project p xs) hz (s.setWidth p)
  have hpar : xnorParity (project p xs) = xnorParity xs := by
    clear h hz he
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      rcases x with ⟨b, a⟩
      change (b ^^ xnorParity (project p xs)) = (b ^^ xnorParity xs)
      rw [ih]
  rw [hpar] at he
  rw [he]
  cases parity <;> cases xnorParity xs <;> simp [normalize, BitVec.setWidth_not, hp]

private theorem extract_project {m p k : ℕ} (_hp : p + k ≤ m) (s : BitVec m) :
    (s.setWidth (k + p)).extractLsb' p k = s.extractLsb' p k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi,
    show p + i < k + p by omega]

private theorem normalize_append {k p : ℕ} (b : Bool) (s : BitVec k) (t : BitVec p) :
    normalize b (s ++ t) = normalize b s ++ normalize b t := by
  cases b <;> simp [normalize, BitVec.not_append]

/-- XNOR parity is additive under concatenation. -/
theorem xnorParity_append {m : ℕ} (xs ys : List (Bool × BitVec m)) :
    xnorParity (xs ++ ys) = (xnorParity xs ^^ xnorParity ys) := by
  induction xs with
  | nil => simp [xnorParity]
  | cons x xs ih =>
    rcases x with ⟨b, a⟩
    simp only [List.cons_append, xnorParity, ih, Bool.xor_assoc]


/-- A guard at any bit position forces the same two patterns, even with an
arbitrary later chain. The hypotheses specify actual projected operands and
fields; the conclusion constrains the four freely chosen operators. -/
theorem guard_forces_pattern {m p : ℕ} (hp : p + 4 ≤ m)
    (b c d e : Bool) (s u v : BitVec m) (low : BitVec p)
    (hs : s.setWidth (4 + p) = 1#4 ++ low)
    (hu : u.setWidth (4 + p) = 3#4 ++ 0#p)
    (hv : v.setWidth (4 + p) = 13#4 ++ 0#p)
    (tail : List (Bool × BitVec m))
    (ht : ∀ x ∈ tail, x.2.setWidth (4 + p) = 0)
    (hfinal :
      (normalize (xnorParity (fourSteps b c d e u v ++ tail))
        (eval (fourSteps b c d e u v ++ tail) s)).extractLsb' p 4 = 1#4) :
    (b = false ∧ c = false ∧ d = false ∧ e = false) ∨
    (b = true ∧ c = true ∧ d = true ∧ e = true) := by
  rw [eval_append, xnorParity_append] at hfinal
  have hlow := normalized_low_invariant (show 4 + p ≤ m by omega) tail ht
    (eval (fourSteps b c d e u v) s) (xnorParity (fourSteps b c d e u v))
  have hfield := congrArg (fun x : BitVec (4 + p) => x.extractLsb' p 4) hlow
  rw [extract_project hp, extract_project hp, hfinal] at hfield
  have hg : project (4 + p) (fourSteps b c d e u v) =
      scaled p (fourSteps b c d e 3#4 13#4) := by
    simp [fourSteps, project, scaled, hu, hv]
  have he := eval_project (show 4 + p ≤ m by omega) (fourSteps b c d e u v) s
  rw [hg, hs, eval_scaled] at he
  have hn := congrArg (normalize (xnorParity (fourSteps b c d e u v))) he
  rw [← normalize_project (show 4 + p ≤ m by omega), normalize_append] at hn
  have hp4 : xnorParity (fourSteps b c d e u v) =
      xnorParity (fourSteps b c d e 3#4 13#4) := rfl
  have hf := congrArg (fun x : BitVec (4 + p) => x.extractLsb' p 4) hn
  rw [extract_project hp, BitVec.extractLsb'_append_eq_left, hp4] at hf
  apply (four_bit_guard b c d e).1
  rw [hp4] at hfield
  exact hf.symm.trans hfield.symm


end Cslib.Cryptanalysis.AddXNOR
