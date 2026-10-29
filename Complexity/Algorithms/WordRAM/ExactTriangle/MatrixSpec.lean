/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.WriteMatrices
public import Complexity.Algorithms.ExactTriangle.Splitting

/-!
# Modular meaning of the native instance matrices

The active middle positions use the ordinary flattening `vertex * p + label`. The left and
right zero/one entries test exactly the two modular adjacency relations of `lopInstance`.
The remaining positions are zero. All residues here are Euclidean natural residues of signed
weights, as produced by the existing native signed-residue kernel.

## Main results

* `MatrixSpec.left_entry`: left adjacency is `label ≡ weight + rho`.
* `MatrixSpec.right_entry`: right adjacency is `label ≡ -weight`.
* `MatrixSpec.left_padding`, `MatrixSpec.right_padding`: padded middle positions are zero.
* `MatrixSpec.left_lopInstance`, `MatrixSpec.right_lopInstance`: raw matrix ones are exactly
  the corresponding edges of the existing finite lopsided instance.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.MatrixSpec

open Cslib.Algorithms.ExactTriangle WriteMatrices

private theorem eq_mod_iff {p label r : ℕ} (hl : label < p) :
    label = r % p ↔ (label : ℤ) ≡ (r : ℤ) [ZMOD (p : ℤ)] := by
  rw [Int.natCast_modEq_iff]
  change label = r % p ↔ label % p = r % p
  rw [Nat.mod_eq_of_lt hl]

private theorem residue_modEq {p : ℕ} (hp : 0 < p) (w : ℤ) :
    ((w.natMod p : ℕ) : ℤ) ≡ w [ZMOD (p : ℤ)] := resFin_modEq (by omega) w

private theorem left_label {p label rho : ℕ} (hl : label < p) (w : ℤ) :
    label = (w.natMod p + rho) % p ↔
      (label : ℤ) ≡ w + (rho : ℤ) [ZMOD (p : ℤ)] := by
  rw [eq_mod_iff hl]
  have h := (residue_modEq (by omega : 0 < p) w).add (Int.ModEq.refl (rho : ℤ))
  rw [Nat.cast_add]
  exact ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩

private theorem right_label {p label : ℕ} (hl : label < p) (w : ℤ) :
    label = (p - w.natMod p) % p ↔ (label : ℤ) ≡ -w [ZMOD (p : ℤ)] := by
  rw [eq_mod_iff hl]
  have hr : w.natMod p < p := Int.natMod_lt (by omega)
  have hp0 : (p : ℤ) ≡ 0 [ZMOD (p : ℤ)] := Int.modEq_zero_iff_dvd.mpr (dvd_refl _)
  have h := hp0.sub (residue_modEq (by omega : 0 < p) w)
  rw [Nat.cast_sub hr.le]
  simp only [zero_sub] at h
  exact ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩

private theorem flat_div {d a b : ℕ} (hd : 0 < d) (hb : b < d) :
    (a * d + b) / d = a := by
  rw [Nat.mul_comm a d, Nat.mul_add_div hd, Nat.div_eq_of_lt hb, Nat.add_zero]

/-- The native left matrix has exactly the intended modular adjacency at every active middle
vertex. Pointers do not enter this semantic assertion. -/
theorem left_entry (A : Args) (R : ℕ → ℕ) (a : Fin A.n) (v : Fin A.length)
    (label : Fin A.p) (hpad : A.length * A.p ≤ A.D) (w : ℤ)
    (hR : R (a.val * A.n + A.first + v.val) = w.natMod A.p) :
    entry false A R (a.val * A.D + (v.val * A.p + label.val)) =
      if (label.val : ℤ) ≡ w + (A.rho : ℤ) [ZMOD (A.p : ℤ)] then 1 else 0 := by
  have hp : 0 < A.p := Nat.pos_of_ne_zero (by intro h; simpa [h] using label.isLt)
  have hm : v.val * A.p + label.val < A.D := by
    have hv : (v.val + 1) * A.p ≤ A.length * A.p := Nat.mul_le_mul_right A.p v.isLt
    rw [Nat.add_mul, Nat.one_mul] at hv
    omega
  have hd : 0 < A.D := by omega
  simp only [entry, Bool.false_eq_true, ↓reduceIte, flat_div hd hm,
    Nat.mul_add_mod_of_lt hm, Nat.mul_add_mod_of_lt label.isLt, flat_div hp label.isLt,
    v.isLt, hR]
  simp only [left_label label.isLt]

/-- The right matrix uses the negated B–C weight and the transposed residue lookup. -/
theorem right_entry (A : Args) (R : ℕ → ℕ) (b : Fin A.n) (v : Fin A.length)
    (label : Fin A.p) (w : ℤ)
    (hR : R (b.val * A.n + A.first + v.val) = w.natMod A.p) :
    entry true A R ((v.val * A.p + label.val) * A.n + b.val) =
      if (label.val : ℤ) ≡ -w [ZMOD (A.p : ℤ)] then 1 else 0 := by
  have hn : 0 < A.n := Nat.pos_of_ne_zero (by intro h; simpa [h] using b.isLt)
  have hp : 0 < A.p := Nat.pos_of_ne_zero (by intro h; simpa [h] using label.isLt)
  simp only [entry, ↓reduceIte, flat_div hn b.isLt, Nat.mul_add_mod_of_lt b.isLt,
    Nat.mul_add_mod_of_lt label.isLt, flat_div hp label.isLt, v.isLt, hR]
  simp only [right_label label.isLt]

/-- A padded middle column is zero even if its input residue would otherwise match. -/
theorem left_padding (A : Args) (R : ℕ → ℕ) (a : Fin A.n) (middle : Fin A.D)
    (hpad : A.length ≤ middle.val / A.p) :
    entry false A R (a.val * A.D + middle.val) = 0 := by
  simp only [entry, Bool.false_eq_true, ↓reduceIte,
    Nat.mul_add_mod_of_lt middle.isLt, show ¬middle.val / A.p < A.length by omega]

/-- A padded middle row of the right matrix is zero. -/
theorem right_padding (A : Args) (R : ℕ → ℕ) (b : Fin A.n) (middle : Fin A.D)
    (hpad : A.length ≤ middle.val / A.p) :
    entry true A R (middle.val * A.n + b.val) = 0 := by
  have hn : 0 < A.n := Nat.pos_of_ne_zero (by intro h; simpa [h] using b.isLt)
  simp only [entry, ↓reduceIte, flat_div hn b.isLt,
    show ¬middle.val / A.p < A.length by omega]

/-- Active left cells are precisely the adjacency of the existing finite lopsided instance.
The source-array equation relates original weights to their actual Euclidean residues, and
the local-to-original vertex equation identifies the selected piece coordinate. -/
theorem left_lopInstance (A : Args) (R : ℕ → ℕ)
    (wAB wBC wAC : Fin A.n → Fin A.n → ℤ) (g chunk k : ℕ) (rho : Fin A.p)
    (hrho : A.rho = rho.val) (a c : Fin A.n) (v : Fin A.length) (label : Fin A.p)
    (hpiece : c ∈ piece A.n A.D g k) (hvertex : A.first + v.val = c.val)
    (hpad : A.length * A.p ≤ A.D)
    (hR : ∀ a c, R (a.val * A.n + c.val) = (wAC a c).natMod A.p) :
    entry false A R (a.val * A.D + (v.val * A.p + label.val)) = 1 ↔
      (lopInstance wAB wBC wAC A.D g A.p (rho, chunk, k)).adjA
        a (⟨c, hpiece⟩, label) := by
  have hload : R (a.val * A.n + A.first + v.val) = (wAC a c).natMod A.p := by
    rw [Nat.add_assoc, hvertex]
    exact hR a c
  rw [left_entry A R a v label hpad (wAC a c) hload, hrho]
  simp only [lopInstance]
  split_ifs <;> simp_all

/-- Active right cells are precisely the adjacency of the same finite lopsided instance;
the stored right matrix uses its original B–C row and local middle vertex. -/
theorem right_lopInstance (A : Args) (R : ℕ → ℕ)
    (wAB wBC wAC : Fin A.n → Fin A.n → ℤ) (g chunk k : ℕ) (rho : Fin A.p)
    (b c : Fin A.n) (v : Fin A.length) (label : Fin A.p)
    (hpiece : c ∈ piece A.n A.D g k) (hvertex : A.first + v.val = c.val)
    (hR : ∀ b c, R (b.val * A.n + c.val) = (wBC b c).natMod A.p) :
    entry true A R ((v.val * A.p + label.val) * A.n + b.val) = 1 ↔
      (lopInstance wAB wBC wAC A.D g A.p (rho, chunk, k)).adjB
        (⟨c, hpiece⟩, label) b := by
  have hload : R (b.val * A.n + A.first + v.val) = (wBC b c).natMod A.p := by
    rw [Nat.add_assoc, hvertex]
    exact hR b c
  rw [right_entry A R b v label (wBC b c) hload]
  simp only [lopInstance]
  split_ifs <;> simp_all

end Cslib.Algorithms.WordRAM.ExactTriangle.MatrixSpec
