/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Raw.Primrec

/-!
# Relativized interpretations of raw formulas

A one-dimensional relativized interpretation of raw formulas is given by a domain formula `D x`
(with free variable `x`) and, for each atom `R_r(x̄)`, a defining formula `θ r x̄`.
`Cslib.Logic.FO.RawFormula.interpret D θ φ` replaces each atom of `φ` by its defining formula and
relativizes each quantifier `∀ x` to `D x`. If, in a structure `E` on `G`, the formula `D x`
defines the set `P` and the formulas `θ r x̄` define relations `R r` on the subtype `P`, then
`interpret D θ φ` holds in `E` exactly when `φ` holds in `R`
(`Cslib.Logic.FO.RawFormula.realize_interpret`). The defining formulas may use variables at or
above a bound `B` as bound variables, provided the formulas `φ` have their variables below `B`.

The map `φ ↦ interpret D θ φ` is primitive recursive whenever `D` and `θ` are
(`Cslib.Logic.FO.RawFormula.primrec₂_interpret`). This is what the reductions in this library
need: Mathlib-syntax interpretations (`Cslib.Logic.FO.Interpretation`,
`CslibFrontier/Logics/FirstOrder/Interpretation.lean`) are multi-dimensional and handle Mathlib's
`L.Formula`, but they choose enumerations of finite types and are noncomputable.

## Main definitions

* `Cslib.Logic.FO.RawFormula.interpret`: the translation of formulas.

## Main results

* `Cslib.Logic.FO.RawFormula.realize_interpret`: the interpretation lemma.
* `Cslib.Logic.FO.RawFormula.atoms_interpret`: the atoms of the translation.
* `Cslib.Logic.FO.RawFormula.primrec₂_interpret`: the translation is primitive recursive.
-/

public section

namespace Cslib.Logic.FO

namespace RawFormula

/-- The relativized one-dimensional interpretation: atoms `R_r(x̄)` are replaced by `θ r x̄` and
quantifiers `∀ x` are relativized to the domain formula `D x`. -/
def interpret (D : ℕ → RawFormula) (θ : ℕ → List ℕ → RawFormula) : RawFormula → RawFormula
  | falsum => falsum
  | equal x y => equal x y
  | rel r args => θ r args
  | imp φ ψ => imp (interpret D θ φ) (interpret D θ ψ)
  | all x φ => all x (imp (D x) (interpret D θ φ))

/-- **The interpretation lemma.** Suppose `D x` defines the domain `P` and `θ r x̄` defines the
relation `R r` on `P`, for argument variables below `B` and atoms satisfying `Q`. Then a formula
with variables below `B` and atoms satisfying `Q` holds of its interpretation under `w` exactly
when it holds in `R` under any assignment `u` into `P` agreeing with `w` below `B`. -/
theorem realize_interpret {G : Type*} {E : ℕ → List G → Prop} {P : G → Prop}
    {R : ℕ → List (Subtype P) → Prop} {D : ℕ → RawFormula} {θ : ℕ → List ℕ → RawFormula}
    {B : ℕ} {Q : ℕ × ℕ → Prop} (hD : ∀ x (w : ℕ → G), (D x).Realize E w ↔ P (w x))
    (hθ : ∀ r args (w : ℕ → G) (u : ℕ → Subtype P), (∀ x ∈ args, x < B) →
      (∀ x < B, w x = u x) → Q (r, args.length) →
      ((θ r args).Realize E w ↔ R r (args.map u))) :
    ∀ (φ : RawFormula), (∀ a ∈ φ.atoms, Q a) → φ.varBound ≤ B →
      ∀ (w : ℕ → G) (u : ℕ → Subtype P), (∀ x < B, w x = u x) →
      ((interpret D θ φ).Realize E w ↔ φ.Realize R u)
  | falsum, _, _, _, _, _ => Iff.rfl
  | equal x y, _, hB, w, u, hwu => by
    simp only [varBound] at hB
    simp only [interpret, realize_equal, hwu x (by omega), hwu y (by omega), Subtype.ext_iff]
  | rel r args, hat, hB, w, u, hwu => by
    simp only [interpret, realize_rel]
    exact hθ r args w u (fun x hx => (lt_varBound_of_mem hx).trans_le hB) hwu
      (hat _ (by simp [atoms]))
  | imp φ₁ φ₂, hat, hB, w, u, hwu => by
    simp only [varBound, max_le_iff] at hB
    simp only [atoms, List.mem_append] at hat
    simp only [interpret, realize_imp,
      realize_interpret hD hθ φ₁ (fun a ha => hat a (Or.inl ha)) hB.1 w u hwu,
      realize_interpret hD hθ φ₂ (fun a ha => hat a (Or.inr ha)) hB.2 w u hwu]
  | all x φ, hat, hB, w, u, hwu => by
    simp only [varBound, max_le_iff] at hB
    simp only [interpret, realize_all, realize_imp, hD, Function.update_self]
    have hupd : ∀ (m : Subtype P), ∀ y < B,
        Function.update w x (m : G) y = (Function.update u x m y : G) := by
      intro m y hy
      by_cases hyx : y = x
      · subst hyx; simp
      · simp [Function.update_of_ne hyx, hwu y hy]
    constructor
    · intro h m
      exact (realize_interpret hD hθ φ hat hB.2 _ _ (hupd m)).1 (h m m.2)
    · intro h g hg
      exact (realize_interpret hD hθ φ hat hB.2 _ _ (hupd ⟨g, hg⟩)).2 (h ⟨g, hg⟩)

theorem atoms_interpret {D : ℕ → RawFormula} {θ : ℕ → List ℕ → RawFormula} {Q : ℕ × ℕ → Prop}
    (hD : ∀ x, ∀ a ∈ (D x).atoms, Q a) (hθ : ∀ r args, ∀ a ∈ (θ r args).atoms, Q a) :
    ∀ φ : RawFormula, ∀ a ∈ (interpret D θ φ).atoms, Q a
  | falsum, _, h => by simp [interpret, atoms] at h
  | equal _ _, _, h => by simp [interpret, atoms] at h
  | rel r args, a, h => hθ r args a h
  | imp φ ψ, a, h => by
    simp only [interpret, atoms, List.mem_append] at h
    exact h.elim (atoms_interpret hD hθ φ a) (atoms_interpret hD hθ ψ a)
  | all x φ, a, h => by
    simp only [interpret, atoms, List.mem_append] at h
    exact h.elim (hD x a) (atoms_interpret hD hθ φ a)

open Primrec in
theorem primrec₂_interpret {α : Type*} [Primcodable α] {D : α → ℕ → RawFormula}
    {θ : α → ℕ → List ℕ → RawFormula} (hD : Primrec₂ D)
    (hθ : Primrec₂ fun a (p : ℕ × List ℕ) => θ a p.1 p.2) :
    Primrec₂ fun a φ => interpret (D a) (θ a) φ :=
  primrec₂_of_rec (σ := RawFormula) _ (const falsum)
    (e := fun _ p => equal p.1 p.2) (primrec_equal (fst.comp snd) (snd.comp snd)).to₂
    (r := fun a p => θ a p.1 p.2) hθ
    (i := fun _ p => imp p.2.1 p.2.2)
    (primrec_imp (fst.comp (snd.comp snd)) (snd.comp (snd.comp snd))).to₂
    (l := fun a p => all p.1.1 (imp (D a p.1.1) p.2))
    (primrec_all (fst.comp (fst.comp snd))
      (primrec_imp (hD.comp fst (fst.comp (fst.comp snd))) (snd.comp snd))).to₂
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)

end RawFormula

end Cslib.Logic.FO
