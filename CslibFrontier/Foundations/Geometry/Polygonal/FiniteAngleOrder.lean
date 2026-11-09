/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.CircleGaps

/-!
# Real representatives of a finite directed circular order

A finite clockwise enumeration admits real angle representatives in one open turn,
in reverse linear order. The argument cut is chosen in the prescribed gap before the
last clockwise entry. Singleton enumerations are included.
-/

public section

namespace Cslib.Polygonal

/-- Choose one open turn of real representatives for a finite clockwise enumeration.
Only the circular order at its specified last entry is needed. -/
theorem exists_reverse_ordered_angle_lift (n : ℕ) (dir : Fin (n + 1) → Real.Angle)
    (hinj : Function.Injective dir)
    (horder : ∀ i j, i ≠ Fin.last n → j ≠ Fin.last n → i ≠ j →
      (sbtw (dir (Fin.last n)) (dir i) (dir j) ↔ j.val < i.val)) :
    ∃ cut : ℝ, ∃ L : Real.Angle → ℝ,
      (∀ i, L (dir i) ∈ Set.Ioo cut (cut + 2 * Real.pi)) ∧
      (∀ φ, (L φ : Real.Angle) = φ) ∧
      (∀ i j, L (dir i) < L (dir j) ↔ j.val < i.val) := by
  classical
  let : Fact ((0 : ℝ) < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  let base := (dir (Fin.last n)).toReal
  let L : Real.Angle → ℝ := fun φ => (AddCircle.equivIco (2 * Real.pi) base φ).val
  have hcoe (φ : Real.Angle) : (L φ : Real.Angle) = φ := AddCircle.coe_equivIco
  have hmem (φ : Real.Angle) : L φ ∈ Set.Ico base (base + 2 * Real.pi) :=
    (AddCircle.equivIco (2 * Real.pi) base φ).property
  have ho : L (dir (Fin.last n)) = base := by
    have h := AddCircle.equivIco_coe_of_mem (p := 2 * Real.pi)
      (a := base) ⟨le_rfl, by linarith [Real.pi_pos]⟩
    change L (dir (Fin.last n)) = base
    rw [← Real.Angle.coe_toReal (dir (Fin.last n))]
    exact h
  have hstrict (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
      base < L (dir i) := by
    have hne : L (dir i) ≠ base := by
      intro heq
      have hangle := congrArg (fun t : ℝ => (t : Real.Angle)) (heq.trans ho.symm)
      rw [hcoe, hcoe] at hangle
      exact hi (hinj hangle)
    exact lt_of_le_of_ne (hmem _).1 hne.symm
  let T := Finset.univ.image (fun i => L (dir i))
  have hT : T.Nonempty := ⟨L (dir (Fin.last n)), Finset.mem_image.mpr
    ⟨Fin.last n, Finset.mem_univ _, rfl⟩⟩
  let M := T.sup' hT id
  have hM : M < base + 2 * Real.pi := by
    apply (Finset.sup'_lt_iff hT).mpr
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (hmem _).2
  let ε := (base + 2 * Real.pi - M) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  refine ⟨base - ε, L, ?_, hcoe, ?_⟩
  · intro i
    have hMi : L (dir i) ≤ M := by
      change L (dir i) ≤ T.sup' hT id
      exact Finset.le_sup' id (show L (dir i) ∈ T from
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    have hlo := (hmem (dir i)).1
    constructor <;> dsimp [ε] <;> linarith
  · intro i j
    by_cases hi : i = Fin.last n
    · subst i
      by_cases hj : j = Fin.last n
      · subst j
        simp
      · rw [ho]
        have hjv : j.val < n := by
          have h := j.isLt
          have hn : j.val ≠ n := fun heq => hj (Fin.ext heq)
          omega
        exact iff_of_true (hstrict j hj) hjv
    · by_cases hj : j = Fin.last n
      · subst j
        rw [ho]
        exact iff_of_false (not_lt.mpr (hmem _).1) (by change ¬n < i.val; omega)
      · by_cases hij : i = j
        · subst j
          simp
        · have h := sbtw_angle_cut_iff_lt
            ⟨hstrict i hi, (hmem _).2⟩ ⟨hstrict j hj, (hmem _).2⟩
          rw [hcoe, hcoe, ← ho, hcoe] at h
          exact h.symm.trans (horder i j hi hj hij)

end Cslib.Polygonal
