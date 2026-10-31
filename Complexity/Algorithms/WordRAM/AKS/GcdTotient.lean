/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.NatGcd
public import Complexity.Computability.WordRAM.RegisterFrame
public import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.FinCases

/-!
# Step 3 of the AKS algorithm and Euler's totient on the word RAM

Step 3 of the AKS algorithm [Agrawal, Kayal, Saxena, Section 4][AKS2004] outputs COMPOSITE if
`1 < gcd(a, n) < n` for some `a ≤ r`, and step 5 needs `φ(r)`. One loop over `0 ≤ a ≤ r` does
both, with two runs of Euclid's algorithm (`Cslib.Algorithms.WordRAM.NatGcd.program`) per `a`: it
clears a flag when `gcd(n, a)` is neither `1` nor `n`, and counts the `a` with `gcd(r, a) = 1`.
The index `a = 0` is harmless (`gcd(n, 0) = n`), and for `r ≥ 2` neither `0` nor `r` is coprime
to `r`, so the count is `φ(r)`.

## Main definitions

* `Cslib.Algorithms.WordRAM.AKS.GcdTotient.program`: the loop.
* `Cslib.Algorithms.WordRAM.AKS.GcdTotient.time`: its instruction bound.

## Main results

* `Cslib.Algorithms.WordRAM.AKS.GcdTotient.exec`: the flag records step 3 and the count is `φ(r)`,
  within `time r` instructions.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.AKS.GcdTotient

open Cslib.WordRAM

/-- The number `n`, preserved. -/
abbrev n : Fin 11 := 0
/-- The modulus `r`, preserved. -/
abbrev r : Fin 11 := 1
/-- The loop index `a`. -/
abbrev a : Fin 11 := 2
/-- The loop end `r + 1`. -/
abbrev lim : Fin 11 := 3
/-- `1` while every `gcd(n, a)` seen is `1` or `n`. -/
abbrev ok : Fin 11 := 4
/-- The number of `a` seen with `gcd(r, a) = 1`. -/
abbrev phi : Fin 11 := 5
/-- Constant one. -/
abbrev one : Fin 11 := 6
/-- First argument of the gcd, and its result. -/
abbrev ga : Fin 11 := 7
/-- Second argument of the gcd. -/
abbrev gb : Fin 11 := 8

/-- Euclid's algorithm runs on `ga`, `gb` and two scratch registers. -/
def gcdMap : Fin 4 → Fin 11 := ![ga, gb, 9, 10]

theorem gcdMap_injective : gcdMap.Injective := by decide

/-- The gcd on `ga` and `gb`. -/
def gcd : Code .standard 11 := NatGcd.program.rename gcdMap

/-- Test `gcd(n, a)`, count `gcd(r, a) = 1`, and advance `a`. -/
def body : Code .standard 11 :=
  .seq (ram[ ga ← n; gb ← a ]) (.seq gcd
    (.seq (ram[ if ga = one then [ ok ← ok ] else [ if ga = n then [ ok ← ok ] else [ ok ← #0 ] ];
      ga ← r; gb ← a ]) (.seq gcd
    (ram[ if ga = one then [ phi ← phi + one ] else [ phi ← phi ]; a ← a + one ]))))

/-- Run the body for `a = 0, 1, …, r`. -/
def program : Code .standard 11 :=
  .seq (ram[ one ← #1; lim ← r + one; a ← #0; ok ← #1; phi ← #0 ]) (.loop (.lt a lim) body)

/-- The instruction bound of `program`. -/
def time (r : ℕ) : ℕ := (r + 1) * (10 * r + 21) + 7

/-- The gcd changes only `ga`, `gb` and its scratch registers. -/
private theorem gcd_regs {w T : ℕ} {x y : Data 11} (h : ExecWithin w gcd x y T) (j : Fin 11)
    (hj : j.val < 7) : y.regs j = x.regs j := by
  refine h.regs_eq (Code.preserves_rename_of_forall_ne _ _ _ ?_)
  intro b hb
  subst hb
  fin_cases b <;> simp [gcdMap] at hj

private theorem gcd_exec {w : ℕ} (x : Data 11) {u v : ℕ} (hu : x.regs ga = u) (hv : x.regs gb = v)
    (hfu : Fits w u) (hfv : Fits w v) :
    ∃ y, ExecWithin w gcd x y (5 * v + 3) ∧ y.regs ga = Nat.gcd u v ∧
      ∀ j : Fin 11, j.val < 7 → y.regs j = x.regs j := by
  obtain ⟨y, hy, hg, -⟩ := NatGcd.exec_rename gcdMap gcdMap_injective x
    (by rw [show gcdMap NatGcd.a = ga from rfl, hu]; exact hfu)
    (by rw [show gcdMap NatGcd.b = gb from rfl, hv]; exact hfv)
  refine ⟨y, ?_, ?_, fun j hj => gcd_regs hy j hj⟩
  · rw [show gcdMap NatGcd.b = gb from rfl, hv] at hy; exact hy
  · rw [show ga = gcdMap NatGcd.a from rfl, hg, show gcdMap NatGcd.a = ga from rfl,
      show gcdMap NatGcd.b = gb from rfl, hu, hv]

/-- Counting the residues coprime to `r ≥ 2` up to `r` inclusive gives `φ(r)`. -/
private theorem card_filter_coprime_range_succ {R : ℕ} (hR : 2 ≤ R) :
    ((Finset.range (R + 1)).filter R.Coprime).card = Nat.totient R := by
  rw [Finset.range_add_one, Finset.filter_insert]
  simp [Nat.coprime_self, show R ≠ 1 by omega, Nat.totient_eq_card_coprime]

/-- The loop invariant. -/
private def Inv (N R : ℕ) (y : Data 11) : Prop :=
  y.regs n = N ∧ y.regs r = R ∧ y.regs one = 1 ∧ y.regs lim = R + 1 ∧ y.regs a ≤ R + 1 ∧
    y.regs ok ≤ 1 ∧ (y.regs ok = 1 ↔ ∀ b < y.regs a, Nat.gcd N b = 1 ∨ Nat.gcd N b = N) ∧
    y.regs phi = ((Finset.range (y.regs a)).filter R.Coprime).card

private theorem body_step {w N R : ℕ} (hfN : Fits w N) (hfR : Fits w (R + 1)) (y : Data 11)
    (hy : Inv N R y) (hc : (Cond.lt a lim).Holds y) :
    ∃ z, ExecWithin w body y z (10 * R + 19) ∧ Inv N R z ∧
      R + 1 - z.regs a < R + 1 - y.regs a := by
  classical
  obtain ⟨hyn, hyr, hy1, hyl, hya, hyok, hyiff, hyphi⟩ := hy
  obtain ⟨A, hA⟩ : ∃ A, y.regs a = A := ⟨_, rfl⟩
  have hAR : A ≤ R := by simp only [Cond.holds_lt, hA, hyl] at hc; omega
  rw [hA] at hyiff hyphi
  have hfA : Fits w A := hfR.of_le (by omega)
  have h1f : Fits w 1 := hfR.of_le (by omega)
  -- `gcd(n, a)`.
  let y₁ := (y.set ga N).set gb A
  have hrun₁ : ExecWithin (B := .standard) w (ram[ ga ← n; gb ← a ]) y y₁ 2 := by
    ram_eval [y₁, hyn, hA]
  have hy₁ (j : Fin 11) (hj : j.val < 7) : y₁.regs j = y.regs j := by
    have h9 : j ≠ ga ∧ j ≠ gb := by constructor <;> (intro h; subst h; simp at hj)
    simp [y₁, h9.1, h9.2]
  obtain ⟨y₂, hrun₂, hg₂, hy₂⟩ := gcd_exec (w := w) y₁ (u := N) (v := A) (by simp +decide [y₁])
    (by simp +decide [y₁]) hfN hfA
  have hy₂' (j : Fin 11) (hj : j.val < 7) : y₂.regs j = y.regs j := by rw [hy₂ j hj, hy₁ j hj]
  -- Record step 3.
  let o := if Nat.gcd N A = 1 ∨ Nat.gcd N A = N then y.regs ok else 0
  let y₃ := ((y₂.set ok o).set ga R).set gb A
  have hy₂ok : y₂.regs ok = y.regs ok := hy₂' ok (by simp)
  have hy₂n : y₂.regs n = N := by rw [hy₂' n (by simp), hyn]
  have hy₂1 : y₂.regs one = 1 := by rw [hy₂' one (by simp), hy1]
  have hy₂r : y₂.regs r = R := by rw [hy₂' r (by simp), hyr]
  have hy₂a : y₂.regs a = A := by rw [hy₂' a (by simp), hA]
  have hrun₃ : ExecWithin (B := .standard) w
      (ram[ if ga = one then [ ok ← ok ] else [ if ga = n then [ ok ← ok ] else [ ok ← #0 ] ];
        ga ← r; gb ← a ]) y₂ y₃ 7 := by
    by_cases hg1 : Nat.gcd N A = 1
    · refine ExecWithin.mono (T := 4) ?_ (by omega)
      ram_eval [y₃, o, hg₂, hg1, hy₂1, hy₂ok, hy₂r, hy₂a]
    · by_cases hgN : Nat.gcd N A = N
      · have hN1 : ¬ N = 1 := fun h => hg1 (hgN.trans h)
        refine ExecWithin.mono (T := 6) ?_ (by omega)
        ram_eval [y₃, o, hg₂, hg1, hgN, hN1, hy₂1, hy₂n, hy₂ok, hy₂r, hy₂a]
      · ram_eval [y₃, o, hg₂, hg1, hgN, hy₂1, hy₂n, hy₂r, hy₂a]
  -- `gcd(r, a)`.
  obtain ⟨y₄, hrun₄, hg₄, hy₄⟩ := gcd_exec (w := w) y₃ (u := R) (v := A) (by simp +decide [y₃])
    (by simp +decide [y₃]) (hfR.of_le (by omega)) hfA
  have hy₄' (j : Fin 11) (hj : j.val < 7) (hjo : j ≠ ok) : y₄.regs j = y.regs j := by
    rw [hy₄ j hj]
    have h9 : j ≠ ga ∧ j ≠ gb := by constructor <;> (intro h; subst h; simp at hj)
    simp only [y₃, Data.set_regs, Function.update_of_ne h9.1, Function.update_of_ne h9.2,
      Function.update_of_ne hjo]
    exact hy₂' j hj
  have hy₄ok : y₄.regs ok = o := by rw [hy₄ ok (by simp)]; simp +decide [y₃]
  have hy₄1 : y₄.regs one = 1 := by rw [hy₄' one (by simp) (by decide), hy1]
  have hy₄phi : y₄.regs phi = y.regs phi := hy₄' phi (by simp) (by decide)
  have hy₄a : y₄.regs a = A := by rw [hy₄' a (by simp) (by decide), hA]
  -- Count and advance.
  have hphiA : ((Finset.range A).filter R.Coprime).card ≤ A :=
    (Finset.card_filter_le _ _).trans (Finset.card_range A).le
  let ph := if Nat.gcd R A = 1 then y.regs phi + 1 else y.regs phi
  let z := (y₄.set phi ph).set a (A + 1)
  have hfph : Fits w (y.regs phi + 1) := hfR.of_le (by omega)
  have hfA1 : Fits w (A + 1) := hfR.of_le (by omega)
  have hrun₅ : ExecWithin (B := .standard) w
      (ram[ if ga = one then [ phi ← phi + one ] else [ phi ← phi ]; a ← a + one ]) y₄ z 4 := by
    by_cases hg1 : Nat.gcd R A = 1
    · refine ExecWithin.mono (T := 3) ?_ (by omega)
      ram_eval [z, ph, hg₄, hg1, hy₄1, hy₄phi, hy₄a, hfph, hfA1]
    · ram_eval [z, ph, hg₄, hg1, hy₄1, hy₄phi, hy₄a, hfA1]
  have hza : z.regs a = A + 1 := by simp [z]
  refine ⟨z, (hrun₁.seq (hrun₂.seq (hrun₃.seq (hrun₄.seq hrun₅)))).mono (by omega), ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp +decide only [z, Data.set_regs, Function.update_apply, ↓reduceIte]
      rw [hy₄' n (by simp) (by decide), hyn]
    · simp +decide only [z, Data.set_regs, Function.update_apply, ↓reduceIte]
      rw [hy₄' r (by simp) (by decide), hyr]
    · simp +decide only [z, Data.set_regs, Function.update_apply, ↓reduceIte]; exact hy₄1
    · simp +decide only [z, Data.set_regs, Function.update_apply, ↓reduceIte]
      rw [hy₄' lim (by simp) (by decide), hyl]
    · rw [hza]; omega
    · simp +decide only [z, Data.set_regs, Function.update_apply, ↓reduceIte]
      rw [hy₄ok]; simp only [o]; split_ifs <;> omega
    · have hzo : z.regs ok = o := by simp +decide [z, hy₄ok]
      rw [hzo, hza]
      simp only [o]
      constructor
      · intro h b hb
        split_ifs at h with hc
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | rfl
          · exact hyiff.mp h b hb
          · exact hc
      · intro h
        have hc : Nat.gcd N A = 1 ∨ Nat.gcd N A = N := h A (by omega)
        simp only [hc, ↓reduceIte]
        exact hyiff.mpr fun b hb => h b (by omega)
    · have hzp : z.regs phi = ph := by simp +decide [z]
      rw [hzp, hza, Finset.range_add_one, Finset.filter_insert]
      simp only [ph, hyphi, Nat.Coprime]
      split_ifs with hg
      · rw [Finset.card_insert_of_notMem (by simp)]
      · rfl
  · rw [hza, hA]; omega

/-- **Step 3 and the totient.** For `r ≥ 2`, with the word size holding `n` and `r + 1`, within
`time r` instructions the flag `ok` is `1` exactly when every `1 ≤ a ≤ r` has `gcd(a, n) = 1` or
`gcd(a, n) = n`, and `phi` is `φ(r)`. For `n ≥ 1` the flag condition says that no `1 ≤ a ≤ r` has
`1 < gcd(a, n) < n`; for `n = 0` it is stronger, since `gcd(a, 0) = a`. -/
theorem exec {w : ℕ} (x : Data 11) {N R : ℕ} (hn : x.regs n = N) (hr : x.regs r = R)
    (hR : 2 ≤ R) (hfN : Fits w N) (hfR : Fits w (R + 1)) :
    ∃ y, ExecWithin w program x y (time R) ∧ y.regs ok ≤ 1 ∧
      (y.regs ok = 1 ↔ ∀ b, 1 ≤ b → b ≤ R → b.gcd N = 1 ∨ b.gcd N = N) ∧
      y.regs phi = Nat.totient R ∧ y.regs n = N ∧ y.regs r = R := by
  have h1f : Fits w 1 := hfR.of_le (by omega)
  let x₀ := ((((x.set one 1).set lim (R + 1)).set a 0).set ok 1).set phi 0
  have hrun₀ : ExecWithin (B := .standard) w
      (ram[ one ← #1; lim ← r + one; a ← #0; ok ← #1; phi ← #0 ]) x x₀ 5 := by
    ram_eval [x₀, hr, h1f, hfR]
  have hx₀ : Inv N R x₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp +decide [x₀, hn, hr]
  obtain ⟨y, hrun, hy, hc⟩ := ExecWithin.loop_invariant (Inv N R) (fun y => R + 1 - y.regs a)
    (body_step hfN hfR) hx₀
  obtain ⟨hyn, hyr, -, hyl, hya, hyok, hyiff, hyphi⟩ := hy
  have hend : y.regs a = R + 1 := by simp only [Cond.holds_lt, hyl] at hc; omega
  rw [hend] at hyiff hyphi
  refine ⟨y, (hrun₀.seq hrun).mono ?_, hyok, ?_, ?_, hyn, hyr⟩
  · have : x₀.regs a = 0 := by simp +decide [x₀]
    rw [this, Nat.sub_zero, show 10 * R + 19 + 2 = 10 * R + 21 by ring]
    unfold time
    omega
  · rw [hyiff]
    constructor
    · intro h b hb1 hbR
      rw [Nat.gcd_comm]
      exact h b (by omega)
    · intro h b hb
      rcases Nat.eq_zero_or_pos b with rfl | hb0
      · right; exact Nat.gcd_zero_right N
      · rw [Nat.gcd_comm]; exact h b hb0 (by omega)
  · rw [hyphi, card_filter_coprime_range_succ hR]

end Cslib.Algorithms.WordRAM.AKS.GcdTotient
