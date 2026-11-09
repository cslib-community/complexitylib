/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Stack

/-!
# Native computation of query-prefix children

The real scalar programs calculate each child descriptor from the popped prefix.
All arithmetic fits follow from the original prefix, power and small alphabet bound;
there is no child-layout or execution certificate in these interfaces.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM

/-- Registers changed while computing one child descriptor. -/
@[expose] def ChildSetupLocal (i : Fin registers) : Prop :=
  i = Reg.temporary ∨ i = Reg.childCode ∨ i = Reg.childUsed ∨ i = Reg.childStars

instance (i : Fin registers) : Decidable (ChildSetupLocal i) :=
  inferInstanceAs (Decidable (i = Reg.temporary ∨ i = Reg.childCode ∨
    i = Reg.childUsed ∨ i = Reg.childStars))

private theorem indexedSetup_preserves (d : Fin 9) (i : Fin registers) :
    ¬ChildSetupLocal i → (indexedSetup d).Preserves i := by decide +revert

private theorem p0Setup_preserves (i : Fin registers) :
    ¬ChildSetupLocal i → p0Setup.Preserves i := by decide +revert

private theorem privateSetup_preserves (i : Fin registers) :
    ¬ChildSetupLocal i → privateSetup.Preserves i := by decide +revert

/-- Compute one indexed child's fields within five native instructions. -/
theorem exec_indexedSetup {w c u e p : ℕ} (d : Fin 9) (x : Data registers)
    (hc : x.regs Reg.code = c) (hu : x.regs Reg.used = u)
    (he : x.regs Reg.stars = e) (hp : x.regs Reg.power = p)
    (h1 : x.regs BoxTable.Reg.one = 1) (hfit : Fits w (c + 9 * p + u + 16)) :
    ∃ y, ExecWithin w (indexedSetup d) x y 5 ∧
      y.regs Reg.childCode = c + d.val * p ∧ y.regs Reg.childUsed = u + 1 ∧
      y.regs Reg.childStars = e ∧ y.mem = x.mem ∧
      (∀ i, ¬ChildSetupLocal i → y.regs i = x.regs i) := by
  have hd : d.val ≤ 8 := by omega
  have hdm : d.val * p ≤ 9 * p := Nat.mul_le_mul_right p (by omega)
  have hfd : Fits w d.val := hfit.of_le (by omega)
  have hfm : Fits w (d.val * p) := hfit.of_le (by omega)
  have hfc : Fits w (c + d.val * p) := hfit.of_le (by omega)
  have hfu : Fits w (u + 1) := hfit.of_le (by omega)
  let y := ((((x.set Reg.temporary d.val).set Reg.temporary (d.val * p)).set
    Reg.childCode (c + d.val * p)).set Reg.childUsed (u + 1)).set Reg.childStars e
  have hy : ExecWithin w (indexedSetup d) x y 5 := by
    ram_eval [indexedSetup, y, hc, hu, he, hp, h1, hfd, hfm, hfc, hfu,
      Reg.temporary, Reg.childCode, Reg.childUsed, Reg.childStars, Reg.code,
      Reg.used, Reg.stars, Reg.power, BoxTable.Reg.one, Fin.mk.injEq]
  exact ⟨y, hy, by simp [y, Reg.childCode, Reg.childUsed, Reg.childStars],
    by simp [y, Reg.childUsed, Reg.childStars], by simp [y], rfl,
    fun i hi => hy.regs_eq (indexedSetup_preserves d i hi)⟩

/-- P0 extends the initial star count precisely before any indexed inner term was chosen. -/
theorem exec_p0Setup {w c u e p : ℕ} (x : Data registers)
    (hc : x.regs Reg.code = c) (hu : x.regs Reg.used = u)
    (he : x.regs Reg.stars = e) (hp : x.regs Reg.power = p)
    (h1 : x.regs BoxTable.Reg.one = 1) (h9 : x.regs BoxTable.Reg.nine = 9)
    (h0 : x.regs BoxTable.Reg.nil = 0) (hfit : Fits w (c + 9 * p + u + e + 16)) :
    ∃ y, ExecWithin w p0Setup x y 6 ∧ y.regs Reg.childCode = c + 9 * p ∧
      y.regs Reg.childUsed = u ∧ y.regs Reg.childStars = (if u = 0 then e + 1 else e) ∧
      y.mem = x.mem ∧ (∀ i, ¬ChildSetupLocal i → y.regs i = x.regs i) := by
  have hfm : Fits w (9 * p) := hfit.of_le (by omega)
  have hfc : Fits w (c + 9 * p) := hfit.of_le (by omega)
  have hfe : Fits w (e + 1) := hfit.of_le (by omega)
  let y := (((x.set Reg.temporary (9 * p)).set Reg.childCode (c + 9 * p)).set
    Reg.childUsed u).set Reg.childStars (if u = 0 then e + 1 else e)
  have hy : ExecWithin w p0Setup x y 6 := by
    by_cases hz : u = 0
    all_goals ram_eval [p0Setup, y, hc, hu, he, hp, h1, h9, h0, hz, hfm, hfc, hfe,
      Reg.temporary, Reg.childCode, Reg.childUsed, Reg.childStars, Reg.code,
      Reg.used, Reg.stars, Reg.power, BoxTable.Reg.one, BoxTable.Reg.nine,
      BoxTable.Reg.nil, Fin.mk.injEq]
  exact ⟨y, hy, by simp [y, Reg.childCode, Reg.childUsed, Reg.childStars],
    by simp [y, Reg.childUsed, Reg.childStars], by simp [y], rfl,
    fun i hi => hy.regs_eq (p0Setup_preserves i hi)⟩

/-- The private term at an outer coordinate leaves both inner counters unchanged. -/
theorem exec_privateSetup {w c u e p d : ℕ} (x : Data registers) (hd : d ≤ 9)
    (hc : x.regs Reg.code = c) (hu : x.regs Reg.used = u)
    (he : x.regs Reg.stars = e) (hp : x.regs Reg.power = p)
    (hdigit : x.regs Reg.digit = d) (hfit : Fits w (c + 9 * p + 16)) :
    ∃ y, ExecWithin w privateSetup x y 4 ∧ y.regs Reg.childCode = c + d * p ∧
      y.regs Reg.childUsed = u ∧ y.regs Reg.childStars = e ∧ y.mem = x.mem ∧
      (∀ i, ¬ChildSetupLocal i → y.regs i = x.regs i) := by
  have hdm : d * p ≤ 9 * p := Nat.mul_le_mul_right p hd
  have hfm : Fits w (d * p) := hfit.of_le (by omega)
  have hfc : Fits w (c + d * p) := hfit.of_le (by omega)
  let y := (((x.set Reg.temporary (d * p)).set Reg.childCode (c + d * p)).set
    Reg.childUsed u).set Reg.childStars e
  have hy : ExecWithin w privateSetup x y 4 := by
    ram_eval [privateSetup, y, hc, hu, he, hp, hdigit, hfm, hfc,
      Reg.temporary, Reg.childCode, Reg.childUsed, Reg.childStars, Reg.code,
      Reg.used, Reg.stars, Reg.power, Reg.digit, Fin.mk.injEq]
  exact ⟨y, hy, by simp [y, Reg.childCode, Reg.childUsed, Reg.childStars],
    by simp [y, Reg.childUsed, Reg.childStars], by simp [y], rfl,
    fun i hi => hy.regs_eq (privateSetup_preserves i hi)⟩

/-- Registers modified by actual output-digit decoding and child-depth/power setup. -/
@[expose] def ExpandSetupLocal (i : Fin registers) : Prop :=
  i = Reg.digit ∨ i = Reg.depth ∨ i = Reg.childPower

instance (i : Fin registers) : Decidable (ExpandSetupLocal i) :=
  inferInstanceAs (Decidable (i = Reg.digit ∨ i = Reg.depth ∨ i = Reg.childPower))

private theorem expandSetup_preserves (i : Fin registers) :
    ¬ExpandSetupLocal i → expandSetup.Preserves i := by decide +revert

/-- Decode the real next output digit with native division/remainder, then prepare the child. -/
theorem exec_expandSetup {w q k p : ℕ} (x : Data registers)
    (hq : x.regs Reg.query = q) (hk : x.regs Reg.depth = k)
    (hp : x.regs Reg.power = p) (h1 : x.regs BoxTable.Reg.one = 1)
    (h10 : x.regs BoxTable.Reg.ten = 10) (hfit : Fits w (q + k + 10 * p + 16)) :
    ∃ y, ExecWithin w expandSetup x y 4 ∧
      y.regs Reg.digit = q / p % 10 ∧ y.regs Reg.depth = k + 1 ∧
      y.regs Reg.childPower = p * 10 ∧ y.mem = x.mem ∧
      (∀ i, ¬ExpandSetupLocal i → y.regs i = x.regs i) := by
  have hdiv : q / p ≤ q := Nat.div_le_self _ _
  have hmod : q / p % 10 < 10 := Nat.mod_lt _ (by decide)
  have hfd : Fits w (q / p) := hfit.of_le (by omega)
  have hfm : Fits w (q / p % 10) := hfit.of_le (by omega)
  have hfk : Fits w (k + 1) := hfit.of_le (by omega)
  have hfp : Fits w (p * 10) := hfit.of_le (by omega)
  let y := (((x.set Reg.digit (q / p)).set Reg.digit (q / p % 10)).set
    Reg.depth (k + 1)).set Reg.childPower (p * 10)
  have hy : ExecWithin w expandSetup x y 4 := by
    ram_eval [expandSetup, y, hq, hk, hp, h1, h10, hfd, hfm, hfk, hfp,
      Reg.digit, Reg.depth, Reg.childPower, Reg.query, Reg.power,
      BoxTable.Reg.one, BoxTable.Reg.ten, Fin.mk.injEq]
  exact ⟨y, hy, by simp [y, Reg.digit, Reg.depth, Reg.childPower],
    by simp [y, Reg.depth, Reg.childPower], by simp [y], rfl,
    fun i hi => hy.regs_eq (expandSetup_preserves i hi)⟩

/-- Registers changed by descriptor computation and actual indexed-child stores. -/
@[expose] def IndexedPushLocal (i : Fin registers) : Prop := ChildSetupLocal i ∨ PushLocal i

instance (i : Fin registers) : Decidable (IndexedPushLocal i) :=
  inferInstanceAs (Decidable (ChildSetupLocal i ∨ PushLocal i))

private theorem push_preserves_local (i : Fin registers) :
    ¬PushLocal i → push.Preserves i := by decide +revert

private theorem indexedChildren_preserves (ds : List (Fin 9)) (i : Fin registers)
    (hi : ¬IndexedPushLocal i) : (indexedChildren ds).Preserves i := by
  induction ds with
  | nil =>
    simp only [indexedChildren, Code.Preserves, Op.dest]
    have hne : Reg.temporary ≠ i := fun h => hi (Or.inl (Or.inl h.symm))
    simpa using hne
  | cons d ds ih =>
    exact ⟨⟨indexedSetup_preserves d i (fun h => hi (Or.inl h)),
      push_preserves_local i (fun h => hi (Or.inr h))⟩, ih⟩

/-- The actual consecutive stores of a fixed indexed-child dispatch. -/
@[expose] def writeIndexedChildren (F k c u e p cp : ℕ) : ℕ → List (Fin 9) →
    (ℕ → ℕ) → (ℕ → ℕ)
  | _, [], μ => μ
  | n, d :: ds, μ => writeIndexedChildren F k c u e p cp (n + 1) ds
      (writeTask F n k (c + d.val * p) (u + 1) e cp μ)

/-- The fixed finite dispatch charges seventeen instructions per indexed child and one exit copy. -/
theorem exec_indexedChildren {w F n k c u e p cp : ℕ} (ds : List (Fin 9))
    (x : Data registers) (hF : x.regs Reg.stack = F) (hn : x.regs Reg.top = n)
    (hk : x.regs Reg.depth = k) (hc : x.regs Reg.code = c)
    (hu : x.regs Reg.used = u) (he : x.regs Reg.stars = e)
    (hp : x.regs Reg.power = p) (hcp : x.regs Reg.childPower = cp)
    (h5 : x.regs Reg.five = 5) (h1 : x.regs BoxTable.Reg.one = 1)
    (hfit : Fits w (F + 5 * (n + ds.length + 1) + c + 9 * p + u + e + 32)) :
    ∃ y, ExecWithin w (indexedChildren ds) x y (17 * ds.length + 1) ∧
      y.regs Reg.top = n + ds.length ∧
      y.mem = writeIndexedChildren F k c u e p cp n ds x.mem ∧
      (∀ i, ¬IndexedPushLocal i → y.regs i = x.regs i) := by
  induction ds generalizing n x with
  | nil =>
    let y := x.set Reg.temporary (x.regs Reg.temporary)
    have hy : ExecWithin w (indexedChildren []) x y 1 := ExecWithin.copy
    exact ⟨y, hy, by simpa [y, Reg.top, Reg.temporary] using hn, rfl,
      fun i hi => hy.regs_eq (indexedChildren_preserves [] i hi)⟩
  | cons d ds ih =>
    obtain ⟨a, ha, ac, au, ae, am, af⟩ := exec_indexedSetup d x hc hu he hp h1
      (hfit.of_le (by omega))
    have afr (i : Fin registers) (hi : ¬ChildSetupLocal i) : a.regs i = x.regs i := af i hi
    obtain ⟨b, hb, bn, bm, bf⟩ := exec_push a
      ((afr _ (by decide)).trans hF) ((afr _ (by decide)).trans hn)
      ((afr _ (by decide)).trans hk) ac au ae
      ((afr _ (by decide)).trans hcp) ((afr _ (by decide)).trans h5)
      ((afr _ (by decide)).trans h1) (hfit.of_le (by simp only [List.length_cons] at *; omega))
    have bfr (i : Fin registers) (hi : ¬IndexedPushLocal i) : b.regs i = x.regs i :=
      (bf i (fun h => hi (Or.inr h))).trans (af i (fun h => hi (Or.inl h)))
    obtain ⟨y, hy, yn, ym, _⟩ := ih b
      ((bfr _ (by decide)).trans hF) bn
      ((bfr _ (by decide)).trans hk) ((bfr _ (by decide)).trans hc)
      ((bfr _ (by decide)).trans hu) ((bfr _ (by decide)).trans he)
      ((bfr _ (by decide)).trans hp) ((bfr _ (by decide)).trans hcp)
      ((bfr _ (by decide)).trans h5) ((bfr _ (by decide)).trans h1)
      (hfit.of_le (by simp only [List.length_cons]; omega))
    have hex : ExecWithin w (indexedChildren (d :: ds)) x y
        (17 * (d :: ds).length + 1) := (ha.seq hb |>.seq hy).mono (by simp; omega)
    refine ⟨y, hex, by simpa only [List.length_cons, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using yn, ?_,
      fun i hi => hex.regs_eq (indexedChildren_preserves (d :: ds) i hi)⟩
    simpa only [writeIndexedChildren, bm, am] using ym

/-- The actual nine indexed children require at most 154 native instructions. -/
theorem exec_nineChildren {w F n k c u e p cp : ℕ} (x : Data registers)
    (hF : x.regs Reg.stack = F) (hn : x.regs Reg.top = n)
    (hk : x.regs Reg.depth = k) (hc : x.regs Reg.code = c)
    (hu : x.regs Reg.used = u) (he : x.regs Reg.stars = e)
    (hp : x.regs Reg.power = p) (hcp : x.regs Reg.childPower = cp)
    (h5 : x.regs Reg.five = 5) (h1 : x.regs BoxTable.Reg.one = 1)
    (hfit : Fits w (F + 5 * (n + 10) + c + 9 * p + u + e + 32)) :
    ∃ y, ExecWithin w nineChildren x y 154 ∧ y.regs Reg.top = n + 9 ∧
      y.mem = writeIndexedChildren F k c u e p cp n
        (List.ofFn fun i : Fin 9 => ⟨8 - i.val, by omega⟩) x.mem ∧
      (∀ i, ¬IndexedPushLocal i → y.regs i = x.regs i) := by
  simpa only [nineChildren, List.length_ofFn] using exec_indexedChildren
    (List.ofFn fun i : Fin 9 => ⟨8 - i.val, by omega⟩) x hF hn hk hc hu he hp hcp h5 h1
    (by simpa only [List.length_ofFn] using hfit)

/-- Consecutive child stores preserve every word outside their actual written interval. -/
theorem writeIndexedChildren_frame (F k c u e p cp n : ℕ) (ds : List (Fin 9))
    (μ : ℕ → ℕ) (q : ℕ)
    (hq : ¬(F + n * 5 ≤ q ∧ q < F + (n + ds.length) * 5)) :
    writeIndexedChildren F k c u e p cp n ds μ q = μ q := by
  induction ds generalizing n μ with
  | nil => rfl
  | cons d ds ih =>
    rw [writeIndexedChildren, ih]
    · exact writeTask_frame _ _ _ _ _ _ _ _ _ (by
        simp only [List.length_cons] at hq
        omega)
    · simp only [List.length_cons] at hq
      omega

/-- Each indexed task is read back at its actual consecutive stack position, in push order. -/
theorem writeIndexedChildren_read (F k c u e p cp n : ℕ) (ds : List (Fin 9))
    (μ : ℕ → ℕ) {j : ℕ} (hj : j < ds.length) :
    let ν := writeIndexedChildren F k c u e p cp n ds μ
    let a := F + (n + j) * 5
    ν a = k ∧ ν (a + 1) = c + (ds[j]).val * p ∧ ν (a + 2) = u + 1 ∧
      ν (a + 3) = e ∧ ν (a + 4) = cp := by
  dsimp only
  induction ds generalizing n μ j with
  | nil => simp at hj
  | cons d ds ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.getElem_cons_zero]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      all_goals
        rw [writeIndexedChildren, writeIndexedChildren_frame]
        · simp [writeTask]
        · omega
    | succ j =>
      have hj' : j < ds.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hj
      simpa only [writeIndexedChildren, List.getElem_cons_succ,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (n + 1) (writeTask F n k (c + d.val * p) (u + 1) e cp μ) hj'

/-- The complete P0 child stores its computed descriptor, with no old-memory premise. -/
theorem exec_p0Child {w F n k c u e p cp : ℕ} (x : Data registers)
    (hF : x.regs Reg.stack = F) (hn : x.regs Reg.top = n)
    (hk : x.regs Reg.depth = k) (hc : x.regs Reg.code = c)
    (hu : x.regs Reg.used = u) (he : x.regs Reg.stars = e)
    (hp : x.regs Reg.power = p) (hcp : x.regs Reg.childPower = cp)
    (h5 : x.regs Reg.five = 5) (h1 : x.regs BoxTable.Reg.one = 1)
    (h9 : x.regs BoxTable.Reg.nine = 9) (h0 : x.regs BoxTable.Reg.nil = 0)
    (hfit : Fits w (F + 5 * (n + 1) + c + 9 * p + u + e + 32)) :
    ∃ y, ExecWithin w p0Child x y 18 ∧ y.regs Reg.top = n + 1 ∧
      y.mem = writeTask F n k (c + 9 * p) u (if u = 0 then e + 1 else e) cp x.mem ∧
      (∀ i, ¬IndexedPushLocal i → y.regs i = x.regs i) := by
  obtain ⟨a, ha, ac, au, ae, am, af⟩ := exec_p0Setup x hc hu he hp h1 h9 h0
    (hfit.of_le (by omega))
  obtain ⟨y, hy, yn, ym, _⟩ := exec_push a
    ((af _ (by decide)).trans hF) ((af _ (by decide)).trans hn)
    ((af _ (by decide)).trans hk) ac au ae
    ((af _ (by decide)).trans hcp) ((af _ (by decide)).trans h5)
    ((af _ (by decide)).trans h1) (hfit.of_le (by omega))
  have hex : ExecWithin w p0Child x y 18 := ha.seq hy
  refine ⟨y, hex, yn, ?_, ?_⟩
  · simpa only [am] using ym
  · intro i hi
    apply hex.regs_eq
    exact ⟨p0Setup_preserves i (fun h => hi (Or.inl h)),
      push_preserves_local i (fun h => hi (Or.inr h))⟩

/-- The sole private child at an outer coordinate is computed and stored in sixteen steps. -/
theorem exec_privateChild {w F n k c u e p cp d : ℕ} (x : Data registers) (hd : d ≤ 9)
    (hF : x.regs Reg.stack = F) (hn : x.regs Reg.top = n)
    (hk : x.regs Reg.depth = k) (hc : x.regs Reg.code = c)
    (hu : x.regs Reg.used = u) (he : x.regs Reg.stars = e)
    (hp : x.regs Reg.power = p) (hcp : x.regs Reg.childPower = cp)
    (hdigit : x.regs Reg.digit = d)
    (h5 : x.regs Reg.five = 5) (h1 : x.regs BoxTable.Reg.one = 1)
    (hfit : Fits w (F + 5 * (n + 1) + c + 9 * p + u + e + 32)) :
    ∃ y, ExecWithin w privateChild x y 16 ∧ y.regs Reg.top = n + 1 ∧
      y.mem = writeTask F n k (c + d * p) u e cp x.mem ∧
      (∀ i, ¬IndexedPushLocal i → y.regs i = x.regs i) := by
  obtain ⟨a, ha, ac, au, ae, am, af⟩ := exec_privateSetup x hd hc hu he hp hdigit
    (hfit.of_le (by omega))
  obtain ⟨y, hy, yn, ym, _⟩ := exec_push a
    ((af _ (by decide)).trans hF) ((af _ (by decide)).trans hn)
    ((af _ (by decide)).trans hk) ac au ae
    ((af _ (by decide)).trans hcp) ((af _ (by decide)).trans h5)
    ((af _ (by decide)).trans h1) (hfit.of_le (by omega))
  have hex : ExecWithin w privateChild x y 16 := ha.seq hy
  refine ⟨y, hex, yn, ?_, ?_⟩
  · simpa only [am] using ym
  · intro i hi
    apply hex.regs_eq
    exact ⟨privateSetup_preserves i (fun h => hi (Or.inl h)),
      push_preserves_local i (fun h => hi (Or.inr h))⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
