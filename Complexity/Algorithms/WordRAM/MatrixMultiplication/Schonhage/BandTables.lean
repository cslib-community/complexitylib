/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPopulation

/-!
# Charged materialization of the subset tables

## Main definitions

* `BandPreparation.tableStep`: the exact memory writes made by one table iteration.

## Main results

* `BandPreparation.exec_tableWrite`: actual inverse/forward table stores and counter updates.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open MaskTable

/-- The inverse word is initialized even for an unselected mask. Selected masks also write
one forward-table cell. This is only a mathematical description of the two native stores. -/
def tableStep (L m inv tab t : ℕ) (μ : ℕ → ℕ) : ℕ → ℕ :=
  let μ' := Function.update μ (inv + t) (lookup L m t)
  if lookup L m t = 0 then μ' else Function.update μ' (tab + prefixCount L m t) t

/-- The part of both tables computed after visiting `t` masks. The outside frame permits
arbitrary caller memory, including future query inputs and scratch regions. -/
structure TablesPrefix (L m inv tab t : ℕ) (initial current : ℕ → ℕ) : Prop where
  /-- Every visited inverse word has been initialized. -/
  inverse : ∀ a < t, current (inv + a) = lookup L m a
  /-- Every selected visited mask has been placed at its prefix rank. -/
  forward : ∀ a < t, lookup L m a ≠ 0 → current (tab + prefixCount L m a) = a
  /-- Only the two explicitly reserved table blocks may change. -/
  frame : ∀ a, ¬(inv ≤ a ∧ a < inv + 2 ^ L) → ¬(tab ≤ a ∧ a < tab + 2 ^ L) →
    current a = initial a

/-- Empty scan prefix, with no initialized-memory assumption. -/
theorem TablesPrefix.zero (L m inv tab : ℕ) (μ : ℕ → ℕ) :
    TablesPrefix L m inv tab 0 μ μ :=
  ⟨fun _ h => (Nat.not_lt_zero _ h).elim,
    fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ _ => rfl⟩

/-- The actual two stores extend the initialized table prefix by one mask. -/
theorem TablesPrefix.step {L m inv tab t : ℕ} {μ μ' : ℕ → ℕ}
    (h : TablesPrefix L m inv tab t μ μ') (ht : t < 2 ^ L)
    (hsep : inv + 2 ^ L ≤ tab) :
    TablesPrefix L m inv tab (t + 1) μ (tableStep L m inv tab t μ') := by
  have hr : prefixCount L m t < 2 ^ L := (prefixCount_le L m t).trans_lt ht
  constructor
  · intro a ha
    by_cases hat : a = t
    · subst a
      unfold tableStep
      split
      · exact Function.update_self _ _ _
      · rw [Function.update_of_ne (by omega), Function.update_self]
    · have haold : a < t := by omega
      unfold tableStep
      split
      · rw [Function.update_of_ne (by omega)]
        exact h.inverse a haold
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact h.inverse a haold
  · intro a ha hselected
    by_cases hat : a = t
    · subst a
      simp only [tableStep, hselected, ↓reduceIte, Function.update_self]
    · have haold : a < t := by omega
      have hpop := (lookup_ne_zero_iff L m a).mp hselected |>.2.1
      have hless := prefixCount_lt hpop haold
      unfold tableStep
      split
      · rw [Function.update_of_ne (by omega)]
        exact h.forward a haold hselected
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact h.forward a haold hselected
  · intro a hi hf
    have hia : a ≠ inv + t := by omega
    have hta : a ≠ tab + prefixCount L m t := by omega
    unfold tableStep
    split
    · rw [Function.update_of_ne hia]
      exact h.frame a hi hf
    · rw [Function.update_of_ne hta, Function.update_of_ne hia]
      exact h.frame a hi hf

/-- Execute the stores after the population loop. The code neither searches a supplied
table nor receives a table-validity certificate. -/
theorem exec_tableWrite {w : ℕ} (L m inv tab t : ℕ) (x : Data 96)
    (ht : t < 2 ^ L) (hinv : x.regs inverse = inv) (htab : x.regs table = tab)
    (hmask : x.regs mask = t) (hrank : x.regs rank = prefixCount L m t)
    (hpop : x.regs population = MaskTable.population L t) (hm : x.regs inner = m)
    (hsq : x.regs square = K0 L m * K0 L m)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hfit : Fits w (inv + tab + 2 ^ L + 4)) :
    ∃ y, ExecWithin w tableWrite x y 10 ∧ y.mem = tableStep L m inv tab t x.mem ∧
      y.regs mask = t + 1 ∧ y.regs rank = prefixCount L m (t + 1) ∧
      (∀ i, i ≠ address → i ≠ temporary → i ≠ mask → i ≠ rank → y.regs i = x.regs i) := by
  have hbound := prefixCount_le L m t
  have ha : Fits w (inv + t) := hfit.of_le (by omega)
  have htaddr : Fits w (tab + prefixCount L m t) := hfit.of_le (by omega)
  have hr : Fits w (prefixCount L m t + 1) := hfit.of_le (by omega)
  have ht1 : Fits w (t + 1) := hfit.of_le (by omega)
  by_cases hp : MaskTable.population L t = m
  · by_cases hselected : prefixCount L m t < K0 L m * K0 L m
    · let y := (((((((x.set address (inv + t)).write (inv + t) 0).set temporary
          (prefixCount L m t + 1)).write (inv + t) (prefixCount L m t + 1)).set
          address (tab + prefixCount L m t)).write (tab + prefixCount L m t) t).set
          rank (prefixCount L m t + 1)).set mask (t + 1)
      refine ⟨y, ?_, ?_, ?_, ?_, ?_⟩
      · ram_eval [tableWrite, y, hinv, htab, hmask, hrank, hpop, hm, hsq, h0, h1,
          ha, htaddr, hr, ht1, hp, hselected,
          inverse, table, mask, rank, population, inner, square, zero, one, address,
          temporary, Fin.mk.injEq]
      · simp [y, tableStep, lookup, ht, hp, hselected, Data.write, Data.set,
          Function.update_idem]
      · simp [y, Data.set, address, temporary, mask, rank]
      · simp [y, Data.set, address, temporary, mask, rank, prefixCount_succ, hp]
      · intro i ha ht hm hr
        simp only [y, Data.set_regs, Data.write_regs,
          Function.update_of_ne ha, Function.update_of_ne ht,
          Function.update_of_ne hm, Function.update_of_ne hr]
    · let y := ((((x.set address (inv + t)).write (inv + t) 0).set rank
          (x.regs rank)).set rank (prefixCount L m t + 1)).set mask (t + 1)
      refine ⟨y, ?_, ?_, ?_, ?_, ?_⟩
      · ram_eval [tableWrite, y, hinv, htab, hmask, hrank, hpop, hm, hsq, h0, h1,
          ha, ht1, hr, hp, hselected, inverse, table, mask, rank, population, inner,
          square, zero, one, address, temporary, Fin.mk.injEq]
      · simp [y, tableStep, lookup, ht, hp, hselected, Data.write, Data.set]
      · simp [y, Data.set, address, mask, rank]
      · simp [y, Data.set, address, mask, rank, prefixCount_succ, hp]
      · intro i ha _ hm hr
        simp only [y, Data.set_regs, Data.write_regs, Function.update_of_ne ha,
          Function.update_of_ne hm, Function.update_of_ne hr]
  · let y := (((x.set address (inv + t)).write (inv + t) 0).set rank
        (x.regs rank)).set mask (t + 1)
    refine ⟨y, ?_, ?_, ?_, ?_, ?_⟩
    · ram_eval [tableWrite, y, hinv, htab, hmask, hrank, hpop, hm, hsq, h0, h1,
        ha, ht1, hp, inverse, mask, rank, population, inner, zero, one,
        address, Fin.mk.injEq]
    · simp [y, tableStep, lookup, ht, hp, Data.write, Data.set]
    · simp [y, Data.set, address, mask, rank]
    · simp [y, Data.set, address, mask, rank, prefixCount_succ, hp, hrank]
    · intro i ha _ hm hr
      simp only [y, Data.set_regs, Data.write_regs, Function.update_of_ne ha,
        Function.update_of_ne hm, Function.update_of_ne hr]

/-- Persistent scalar parameters read by the table loops. These are register contents only;
there is no execution, fit or cost assumption in this postcondition. -/
structure TableParameters (L m inv tab : ℕ) (x : Data 96) : Prop where
  /-- Original depth. -/
  levels : x.regs levels = L
  /-- Original inner cardinality. -/
  inner : x.regs inner = m
  /-- Computed complete binary-mask range. -/
  masks : x.regs masks = 2 ^ L
  /-- Inverse-table base. -/
  inverse : x.regs inverse = inv
  /-- Forward-table base. -/
  table : x.regs table = tab
  /-- Computed number of selected masks. -/
  square : x.regs square = K0 L m * K0 L m
  /-- Constant zero. -/
  zero : x.regs zero = 0
  /-- Constant one. -/
  one : x.regs one = 1
  /-- Constant two. -/
  two : x.regs two = 2

private def tableParameterRegisters : Finset (Fin 96) :=
  {levels, inner, masks, inverse, table, square, zero, one, two}

private theorem TableParameters.of_eq {L m inv tab : ℕ} {x y : Data 96}
    (hx : TableParameters L m inv tab x)
    (h : ∀ i ∈ tableParameterRegisters, y.regs i = x.regs i) :
    TableParameters L m inv tab y := by
  exact ⟨(h _ (by decide)).trans hx.levels, (h _ (by decide)).trans hx.inner,
    (h _ (by decide)).trans hx.masks, (h _ (by decide)).trans hx.inverse,
    (h _ (by decide)).trans hx.table, (h _ (by decide)).trans hx.square,
    (h _ (by decide)).trans hx.zero, (h _ (by decide)).trans hx.one,
    (h _ (by decide)).trans hx.two⟩

/-- The complete native scan computes both tables, with all inner population scans and
outer controls charged. Outside memory may contain arbitrary caller data. -/
theorem exec_tables {w : ℕ} (L m inv tab : ℕ) (x : Data 96)
    (hx : TableParameters L m inv tab x) (hsep : inv + 2 ^ L ≤ tab)
    (hfit : Fits w (inv + tab + 2 ^ L + L + 4)) :
    ∃ y, ExecWithin w tablesCode x y ((6 * L + 17) * 2 ^ L + 4) ∧
      TableParameters L m inv tab y ∧
      (∀ a < 2 ^ L, y.mem (inv + a) = lookup L m a) ∧
      (∀ gh : Fin (K0 L m) × Fin (K0 L m),
        y.mem (tab + (pairRank gh).val) = (selectedMask gh).val) ∧
      (∀ a, ¬(inv ≤ a ∧ a < inv + 2 ^ L) → ¬(tab ≤ a ∧ a < tab + 2 ^ L) →
        y.mem a = x.mem a) := by
  have h0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
  let start := (x.set mask 0).set rank 0
  have hs : ExecWithin (B := .standard) w (ram[ mask ← #0; rank ← #0 ]) x start 2 := by
    ram_eval [start, h0, mask, rank, Fin.mk.injEq]
  have hstart : TableParameters L m inv tab start := hx.of_eq (by
    intro i hi
    have hf : ∀ i ∈ tableParameterRegisters, i ≠ mask ∧ i ≠ rank := by decide
    simp only [start, Data.set_regs, Function.update_of_ne (hf i hi).1,
      Function.update_of_ne (hf i hi).2])
  let I (y : Data 96) : Prop :=
    TableParameters L m inv tab y ∧ y.regs mask ≤ 2 ^ L ∧
      y.regs rank = prefixCount L m (y.regs mask) ∧
      TablesPrefix L m inv tab (y.regs mask) x.mem y.mem
  have hi : I start := by
    refine ⟨hstart, ?_, ?_, ?_⟩
    · simp [start, mask, rank]
    · simp [start, mask, rank, prefixCount_zero]
    · simpa [start, mask, rank] using TablesPrefix.zero L m inv tab x.mem
  have hb (y : Data 96) (hy : I y) (hc : (Cond.lt mask masks).Holds y) :
      ∃ z, ExecWithin w tableBody y z (6 * L + 15) ∧ I z ∧
        2 ^ L - z.regs mask < 2 ^ L - y.regs mask := by
    obtain ⟨hp, ht, hrank, hmem⟩ := hy
    have htlt : y.regs mask < 2 ^ L := by simpa only [Cond.holds_lt, hp.masks] using hc
    obtain ⟨u, hu, hpop, humem, huf⟩ := exec_population L (y.regs mask) y hp.levels rfl
      hp.one hp.two (hfit.of_le (by omega))
    have hup : TableParameters L m inv tab u := hp.of_eq (by
      intro i hi
      have hf : ∀ i ∈ tableParameterRegisters,
          i ≠ residue ∧ i ≠ population ∧ i ≠ counter ∧ i ≠ digit := by decide
      exact huf i (hf i hi).1 (hf i hi).2.1 (hf i hi).2.2.1 (hf i hi).2.2.2)
    have hut : u.regs mask = y.regs mask :=
      huf mask (by decide) (by decide) (by decide) (by decide)
    have hur : u.regs rank = prefixCount L m (y.regs mask) :=
      (huf rank (by decide) (by decide) (by decide) (by decide)).trans hrank
    obtain ⟨z, hz, hzmem, hzt, hzr, _⟩ := exec_tableWrite L m inv tab (y.regs mask) u
      htlt hup.inverse hup.table hut hur hpop hup.inner hup.square hup.zero hup.one
      (hfit.of_le (by omega))
    have he : ExecWithin w tableBody y z (6 * L + 15) := hu.seq hz
    have hzp : TableParameters L m inv tab z := hp.of_eq (by
      intro i hi
      apply he.regs_eq
      have hf : ∀ i ∈ tableParameterRegisters, tableBody.Preserves i := by
        simp only [tableBody, tableWrite, populationCode, Code.Preserves, Op.dest, Op.bin]
        decide
      exact hf i hi)
    refine ⟨z, he, ⟨hzp, ?_, ?_, ?_⟩, ?_⟩
    · rw [hzt]
      omega
    · simpa only [hzt] using hzr
    · rw [hzt, hzmem, humem]
      exact hmem.step htlt hsep
    · rw [hzt]
      omega
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => 2 ^ L - y.regs mask) hb hi
  have ht : y.regs mask = 2 ^ L := by
    simp only [Cond.holds_lt, hy.1.masks] at hc
    have := hy.2.1
    omega
  have hwhole : ExecWithin w tablesCode x y ((6 * L + 17) * 2 ^ L + 4) := by
    apply (hs.seq he).mono
    have hs0 : start.regs mask = 0 := by simp [start, mask, rank]
    rw [hs0, Nat.sub_zero]
    nlinarith
  refine ⟨y, hwhole, hy.1, ?_, ?_, hy.2.2.2.frame⟩
  · intro a ha
    exact hy.2.2.2.inverse a (ht ▸ ha)
  · intro gh
    have hlookup : lookup L m (selectedMask gh).val ≠ 0 := by rw [lookup_selectedMask]; omega
    have hb : (selectedMask gh).val < y.regs mask := by rw [ht]; exact (selectedMask gh).isLt
    have h := hy.2.2.2.forward (selectedMask gh).val hb hlookup
    simpa only [prefixCount_selectedMask] using h

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
