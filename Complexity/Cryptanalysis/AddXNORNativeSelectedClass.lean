/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeCounterPair
public import Complexity.Cryptanalysis.AddXNORNativeClassCounts
import all Complexity.Cryptanalysis.AddXNORNativeClassCounts
import all Complexity.Cryptanalysis.AddXNORNativeCounterPair
import all Complexity.Cryptanalysis.AddXNORNativeOrientedSearch

/-!
# Counter-table selected native class search

The branch reads the actual forward and complemented backward counter cells,
retains the smaller side (forward on ties), runs the correct conjugated inverse
construction when needed and releases the physical dictionary in either branch.
The table semantics here are an intermediate contract supplied by native paired
preprocessing, not class-size inputs to the raw-input composed endpoint.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Driver

open Cslib.WordRAM Quarter

/-- Actual table cells and addresses surviving while full-width classes execute. -/
def Ready {W m p : ℕ} (as bs cs ds : List (BitVec m)) (s t : BitVec m)
    (L : SearchLayout W m p as.length bs.length cs.length ds.length) (x : Data 40) : Prop :=
  (∀ g : BitVec p, x.mem (x.regs forwardPointer + g.toNat) = forwardCount as bs s g) ∧
  (∀ g : BitVec p, x.mem (x.regs backwardPointer + (~~~g).toNat) = backwardCount cs ds t g) ∧
  x.regs forwardPointer + 2 ^ p ≤ L.q₂ ∧ x.regs backwardPointer + 2 ^ p ≤ L.q₂ ∧
  x.regs zero = 0

/-- Scratch registers used only to load and compare the two counters. -/
abbrev forwardValue : Fin 40 := 0
/-- Actual backward multiplicity loaded for the current class. -/
abbrev backwardValue : Fin 40 := 1
/-- Address scratch for the two native counter loads. -/
abbrev countAddress : Fin 40 := 2
/-- Physical result tag of the embedded native class search. -/
abbrev tag : Fin 40 := bank Quarter.operand

/-- The direction is selected by native loads and a native comparison. -/
@[expose] def selectedClass {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (s t : BitVec m) (g : BitVec p) : Code .standard 40 :=
  .seq (ram[ countAddress ← #g.toNat; countAddress ← forwardPointer + countAddress;
    forwardValue ← *countAddress; countAddress ← #(~~~g).toNat;
    countAddress ← backwardPointer + countAddress; backwardValue ← *countAddress ])
    (.branch (.lt backwardValue forwardValue)
      (.seq (ram[ orientation ← #1 ])
        ((orientedCycle L (~~~t).toNat (~~~s).toNat (~~~g).toNat true).rename bank))
      (.seq (ram[ orientation ← #0 ])
        ((orientedCycle L s.toNat t.toNat g.toNat false).rename bank)))

/-- A uniform budget covers either selected orientation and every native load. -/
def selectedTime {m p : ℕ} (as bs cs ds : List (BitVec m))
    (s t : BitVec m) (g : BitVec p) : ℕ :=
  max (orientedTime false as bs cs ds s t g) (orientedTime true as bs cs ds s t g) + 9

/-- The high-bank direction bit interprets returned indices as an original witness. -/
def witness {m : ℕ} (as bs cs ds : List (BitVec m)) (y : Data 40) :
    List (Bool × BitVec m) :=
  orientedWitness (Decidable.decide (y.regs orientation = 1)) as bs cs ds (y.comap bank)

/-- Every high register is preserved by the embedded class lifetime. -/
theorem cycle_preserves {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (s t g : ℕ) (back : Bool) (i : Fin 40) (hi : 32 ≤ i.val) :
    ((orientedCycle L s t g back).rename bank).Preserves i := by
  apply Code.preserves_rename_of_forall_ne
  intro j he
  have hj := j.isLt
  have hv := congrArg (fun r : Fin 40 => r.val) he
  change j.val = i.val at hv
  omega

/-- The actual branch derives its direction from constructed table cells, runs
that native orientation and restores an empty dictionary for the next class. -/
theorem selectedClass_exec {W m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (g : BitVec p)
    (L : SearchLayout W m p as.length bs.length cs.length ds.length) (x : Data 40)
    (hx : L.Raw as bs cs ds (x.comap bank)) (hr : Ready as bs cs ds s t L x)
    (hfit : Fits W (L.D + 4 * 2 ^ m + 8))
    (hload : Fits W (2 * L.q₂ + 2 * 2 ^ p + 4)) :
    ∃ y, ExecWithin W (selectedClass L s t g) x y (selectedTime as bs cs ds s t g) ∧
      StoresWithin W (selectedClass L s t g) x y (selectedTime as bs cs ds s t g)
        (lifetimeStores (p := p) as bs cs ds s t) ∧
      (y.regs tag ≠ 0 ↔ PackedClassSolution as bs cs ds s t g) ∧
      (y.regs tag ≠ 0 → eval (witness as bs cs ds y) s = t) ∧
      y.regs orientation = (if backwardCount cs ds t g < forwardCount as bs s g then 1 else 0) ∧
      (∀ a, a < L.q₂ → y.mem a = x.mem a) ∧
      L.Raw as bs cs ds (y.comap bank) ∧ Ready as bs cs ds s t L y ∧
      y.regs balance = x.regs balance := by
  let F := forwardCount as bs s g
  let B := backwardCount cs ds t g
  let u := x.set countAddress g.toNat
    |>.set countAddress (x.regs forwardPointer + g.toNat) |>.set forwardValue F
    |>.set countAddress (~~~g).toNat
    |>.set countAddress (x.regs backwardPointer + (~~~g).toNat) |>.set backwardValue B
  have hg : Fits W g.toNat := hload.of_le (by have := g.isLt; omega)
  have hng : Fits W (~~~g).toNat := hload.of_le (by have := (~~~g).isLt; omega)
  have hfg : Fits W (x.regs forwardPointer + g.toNat) :=
    hload.of_le (by have := hr.2.2.1; have := g.isLt; omega)
  have hbg : Fits W (x.regs backwardPointer + (~~~g).toNat) :=
    hload.of_le (by have := hr.2.2.2.1; have := (~~~g).isLt; omega)
  have load : ExecWithin (B := .standard) W
      (ram[ countAddress ← #g.toNat; countAddress ← forwardPointer + countAddress;
        forwardValue ← *countAddress; countAddress ← #(~~~g).toNat;
        countAddress ← backwardPointer + countAddress; backwardValue ← *countAddress ]) x u 6 := by
    ram_eval [u, F, B, hr.1 g, hr.2.1 g, hg, hng, hfg, hbg,
      countAddress, forwardPointer, backwardPointer, forwardValue, backwardValue, Fin.mk.injEq]
  have run (back : Bool) : ∃ y,
      ExecWithin W (.seq (ram[ orientation ← #(if back then 1 else 0) ])
        ((orientedCycle L (if back then (~~~t).toNat else s.toNat)
          (if back then (~~~s).toNat else t.toNat)
          (if back then (~~~g).toNat else g.toNat) back).rename bank)) u y
        (1 + orientedTime back as bs cs ds s t g) ∧
      StoresWithin W (.seq (ram[ orientation ← #(if back then 1 else 0) ])
        ((orientedCycle L (if back then (~~~t).toNat else s.toNat)
          (if back then (~~~s).toNat else t.toNat)
          (if back then (~~~g).toNat else g.toNat) back).rename bank)) u y
        (1 + orientedTime back as bs cs ds s t g)
        (orientedStores back as bs cs ds s t g) ∧
      (y.regs tag ≠ 0 ↔ PackedClassSolution as bs cs ds s t g) ∧
      (y.regs tag ≠ 0 → eval (witness as bs cs ds y) s = t) ∧
      y.regs orientation = (if back then 1 else 0) ∧
      (∀ a, a < L.q₂ → y.mem a = x.mem a) ∧
      L.Raw as bs cs ds (y.comap bank) ∧ Ready as bs cs ds s t L y ∧
      y.regs balance = x.regs balance := by
    let v := u.set orientation (if back then 1 else 0)
    have flag : ExecWithin (B := .standard) W
        (ram[ orientation ← #(if back then 1 else 0) ]) u v 1 := by
      apply ExecWithin.const
      split <;> exact hload.of_le (by omega)
    obtain ⟨z, hz, stored, hit, sound, frame, raw⟩ :=
      oriented_cycle_exec hp as bs cs ds s t g L back
      (v.comap bank) (by simpa only [SearchLayout.Raw, v, u, Data.comap_mem, Data.set_mem] using hx)
      hfit
    let y := z.extend bank v
    have cycle := hz.rename bank_injective
    have yh (i : Fin 40) (hi : 32 ≤ i.val) : y.regs i = v.regs i :=
      cycle.regs_eq (cycle_preserves L _ _ _ back i hi)
    have ydir : y.regs orientation = (if back then 1 else 0) := by
      rw [yh _ (by decide)]; simp [v]
    have ym (a : ℕ) (ha : a < L.q₂) : y.mem a = x.mem a := frame a ha
    have yp : y.regs forwardPointer = x.regs forwardPointer := by
      rw [yh _ (by decide)]; simp +decide [v, u, forwardPointer, orientation,
        countAddress, forwardValue, backwardValue]
    have yq : y.regs backwardPointer = x.regs backwardPointer := by
      rw [yh _ (by decide)]; simp +decide [v, u, backwardPointer, orientation,
        countAddress, forwardValue, backwardValue]
    refine ⟨y, flag.seq cycle, ?_, ?_, ?_, ydir, ym, ?_, ?_, ?_⟩
    · simpa only [Nat.zero_add] using
        (flag.withoutStores (of_decide_eq_true rfl)).seq (stored.rename bank_injective)
    · simpa only [tag, y, Data.extend, bank_injective.extend_apply] using hit
    · intro h
      have hd : Decidable.decide (y.regs orientation = 1) = back := by
        rw [ydir]; cases back <;> decide
      simp only [witness, hd, y, Data.comap_extend bank_injective]
      exact sound (by simpa only [tag, y, Data.extend, bank_injective.extend_apply] using h)
    · simpa only [y, Data.comap_extend bank_injective] using raw
    · refine ⟨?_, ?_, by simpa only [yp] using hr.2.2.1, by simpa only [yq] using hr.2.2.2.1, ?_⟩
      · intro k; rw [yp, ym _ (by have := hr.2.2.1; have := k.isLt; omega)]; exact hr.1 k
      · intro k; rw [yq, ym _ (by have := hr.2.2.2.1; have := (~~~k).isLt; omega)]
        exact hr.2.1 k
      · rw [yh _ (by decide)]
        simpa +decide [v, u, zero, orientation, countAddress, forwardValue, backwardValue]
          using hr.2.2.2.2
    · rw [yh _ (by decide)]
      simp +decide [v, u, balance, orientation, countAddress, forwardValue, backwardValue]
  by_cases h : B < F
  · obtain ⟨y, he, stored, rest⟩ := run true
    refine ⟨y, (load.seq (ExecWithin.branch_pos ?_ he)).mono ?_, ?_, ?_⟩
    · simpa +decide [u, Cond.holds_lt, forwardValue, backwardValue, countAddress] using h
    · dsimp only [selectedTime]
      have hh := Nat.le_max_right (orientedTime false as bs cs ds s t g)
        (orientedTime true as bs cs ds s t g)
      omega
    · have hm := min_count_le_computedBalance (p := p) as bs cs ds s t g
      change min F B ≤ _ at hm
      rw [min_eq_right (Nat.le_of_lt h)] at hm
      have bound := (orientedStores_backward_le hp as bs cs ds s t g).trans
        (Nat.mul_le_mul_left _ (Nat.add_le_add_left hm _))
      refine ((load.withoutStores (of_decide_eq_true rfl)).seq
        (StoresWithin.branch_pos ?_ stored)).mono ?_ ?_
      · simpa +decide [u, Cond.holds_lt, forwardValue, backwardValue, countAddress] using h
      · dsimp only [selectedTime]
        have hh := Nat.le_max_right (orientedTime false as bs cs ds s t g)
          (orientedTime true as bs cs ds s t g)
        omega
      · simpa only [Nat.zero_add, lifetimeStores] using bound
    · simpa only [B, F, h, ↓reduceIte, Bool.true_eq] using rest
  · obtain ⟨y, he, stored, rest⟩ := run false
    refine ⟨y, (load.seq (ExecWithin.branch_neg ?_ he)).mono ?_, ?_, ?_⟩
    · simpa +decide [u, Cond.holds_lt, forwardValue, backwardValue, countAddress] using h
    · dsimp only [selectedTime]
      have hh := Nat.le_max_left (orientedTime false as bs cs ds s t g)
        (orientedTime true as bs cs ds s t g)
      omega
    · have hm := min_count_le_computedBalance (p := p) as bs cs ds s t g
      change min F B ≤ _ at hm
      rw [min_eq_left (Nat.le_of_not_gt h)] at hm
      have bound := (orientedStores_forward_le hp as bs cs ds s t g).trans
        (Nat.mul_le_mul_left _ (Nat.add_le_add_left hm _))
      refine ((load.withoutStores (of_decide_eq_true rfl)).seq
        (StoresWithin.branch_neg ?_ stored)).mono ?_ ?_
      · simpa +decide [u, Cond.holds_lt, forwardValue, backwardValue, countAddress] using h
      · dsimp only [selectedTime]
        have hh := Nat.le_max_left (orientedTime false as bs cs ds s t g)
          (orientedTime true as bs cs ds s t g)
        omega
      · simpa only [Nat.zero_add, lifetimeStores] using bound
    · simpa only [B, F, h, ↓reduceIte, Bool.false_eq_true] using rest

end Cslib.Cryptanalysis.AddXNOR.Native.Driver
