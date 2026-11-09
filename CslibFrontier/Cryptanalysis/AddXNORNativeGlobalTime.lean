/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORNativeDissection
public import CslibFrontier.Cryptanalysis.AddXNORNativeClassCounts
import all CslibFrontier.Cryptanalysis.AddXNORNativeClassCounts
import all CslibFrontier.Cryptanalysis.AddXNORNativeOrientedSearch
import all CslibFrontier.Cryptanalysis.AddXNORNativeClassRetain
import all CslibFrontier.Cryptanalysis.AddXNORNativeClassProbe
import all CslibFrontier.Cryptanalysis.AddXNORNativeDissection
import all CslibFrontier.Cryptanalysis.AddXNORNativeClassLoop
import all CslibFrontier.Cryptanalysis.AddXNORNativeAllClasses
import all CslibFrontier.Cryptanalysis.AddXNORNativeSelectedClass

/-!
# Charged global work of the fixed native dissection loop

The bounds sum actual indexed native stream counts and both construction
orientations. They are unconditional on balancing or random-instance means.
The explicit parameters expose the source's quarter split and projection width.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Driver

open scoped BigOperators
open Quarter

/-- Exact forward-retained lifetime budget, including dictionary release. -/
theorem orientedTime_forward {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s t : BitVec m) (g : BitVec p) :
    orientedTime false as bs cs ds s t g =
      8 * 2 ^ p + 2 ^ as.length * (11 * as.length + 22) +
      2 ^ ds.length * (18 * ds.length + 37) + 2 ^ bs.length * (18 * bs.length + 35) +
      2 ^ cs.length * (11 * cs.length + 22) + forwardCount as bs s g * (11 * bs.length + 42) +
      backwardCount cs ds t g * (18 * cs.length + 39) + 10 * (bs.length + cs.length) + 88 := by
  simp only [orientedTime, searchTime, Bool.false_eq_true, ↓reduceIte,
    classRetainTime_eq, classProbeTime_eq]
  rw [insertionCount_eq_forwardCount hp]
  rw [show (classEntries bs g (fun k => Forward.records as s p k.toNat) 0
      (2 ^ bs.length)).length = forwardCount as bs s g from
        insertionCount_eq_forwardCount hp _ _ _ _]
  rw [classProbeHits_eq_backwardCount hp]
  ring

/-- Each direction's budget is linear in its actual two class counts. -/
theorem orientedTime_forward_le {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s t : BitVec m) (g : BitVec p) :
    orientedTime false as bs cs ds s t g ≤ workFactor (totalLength as bs cs ds) *
      (quarterWork p as.length bs.length cs.length ds.length +
        forwardCount as bs s g + backwardCount cs ds t g) := by
  rw [orientedTime_forward hp]
  let q := totalLength as bs cs ds
  let C := workFactor q
  have ha : as.length ≤ q := by dsimp [q, totalLength]; omega
  have hb : bs.length ≤ q := by dsimp [q, totalLength]; omega
  have hc : cs.length ≤ q := by dsimp [q, totalLength]; omega
  have hd : ds.length ≤ q := by dsimp [q, totalLength]; omega
  have hA := Nat.mul_le_mul_left (2 ^ as.length)
    (show 11 * as.length + 22 ≤ C by dsimp [C, workFactor]; omega)
  have hB := Nat.mul_le_mul_left (2 ^ bs.length)
    (show 18 * bs.length + 35 ≤ C by dsimp [C, workFactor]; omega)
  have hC := Nat.mul_le_mul_left (2 ^ cs.length)
    (show 11 * cs.length + 22 ≤ C by dsimp [C, workFactor]; omega)
  have hD := Nat.mul_le_mul_left (2 ^ ds.length)
    (show 18 * ds.length + 37 ≤ C by dsimp [C, workFactor]; omega)
  have hF := Nat.mul_le_mul_left (forwardCount as bs s g)
    (show 11 * bs.length + 42 ≤ C by dsimp [C, workFactor]; omega)
  have hG := Nat.mul_le_mul_left (backwardCount cs ds t g)
    (show 18 * cs.length + 39 ≤ C by dsimp [C, workFactor]; omega)
  have hN : 8 * 2 ^ p + 10 * (bs.length + cs.length) + 88 ≤ C * 2 ^ p := by
    have hpos := Nat.two_pow_pos p
    have hq : bs.length + cs.length ≤ q := by dsimp [q, totalLength]; omega
    have hmul := Nat.mul_le_mul_left (2 ^ p) (show 10 * q + 96 ≤ C by dsimp [C, workFactor]; omega)
    nlinarith
  change _ ≤ C * _
  dsimp only [quarterWork]
  nlinarith

/-- The actual table-selected dispatch is bounded without assuming a class mean. -/
theorem selectedTime_le {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s t : BitVec m) (g : BitVec p) :
    selectedTime as bs cs ds s t g ≤ workFactor (totalLength as bs cs ds) *
      (quarterWork p as.length bs.length cs.length ds.length +
        forwardCount as bs s g + backwardCount cs ds t g) + 9 := by
  have hf := orientedTime_forward_le hp as bs cs ds s t g
  have hr := orientedTime_forward_le hp ds.reverse cs.reverse bs.reverse as.reverse
    (~~~t) (~~~s) (~~~g)
  have hi : orientedTime true as bs cs ds s t g =
      orientedTime false ds.reverse cs.reverse bs.reverse as.reverse (~~~t) (~~~s) (~~~g) := by
    simp only [orientedTime, Bool.false_eq_true, ↓reduceIte]
  rw [← hi, reverse_forwardCount hp, reverse_backwardCount hp] at hr
  have len : totalLength ds.reverse cs.reverse bs.reverse as.reverse = totalLength as bs cs ds := by
    simp only [totalLength, List.length_reverse]; omega
  have qw : quarterWork p ds.reverse.length cs.reverse.length bs.reverse.length as.reverse.length =
      quarterWork p as.length bs.length cs.length ds.length := by
    simp only [quarterWork, List.length_reverse]; omega
  rw [len, qw] at hr
  unfold selectedTime
  apply Nat.add_le_add_right
  apply max_le hf
  simpa only [Nat.add_comm (forwardCount as bs s g), Nat.add_assoc,
    Nat.add_left_comm] using hr

/-- The native packed class range enumerates every low-bit value exactly once. -/
theorem sum_classRange {p : ℕ} (f : BitVec p → ℕ) :
    ((List.range' 0 (2 ^ p)).map fun k => f (BitVec.ofNat p k)).sum = ∑ g, f g := by
  rw [← List.range_eq_range', ← List.sum_toFinset _ List.nodup_range,
    List.toFinset_range, Finset.sum_range]
  apply Fintype.sum_equiv BitVec.equivFin.symm.toEquiv
  intro i
  congr 1
  apply BitVec.eq_of_toNat_eq
  exact Nat.mod_eq_of_lt i.isLt

/-- Explicit instruction bound for all class lifetimes and native loop control. -/
def globalTime (p a b c d : ℕ) : ℕ :=
  prepareTime p (a + b) (c + d) +
    2 ^ p * (workFactor (a + b + c + d) * quarterWork p a b c d + 18) +
    workFactor (a + b + c + d) * (2 ^ (a + b) + 2 ^ (c + d)) + 7

/-- Global charged work, including preprocessing, both orientations, release,
and loop control. Early successful prefixes use the same full-range bound. -/
theorem dissectionTime_le {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) :
    prepareTime p (as.length + bs.length) (cs.length + ds.length) +
        (5 + loopTime (p := p) as bs cs ds s t 0 (2 ^ p)) ≤
      globalTime p as.length bs.length cs.length ds.length := by
  have card : Fintype.card (BitVec p) = 2 ^ p := by
    exact (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun g _ => selectedTime_le hp as bs cs ds s t g)
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, card, smul_eq_mul,
    ← Finset.mul_sum, sum_forwardCount hp, sum_backwardCount hp] at hsum
  rw [loopTime_eq_allTime, allTime_eq_sum, sum_classRange]
  dsimp only [globalTime, totalLength] at *
  nlinarith

/-- Counter projections, both native table constructions and the balance scan
have a linear-in-class-range instruction bound, including zero-length halves. -/
theorem prepareTime_le (p a b : ℕ) :
    prepareTime p a b ≤ workFactor (a + b) * 2 ^ p := by
  have hn := Nat.two_pow_pos p
  dsimp only [prepareTime, workFactor]
  nlinarith

/-- Explicit source-quarter specialization: for lengths `k,k,k,k+r` and `p ≤ k`,
the whole native block takes at most a linear polynomial times `2^(2*k+r)`.
For the source's split, `r` is the remainder after division by four. -/
theorem globalTime_quarters {p k r : ℕ} (hp : p ≤ k) :
    globalTime p k k k (k + r) ≤ 1000 * (4 * k + r + 1) * 2 ^ (2 * k + r) := by
  let E := 2 ^ (2 * k + r)
  let C := workFactor (k + k + k + (k + r))
  have hN : 2 ^ p ≤ E := Nat.pow_le_pow_right (by decide) (by omega)
  have hNN : 2 ^ p * 2 ^ p ≤ E := by
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hNA : 2 ^ p * 2 ^ k ≤ E := by
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hND : 2 ^ p * 2 ^ (k + r) ≤ E := by
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hQ : 2 ^ p * quarterWork p k k k (k + r) ≤ 5 * E := by
    dsimp only [quarterWork]
    nlinarith
  have hH : 2 ^ (k + k) + 2 ^ (k + (k + r)) ≤ 2 * E := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) (show k + k ≤ 2 * k + r by omega)
    have eqn : k + (k + r) = 2 * k + r := by omega
    rw [eqn]
    dsimp only [E] at *
    omega
  have hprep := prepareTime_le p (k + k) (k + (k + r))
  have hC : workFactor ((k + k) + (k + (k + r))) = C := by
    dsimp [C, workFactor]; omega
  rw [hC] at hprep
  have hpre := hprep.trans (Nat.mul_le_mul_left C hN)
  have hwork := Nat.mul_le_mul_left C hQ
  have hhalf := Nat.mul_le_mul_left C hH
  have hE : 0 < E := Nat.two_pow_pos _
  dsimp only [globalTime]
  change prepareTime p (k + k) (k + (k + r)) +
    2 ^ p * (C * quarterWork p k k k (k + r) + 18) +
      C * (2 ^ (k + k) + 2 ^ (k + (k + r))) + 7 ≤ _
  have hc : 8 * C + 25 ≤ 1000 * (4 * k + r + 1) := by
    dsimp [C, workFactor]; omega
  have hlast := Nat.mul_le_mul_right E hc
  calc
    _ ≤ C * E + (C * (5 * E) + 18 * E) + C * (2 * E) + 7 := by
      nlinarith only [hpre, hwork, hhalf, hN]
    _ ≤ (8 * C + 25) * E := by nlinarith only [hE]
    _ ≤ _ := hlast

/-- Raw original-input correctness with a global bound derived from native counts. -/
theorem dissection_global_exec {W m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m)
    (L : SearchLayout W m p as.length bs.length cs.length ds.length) (K : CounterLayout L)
    (x : Cslib.WordRAM.Data 40) (hx : L.Raw as bs cs ds (x.comap bank))
    (hprefix : ∀ i (hi : i < (as ++ bs).length),
      x.mem (K.prefixBase + i) = (as ++ bs)[i].toNat)
    (hsuffix : ∀ i (hi : i < (cs ++ ds).reverse.length),
      x.mem (K.suffixBase + i) = (cs ++ ds).reverse[i].toNat)
    (hfit : Cslib.WordRAM.Fits W (L.D + 4 * 2 ^ m + 8))
    (hload : Cslib.WordRAM.Fits W (2 * L.q₂ + 2 * 2 ^ p + 4)) :
    ∃ y, Cslib.WordRAM.ExecWithin W (dissection L K s t) x y
        (globalTime p as.length bs.length cs.length ds.length) ∧
      Cslib.WordRAM.SpaceWithin W (dissection L K s t) x y
        (globalTime p as.length bs.length cs.length ds.length)
        (dissectionSpace (p := p) L.D as bs cs ds s t) ∧
      (y.regs tag ≠ 0 ↔ ∃ g : BitVec p, PackedClassSolution as bs cs ds s t g) ∧
      (y.regs tag = 0 ↔ ¬∃ g : BitVec p, PackedClassSolution as bs cs ds s t g) ∧
      (y.regs tag ≠ 0 → eval (witness as bs cs ds y) s = t) ∧
      y.regs balance = computedBalance (p := p) as bs cs ds s t ∧
      L.Raw as bs cs ds (y.comap bank) := by
  obtain ⟨y, he, space, rest⟩ := dissection_exec hp as bs cs ds s t L K x hx
    hprefix hsuffix hfit hload
  exact ⟨y, he.mono (dissectionTime_le hp as bs cs ds s t),
    space.mono (dissectionTime_le hp as bs cs ds s t) le_rfl, rest⟩

end Cslib.Cryptanalysis.AddXNOR.Native.Driver
