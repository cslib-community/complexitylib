/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORNativeRegisterClass
public import CslibFrontier.Cryptanalysis.AddXNORNativeAllClasses
import all CslibFrontier.Cryptanalysis.AddXNORNativeRegisterClass
import all CslibFrontier.Cryptanalysis.AddXNORNativeAllClasses
import all CslibFrontier.Cryptanalysis.AddXNORNativeSelectedClass

/-!
# Fixed-size native outer class loop

The controller computes the complemented class key, runs actual counter-selected
retention/search/release, and increments the class index after a miss. A hit copies
the bound into the index and exits without changing the original witness. The
finite decreasing-counter proof reuses the per-class native execution and the
same interval solution predicate as the earlier unrolled functional certificate.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Driver

open Cslib.WordRAM Quarter

/-- Complement the current class in its actual exclusive native range. -/
@[expose] def inverseClass : Code .standard 40 :=
  ram[ inverseIndex ← #1; inverseIndex ← classLimit - inverseIndex;
    inverseIndex ← inverseIndex - classIndex ]

/-- Early exit changes only the outer index; a miss advances exactly one class. -/
@[expose] def advanceClass : Code .standard 40 :=
  .branch (.lt zero tag) (ram[ classIndex ← classLimit ])
    (ram[ inverseIndex ← #1; classIndex ← classIndex + inverseIndex ])

/-- One constant-size native class iteration, including dictionary release. -/
@[expose] def classBody {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (s t : BitVec m) : Code .standard 40 :=
  .seq inverseClass (.seq (registerSelected L s t) advanceClass)

/-- Native outer while control, independent of the number of class values. -/
@[expose] def classLoop {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (s t : BitVec m) : Code .standard 40 :=
  .loop (.lt classIndex classLimit) (classBody L s t)

/-- Compute the range with a native shift, initialize the index and clear the tag. -/
@[expose] def searchLoop {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (s t : BitVec m) : Code .standard 40 :=
  .seq (ram[ classLimit ← #p; classIndex ← #1; classLimit ← classIndex <<< classLimit;
    classIndex ← #0; tag ← #0 ]) (classLoop L s t)

/-- Conservative full-interval time, including loop tests and complemented-key
setup. Successful prefixes are bounded by the same remaining-interval budget. -/
def loopTime {m p : ℕ} (as bs cs ds : List (BitVec m)) (s t : BitVec m) (j : ℕ) : ℕ → ℕ
  | 0 => 2
  | n + 1 => selectedTime as bs cs ds s t (BitVec.ofNat p j) +
      (9 + loopTime (p := p) as bs cs ds s t (j + 1) n)

/-- The fixed controller charges seven more instructions per class than the
unrolled reference bound, plus one final loop-exit instruction. -/
theorem loopTime_eq_allTime {m p : ℕ} (as bs cs ds : List (BitVec m))
    (s t : BitVec m) (j n : ℕ) :
    loopTime (p := p) as bs cs ds s t j n = allTime (p := p) as bs cs ds s t j n + 7 * n + 1 := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih => simp only [loopTime, allTime, ih]; omega

/-- Execute one iteration from its actual class index. Class queries, orientation
and release are derived by reuse of the proved physical per-class program. -/
theorem classBody_exec {W m p j : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m)
    (L : SearchLayout W m p as.length bs.length cs.length ds.length) (x : Data 40)
    (hx : L.Raw as bs cs ds (x.comap bank)) (hr : Ready as bs cs ds s t L x)
    (hj : x.regs classIndex = j) (hN : x.regs classLimit = 2 ^ p) (hjN : j < 2 ^ p)
    (hfit : Fits W (L.D + 4 * 2 ^ m + 8))
    (hload : Fits W (2 * L.q₂ + 2 * 2 ^ p + 4)) :
    ∃ y, ExecWithin W (classBody L s t) x y
        (selectedTime as bs cs ds s t (BitVec.ofNat p j) + 7) ∧
      SpaceWithin W (classBody L s t) x y
        (selectedTime as bs cs ds s t (BitVec.ofNat p j) + 7)
        (L.D + lifetimeStores (p := p) as bs cs ds s t) ∧
      (y.regs tag ≠ 0 ↔ PackedClassSolution as bs cs ds s t (BitVec.ofNat p j)) ∧
      (y.regs tag ≠ 0 → eval (witness as bs cs ds y) s = t) ∧
      y.regs classIndex = (if y.regs tag ≠ 0 then 2 ^ p else j + 1) ∧
      y.regs classLimit = 2 ^ p ∧
      (∀ a, a < L.q₂ → y.mem a = x.mem a) ∧
      L.Raw as bs cs ds (y.comap bank) ∧ Ready as bs cs ds s t L y ∧
      y.regs balance = x.regs balance := by
  let g : BitVec p := BitVec.ofNatLT j hjN
  have gnat : g.toNat = j := rfl
  have geq : g = BitVec.ofNat p j := BitVec.ofNatLT_eq_ofNat hjN
  let z := x.set inverseIndex 1 |>.set inverseIndex (2 ^ p - 1)
    |>.set inverseIndex (2 ^ p - 1 - j)
  have h1 : Fits W 1 := hload.of_le (by omega)
  have hmask : Fits W (2 ^ p - 1) := hload.of_le (by omega)
  have hkey : Fits W (2 ^ p - 1 - j) := hload.of_le (by omega)
  have setup : ExecWithin W inverseClass x z 3 := by
    ram_eval [inverseClass, z, hN, hj, h1, hmask, hkey,
      classLimit, classIndex, inverseIndex, Fin.mk.injEq]
  obtain ⟨u, hu, stores, hit, sound, _, frame, raw, ready, ub⟩ :=
    selectedClass_exec hp as bs cs ds s t g L z
      (by simpa only [SearchLayout.Raw, z, Data.comap_mem, Data.set_mem] using hx)
      (by simpa +decide [Ready, z, inverseIndex, forwardPointer, backwardPointer, zero] using hr)
      hfit hload
  have actual : ExecWithin W (registerSelected L s t) z u (selectedTime as bs cs ds s t g) :=
    registerSelected_exec L s t g z u
      (by simpa +decide [z, classIndex, inverseIndex, gnat] using hj)
      (by simp only [z, Data.set_regs, Function.update_self, BitVec.toNat_not]; rfl) hu
  have zsupport : z.SupportLe L.D :=
    z.supportLe_of_zero_tail (fun a ha => hx.2.2.2.2 a ha)
  have stored := registerSelected_stores L s t g z u
    (by simpa +decide [z, classIndex, inverseIndex, gnat] using hj)
    (by simp only [z, Data.set_regs, Function.update_self, BitVec.toNat_not]; rfl) stores
  have spaces := stored.space zsupport
  have setupSpace := (setup.space_writeFree (by decide)
    (x.supportLe_of_zero_tail (fun a ha => hx.2.2.2.2 a ha))).mono le_rfl
      (Nat.le_add_right L.D (lifetimeStores (p := p) as bs cs ds s t))
  have index : u.regs classIndex = j :=
    ((setup.seq actual).regs_eq (by
      exact ⟨by decide, registerSelected_preserves L s t _ (Or.inl rfl)⟩)).trans hj
  have bound : u.regs classLimit = 2 ^ p :=
    ((setup.seq actual).regs_eq (by
      exact ⟨by decide, registerSelected_preserves L s t _ (Or.inr (Or.inr rfl))⟩)).trans hN
  have result (y : Data 40) (hy : ExecWithin W advanceClass u y 4)
      (yi : y.regs classIndex = if u.regs tag ≠ 0 then 2 ^ p else j + 1)
      (ym : y.mem = u.mem) :
      (y.regs tag ≠ 0 ↔ PackedClassSolution as bs cs ds s t (BitVec.ofNat p j)) ∧
      (y.regs tag ≠ 0 → eval (witness as bs cs ds y) s = t) ∧
      y.regs classIndex = (if y.regs tag ≠ 0 then 2 ^ p else j + 1) ∧
      y.regs classLimit = 2 ^ p ∧
      (∀ a, a < L.q₂ → y.mem a = x.mem a) ∧
      L.Raw as bs cs ds (y.comap bank) ∧ Ready as bs cs ds s t L y ∧
      y.regs balance = x.regs balance := by
    have yt := hy.regs_eq (by decide : advanceClass.Preserves tag)
    have yN := (hy.regs_eq (by decide : advanceClass.Preserves classLimit)).trans bound
    have low (i : Fin 32) : y.regs (bank i) = u.regs (bank i) := by
      apply hy.regs_eq
      simp only [advanceClass, Code.Preserves, Op.bin, Op.dest, ne_eq, Option.some.injEq]
      have h36 := bank_ne_high classIndex (by decide) i
      have h37 := bank_ne_high inverseIndex (by decide) i
      exact ⟨Ne.symm h36, Ne.symm h37, Ne.symm h36⟩
    have yw : witness as bs cs ds y = witness as bs cs ds u := by
      have yo := hy.regs_eq (by decide : advanceClass.Preserves orientation)
      simp only [witness, yo, orientedWitness, Data.comap_regs, low]
    refine ⟨?_, ?_, by rwa [yt], yN, ?_, ?_, ?_, ?_⟩
    · simpa only [yt, g, BitVec.ofNatLT_eq_ofNat] using hit
    · intro h; rw [yw]; exact sound (yt ▸ h)
    · intro a ha; rw [ym]; exact frame a ha
    · simpa only [SearchLayout.Raw, Data.comap_mem, ym] using raw
    · have yp := hy.regs_eq (by decide : advanceClass.Preserves forwardPointer)
      have yq := hy.regs_eq (by decide : advanceClass.Preserves backwardPointer)
      have yz := hy.regs_eq (by decide : advanceClass.Preserves zero)
      simpa only [Ready, ym, yp, yq, yz] using ready
    · exact (hy.regs_eq (by decide : advanceClass.Preserves Driver.balance)).trans ub
  by_cases hh : u.regs tag ≠ 0
  · let y := u.set classIndex (2 ^ p)
    have done : ExecWithin (B := .standard) W (ram[ classIndex ← classLimit ]) u y 1 := by
      simpa only [bound] using (ExecWithin.copy (B := .standard) (w := W)
        (d := classIndex) (s := classLimit) (x := u))
    have advance : ExecWithin W advanceClass u y 4 :=
      (ExecWithin.branch_pos (by simp only [Cond.holds_lt, ready.2.2.2.2]; omega)
        done).mono (by omega)
    refine ⟨y, ?_, ?_, result y advance (by simp [y, hh]) rfl⟩
    · have he : ExecWithin W (classBody L s t) x y
        (selectedTime as bs cs ds s t g + 7) :=
        (setup.seq (actual.seq advance)).mono (by omega)
      simpa only [classBody, geq] using he
    · have sp := setupSpace.seq (spaces.seq
        (advance.space_writeFree (by decide) spaces.finish))
      rw [← geq]
      exact sp.mono (by omega) le_rfl
  · let y := u.set inverseIndex 1 |>.set classIndex (j + 1)
    have hnext : Fits W (j + 1) := hload.of_le (by omega)
    have done : ExecWithin (B := .standard) W
        (ram[ inverseIndex ← #1; classIndex ← classIndex + inverseIndex ]) u y 2 := by
      ram_eval [y, index, h1, hnext, classIndex, inverseIndex, Fin.mk.injEq]
    have advance : ExecWithin W advanceClass u y 4 :=
      ExecWithin.branch_neg (by simp only [Cond.holds_lt, ready.2.2.2.2]; omega) done
    refine ⟨y, ?_, ?_, result y advance (by simp [y, hh]) rfl⟩
    · have he : ExecWithin W (classBody L s t) x y
        (selectedTime as bs cs ds s t g + 7) :=
        (setup.seq (actual.seq advance)).mono (by omega)
      simpa only [classBody, geq] using he
    · have sp := setupSpace.seq (spaces.seq
        (advance.space_writeFree (by decide) spaces.finish))
      rw [← geq]
      exact sp.mono (by omega) le_rfl

private theorem two_le_loopTime {m p : ℕ} (as bs cs ds : List (BitVec m))
    (s t : BitVec m) (j n : ℕ) : 2 ≤ loopTime (p := p) as bs cs ds s t j n := by
  cases n <;> simp only [loopTime] <;> omega

/-- The decreasing finite remaining counter proves total native traversal.
Misses continue at the next class; a sound hit exits at the exclusive bound. -/
theorem classLoop_exec {W m p j n : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m)
    (L : SearchLayout W m p as.length bs.length cs.length ds.length)
    (x : Data 40) (hx : L.Raw as bs cs ds (x.comap bank)) (hr : Ready as bs cs ds s t L x)
    (hj : x.regs classIndex = j) (hN : x.regs classLimit = 2 ^ p)
    (hlen : j + n = 2 ^ p) (htag : x.regs tag = 0)
    (hfit : Fits W (L.D + 4 * 2 ^ m + 8))
    (hload : Fits W (2 * L.q₂ + 2 * 2 ^ p + 4)) :
    ∃ y, ExecWithin W (classLoop L s t) x y (loopTime (p := p) as bs cs ds s t j n) ∧
      SpaceWithin W (classLoop L s t) x y (loopTime (p := p) as bs cs ds s t j n)
        (L.D + lifetimeStores (p := p) as bs cs ds s t) ∧
      (y.regs tag ≠ 0 ↔ RangeSolution (p := p) as bs cs ds s t j n) ∧
      (y.regs tag ≠ 0 → eval (witness as bs cs ds y) s = t) ∧
      y.regs classIndex = 2 ^ p ∧ y.regs classLimit = 2 ^ p ∧
      (∀ a, a < L.q₂ → y.mem a = x.mem a) ∧
      L.Raw as bs cs ds (y.comap bank) ∧ Ready as bs cs ds s t L y ∧
      y.regs balance = x.regs balance := by
  induction n generalizing j x with
  | zero =>
    have done : ¬(Cond.lt classIndex classLimit).Holds x := by
      simp only [Cond.holds_lt, hj, hN]; omega
    refine ⟨x, ExecWithin.loop_exit done,
      SpaceWithin.loop_exit done ((x.supportLe_of_zero_tail
        (fun a ha => hx.2.2.2.2 a ha)).mono
          (Nat.le_add_right L.D (lifetimeStores (p := p) as bs cs ds s t))), ?_, ?_, by omega, hN,
      fun _ _ => rfl, hx, hr, rfl⟩
    · simp [htag, RangeSolution]; omega
    · simp [htag]
  | succ n ih =>
    have hjN : j < 2 ^ p := by omega
    have test : (Cond.lt classIndex classLimit).Holds x := by
      simpa only [Cond.holds_lt, hj, hN] using hjN
    obtain ⟨u, hu, space, hit, sound, ui, uN, frame, raw, ready, ub⟩ :=
      classBody_exec hp as bs cs ds s t L x hx hr hj hN hjN hfit hload
    by_cases hh : u.regs tag ≠ 0
    · rw [ite_eq_left hh] at ui
      have exit : ¬(Cond.lt classIndex classLimit).Holds u := by
        simp only [Cond.holds_lt, ui, uN]; omega
      have he := ExecWithin.loop_iter test hu (ExecWithin.loop_exit exit)
      refine ⟨u, he.mono ?_, ?_, ?_, sound, ?_, uN, frame, raw, ready, ub⟩
      · simp only [loopTime]
        have := two_le_loopTime (p := p) as bs cs ds s t (j + 1) n
        omega
      · apply (SpaceWithin.loop_iter test space
          (SpaceWithin.loop_exit exit space.finish)).mono
        · simp only [loopTime]
          have := two_le_loopTime (p := p) as bs cs ds s t (j + 1) n
          omega
        · exact le_rfl
      · rw [range_succ]
        exact ⟨fun _ => Or.inl (hit.mp hh), fun _ => hh⟩
      · exact ui
    · have ui' : u.regs classIndex = j + 1 := by simpa only [hh, ↓reduceIte] using ui
      have miss : u.regs tag = 0 := by omega
      obtain ⟨y, hy, yspace, yh, yw, yi, yN, yf, yr, yt, yb⟩ :=
        ih (j := j + 1) u raw ready ui' uN (by omega) miss
      refine ⟨y, ?_, ?_, ?_, yw, yi, yN, ?_, yr, yt, yb.trans ub⟩
      · have he := ExecWithin.loop_iter test hu hy
        exact he.mono (by simp only [loopTime]; omega)
      · exact (SpaceWithin.loop_iter test space yspace).mono
          (by simp only [loopTime]; omega) le_rfl
      · rw [range_succ]
        have hn : ¬PackedClassSolution as bs cs ds s t (BitVec.ofNat p j) :=
          fun h => hh (hit.mpr h)
        simpa only [hn, false_or] using yh
      · intro a ha; rw [yf a ha, frame a ha]

/-- The range, initial miss tag and every loop-control register are set by native
instructions. Exhaustive correctness follows from the finite counter, not from
an assumed termination or traversal conclusion. -/
theorem searchLoop_exec {W m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m)
    (L : SearchLayout W m p as.length bs.length cs.length ds.length)
    (x : Data 40) (hx : L.Raw as bs cs ds (x.comap bank)) (hr : Ready as bs cs ds s t L x)
    (hfit : Fits W (L.D + 4 * 2 ^ m + 8))
    (hload : Fits W (2 * L.q₂ + 2 * 2 ^ p + 4)) :
    ∃ y, ExecWithin W (searchLoop L s t) x y
        (5 + loopTime (p := p) as bs cs ds s t 0 (2 ^ p)) ∧
      SpaceWithin W (searchLoop L s t) x y
        (5 + loopTime (p := p) as bs cs ds s t 0 (2 ^ p))
        (L.D + lifetimeStores (p := p) as bs cs ds s t) ∧
      (y.regs tag ≠ 0 ↔ ∃ g : BitVec p, PackedClassSolution as bs cs ds s t g) ∧
      (y.regs tag ≠ 0 → eval (witness as bs cs ds y) s = t) ∧
      y.regs classIndex = 2 ^ p ∧ y.regs classLimit = 2 ^ p ∧
      (∀ a, a < L.q₂ → y.mem a = x.mem a) ∧
      L.Raw as bs cs ds (y.comap bank) ∧ Ready as bs cs ds s t L y ∧
      y.regs balance = x.regs balance := by
  let z := x.set classLimit p |>.set classIndex 1 |>.set classLimit (2 ^ p)
    |>.set classIndex 0 |>.set tag 0
  have hn : Fits W (2 ^ p) := hload.of_le (by omega)
  have hpfit : Fits W p := hn.of_le (Nat.lt_two_pow_self.le)
  have h1 : Fits W 1 := hload.of_le (by omega)
  have setup : ExecWithin (B := .standard) W
      (ram[ classLimit ← #p; classIndex ← #1; classLimit ← classIndex <<< classLimit;
        classIndex ← #0; tag ← #0 ]) x z 5 := by
    ram_eval [z, hpfit, hn, h1, fits_zero W, Nat.shiftLeft_eq, one_mul,
      classLimit, classIndex, tag, bank, Quarter.operand, Fin.mk.injEq]
  obtain ⟨y, hy, space, hit, sound, yi, yN, frame, raw, ready, yb⟩ :=
    classLoop_exec (j := 0) (n := 2 ^ p) hp as bs cs ds s t L z
      (by simpa only [SearchLayout.Raw, z, Data.comap_mem, Data.set_mem] using hx)
      (by simpa +decide [Ready, z, classLimit, classIndex, tag, bank, Quarter.operand,
        forwardPointer, backwardPointer, zero] using hr)
      (by simp +decide [z, classLimit, classIndex, tag, bank, Quarter.operand])
      (by simp +decide [z, classLimit, classIndex, tag, bank, Quarter.operand])
      (by omega) (by simp [z]) hfit hload
  refine ⟨y, setup.seq hy, ?_, hit.trans (range_all_iff as bs cs ds s t), sound,
    yi, yN, frame, raw, ready, ?_⟩
  · have setupSpace := (setup.space_writeFree (of_decide_eq_true rfl)
      (x.supportLe_of_zero_tail (fun a ha => hx.2.2.2.2 a ha))).mono le_rfl
        (Nat.le_add_right L.D (lifetimeStores (p := p) as bs cs ds s t))
    exact setupSpace.seq space
  · simpa +decide [z, classLimit, classIndex, tag, bank, Quarter.operand, balance] using yb

/-- The complete outer search has fixed compiled instruction count, independent
of projection width, number of classes, quarter lengths, seeds and layout values. -/
theorem searchLoop_size {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (s t : BitVec m) : (searchLoop L s t).size = 812 := by
  simp only [searchLoop, classLoop, classBody, inverseClass, advanceClass,
    Code.size, registerSelected_size]

end Cslib.Cryptanalysis.AddXNOR.Native.Driver
