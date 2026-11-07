/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Loop
public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.CounterCall
public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Bounds

/-!
# Concrete native minimum-count prime selection

The selector calls the complete cyclic-Strassen counter on actual original signed arrays
for every eligible prime. It derives the counting-call law from that program, retains a
prime satisfying the existing `IsSelectedPrime`, and preserves the original arrays and
caller memory outside one modulus-uniform workspace. No counting, execution, prime list,
layout or running-time oracle is a hypothesis.

The caller supplies ordinary runtime scalar/pointer arguments, original weight bounds and
explicit numerical word admission. Initialized input, derived logarithmic admission and
width-independent prefix/support bounds are exported by the main prime-selection module.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Execute the actual trial-division/minimum controller with the real modular counter.
Every original-array read, argument copy and counter instruction is charged. The common
admission and memory envelope use the largest possible prime; no intermediate state or
execution certificate is supplied. The final halt is excluded from this caller rule. -/
theorem exec {w W n D scratch a b c A : ℕ} (x : Data 160) (u v z : ℕ → ℤ)
    (hD : 16 ≤ D) (hn : x.regs Reg.side = n) (hwindow : x.regs Reg.window = D)
    (hAB : x.regs Reg.inputAB = a) (hBC : x.regs Reg.inputBC = b)
    (hAC : x.regs Reg.inputAC = c) (hs : x.regs Reg.scratch = scratch)
    (ha : a + n * n ≤ scratch) (hb : b + n * n ≤ scratch) (hc : c + n * n ≤ scratch)
    (hu : ∀ i < n * n, (u i).natAbs ≤ A)
    (hv : ∀ i < n * n, (v i).natAbs ≤ A)
    (hz : ∀ i < n * n, (z i).natAbs ≤ A)
    (hinU : ∀ i < n * n, x.mem (a + i) = encode (u i))
    (hinV : ∀ i < n * n, x.mem (b + i) = encode (v i))
    (hinZ : ∀ i < n * n, x.mem (c + i) = encode (z i))
    (hmag : GenericRAM.Signed.Fits w
      (CountPrime.magnitudeBudget (Nat.sqrt D) (Nat.clog 2 n) A : ℤ))
    (hw : Fits (w + 2)
      (CountPrime.addressBudget n (Nat.sqrt D) (Nat.clog 2 n) scratch a b c))
    (hwidth : w + 2 ≤ W)
    (hctrl : Fits W (4 * (D + 2) * (D + 2) + 4)) :
    ∃ y, ExecWithin W (program CountPrime.program) x y (timeBound n D) ∧
      y.regs Reg.found = 1 ∧
      Cslib.Algorithms.ExactTriangle.IsSelectedPrime
        (fun α β : Fin n => u (α.val * n + β.val))
        (fun α β : Fin n => v (α.val * n + β.val))
        (fun α β : Fin n => z (α.val * n + β.val)) D (y.regs Reg.best) ∧
      y.regs Reg.bestCount = Cslib.Algorithms.ExactTriangle.countZeroMod
        (fun α β : Fin n => u (α.val * n + β.val))
        (fun α β : Fin n => v (α.val * n + β.val))
        (fun α β : Fin n => z (α.val * n + β.val)) (y.regs Reg.best) ∧
      (∀ d, d < scratch ∨ CountPrime.memoryEnd n (Nat.sqrt D) (Nat.clog 2 n) scratch ≤ d →
        y.mem d = x.mem d) ∧
      ∀ i, (131 ≤ i.val ∧ i.val ≤ 136) ∨ 143 ≤ i.val → y.regs i = x.regs i := by
  let cap := Nat.sqrt D
  let k := Nat.clog 2 n
  let score := Cslib.Algorithms.ExactTriangle.countZeroMod
    (fun α β : Fin n => u (α.val * n + β.val))
    (fun α β : Fin n => v (α.val * n + β.val))
    (fun α β : Fin n => z (α.val * n + β.val))
  let Source (mem : ℕ → ℕ) : Prop :=
    (∀ i < n * n, mem (a + i) = encode (u i)) ∧
      (∀ i < n * n, mem (b + i) = encode (v i)) ∧
      (∀ i < n * n, mem (c + i) = encode (z i)) ∧
      ∀ d, d < scratch ∨ CountPrime.memoryEnd n cap k scratch ≤ d → mem d = x.mem d
  have hSource : Source x.mem := ⟨hinU, hinV, hinZ, fun _ _ => rfl⟩
  have hcount (q : Data 160) (hqSource : Source q.mem)
      (hstatic : ∀ i, 131 ≤ i.val ∧ i.val ≤ 136 → q.regs i = x.regs i)
      (hpwin : q.regs Reg.cursor ∈ Nat.sqrtPrimeWindow D) :
      ∃ r, ExecWithin W (count CountPrime.program) q r (countTimeBound n D) ∧
        r.regs Reg.countResult = score (q.regs Reg.cursor) ∧ Source r.mem := by
    obtain ⟨qU, qV, qZ, qFrame⟩ := hqSource
    have hp0 : 0 < q.regs Reg.cursor := (Nat.mem_sqrtPrimeWindow_iff_sq.1 hpwin).1.pos
    have hpc : q.regs Reg.cursor ≤ cap := Nat.le_sqrt.2 (by
      simpa only [pow_two] using (Nat.mem_sqrtPrimeWindow_iff_sq.1 hpwin).2.2.le)
    have hmagp : GenericRAM.Signed.Fits w
        (CountPrime.magnitudeBudget (q.regs Reg.cursor) k A : ℤ) :=
      hmag.of_natAbs_le (by simpa using CountPrime.magnitudeBudget_monotone_modulus k A hpc)
    have hwp : Fits (w + 2)
        (CountPrime.addressBudget n (q.regs Reg.cursor) k scratch a b c) :=
      hw.of_le (CountPrime.addressBudget_monotone_modulus n k scratch a b c hpc)
    obtain ⟨r, he, hr, frame⟩ := exec_count q u v z hp0
      ((hstatic Reg.side (by decide)).trans hn) rfl
      ((hstatic Reg.inputAB (by decide)).trans hAB)
      ((hstatic Reg.inputBC (by decide)).trans hBC)
      ((hstatic Reg.inputAC (by decide)).trans hAC)
      ((hstatic Reg.scratch (by decide)).trans hs) ha hb hc hu hv hz qU qV qZ hmagp hwp
    have hM : CountPrime.memoryEnd n (q.regs Reg.cursor) k scratch ≤
        CountPrime.memoryEnd n cap k scratch :=
      CountPrime.memoryEnd_monotone_modulus n k scratch hpc
    have noWidth : ¬(count CountPrime.program).ReadsWidth := by decide +kernel
    refine ⟨r, (he.mono_width noWidth hwidth).mono ?_, hr, ?_⟩
    · exact Nat.add_le_add_right (CountPrime.cost_monotone_modulus n hpc) 6
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro i hi
        exact (frame (a + i) (Or.inl (by omega))).trans (qU i hi)
      · intro i hi
        exact (frame (b + i) (Or.inl (by omega))).trans (qV i hi)
      · intro i hi
        exact (frame (c + i) (Or.inl (by omega))).trans (qZ i hi)
      · intro d hd
        exact (frame d (hd.elim Or.inl (fun h => Or.inr (hM.trans h)))).trans (qFrame d hd)
  obtain ⟨p, hp⟩ := Cslib.Algorithms.ExactTriangle.exists_isSelectedPrime
    (fun α β : Fin n => u (α.val * n + β.val))
    (fun α β : Fin n => v (α.val * n + β.val))
    (fun α β : Fin n => z (α.val * n + β.val)) D hD
  obtain ⟨y, he, hfound, hprime, hvalue, hmin, hSourceY, hregs⟩ :=
    exec_of_count CountPrime.program score Source x (by omega) ⟨p, hp.1⟩ hwindow
      hctrl hSource hcount
  obtain ⟨_, _, _, frame⟩ := hSourceY
  exact ⟨y, he, hfound, ⟨hprime, hmin⟩, hvalue, frame, hregs⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection
