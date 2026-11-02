/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Exec
public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Header
import Mathlib.Data.List.GetD

/-!
# Initialized concrete minimum-count prime selection

The actual fifteen-instruction header reads raw `(n,D)` followed by the three original
canonical signed matrices. It computes all original array pointers and the dirty workspace
start. The selector then executes the concrete counter for every eligible prime. This rule
uses only original numerical admission; no selected prime or intermediate execution is supplied.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Complete original-input execution at explicit numerical admission. The final state
contains an attained minimum modular count and preserves all original input cells. The
fifteen-instruction header is charged; the final halt is excluded. -/
theorem exec_input_at {w W n D A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D)
    (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hmag : GenericRAM.Signed.Fits w
      (CountPrime.magnitudeBudget (Nat.sqrt D) (Nat.clog 2 n) A : ℤ))
    (hw : Fits (w + 2) (CountPrime.addressBudget n (Nat.sqrt D) (Nat.clog 2 n)
      (3 + 3 * (n * n)) 3 (3 + n * n) (3 + 2 * (n * n))))
    (hwidth : w + 2 ≤ W)
    (hctrl : Fits W (4 * (D + 2) * (D + 2) + 4)) :
    InputFits W (CountPrime.inputWords n D values) ∧
    ∃ y, ExecWithin W entryProgram (.init (CountPrime.inputWords n D values)) y
        (timeBound n D + 15) ∧
      y.regs Reg.found = 1 ∧
      Cslib.Algorithms.ExactTriangle.IsSelectedPrime
        (fun α β : Fin n => values.getD (α.val * n + β.val) 0)
        (fun α β : Fin n => values.getD (n * n + α.val * n + β.val) 0)
        (fun α β : Fin n => values.getD (2 * (n * n) + α.val * n + β.val) 0)
        D (y.regs Reg.best) ∧
      y.regs Reg.bestCount = Cslib.Algorithms.ExactTriangle.countZeroMod
        (fun α β : Fin n => values.getD (α.val * n + β.val) 0)
        (fun α β : Fin n => values.getD (n * n + α.val * n + β.val) 0)
        (fun α β : Fin n => values.getD (2 * (n * n) + α.val * n + β.val) 0)
        (y.regs Reg.best) ∧ y.Bounded W ∧
      ∀ d, d < 3 + 3 * (n * n) ∨
          CountPrime.memoryEnd n (Nat.sqrt D) (Nat.clog 2 n) (3 + 3 * (n * n)) ≤ d →
        y.mem d = (Data.init (CountPrime.inputWords n D values) : Data 160).mem d := by
  let k := Nat.clog 2 n
  have h4 : 0 < 4 ^ Nat.clog 2 n := by positivity
  have h2 : 0 < 2 ^ Nat.clog 2 n := by positivity
  have hA : A ≤ CountPrime.magnitudeBudget (Nat.sqrt D) k A := by
    unfold CountPrime.magnitudeBudget; omega
  have original (q : ℕ) (hq : q < 3 * (n * n)) : (values.getD q 0).natAbs ≤ A := by
    have hq' : q < values.length := by omega
    have hm : values.getD q 0 ∈ values := by
      rw [List.getD_eq_getElem _ _ hq']
      exact List.getElem_mem hq'
    exact hv _ hm
  have hwW := hw.mono hwidth
  have hi : InputFits W (CountPrime.inputWords n D values) := by
    refine ⟨?_, ?_⟩
    · simpa only [CountPrime.inputWords, List.length_append, List.length_cons, List.length_nil,
        List.length_map, hlen, Nat.reduceAdd] using
        hwW.of_le (by unfold CountPrime.addressBudget; omega : 2 + 3 * (n * n) ≤ _)
    · intro v hm
      rcases List.mem_append.mp hm with hm | hm
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl
        · exact hwW.of_le (by unfold CountPrime.addressBudget; omega)
        · exact hctrl.of_le (by nlinarith)
      · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hm
        exact (encode_fits (hmag.of_natAbs_le ((hv z hz).trans hA))).mono (by omega)
  obtain ⟨x, hx, memory, hn, hd, ha, hb, hc, hs⟩ := exec_header (n := n) (D := D)
    (.init (CountPrime.inputWords n D values)) (by rfl) (by rfl)
    (hwW.of_le (by unfold CountPrime.addressBudget; omega))
  have inputWord (q : ℕ) : (Data.init (CountPrime.inputWords n D values) : Data 160).mem
      (3 + q) = encode (values.getD q 0) := CountPrime.input_word n D values q
  obtain ⟨y, he, hf, hp, hvCount, frame, _⟩ := exec x
    (fun i => values.getD i 0) (fun i => values.getD (n * n + i) 0)
    (fun i => values.getD (2 * (n * n) + i) 0)
    hD hn hd ha hb hc hs (by omega) (by omega) (by omega)
    (fun i hi => original i (by omega)) (fun i hi => original (n * n + i) (by omega))
    (fun i hi => original (2 * (n * n) + i) (by omega))
    (by intro i hi; rw [memory]; exact inputWord i)
    (by intro i hi; rw [memory];
        simpa only [Nat.add_assoc] using inputWord (n * n + i))
    (by intro i hi; rw [memory];
        simpa only [Nat.add_assoc] using inputWord (2 * (n * n) + i))
    hmag hw hwidth hctrl
  have full : ExecWithin W entryProgram (.init (CountPrime.inputWords n D values)) y
      (timeBound n D + 15) := (hx.seq he).mono (by omega)
  refine ⟨hi, y, full, hf, ?_, ?_, full.bounded (.init hi), ?_⟩
  · simpa only [Nat.add_assoc] using hp
  · simpa only [Nat.add_assoc] using hvCount
  · intro d hd
    exact (frame d hd).trans (congrFun memory d)

end Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection
