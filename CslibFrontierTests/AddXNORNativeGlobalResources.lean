/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import all CslibFrontier.Cryptanalysis.AddXNORNativeGlobalResources
import all CslibFrontier.Cryptanalysis.AddXNORNativeGlobalLayout
import all CslibFrontier.Cryptanalysis.AddXNORNativeGlobalTime
import all CslibFrontier.Cryptanalysis.AddXNORNativeClassCounts
import all CslibFrontier.Cryptanalysis.AddXNORNativeSelectedClass
import all CslibFrontier.Cryptanalysis.AddXNORNativeClassSemantics

/-!
# Native global time and simultaneous prefix-space clients

The first client uses unequal quarters, non-self-inverse addition, colliding
low-bit states and strict inverse selection. It derives a real hit and the
actual computed maximum, and charges all forty registers at every compiled
prefix. Empty-quarter misses and zero-width multiplicity collisions instantiate
the same unrestricted theorem without layout, width or resource premises.
-/

set_option linter.privateModule false

open Cslib.WordRAM Cslib.Cryptanalysis.AddXNOR
open Cslib.Cryptanalysis.AddXNOR.Native.Quarter
open Cslib.Cryptanalysis.AddXNOR.Native.Driver

private def first : List (BitVec 3) := [1#3, 2#3, 4#3]
private def middle : List (BitVec 3) := [1#3]
private def L := compactSearchLayout 3 2 3 1 1 1
private def K := compactCounterLayout 3 2 3 1 1 1
private def input : Data 40 := Data.init (quarterInput first middle middle middle)

example : backwardCount middle middle 2#3 0#2 = 1 ∧
    forwardCount first middle 1#3 0#2 = 4 ∧
    computedBalance (p := 2) first middle middle middle 1#3 2#3 = 2 ∧
    (1#3 + 1#3) + 1#3 ≠ 1#3 := by decide +kernel

/-- The bound includes preprocessing, all directions, release, early exit,
actual input cells and all registers; it is simultaneous at every compiled prefix. -/
example : ∃ y n ts, n + 1 ≤ 65109 ∧
    TraceExec 16 (dissection L K 1#3 2#3) input y n ts ∧
    Executes 16 ((dissection L K 1#3 2#3).program tag) ⟨0, input⟩ (y.regs tag) (n + 1) ∧
    y.regs tag ≠ 0 ∧ eval (witness first middle middle middle y) 1#3 = 2#3 ∧
    y.regs balance = 2 ∧
    (∀ k u, k ≤ n → Runs 16 ((dissection L K 1#3 2#3).program tag) ⟨0, input⟩ u k →
      u.data.Bounded 16 ∧ ∃ cover : Finset ℕ,
        (∀ a, u.data.mem a ≠ 0 → a ∈ cover) ∧ (cover.card + 40) * 16 ≤ 236320) := by
  obtain ⟨y, n, ts, hn, ht, he, hit, _, sound, mu, peak, _⟩ :=
    original_resources (p := 2) (by decide) first middle middle middle 1#3 2#3
  have solvable : Solvable ((first ++ middle) ++ (middle ++ middle)) 1#3 2#3 :=
    ⟨decode 3 4 ++ decode 1 0 ++ decode 1 0 ++ decode 1 0, by decide, by decide +kernel⟩
  have hh := hit.mpr solvable
  have balance : computedBalance (p := 2) first middle middle middle 1#3 2#3 = 2 :=
    by decide +kernel
  refine ⟨y, n, ts, by change n ≤ 65108 at hn; omega, ht, he, hh, sound hh,
    mu.trans balance, ?_⟩
  intro k u hk hu
  obtain ⟨hs, hb⟩ := peak k u hk hu
  rw [balance] at hs
  obtain ⟨cover, hc, hcover⟩ := hs
  refine ⟨hb, cover, hcover, ?_⟩
  change cover.card ≤ 14730 at hc
  omega

/-- With no operands and distinct endpoints, the actual fixed program halts
with a miss. No semantic miss, traversal or completion premise is supplied. -/
example : ∃ (y : Data 40) (n : ℕ), Executes (globalWidth 1 1 0 0 0 0)
      ((dissection (compactSearchLayout 1 1 0 0 0 0)
        (compactCounterLayout 1 1 0 0 0 0) 0#1 1#1).program tag)
      ⟨0, Data.init (quarterInput (m := 1) [] [] [] [])⟩ 0 (n + 1) ∧
    y.regs balance = 0 := by
  obtain ⟨y, n, _, _, _, he, _, miss, _, mu, _, _⟩ :=
    original_resources (p := 1) (by decide) [] [] [] [] 0#1 1#1
  have hn : ¬Solvable (([] ++ []) ++ ([] ++ [])) 0#1 1#1 := by
    rintro ⟨ops, hlen, hsol⟩
    have ho : ops = [] := List.length_eq_zero_iff.mp hlen
    subst ops
    exact (by decide : (0#1 : BitVec 1) ≠ 1#1) hsol
  have hz := miss.mpr hn
  exact ⟨y, n, by simpa only [hz, List.length_nil] using he, mu.trans (by decide +kernel)⟩

/-- Zero width keeps indexed multiplicity four even though the dictionary has
only one distinct state. The general resource theorem admits these collisions. -/
example : ∃ y n ts, n ≤ 8760 ∧
    TraceExec (globalWidth 0 0 1 1 1 1)
      (dissection (compactSearchLayout 0 0 1 1 1 1) (compactCounterLayout 0 0 1 1 1 1)
        0#0 0#0) (Data.init (quarterInput [0#0] [0#0] [0#0] [0#0])) y n ts ∧
    y.regs balance = 4 ∧ y.regs tag ≠ 0 := by
  obtain ⟨y, n, ts, hn, ht, _, hit, _, _, mu, _, _⟩ :=
    original_resources (p := 0) (by decide) [0#0] [0#0] [0#0] [0#0] 0#0 0#0
  refine ⟨y, n, ts, hn, ht, mu.trans (by decide +kernel), hit.mpr ?_⟩
  exact ⟨[false, false, false, false], by decide, by decide⟩

/-- The bounds are uniform in admitted widths and all source-quarter lengths. -/
example {p k r μ : ℕ} (hp : p ≤ k) :
    globalTime p k k k (k + r) ≤ 1000 * (4 * k + r + 1) * 2 ^ (2 * k + r) ∧
    peakCells p k k k (k + r) μ ≤ 1000 * (4 * k + r + 1) * (2 ^ (k + r) + μ) :=
  ⟨globalTime_quarters hp, peakCells_quarters hp⟩
