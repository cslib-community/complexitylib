/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.NodeSpec
meta import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.NodeSpec

-- Regression clients intentionally export no public declarations.
set_option linter.privateModule false

/-!
# Complete native Chan–He node regression clients

The native interpreter starts with nonzero arbitrary output memory and nonzero unused
registers. Numeric expectations below are computed from the existing mathematical tags,
including the two negated-Z copies. The tests do not provide a histogram or a heavy/light oracle.
-/

namespace ComplexityTests.NativeChanHeNode

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.NodePacking

private def input (xs : Fin 3 → List ℤ) (M N U : ℕ) : Data 64 :=
  let n₀ := (xs 0).length
  let n₁ := (xs 1).length
  let n₂ := (xs 2).length
  let all := xs 0 ++ xs 1 ++ xs 2
  ⟨fun i =>
    if i = source 0 then 1 else if i = length 0 then n₀
    else if i = source 1 then 1 + n₀ else if i = length 1 then n₁
    else if i = source 2 then 1 + n₀ + n₁ else if i = length 2 then n₂
    else if i = base then 1 + n₀ + n₁ + n₂ else if i = groups then N
    else if i = magnitude then U else if i = modulus then M else 777,
    fun a => if a = 0 then 999 else if a ≤ all.length then encode (all[a - 1]?.getD 0) else 99⟩

private def run (w : ℕ) (xs : Fin 3 → List ℤ) (M N U : ℕ) : Option (Data 64 × ℕ) :=
  program.eval w 64 (input xs M N U)

private def observe (w : ℕ) (xs : Fin 3 → List ℤ) (M N U : ℕ) :
    Option (List (List ℕ)) := do
  let (y, _) ← run w xs M N U
  let L := layout (input xs M N U)
  pure ([List.ofFn (fun j : Fin 3 => y.mem (L.descriptor j))] ++
    List.ofFn (fun j : Fin 3 => (List.range (y.mem (L.descriptor j))).map fun k =>
      y.mem (L.heavy j + k)) ++
    [(List.range (4 * N)).map (fun k => y.mem (L.packed + k)),
      [y.mem 0, y.mem L.endpoint],
      List.ofFn (fun i : Fin 10 => y.regs ⟨46 + i.val, by omega⟩)])

private def empty : Fin 3 → List ℤ := ![[], [], []]
private def singleton : Fin 3 → List ℤ := ![[-1], [0], [1]]
private def mixed : Fin 3 → List ℤ := ![[-2, 1], [2], [-2, 2]]
private def endpoints : Fin 3 → List ℤ := ![[-4], [4], [0]]
private def allHeavy : Fin 3 → List ℤ := ![[-2, 1], [-1, 2], [-3, 0]]
private def twoUnique : Fin 3 → List ℤ := ![[-1, 0], [0, 1], [-1, 0]]

-- Empty inputs still clear and pad all cells, and write all three zero descriptors.
/-- info: true -/
#guard_msgs in
#eval decide (observe 16 empty 1 2 0 = some
    [[0, 0, 0], [], [], [], [80, 10, 26, 30, 80, 10, 26, 30],
      [999, 99], [1, 0, 1, 0, 1, 0, 1, 2, 0, 1]])

-- Unique negative and zero buckets are placed with their exact signed tags.
/-- info: true -/
#guard_msgs in
#eval decide (observe 16 singleton 3 6 1 = some
    [[0, 0, 0], [], [], [],
      [200, 26, 60, 74, 200, 26, 66, 74, 200, 18, 66, 78,
        200, 26, 66, 74, 200, 26, 66, 74, 200, 26, 66, 78],
      [999, 99], [1, 1, 2, 1, 3, 1, 4, 6, 1, 3]])

-- Two colliding X values are compacted while unique Y/Z buckets are placed.
/-- info: true -/
#guard_msgs in
#eval decide (observe 16 mixed 3 6 2 = some
    [[2, 0, 0], [5, 2], [], [],
      [320, 42, 106, 118, 320, 42, 106, 124, 320, 42, 100, 132,
        320, 42, 106, 118, 320, 42, 106, 124, 320, 42, 106, 132],
      [999, 99], [1, 2, 3, 1, 4, 2, 6, 6, 2, 3]])

-- Both admissible magnitude endpoints work at `M=1`, `N=2M`.
/-- info: true -/
#guard_msgs in
#eval decide (observe 16 endpoints 1 2 4 = some
    [[0, 0, 0], [], [], [], [560, 48, 176, 224, 560, 74, 186, 224],
      [999, 99], [1, 1, 2, 1, 3, 1, 4, 2, 4, 1]])

-- All three compact outputs contain the original signed integers, including the Z output.
/-- info: true -/
#guard_msgs in
#eval decide (observe 16 allHeavy 3 6 3 = some
    [[2, 2, 2], [5, 2], [3, 4], [7, 0],
      [440, 58, 146, 162, 440, 58, 146, 162, 440, 58, 146, 162,
        440, 58, 146, 162, 440, 58, 146, 162, 440, 58, 146, 162],
      [999, 99], [1, 2, 3, 2, 5, 2, 7, 6, 3, 3]])

-- Two distinct singleton buckets exercise the negative-residue permutation at modulus two.
/-- info: true -/
#guard_msgs in
#eval decide (observe 16 twoUnique 2 4 1 = some
    [[0, 0, 0], [], [], [],
      [200, 20, 60, 80, 200, 18, 62, 82, 200, 26, 66, 80, 200, 26, 66, 82],
      [999, 99], [1, 2, 3, 2, 5, 2, 7, 4, 1, 2]])

-- An extra group beyond `2M` is fully padded, including the duplicated-Z column.
/-- info: true -/
#guard_msgs in
#eval decide ((run 16 singleton 3 7 1).map (fun q =>
    (List.range 4).map (fun k => q.1.mem ((layout (input singleton 3 7 1)).packed + 24 + k))) =
  some [200, 26, 66, 74])

-- The full charged execution, including Count, is observed rather than assumed.
/-- info: some true -/
#guard_msgs in
#eval (run 16 mixed 3 6 2).map (fun q => decide (q.2 ≤ 675))

-- The small width fails during native address computation.
/-- info: true -/
#guard_msgs in
#eval (run 4 singleton 3 6 1).isNone

-- The failing executed width is also below the theorem's sufficient signed-fit promise.
example : ¬Cslib.GenericRAM.Signed.Fits 4 ((layout (input singleton 3 6 1)).budget : ℤ) := by
  decide

-- The theorem's polynomial fit/layout assumptions admit actual supplied native inputs.
example : Cslib.GenericRAM.Signed.Fits 32 ((layout (input empty 1 2 0)).budget : ℤ) := by decide

example : ∃ y, ExecWithin 34 program (input empty 1 2 0) y
      (256 * ((layout (input empty 1 2 0)).total + 1 + 2 + 1)) ∧
    Output (layout (input empty 1 2 0)) (fun _ _ => 0) (input empty 1 2 0).mem y.mem ∧
    Parameters (input empty 1 2 0) y := by
  apply exec_spec _ _ (by decide) (by decide) (by decide)
  · intro j
    fin_cases j <;> decide
  · intro j i hi
    fin_cases j <;> norm_num [layout, input, empty, length, source] at hi
  · intro j i hi
    fin_cases j <;> norm_num [layout, input, empty, length, source] at hi
  · intro j i hi
    fin_cases j <;> norm_num [layout, input, empty, length, source] at hi

private def singletonValues (j : Fin 3) (_ : ℕ) : ℤ := ![-1, 0, 1] j

-- A nonempty square-length client reads the final packed cell from the actual native state.
example : ∃ y, ExecWithin 34 program (input singleton 1 2 1) y 1792 ∧
    Output (layout (input singleton 1 2 1)) singletonValues
      (input singleton 1 2 1).mem y.mem ∧ Parameters (input singleton 1 2 1) y ∧
    y.mem ((layout (input singleton 1 2 1)).packed + 7) =
      Signed.encode ((node (layout (input singleton 1 2 1)) singletonValues).oneArray 1 7) := by
  have hclient : ∃ y, ExecWithin 34 program (input singleton 1 2 1) y 1792 ∧
      Output (layout (input singleton 1 2 1)) singletonValues
        (input singleton 1 2 1).mem y.mem ∧ Parameters (input singleton 1 2 1) y := by
    apply exec_spec _ _ (by decide) (by decide) (by decide)
    · intro j
      fin_cases j <;> decide
    · intro j i hi
      rw [show (layout (input singleton 1 2 1)).U = 1 by decide]
      fin_cases j <;> norm_num [singletonValues]
    · intro j i hi
      have hi0 : i = 0 := by
        fin_cases j <;> norm_num [layout, input, singleton, length, source] at hi <;> omega
      subst i
      fin_cases j <;> decide
    · intro j i hi k hk _
      fin_cases j <;> norm_num [layout, input, singleton, length, source] at hi hk <;> omega
  obtain ⟨y, he, ho, hp⟩ := hclient
  exact ⟨y, he, ho, hp, ho.packed_square (m := 1) (by decide) (by decide)⟩

end ComplexityTests.NativeChanHeNode
