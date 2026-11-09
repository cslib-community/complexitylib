/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Realization.Grade

/-! The grading keeps actual replies, changed memory and query-free loop control visible. -/

namespace ComplexityTests.WordRAMRealizationGrade

open Cslib.DataStructure Cslib.WordRAM.Realization

private def initial : Memory.State := ⟨fun _ => 7, 3⟩

private def first : Memory.Prog ℕ := do
  Memory.write 0 5
  Memory.read 0

private def next (a : ℕ) : Memory.Prog Unit := Memory.write 1 a

-- The continuation receives reply5 and the updated cell0=5, not the initial cell0=7.
example : combinedCost (first.bind next)
    (fun s => s.frontier + ((Memory.spec 0).clientResult s first +
      ((Memory.spec 0).clientState s first).mem 0) + 1) initial = 17 := by
  rw [combinedCost_bind first next (fun s => s.frontier) (fun a s => a + s.mem 0)]
  decide

example : (Memory.spec 3).ValidHistory initial
    ((Memory.spec 3).clientHistory initial (first.bind next)) := by
  decide

-- Pure work is explicit: a semantic return does not erase the supplied glue charge.
example : combinedCost (pure () : Memory.Prog Unit) (fun s => s.frontier + 4) initial = 7 := by
  rw [combinedCost_pure]
  rfl

private def growBody (d : Unit × ℕ) : Memory.Prog ℕ := do
  let base ← Memory.allocDirty 1
  pure (base + d.2)

private def growWork (d : Unit × ℕ) (s : Memory.State) : ℕ := d.2 + s.frontier

-- Two allocations move the frontier3→4→5 and returned accumulator0→3→7.
-- The local body charges3+7 and two control units accompany the two memory charges.
example : combinedCost (iterate growBody () 2 0) (iterationWork growBody growWork () 2 0)
    initial = 14 := by
  rw [combinedCost_iterate]
  decide

example : (Memory.spec 3).ValidHistory initial
    ((Memory.spec 3).clientHistory initial (iterate growBody () 2 0)) := by
  decide

-- A uniform local-work hypothesis justifies the optional memory-only arithmetic estimate.
example (s : Memory.State) :
    combinedCost (Memory.read 0) (fun _ => 5) s ≤ 3 * memoryCost (Memory.read 0) s + 3 := by
  apply combinedCost_le_of_work_le (a := 2) (b := 3)
  intro t
  change 5 ≤ 2 * 1 + 3
  decide

-- A nonzero potential decrease pays memory charge12 from amortized charge9. All three
-- premises are tight: work29=2*12+5 and native budget126=3*(12+29+1).
example : 126 + 3 * (2 + 1) * 4 ≤
    3 * (2 + 1) * 9 + 3 * (5 + 1) + 3 * (2 + 1) * 7 := by
  exact scaled_potential_pay 12 29 126 7 4 9 3 2 5 (by decide) (by decide) (by decide)

-- The queue's charge9 payment adapter can use its certified budget itself for n; the clock
-- premise is reflexive. Local work and the actual memory-potential inequality stay visible.
example (M G Φpre Φpost factor a b : ℕ) (hwork : G ≤ a * M + b)
    (hmem : M + Φpost ≤ 9 + Φpre) :
    factor * (M + G + 1) + factor * (a + 1) * Φpost ≤
      factor * (a + 1) * 9 + factor * (b + 1) + factor * (a + 1) * Φpre :=
  scaled_potential_pay M G (factor * (M + G + 1)) Φpre Φpost 9 factor a b le_rfl hwork hmem

private def idleBody (_ : Unit × Unit) : Memory.Prog Unit := pure ()

private theorem idle_eq (n : ℕ) : iterate idleBody () n () = pure () := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

private theorem idle_work (n : ℕ) (s : Memory.State) :
    iterationWork idleBody (fun _ _ => 0) () n () s = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 0 + iterationWork idleBody (fun _ _ => 0) () n () s + 1 = n + 1
    rw [ih]
    simp only [Nat.zero_add]

private theorem idle_cost (n : ℕ) (s : Memory.State) :
    combinedCost (iterate idleBody () n ()) (iterationWork idleBody (fun _ _ => 0) () n ()) s =
      n := by
  rw [idle_eq, combinedCost_pure, idle_work]

-- Although every idle program is extensionally pure, its chosen loop grading is unbounded.
-- No uniform constant can pay this grading from its zero memory charge alone.
example : ¬∃ C, ∀ n,
    combinedCost (iterate idleBody () n ())
        (iterationWork idleBody (fun _ _ => 0) () n ()) initial ≤
      C * (memoryCost (iterate idleBody () n ()) initial + 1) := by
  rintro ⟨C, h⟩
  have hc := h (C + 1)
  rw [idle_cost, idle_eq] at hc
  change C + 1 ≤ C * (0 + 1) at hc
  omega

end ComplexityTests.WordRAMRealizationGrade
