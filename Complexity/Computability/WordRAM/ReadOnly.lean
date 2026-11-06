/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Footprint

/-!
# Memory preservation by programs without stores

A flat program containing no store instruction preserves all memory at every
continuing execution prefix. In particular it cannot enlarge the initial memory
support, even when it reads only part of that support. This gives an occupancy
bound independent of the number of loop iterations or representable addresses.
-/

public section

namespace Cslib.WordRAM

/-- A continuing step of a program without stores leaves memory unchanged. -/
theorem Next.mem_eq_of_no_store {B : Basis} {r w : ℕ} {p : Program B r}
    {s t : State r} (h : Next w p s t)
    (hp : ∀ a v, Instr.op (Op.store a v) ∉ p) : t.data.mem = s.data.mem := by
  have hw : Probe.writes (probes p s) = ∅ := by
    unfold probes
    cases hi : p[s.pc]? with
    | none => rfl
    | some i =>
      cases i with
      | op o =>
        cases o with
        | store a v => exact False.elim (hp a v (List.mem_of_getElem? hi))
        | _ => rfl
      | _ => rfl
  funext a
  exact h.modifies a (by rw [hw]; exact Finset.notMem_empty a)

/-- Every continuing prefix of a program without stores has the initial memory.
The bound includes cells installed in the input but never accessed by the run. -/
theorem Runs.mem_eq_of_no_store {B : Basis} {r w n : ℕ} {p : Program B r}
    {s t : State r} (h : Runs w p s t n)
    (hp : ∀ a v, Instr.op (Op.store a v) ∉ p) : t.data.mem = s.data.mem := by
  induction h with
  | refl => rfl
  | @tail u t n h hstep ih => exact (hstep.mem_eq_of_no_store hp).trans ih

end Cslib.WordRAM
