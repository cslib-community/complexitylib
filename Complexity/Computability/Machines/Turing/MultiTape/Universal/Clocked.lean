/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (local addition beside the vendored `Turing.MultiTapeTM.Universal` files)

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Halting.Computable
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Clocked runs of Boolean machines

`Turing.MultiTapeTM.Universal.runBool d w t` runs the machine described by `d` on the bit word `w`
for `t` steps with the universal function, and returns the bit it has output if it has halted
with a single bit, and `none` otherwise. With the number of steps in unary, it is
polynomial-time (`Turing.MultiTapeTM.Universal.computableInPolyTime_runBool`).

Every computable Boolean function has a description whose clocked runs are sound and eventually
complete (`Turing.MultiTapeTM.IsComputable.exists_runBool`): a run never returns a wrong bit, and
returns the right one once it is allowed enough steps. Delayed diagonalization uses this to
compare computable sets on short words within a polynomial time budget, without knowing how long
the machines take.

## Main definitions

* `Turing.MultiTapeTM.Universal.runBool`: the bit output by a described machine within a number
  of steps, if any.

## Main results

* `Turing.MultiTapeTM.Universal.runBool_eq_some_iff`: `runBool` through the universal function.
* `Turing.MultiTapeTM.Universal.computableInPolyTime_runBool`: `runBool` is polynomial-time with
  the number of steps in unary.
* `Turing.MultiTapeTM.IsComputable.exists_runBool`: clocked runs of a computable Boolean function
  are sound and eventually complete.
-/

@[expose] public section

namespace Turing.MultiTapeTM

namespace Universal

/-- The bit output by the machine described by `d` on the bit word `w` within `t` steps: `some b`
if it has halted with output `[b]`, `none` otherwise. -/
def runBool (d : Desc) (w : List Bool) (t : ℕ) : Option Bool :=
  if universal (d, w.map eBit, t) = ([eBit true], true) then some true
  else if universal (d, w.map eBit, t) = ([eBit false], true) then some false
  else none

theorem runBool_eq_some_iff {d : Desc} {w : List Bool} {t : ℕ} {b : Bool} :
    runBool d w t = some b ↔ universal (d, w.map eBit, t) = ([eBit b], true) := by
  unfold runBool
  cases b <;> split_ifs with h₁ h₂ <;> simp_all [eBit]

/-- **Clocked runs are polynomial-time** with the number of steps in unary. -/
@[fun_prop]
theorem computableInPolyTime_runBool {α : Type} {input : α ↪ List Bool}
    {d : α → Desc} {w : α → List Bool} {t : α → ℕ}
    (hd : ComputableInPolyTime d input eDesc) (hw : ComputableInPolyTime w input encBits)
    (ht : ComputableInPolyTime t input encUnary) :
    ComputableInPolyTime (fun a => runBool (d a) (w a) (t a)) input (encOption encBool) := by
  unfold runBool
  fun_prop

end Universal

open Universal

/-- **Clocked runs of a computable Boolean function.** A computable `f` has a description whose
clocked runs never return a wrong bit and return the right one from some number of steps on. -/
theorem IsComputable.exists_runBool {α : Type} {enc : α ↪ List Bool} {f : α → Bool}
    (hf : IsComputable f enc encBool) :
    ∃ d : Desc, (∀ a t b, runBool d (enc a) t = some b → b = f a) ∧
      ∀ a, ∃ T, ∀ t, T ≤ t → runBool d (enc a) t = some (f a) := by
  obtain ⟨k, State, hfin, tm, htm⟩ := isComputable_iff.mp hf
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  refine ⟨desc eS eBit tm, fun a t b hb => ?_, fun a => ?_⟩
  · obtain ⟨u, hhalt, hout⟩ := htm a
    rw [runBool_eq_some_iff, universal_desc, Prod.mk.injEq, Option.isNone_iff_eq_none] at hb
    obtain ⟨hb, ht⟩ := hb
    -- the runs for `t` and `u` steps have both halted, so they agree
    have heq : tm.runFrom (tm.initCfg (enc a)) t = tm.runFrom (tm.initCfg (enc a)) u := by
      rcases le_total t u with h | h
      · exact (runFrom_eq_of_halt tm _ h ht).symm
      · exact runFrom_eq_of_halt tm _ h hhalt
    rw [heq, hout] at hb
    exact (eBit.injective (List.singleton_injective hb)).symm
  · -- past its halting time, the machine has halted with output `[f a]`
    obtain ⟨u, hhalt, hout⟩ := htm a
    refine ⟨u, fun t ht => runBool_eq_some_iff.mpr ?_⟩
    rw [universal_desc, runFrom_eq_of_halt tm _ ht hhalt, hout, hhalt]
    rfl

end Turing.MultiTapeTM
