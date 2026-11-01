/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayGate
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayMotionCorrect

/-!
# Correctness of the native local gate subroutine

The subroutine queries the original input and emits the existing Boolean label of the native
leaving view precisely when all movement labels hold. The fixed template supplies no free
input-dependent initial data: initialization and run time are explicit in the statements.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.Gate

open MultiTapeTM MultiTapeNTM.ChoiceTable

variable {k s : ℕ} {Q : Type}

/-- Retaining scheduling context preserves each physical replay transition exactly. -/
theorem runFrom_eq (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (context : Context k) (q : Config k Q) (t : ℕ) :
    (machine M e).runFrom w (context, q) t =
      (context, (QueryReplay.machine M).runFrom w q t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [QueryMachine.runFrom_succ, ih, QueryMachine.runFrom_succ]
    simp only [QueryMachine.step, machine, QueryMachine.read]
    by_cases h : (QueryReplay.machine M).halted ((QueryReplay.machine M).runFrom w q t) = true
    · simp [h]
    · simp [h]

/-- Finishing a loaded replay emits exactly the encoded leaving view on successful all-head
motion validation, and the exact FAIL code otherwise. Retained context and windows are explicit. -/
theorem finish_runFrom_load (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (b positive negative : ℕ) [NeZero b] (expected : Option (Fin k) → SignType)
    (raw : RawResult k Q) (hcanonical : Load.CanonicalWindows b raw)
    (J : Option (Fin k) → ℤ) (hinput : J none = (positive : ℤ) - negative) :
    let view := raw.toView b
    let c := M.runFrom (embedCfg (input := w) b J view.1 view.2) b
    (machine M e).finish ((machine M e).runFrom w
      ((positive, negative, expected), Load.load (w.length, b, (positive, negative), raw)) b) =
      List.ofFn (Encoding.encode e
        (if ∀ head, c.blockIndex b head = J head + (expected head : ℤ)
        then some (c.blockControl b, c.windowContents b J) else none)) := by
  dsimp only
  rw [runFrom_eq, Load.load_eq_loadView w.length b positive negative raw hcanonical J hinput]
  let view := raw.toView b
  let q := (QueryReplay.machine M).runFrom w (loadView w.length b J view) b
  let c := M.runFrom (embedCfg (input := w) b J view.1 view.2) b
  have hwidth : q.width = b := width_runFrom M w _ b
  have hrep := runFrom_loadView_represents (w := w) M b J view le_rfl
  have hmotion := Motion.valid_iff positive negative expected q c J hwidth hinput hrep
  have hview : (rawResult q).toView b = (c.blockControl b, c.windowContents b J) :=
    (toView_rawResult q b hwidth).trans (result_runFrom_loadView (w := w) M b J view)
  have hvalid : Encoding.NativeEncode.valid (b, true, rawResult q) = true := by
    apply List.all_eq_true.mpr
    intro flag hflag
    obtain ⟨h, rfl⟩ := List.mem_ofFn.mp hflag
    apply decide_eq_true
    change (((QueryReplay.machine M).runFrom w (loadView w.length b J view) b).cells h).length = _
    rw [length_cells_runFrom]
    simp [loadView]
  change Encoding.NativeEncode.serialize e
    (q.width, Motion.valid (positive, negative, expected, q), rawResult q) =
      List.ofFn (Encoding.encode e (if ∀ head,
        c.blockIndex b head = J head + (expected head : ℤ)
        then some (c.blockControl b, c.windowContents b J) else none))
  rw [hwidth]
  by_cases hm : ∀ head, c.blockIndex b head = J head + (expected head : ℤ)
  · have hc : Motion.valid (positive, negative, expected, q) = true := hmotion.mpr hm
    rw [hc, Encoding.NativeEncode.serialize_some e (rawResult q) hvalid, hview]
    simp [hm]
  · have hc : Motion.valid (positive, negative, expected, q) = false :=
      Bool.eq_false_iff.mpr (fun h => hm (hmotion.mp h))
    rw [hc, Encoding.NativeEncode.serialize_fail e (rawResult q) hvalid]
    simp [hm]

variable [Finite Q]

/-- Every physical subroutine clock charges retained context plus the actual replay state. -/
theorem length_runFrom_load_le (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (b positive negative : ℕ) [NeZero b] (expected : Option (Fin k) → SignType)
    (raw : RawResult k Q) (hcanonical : Load.CanonicalWindows b raw)
    (J : Option (Fin k) → ℤ) (hinput : J none = (positive : ℤ) - negative) (t : ℕ) :
    (encState ((machine M e).runFrom w
      ((positive, negative, expected),
        Load.load (w.length, b, (positive, negative), raw)) t)).length ≤
      2 * (encContext (positive, negative, expected)).length + 1 +
        1024 * (k + 1) * (b + Nat.log2 w.length + Nat.card (Option Q) +
          Nat.card OutputTrack + 1) := by
  rw [runFrom_eq]
  have h := Load.length_runFrom_load_le M w b positive negative raw hcanonical J hinput t
  rw [encState, length_encPair]
  dsimp only [Prod.fst, Prod.snd]
  omega

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Gate
