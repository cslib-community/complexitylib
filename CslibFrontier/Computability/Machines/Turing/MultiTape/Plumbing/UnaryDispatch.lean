/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.RunsBetween
import Mathlib.Basic.Finite.Sigma
import Mathlib.Basic.Finite.Sum
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.Option

/-!
# Native finite dispatch from a bounded unary tag

An empty tag selects the default continuation; `j+1` true bits select continuation `j`.
The controller reads and rewinds the selected work tape, preserving its contents and every
other tape, before entering the selected continuation. Continuation state types may depend on
the selection. The dispatch time is `2*tag.length+2`, independent of the continuation's clock.
-/

public section

namespace Turing.MultiTapeTM.UnaryDispatch

/-- Empty means the default case; a positive unary length selects one of the finite cases. -/
@[expose] def code {n : ℕ} : Option (Fin n) → List Bool
  | none => []
  | some j => List.replicate (j.val + 1) true

/-- Every represented tag has length bounded by the finite family size. -/
theorem length_code_le {n : ℕ} (j : Option (Fin n)) : (code j).length ≤ n := by
  cases j <;> simp [code]; omega

/-- The finite controller reads a bounded tag, rewinds, then runs the chosen state family. -/
inductive State (n : ℕ) (S : Option (Fin n) → Type) where
  /-- Number of true bits read. -/
  | read (count : Fin (n + 1))
  /-- Selected case and remaining rewind distance. -/
  | rewind (choice : Option (Fin n)) (count : Fin (n + 1))
  /-- State of the selected continuation. -/
  | continuation (choice : Option (Fin n)) (state : S choice)

instance {n : ℕ} {S : Option (Fin n) → Type} [∀ j, Finite (S j)] : Finite (State n S) :=
  Finite.of_injective (fun q : State n S => match q with
    | .read count => (Sum.inl count : Fin (n + 1) ⊕ (Option (Fin n) × Fin (n + 1)) ⊕ Sigma S)
    | .rewind choice count => .inr (.inl (choice, count))
    | .continuation choice state => .inr (.inr ⟨choice, state⟩)) (by
      intro a b h
      cases a <;> cases b <;> simp_all)

private def choice {n : ℕ} (count : Fin (n + 1)) : Option (Fin n) :=
  if h : count.val = 0 then none else some ⟨count.val - 1, by omega⟩

private theorem choice_length {n : ℕ} (j : Option (Fin n)) :
    choice ⟨(code j).length, Nat.lt_succ_of_le (length_code_le j)⟩ = j := by
  cases j <;> simp [choice, code]

private def moveAction {K n : ℕ} {S : Option (Fin n) → Type} (i : Fin K) (d : SignType)
    (next : State n S) : Action K Bool (State n S) :=
  ⟨0, fun j => (none, if j = i then d else 0), none, some next⟩

/-- Read a bounded unary tag, restore the selected head, and enter its native continuation.
No tag or continuation index is supplied as a runtime external choice. -/
noncomputable def machine {K n : ℕ} {S : Option (Fin n) → Type} (i : Fin K)
    (family : (j : Option (Fin n)) → MultiTapeTM K Bool (S j)) :
    MultiTapeTM K Bool (State n S) :=
  .ofTr (.read 0) fun state input work => match state with
    | .read count =>
      if h : work i = some true ∧ count.val < n then
        moveAction i 1 (.read ⟨count.val + 1, by omega⟩)
      else moveAction i 0 (.rewind (choice count) count)
    | .rewind j count =>
      if h : count.val = 0 then moveAction i 0 (.continuation j (family j).q₀)
      else moveAction i (-1) (.rewind j ⟨count.val - 1, by omega⟩)
    | .continuation j q =>
      let action := (family j).tr q input work
      { action with state := action.state.map (.continuation j) }

private theorem continuation_follows {K n : ℕ} {S : Option (Fin n) → Type} (i : Fin K)
    (family : (j : Option (Fin n)) → MultiTapeTM K Bool (S j)) (j : Option (Fin n)) :
    (machine i family).Follows (family j) (.continuation j)
      (.mapState (Option.map (.continuation j))) :=
  fun _ _ _ h => tr_iff.mp h ▸ rfl

private theorem runFrom_continuation {K n : ℕ} {S : Option (Fin n) → Type}
    {input : List Bool} (i : Fin K)
    (family : (j : Option (Fin n)) → MultiTapeTM K Bool (S j)) (j : Option (Fin n))
    (c : Cfg K Bool (S j) input) (t : ℕ) :
    (machine i family).runFrom (c.mapState (Option.map (.continuation j))) t =
      ((family j).runFrom c t).mapState (Option.map (.continuation j)) :=
  runFrom_map ((continuation_follows i family j).stepHom
    (Cfg.mapState (Option.map (.continuation j))) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl)) c t

private def config {K : ℕ} (input : List Bool) (ws : Fin K → List Bool) (i : Fin K)
    (pos : ℕ) (out : List Bool) : Cfg K Bool Unit input :=
  tapesCfg input ws 0 (Function.update (fun _ => 0) i pos) out

private theorem config_zero {K : ℕ} (input : List Bool) (ws : Fin K → List Bool) (i : Fin K)
    (out : List Bool) : config input ws i 0 out = tapesCfg input ws 0 0 out := by
  refine Cfg.ext rfl rfl rfl ?_ rfl
  funext j
  simp [config, tapesCfg]

private theorem runFrom_read {K n : ℕ} {S : Option (Fin n) → Type} (i : Fin K)
    (family : (j : Option (Fin n)) → MultiTapeTM K Bool (S j)) (input out : List Bool)
    (ws : Fin K → List Bool) (j : Option (Fin n)) (hw : ws i = code j)
    (r : ℕ) (hr : r ≤ (code j).length) :
    (machine i family).runFrom
      ((config input ws i 0 out).withState (some (.read 0))) r =
      (config input ws i r out).withState
        (some (.read ⟨r, by have := length_code_le j; omega⟩)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hm := length_code_le j
    have htrue : tapeOfList (ws i) (r : ℤ) = some true := by
      rw [hw]
      cases j with
      | none => simp [code] at hr
      | some j =>
        have hr' : r < j.val + 1 := by
          simp only [code, List.length_replicate] at hr
          omega
        simp [code, hr']
    have hs : (machine i family).step
        ((config input ws i r out).withState (some (.read ⟨r, by omega⟩))) =
        (config input ws i (r + 1) out).withState (some (.read ⟨r + 1, by omega⟩)) := by
      apply step_tapesCfg (a := moveAction i 1 (.read ⟨r + 1, by omega⟩))
      · simp [machine, tapesCfg, htrue, show r < n by omega]
      · rfl
      · rfl
      · intro x; rfl
      · intro x; by_cases hx : x = i <;> simp [moveAction, hx]
    rw [runFrom_succ, ih (by omega), hs]

private theorem runFrom_rewind {K n : ℕ} {S : Option (Fin n) → Type} (i : Fin K)
    (family : (j : Option (Fin n)) → MultiTapeTM K Bool (S j)) (input out : List Bool)
    (ws : Fin K → List Bool) (j : Option (Fin n)) (r : ℕ) (hr : r ≤ n) :
    (machine i family).runFrom
      ((config input ws i r out).withState (some (.rewind j ⟨r, by omega⟩))) (r + 1) =
      ((config input ws i 0 out).withState (some (family j).q₀)).mapState
        (Option.map (.continuation j)) := by
  induction r with
  | zero =>
    rw [runFrom_one]
    apply step_tapesCfg (a := moveAction i 0 (.continuation j (family j).q₀))
    · simp [machine]
    · rfl
    · rfl
    · intro x; rfl
    · intro x; simp [moveAction, config, tapesCfg]
  | succ r ih =>
    have hs : (machine i family).step
        ((config input ws i (r + 1) out).withState (some (.rewind j ⟨r + 1, by omega⟩))) =
        (config input ws i r out).withState (some (.rewind j ⟨r, by omega⟩)) := by
      apply step_tapesCfg (a := moveAction i (-1) (.rewind j ⟨r, by omega⟩))
      · simp [machine]
      · rfl
      · rfl
      · intro x; rfl
      · intro x; by_cases hx : x = i <;> simp [moveAction, hx]
    rw [show r + 1 + 1 = 1 + (r + 1) by omega, runFrom_add, runFrom_one, hs]
    exact ih (by omega)

/-- A native finite dispatch adds only a read/rewind clock to the selected continuation.
The tag, all other tape contents, previous output and initial head positions are preserved
before the continuation starts. The theorem assumes all heads initially at zero. -/
theorem runsBetween {K n : ℕ} {S : Option (Fin n) → Type} (i : Fin K)
    (family : (j : Option (Fin n)) → MultiTapeTM K Bool (S j)) (input out : List Bool)
    (ws : Fin K → List Bool) (j : Option (Fin n)) (hw : ws i = code j)
    {final : Cfg K Bool Unit input} {t s : ℕ}
    (h : RunsBetween (family j) (tapesCfg input ws 0 0 out) final t s) :
    RunsBetween (machine i family) (tapesCfg input ws 0 0 out) final
      (2 * (code j).length + 2 + t) (K * (2 * (code j).length + 2 + t + 1)) := by
  let m := (code j).length
  have hm : m ≤ n := length_code_le j
  have hblank : tapeOfList (ws i) (m : ℤ) = none := by
    rw [hw, tapeOfList_eq_none_iff]
    exact Or.inr (by omega)
  have hs : (machine i family).step
      ((config input ws i m out).withState (some (.read ⟨m, by omega⟩))) =
      (config input ws i m out).withState (some (.rewind j ⟨m, by omega⟩)) := by
    apply step_tapesCfg (a := moveAction i 0 (.rewind j ⟨m, by omega⟩))
    · simp [machine, tapesCfg, hblank, m, choice_length]
    · rfl
    · rfl
    · intro x; rfl
    · intro x; simp [moveAction]
  apply RunsBetween.of_runFrom
  rw [show 2 * (code j).length + 2 + t = m + (1 + (m + 1 + t)) by dsimp [m]; omega,
    ← config_zero input ws i out, runFrom_add]
  rw [show (machine i family).q₀ = .read 0 from rfl,
    runFrom_read i family input out ws j hw m le_rfl, runFrom_add, runFrom_one, hs,
    runFrom_add, runFrom_rewind i family input out ws j m hm,
    runFrom_continuation, config_zero, h.1]
  rfl

end Turing.MultiTapeTM.UnaryDispatch
