/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Iterative

/-!
# Compact control bounds for iterative Cook–Mertz

On an existing Tree Evaluation tree of height `H`, the iterative controller keeps at most `H`
frames. Every frame's round index remains below the length of the supplied unit enumeration.
These properties hold at every clock, not only at the final return, and also when the unit list
is empty. No saved register bank or subtree is added to a frame.

## Main definitions

* `Cslib.TreeEval.Ary.Iter.ControlBounds`: bounded stack depth and valid round indices.

## Main results

* `Cslib.TreeEval.Ary.Iter.controlBounds_runFrom`: every control step preserves the bounds.
* `Cslib.TreeEval.Ary.Iter.runFrom_initial_bounds`: the bounds for a root call at every clock.

This is a pure control invariant. It does not give a native encoding-length or machine-space
certificate for the registers, lookup operation, coefficients or gate extension.
-/

public section

namespace Cslib.TreeEval.Ary.Iter

variable {K : Type*} {d b r H : ℕ}

/-- The controller has bounded depth and stores only valid unit-round indices. -/
@[expose] def ControlBounds (height rounds : ℕ) (q : Cfg K d r) : Prop :=
  q.stack.length ≤ height ∧ ∀ fr ∈ q.stack, fr.round < rounds

private theorem length_lt_of_nodeAt_gate (T : Tree d b H) {P : List (Fin d)} {f : Gate d b}
    (hf : T.nodeAt P = .gate f) : P.length < H := by
  induction T generalizing P with
  | leaf v => cases P <;> simp [Tree.nodeAt] at hf
  | node g children ih =>
    cases P with
    | nil => simp
    | cons j P =>
      change (children j).nodeAt P = .gate f at hf
      exact Nat.succ_lt_succ (ih j hf)

private theorem controlBounds_cons (S : Ary.State K d r) (fr : Frame K d)
    (st : List (Frame K d)) (mode : Mode K d) {height rounds : ℕ}
    (hdepth : st.length + 1 ≤ height) (hround : fr.round < rounds)
    (hframes : ∀ g ∈ st, g.round < rounds) :
    ControlBounds height rounds ⟨S, fr :: st, mode⟩ := by
  refine ⟨by simpa only [List.length_cons] using hdepth, ?_⟩
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact hround
  · exact hframes g hg

variable [Field K]

private theorem controlBounds_beginRound (hd : 0 < d) (us : List Kˣ) (i : ℕ) (c : K)
    (t : Fin (d + 1)) (S : Ary.State K d r) (st : List (Frame K d))
    (hdepth : st.length < H) (hi : i < us.length)
    (hframes : ∀ fr ∈ st, fr.round < us.length) :
    ControlBounds H us.length (beginRound hd us i c t S st) :=
  controlBounds_cons _ _ _ _ (by omega) hi hframes

/-- For a real tree lookup, a control step preserves depth and unit-round bounds even from an
arbitrary bounded configuration. Invalid node paths return without pushing another frame. -/
theorem controlBounds_step (T : Tree d b H) (hd : 0 < d)
    (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K) (us : List Kˣ)
    {q : Cfg K d r} (hq : ControlBounds H us.length q) :
    ControlBounds H us.length (step hd e E us T.nodeAt q) := by
  rcases q with ⟨S, st, mode⟩
  obtain ⟨hdepth, hframes⟩ := hq
  cases mode with
  | call c t =>
    cases hread : T.nodeAt (path st) with
    | leaf v =>
      rw [step_call_leaf hd e E us T.nodeAt S st c t v hread]
      exact ⟨hdepth, hframes⟩
    | none =>
      simpa only [step, hread] using (show ControlBounds H us.length ⟨S, st, .ret⟩ from
        ⟨hdepth, hframes⟩)
    | gate f =>
      have hlt : st.length < H := by
        simpa only [length_path] using length_lt_of_nodeAt_gate T hread
      cases us with
      | nil =>
        rw [step_call_gate_nil hd e E T.nodeAt S st c t f hread]
        exact ⟨hdepth, hframes⟩
      | cons u us =>
        rw [step_call_gate_cons hd e E u us T.nodeAt S st c t f hread]
        exact controlBounds_beginRound hd (u :: us) 0 c t S st hlt (by simp) hframes
  | ret =>
    cases st with
    | nil => exact ⟨hdepth, hframes⟩
    | cons fr st =>
      have hfr : fr.round < us.length := hframes fr (List.mem_cons_self ..)
      have htail : ∀ g ∈ st, g.round < us.length := fun g hg =>
        hframes g (List.mem_cons_of_mem _ hg)
      have hcons : st.length + 1 ≤ H := by simpa only [List.length_cons] using hdepth
      by_cases hu : fr.undo = true
      · by_cases hj : fr.child.val + 1 < d
        · rw [step_ret_undo_next hd e E us T.nodeAt S fr st hu hj]
          exact controlBounds_cons _ _ _ _ hcons hfr htail
        · by_cases hi : fr.round + 1 < us.length
          · rw [step_ret_undo_round hd e E us T.nodeAt S fr st hu hj hi]
            exact controlBounds_beginRound hd us (fr.round + 1) fr.coeff fr.target _ st
              (by omega) hi htail
          · rw [step_ret_undo_last hd e E us T.nodeAt S fr st hu hj hi]
            exact ⟨by change st.length ≤ H; omega, htail⟩
      · have hu' : fr.undo = false := by
          cases h : fr.undo with
          | false => rfl
          | true => exact (hu h).elim
        by_cases hj : fr.child.val + 1 < d
        · rw [step_ret_forward_next hd e E us T.nodeAt S fr st hu' hj]
          exact controlBounds_cons _ _ _ _ hcons hfr htail
        · rw [step_ret_forward_last hd e E us T.nodeAt S fr st hu' hj]
          exact controlBounds_cons _ _ _ _ hcons hfr htail

/-- Every clocked prefix preserves compact control bounds. No termination or nonempty-round
hypothesis is needed. -/
theorem controlBounds_runFrom (T : Tree d b H) (hd : 0 < d)
    (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K) (us : List Kˣ)
    {q : Cfg K d r} (hq : ControlBounds H us.length q) (n : ℕ) :
    ControlBounds H us.length (runFrom hd e E us T.nodeAt q n) := by
  induction n with
  | zero => exact hq
  | succ n ih =>
    rw [runFrom_succ]
    exact controlBounds_step T hd e E us ih

/-- Starting a root call gives at most one frame per tree level and bounds every round index,
at every clock, including runs with an empty unit enumeration. -/
theorem runFrom_initial_bounds (T : Tree d b H) (hd : 0 < d)
    (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K) (us : List Kˣ)
    (S : Ary.State K d r) (c : K) (t : Fin (d + 1)) (n : ℕ) :
    ControlBounds H us.length (runFrom hd e E us T.nodeAt (initialCfg S c t) n) :=
  controlBounds_runFrom T hd e E us (by simp [ControlBounds, initialCfg]) n

end Cslib.TreeEval.Ary.Iter
