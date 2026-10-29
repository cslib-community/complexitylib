/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Space
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Algorithms.Reachability.Savitch
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Space.Reachability
import Complexity.Foundations.Data.BitString.ShortWords
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Savitch's decider for space-bounded nondeterministic machines

A nondeterministic machine with finitely many states, all of whose computation paths on an input
of length `n` visit at most `c * (n + 1) ^ d` work cells, is decided by the deterministic
`Turing.MultiTapeNTM.savitchDecide`: Savitch's midpoint recursion with an explicit stack
(`Cslib.Reachability.savitch`) on the codes of the finite views of the machine, asking whether
the accepting code is reachable from the code of the initial view.

Every view reachable from the initial view has an encoding of length at most
`Turing.MultiTapeNTM.viewLengthBound`, linear in `n` and the space bound, whatever the length of
the path reaching it (`Turing.MultiTapeNTM.length_encFiniteCfg_le`), so the codes have a width `W`
polynomial in `n`. Acceptance is reachability of the accepting code along the edges between codes
of `2 * W + 2` bits (`Turing.MultiTapeNTM.accepts_iff_reflTransGen_codeStep`). There are
`2 ^ (2 * W + 2)` such words, so it is reachability within as many steps, which the recursion
decides at depth `2 * W + 2`. The edge test, the codes and the width are polynomial-time, so the
decider runs in space polynomial in `n`, charging the stack of frames, the counters and the edge
test (`Cslib.Reachability.exists_polyBounded_space_savitch`); its time is exponential.

The decider retains the whole input, so this is the polynomial-space consequence of Savitch's
theorem; the quadratic bound `NSPACE(s) ⊆ DSPACE(s ^ 2)` for sublinear `s` is not claimed.

## Main definitions

* `Turing.MultiTapeNTM.codeWidth`: the width of the codes of the views.
* `Turing.MultiTapeNTM.viewCodeWidth`: the bit-length `2 * codeWidth + 2` of the codes of the
  views.
* `Turing.MultiTapeNTM.savitchDecide`: the deterministic decider of acceptance.

## Main results

* `Turing.MultiTapeNTM.savitchDecide_eq_true_iff`: the decider decides acceptance.
* `Turing.MultiTapeNTM.computableInPolyTime_codeWidth`: the width of the codes is polynomial-time.
* `Turing.MultiTapeNTM.computableInPolyTime_viewCodeWidth`: the bit-length of the codes of the views
  is polynomial-time.
* `Turing.MultiTapeNTM.exists_polyBounded_space_savitchDecide`: it runs in polynomial space.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.5][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 4.2][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeNTM

open MultiTapeTM

variable {k : ℕ} {State : Type} [Finite State] (ntm : MultiTapeNTM k Bool State)

/-- The width of the codes of the views on `input`, under the space bound
`c * (input.length + 1) ^ d`: the length of the encoding of the initial view plus the bound
`Turing.MultiTapeNTM.viewLengthBound` on the encodings of all reachable views. -/
noncomputable def codeWidth (c d : ℕ) (input : List Bool) : ℕ :=
  (encFiniteCfg (ntm.initView input)).length +
    viewLengthBound k State input.length (c * (input.length + 1) ^ d)

/-- The bit-length `2 * ntm.codeWidth c d input + 2` of the codes (`Turing.MultiTapeNTM.viewCode`
and `Turing.MultiTapeNTM.acceptCode`) of the views on `input`, under the space bound
`c * (input.length + 1) ^ d`. -/
noncomputable def viewCodeWidth (c d : ℕ) (input : List Bool) : ℕ :=
  2 * ntm.codeWidth c d input + 2

/-- **Savitch's decider**: whether the accepting code is reachable from the code of the initial
view, by Savitch's midpoint recursion on words of `ntm.viewCodeWidth c d input` bits at depth
`ntm.viewCodeWidth c d input`. -/
noncomputable def savitchDecide (c d : ℕ) (input : List Bool) : Bool :=
  Cslib.Reachability.savitch ntm.codeEdge (ntm.viewCodeWidth c d input)
    (ntm.viewCodeWidth c d input) (viewCode (ntm.codeWidth c d input) (ntm.initView input))
    (acceptCode (ntm.codeWidth c d input))

variable {ntm}

/-- **Savitch's decider decides acceptance** of a machine whose computation paths on `input`
visit at most `c * (input.length + 1) ^ d` work cells. -/
theorem savitchDecide_eq_true_iff {c d s : ℕ} {input : List Bool} (hs : ntm.RunsInSpace input s)
    (hsc : s ≤ c * (input.length + 1) ^ d) :
    ntm.savitchDecide c d input = true ↔ ntm.Accepts input := by
  set width := ntm.codeWidth c d input with hwidth_def
  have hwidth : ∀ finite, Relation.ReflTransGen ntm.ViewStep (ntm.initView input) finite →
      (encFiniteCfg finite).length ≤ width := fun finite h =>
    ((length_encFiniteCfg_le hs h).trans (viewLengthBound_mono k State _ hsc)).trans
      (Nat.le_add_left _ _)
  have hsrc : (viewCode width (ntm.initView input)).length = 2 * width + 2 :=
    length_viewCode (hwidth _ .refl)
  have hdst : (acceptCode width).length = 2 * width + 2 := List.length_replicate ..
  -- the reachable codes are words of `2 * width + 2` bits
  have hcard : {code | Relation.ReflTransGen (ntm.CodeStep width)
      (viewCode width (ntm.initView input)) code}.encard ≤ 2 ^ (2 * width + 2) + 1 := by
    refine (Set.encard_le_encard fun code hcode => ?_).trans
      ((Cslib.BitString.encard_setOf_length_eq _).le.trans le_self_add)
    induction hcode with
    | refl => exact hsrc
    | tail _ hstep _ => exact hstep.2.1
  rw [savitchDecide, viewCodeWidth, ← hwidth_def, Cslib.Reachability.savitch_iff hsrc hdst,
    accepts_iff_reflTransGen_codeStep hwidth]
  exact (Relation.reflTransGen_iff_relatesWithinSteps_of_encard_le hcard).symm

/-- The width of the codes is polynomial-time, in unary. -/
private theorem computableTidilyInPolyTime_codeWidth {α : Type} {enc : α ↪ List Bool} (c d : ℕ) :
    ComputableTidilyInPolyTime (fun a => ntm.codeWidth c d (enc a)) enc encUnary := by
  have hlength := ComputableTidilyInPolyTime.encoding_length enc
  have hinit := ComputableTidilyInPolyTime.finiteCfg_init (k := k) (.encode enc) ntm.q₀
  have hsize := (ComputableTidilyInPolyTime.encoding_length encFiniteCfg).comp hinit
  simp only [codeWidth, viewLengthBound, initView]
  fun_prop

/-- The width of the codes is polynomial-time, in unary. -/
theorem computableInPolyTime_codeWidth {α : Type} {enc : α ↪ List Bool} (c d : ℕ) :
    ComputableInPolyTime (fun a => ntm.codeWidth c d (enc a)) enc encUnary :=
  (computableTidilyInPolyTime_codeWidth c d).computableInPolyTime

/-- The bit-length of the codes of the views is polynomial-time, in unary. -/
@[fun_prop]
theorem computableInPolyTime_viewCodeWidth (c d : ℕ) :
    ComputableInPolyTime (ntm.viewCodeWidth c d) encBits encUnary := by
  have := computableInPolyTime_codeWidth (ntm := ntm) (enc := encBits) c d
  unfold viewCodeWidth
  fun_prop

variable (ntm) in
/-- **Savitch's decider runs in polynomial space**: within some time and within space
polynomially bounded in the length of the encoded instance. -/
theorem exists_polyBounded_space_savitchDecide {α : Type} (enc : α ↪ List Bool) (c d : ℕ) :
    ∃ t s, PolyBounded (fun a => (enc a).length) s ∧
      ComputableInTimeAndSpace (fun a => ntm.savitchDecide c d (enc a)) enc encBool t s := by
  have hwidth := computableInPolyTime_codeWidth (ntm := ntm) (enc := enc) c d
  have hedge : ComputableInPolyTime
      (fun q : Unit × List Bool × List Bool => (fun _ => ntm.codeEdge) q.1 q.2.1 q.2.2)
      (encPair (encFinEnum Unit) (encPair encBits encBits)) encBool :=
    ntm.computableInPolyTime_codeEdge (by fun_prop) (by fun_prop)
  have hin : ComputableInPolyTime
      (fun a => ((), ntm.viewCodeWidth c d (enc a), ntm.viewCodeWidth c d (enc a),
        viewCode (ntm.codeWidth c d (enc a)) (ntm.initView (enc a)),
        acceptCode (ntm.codeWidth c d (enc a)))) enc
      (Cslib.Reachability.encArgs (encFinEnum Unit)) := by
    have := computableInPolyTime_viewCode_initView (ntm := ntm) hwidth
      (ComputableInPolyTime.of_eq (encIn := enc) (encOut := encBits) fun _ => rfl)
    have := computableInPolyTime_acceptCode hwidth
    unfold viewCodeWidth Cslib.Reachability.encArgs
    fun_prop
  exact Cslib.Reachability.exists_polyBounded_space_savitch (edge := fun _ => ntm.codeEdge)
    (par := fun _ => ()) hedge hin
    (fun _ => length_viewCode (Nat.le_add_right _ _)) fun _ => List.length_replicate ..

end Turing.MultiTapeNTM
