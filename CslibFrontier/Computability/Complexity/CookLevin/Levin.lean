/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.CookLevin.Witness
public import CslibFrontier.Computability.Complexity.CookLevin.PolyTime
public import CslibFrontier.Computability.Complexity.Problems.ThreeSAT.Levin
import CslibFrontier.Computability.Complexity.CookLevin.Parameters
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Logics.Propositional.CNF.PolyTime

/-!
# The Cook–Levin reduction is a Levin reduction

The Cook–Levin reduction `Cslib.Complexity.CookLevin.reduce` of an NP relation to `SAT` carries
explicit witness maps, both computable in polynomial time:

* forward (`Cslib.Complexity.CookLevin.forwardWitness`): a witness `w` for `a` becomes the
  satisfying assignment read off the run of the verifier on `(a, w)`. It is given by the
  variables listed along the run (`Cslib.Complexity.CookLevin.trueVars`), evaluated along the
  occurrences of the tableau and padded;
* backward (`Cslib.Complexity.CookLevin.backwardWitness`): a certificate for the formula becomes
  the certificate bits of the assignment it describes.

`Cslib.Complexity.CookLevin.SAT_levinHard` says that every NP relation, over any encoded type of
instances, Levin-reduces to the NP relation of `SAT`. Composing with the SAT → 3SAT Levin reduction
gives `Cslib.Complexity.CookLevin.ThreeSAT_levinHard`. These are the witness-preserving forms of
`Cslib.Complexity.CookLevin.SAT_npHard` and `Cslib.Complexity.ThreeSAT_npHard`; the forward maps
are what a prover for `SAT` or `ThreeSAT` needs to run on the witnesses of the original relation.

## Main definitions

* `Cslib.Complexity.CookLevin.forwardWitness`, `Cslib.Complexity.CookLevin.backwardWitness`: the
  witness maps.
* `Cslib.Complexity.CookLevin.levinReduction`: the Cook–Levin reduction as a Levin reduction, for a
  machine computing the verifier in polynomial time.

## Main results

* `Cslib.Complexity.CookLevin.isWitness_forwardWitness`,
  `Cslib.Complexity.CookLevin.isWitness_backwardWitness`: the witness maps send witnesses to
  witnesses.
* `Cslib.Complexity.CookLevin.SAT_levinHard`, `Cslib.Complexity.CookLevin.ThreeSAT_levinHard`:
  every NP relation Levin-reduces to `SAT` and to `ThreeSAT`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 2.3.
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2008], Theorem 2.22
  (the relation of SAT is `PC`-complete), with the augmented reductions of Exercise 2.28, from which
  the witness-preserving form for 3SAT also comes (numbering of the author's online draft of
  30 December 2006); the proof here is the tableau reduction of Arora and Barak, not Goldreich's
  route through CSAT.
* [L. A. Levin, *Universal sequential search problems*][Levin1973]
-/

public section

namespace Cslib.Complexity.CookLevin

open _root_.Turing _root_.Turing.MultiTapeTM Cslib.Logic.PL ComputableInPolyTime

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State] {α : Type}

/-- The values, along the occurrences of the tableau of `tm` on inputs `u ++ w'` with `|w'| = L`
unrolled for `T` steps, of the variables listed along the run on `u ++ w`. -/
noncomputable def tableauWitness (tm : MultiTapeTM k Bool State) (u w : List Bool) (L T : ℕ) :
    List Bool :=
  (tableau tm u L T).vars.map fun v => decide (v ∈ trueVars tm u w T)

/-- The forward witness map of the Cook–Levin reduction: the variables listed along the run of
`tm` on `frame (enc a) ++ w`, evaluated along the occurrences of the tableau and padded. -/
noncomputable def forwardWitness (tm : MultiTapeTM k Bool State) (p : Polynomial ℕ) (c d : ℕ)
    (enc : α ↪ List Bool) (x : α × List Bool) : List Bool :=
  let (u, L, T) := parameters p c d enc x.1
  SAT.padCertificate (reduce tm p c d enc x.1) (tableauWitness tm u x.2 L T)

/-- The backward witness map of the Cook–Levin reduction: the certificate bits of the assignment
that a certificate `x.2` for `reduce tm p c d enc x.1` describes. -/
noncomputable def backwardWitness (tm : MultiTapeTM k Bool State) (p : Polynomial ℕ) (c d : ℕ)
    (enc : α ↪ List Bool) (x : α × List Bool) : List Bool :=
  (List.range (p.eval (enc x.1).length)).map fun j =>
    SAT.assignment (reduce tm p c d enc x.1) x.2 (Var.cert (k := k) (State := State) j).index

/-- The runs of `tm` on instance–certificate pairs of the prescribed length halt within
`c * (n + 1) ^ d` steps with the verifier's answer: the hypothesis of
`Cslib.Complexity.CookLevin.reduce_mem_SAT_iff`, for every instance. -/
@[expose]
def RunsVerifier {enc : α ↪ List Bool} (R : NPRelation enc) (tm : MultiTapeTM k Bool State)
    (c d : ℕ) : Prop :=
  ∀ a w, w.length = R.certLength.eval (enc a).length →
    (tm.runFrom (tm.initCfg (encPair enc encBits (a, w)))
        (c * ((encPair enc encBits (a, w)).length + 1) ^ d)).state = none ∧
      (tm.runFrom (tm.initCfg (encPair enc encBits (a, w)))
        (c * ((encPair enc encBits (a, w)).length + 1) ^ d)).output = [R.verifier (a, w)]

variable {enc : α ↪ List Bool} {R : NPRelation enc} {tm : MultiTapeTM k Bool State} {c d : ℕ}

omit [Fintype State] [DecidableEq State] in
/-- The run of `tm` on a certificate of the prescribed length, written with the input prefix and
time bound of `Cslib.Complexity.CookLevin.parameters`. -/
private theorem run_parameters (hrun : RunsVerifier R tm c d) {a : α} {w : List Bool}
    (hw : w.length = R.certLength.eval (enc a).length) :
    (tm.runFrom (tm.initCfg (frame (enc a) ++ w))
        (c * (2 * (enc a).length + 1 + R.certLength.eval (enc a).length + 1) ^ d)).state = none ∧
      (tm.runFrom (tm.initCfg (frame (enc a) ++ w))
        (c * (2 * (enc a).length + 1 + R.certLength.eval (enc a).length + 1) ^ d)).output =
          [R.verifier (a, w)] := by
  have hlen : (encPair enc encBits (a, w)).length =
      2 * (enc a).length + 1 + R.certLength.eval (enc a).length := by
    rw [length_encPair, encBits_apply, hw]
  obtain ⟨hhalt, hout⟩ := hrun a w hw
  rw [hlen, encPair_apply, encBits_apply] at hhalt hout
  exact ⟨hhalt, hout⟩

/-- **Forward witnesses.** A witness for `a` is sent to a witness of `SAT` for the reduced
formula. -/
theorem isWitness_forwardWitness (hrun : RunsVerifier R tm c d) {a : α} {w : List Bool}
    (h : R.IsWitness a w) :
    SAT.npRelation.IsWitness (reduce tm R.certLength c d enc a)
      (forwardWitness tm R.certLength c d enc (a, w)) := by
  obtain ⟨hw, hV⟩ := h
  obtain ⟨hhalt, hout⟩ := run_parameters hrun hw
  rw [hV] at hout
  have heval := eval_tableau_trueVars hhalt hout
  rw [hw] at heval
  exact SAT.isWitness_padCertificate_relabel Var.index_injective heval

/-- **Backward witnesses.** A witness of `SAT` for the reduced formula is sent to a witness for
`a`: the certificate bits of the assignment it describes. -/
theorem isWitness_backwardWitness (hrun : RunsVerifier R tm c d) {a : α} {w : List Bool}
    (h : SAT.npRelation.IsWitness (reduce tm R.certLength c d enc a) w) :
    R.IsWitness a (backwardWitness tm R.certLength c d enc (a, w)) := by
  have hτ := SAT.eval_assignment_of_isWitness h
  rw [reduce, CNF.eval_relabel] at hτ
  have hz : (backwardWitness tm R.certLength c d enc (a, w)).length =
      R.certLength.eval (enc a).length := by
    simp [backwardWitness]
  have hcert : certWord (SAT.assignment (reduce tm R.certLength c d enc a) w ∘
      Var.index (k := k) (State := State))
      (backwardWitness tm R.certLength c d enc (a, w)).length =
      backwardWitness tm R.certLength c d enc (a, w) := by
    rw [hz]
    rfl
  obtain ⟨hhalt, hout⟩ := exists_eval_tableau_iff.1 ⟨_, hcert, by rw [hz]; exact hτ⟩
  obtain ⟨-, hout'⟩ := run_parameters hrun hz
  rw [hout'] at hout
  exact ⟨hz, List.head_eq_of_cons_eq hout⟩

/-! ### Polynomial time -/

/-- The tableau witness is polynomial-time in the input prefix, the certificate and the unary
bounds, for a fixed machine. -/
theorem computableInPolyTime_tableauWitness (tm : MultiTapeTM k Bool State) :
    ComputableInPolyTime
      (fun y : (List Bool × ℕ × ℕ) × List Bool => tableauWitness tm y.1.1 y.2 y.1.2.1 y.1.2.2)
      (encPair (encPair encBits (encPair encUnary encUnary)) encBits) encBits := by
  have hvars := (CNF.computableInPolyTime_vars (encVar (k := k) (State := State))).comp
    ((computableInPolyTime_tableau tm).comp
      (fst (encPair encBits (encPair encUnary encUnary)) encBits))
  have htrue := (computableInPolyTime_trueVars tm).comp
    ((((fst _ _).comp ((fst _ _).comp (fst _ _))).prod ((snd _ _).comp (fst _ _))).prod
      ((snd _ _).comp ((snd _ _).comp ((fst _ _).comp
        (fst (encPair (encPair encBits (encPair encUnary encUnary)) encBits)
          (encVar (k := k) (State := State)))))))
  exact mapToBitsWithInput hvars (decide_mem htrue (snd _ _))

/-- The forward witness map is polynomial-time, for a fixed machine and fixed bounds. -/
theorem computableInPolyTime_forwardWitness (tm : MultiTapeTM k Bool State) (p : Polynomial ℕ)
    (c d : ℕ) (enc : α ↪ List Bool) :
    ComputableInPolyTime (forwardWitness tm p c d enc) (encPair enc encBits) encBits := by
  have hq : ComputableInPolyTime (fun x : α × List Bool => parameters p c d enc x.1)
      (encPair enc encBits) (encPair encBits (encPair encUnary encUnary)) :=
    (computableInPolyTime_parameters p c d enc).comp (fst _ _)
  have h := SAT.computableInPolyTime_padCertificate
    ((computableInPolyTime_reduce tm p c d enc).comp (fst _ _))
    ((computableInPolyTime_tableauWitness tm).comp (hq.prod (snd _ _)))
  exact h

/-- The backward witness map is polynomial-time, for a fixed machine and fixed bounds. -/
theorem computableInPolyTime_backwardWitness (tm : MultiTapeTM k Bool State) (p : Polynomial ℕ)
    (c d : ℕ) (enc : α ↪ List Bool) :
    ComputableInPolyTime (backwardWitness tm p c d enc) (encPair enc encBits) encBits := by
  have hq : ComputableInPolyTime (fun x : α × List Bool => parameters p c d enc x.1)
      (encPair enc encBits) (encPair encBits (encPair encUnary encUnary)) :=
    (computableInPolyTime_parameters p c d enc).comp (fst _ _)
  have hL : ComputableInPolyTime (fun x : α × List Bool => p.eval (enc x.1).length)
      (encPair enc encBits) encUnary := (fst _ _).comp ((snd _ _).comp hq)
  have hbody : ComputableInPolyTime
      (fun y : (α × List Bool) × ℕ => SAT.assignment (reduce tm p c d enc y.1.1) y.1.2
        (Var.cert (k := k) (State := State) y.2).index)
      (encPair (encPair enc encBits) encUnary) encBool :=
    SAT.computableInPolyTime_assignment.comp
      ((((computableInPolyTime_reduce tm p c d enc).comp ((fst _ _).comp (fst _ _))).prod
        ((snd _ _).comp (fst _ _))).prod
        ((computableInPolyTime_index (k := k) (State := State)).comp
          (computableInPolyTime_cert.comp (snd _ _))))
  exact mapToBitsWithInput (range.comp hL) hbody

/-! ### The Levin reduction -/

/-- **The Cook–Levin reduction is a Levin reduction** of an NP relation to the NP relation of
`SAT`, for a machine `tm` computing its verifier within `c * (n + 1) ^ d` steps. -/
noncomputable def levinReduction (R : NPRelation enc) (tm : MultiTapeTM k Bool State) (c d : ℕ)
    (hrun : RunsVerifier R tm c d) : LevinReduction R SAT.npRelation where
  toFun := reduce tm R.certLength c d enc
  forwardWitness := forwardWitness tm R.certLength c d enc
  backwardWitness := backwardWitness tm R.certLength c d enc
  computableInPolyTime_toFun := computableInPolyTime_reduce tm R.certLength c d enc
  computableInPolyTime_forwardWitness := computableInPolyTime_forwardWitness tm _ c d enc
  computableInPolyTime_backwardWitness := computableInPolyTime_backwardWitness tm _ c d enc
  isWitness_forwardWitness _ _ := isWitness_forwardWitness hrun
  isWitness_backwardWitness _ _ := isWitness_backwardWitness hrun

/-- **Cook–Levin, witness-preserving form.** Every NP relation, over any encoded type of
instances, Levin-reduces to the NP relation of `SAT`. -/
theorem SAT_levinHard : LevinHard SAT.npRelation := fun α enc R => by
  obtain ⟨t, _, ht, -, k, State, hfin, tm, htm⟩ := R.computableInPolyTime_verifier
  obtain ⟨c, d, ht⟩ := polynomiallyBounded_iff_le.mp ht
  have := Fintype.ofFinite State
  classical
  exact ⟨levinReduction R tm c d fun a w _ => (htm (a, w)).runFrom_of_le (ht _)⟩

/-- **Every NP relation Levin-reduces to 3SAT**: the Cook–Levin Levin reduction followed by the
SAT → 3SAT Levin reduction. -/
theorem ThreeSAT_levinHard : LevinHard ThreeSAT.npRelation :=
  SAT_levinHard.trans toThreeSATLevinReduction

end Cslib.Complexity.CookLevin
