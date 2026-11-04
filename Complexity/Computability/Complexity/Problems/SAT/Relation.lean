/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP.Relation
public import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# SAT as an NP relation

`Cslib.Complexity.SAT.npRelation` is the NP relation of `SAT`: a certificate for a formula `φ`
has the length of the encoded formula and lists the values of the variables in order of first
occurrence (`Cslib.Complexity.SAT.assignment`). Its language is `SAT`.

Witness maps into `SAT` build certificates from assignments. If the formula is a relabelling
`ψ.relabel f` along an injective `f`, an assignment `σ` of the variables of `ψ` is described by
the values `ψ.vars.map σ`, read along the occurrences of `ψ` itself, followed by padding
(`Cslib.Complexity.SAT.padCertificate`); no inverse of `f` is needed
(`Cslib.Complexity.SAT.verifier_relabel_vars_map_append`). This is how the explicit witness maps
of the Levin reductions to `SAT` and `ThreeSAT` are written.

## Main definitions

* `Cslib.Complexity.SAT.npRelation`: the NP relation of `SAT`.
* `Cslib.Complexity.SAT.padCertificate`: a certificate prefix padded with `false` to the length
  prescribed for a formula.

## Main results

* `Cslib.Complexity.SAT.language_npRelation`: its language is `SAT`.
* `Cslib.Complexity.SAT.verifier_relabel_vars_map_append`: the values of an assignment along the
  occurrences of `ψ` are a certificate for `ψ.relabel f` that the verifier evaluates as `σ`.
* `Cslib.Complexity.SAT.isWitness_padCertificate_relabel`,
  `Cslib.Complexity.SAT.isWitness_padCertificate`: satisfying assignments give witnesses.
* `Cslib.Complexity.SAT.computableInPolyTime_padCertificate`: padding is polynomial-time.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Complexity.SAT

open Cslib.Logic.PL Turing.MultiTapeTM

/-- The NP relation of `SAT`: certificates as long as the encoded formula, checked by
`Cslib.Complexity.SAT.verifier`. -/
@[expose]
noncomputable def npRelation : NPRelation encCNF :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier⟩

@[simp] theorem npRelation_certLength : npRelation.certLength = Polynomial.X := rfl

@[simp] theorem npRelation_verifier : npRelation.verifier = verifier := rfl

theorem isWitness_npRelation_iff {φ : CNF ℕ} {w : List Bool} :
    npRelation.IsWitness φ w ↔ w.length = (encCNF φ).length ∧ verifier (φ, w) = true := by
  rw [NPRelation.isWitness_iff, npRelation_certLength, npRelation_verifier, Polynomial.eval_X]

/-- The language of the NP relation of `SAT` is `SAT`. -/
theorem language_npRelation : npRelation.language = SAT :=
  npRelation.language_eq_of_isVerifier isVerifier

/-! ### Certificates from assignments -/

/-- A certificate prefix `u` for `φ`, padded on the right with `false` to the length of the
encoded formula. -/
@[expose]
def padCertificate (φ : CNF ℕ) (u : List Bool) : List Bool :=
  u.rightpad (encCNF φ).length false

theorem length_padCertificate {φ : CNF ℕ} {u : List Bool} (h : u.length ≤ (encCNF φ).length) :
    (padCertificate φ u).length = (encCNF φ).length := by
  rw [padCertificate, List.rightpad, List.length_append, List.length_replicate,
    Nat.add_sub_cancel' h]

/-- Read along the occurrences of `ψ.relabel f`, for an injective `f`, the values of `σ` listed
along the occurrences of `ψ` describe `σ`: the certificate assignment at `f x` is `σ x`. -/
theorem assignment_relabel_vars_map_append {V : Type*} {f : V → ℕ} (hf : Function.Injective f)
    (ψ : CNF V) (σ : V → Bool) (v : List Bool) {x : V} (hx : x ∈ ψ.vars) :
    assignment (ψ.relabel f) (ψ.vars.map σ ++ v) (f x) = σ x := by
  rw [assignment, CNF.vars_relabel]
  have hlt : (ψ.vars.map f).idxOf (f x) < (ψ.vars.map f).length :=
    List.idxOf_lt_length_iff.2 (List.mem_map_of_mem hx)
  have hget := List.getElem_idxOf hlt
  rw [List.getElem_map] at hget
  have hlt' : (ψ.vars.map f).idxOf (f x) < ψ.vars.length := by simpa using hlt
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hlt),
    List.getElem?_map, List.getElem?_eq_getElem hlt', Option.map_some, Option.getD_some,
    hf hget]

/-- The verifier of `SAT`, on `ψ.relabel f` for an injective `f` and the values of `σ` along the
occurrences of `ψ` followed by any bits, evaluates `ψ` under `σ`. -/
theorem verifier_relabel_vars_map_append {V : Type*} {f : V → ℕ} (hf : Function.Injective f)
    (ψ : CNF V) (σ : V → Bool) (v : List Bool) :
    verifier (ψ.relabel f, ψ.vars.map σ ++ v) = ψ.eval σ := by
  rw [verifier, CNF.eval_relabel]
  exact CNF.eval_congr fun x hx => assignment_relabel_vars_map_append hf ψ σ v hx

/-- An assignment `σ` satisfying `ψ` gives a witness for `ψ.relabel f`, for an injective `f`: its
values along the occurrences of `ψ`, padded. -/
theorem isWitness_padCertificate_relabel {V : Type*} {f : V → ℕ} (hf : Function.Injective f)
    {ψ : CNF V} {σ : V → Bool} (h : ψ.eval σ = true) :
    npRelation.IsWitness (ψ.relabel f) (padCertificate (ψ.relabel f) (ψ.vars.map σ)) := by
  refine isWitness_npRelation_iff.2 ⟨length_padCertificate ?_, ?_⟩
  · simpa [CNF.vars_relabel] using length_vars_le (ψ.relabel f)
  · rw [padCertificate, List.rightpad, verifier_relabel_vars_map_append hf, h]

/-- An assignment `σ` satisfying `φ` gives a witness for `φ`: its values along the occurrences of
`φ`, padded. -/
theorem isWitness_padCertificate {φ : CNF ℕ} {σ : ℕ → Bool} (h : φ.eval σ = true) :
    npRelation.IsWitness φ (padCertificate φ (φ.vars.map σ)) := by
  simpa using isWitness_padCertificate_relabel Function.injective_id h

/-- The assignment described by a witness satisfies the formula. -/
theorem eval_assignment_of_isWitness {φ : CNF ℕ} {w : List Bool}
    (h : npRelation.IsWitness φ w) : φ.eval (assignment φ w) = true :=
  h.2

/-- Padding a certificate prefix is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_padCertificate {γ : Type} {input : γ ↪ List Bool}
    {φ : γ → CNF ℕ} {u : γ → List Bool} (hφ : ComputableInPolyTime φ input encCNF)
    (hu : ComputableInPolyTime u input encBits) :
    ComputableInPolyTime (fun x => padCertificate (φ x) (u x)) input encBits := by
  have henc := ComputableInPolyTime.encoding_comp hφ
  have hlen : ComputableInPolyTime (fun x => (encCNF (φ x)).length) input encUnary := by
    fun_prop
  unfold padCertificate List.rightpad
  exact hu.bitsAppend ((ComputableInPolyTime.bitsReplicate false).comp (by fun_prop))

end Cslib.Complexity.SAT
