/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT.Relation
public import CslibFrontier.Computability.Complexity.Problems.ThreeSAT
public import CslibFrontier.Computability.Complexity.Reduction.Levin
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Logics.Propositional.CNF.ThreeCNF.PolyTime

/-!
# The Levin reduction from SAT to 3SAT

`Cslib.Complexity.ThreeSAT.npRelation` is the NP relation of `ThreeSAT`, and
`Cslib.Complexity.toThreeSATLevinReduction` is a Levin reduction of the NP relation of `SAT` to
it, with instance map `Cslib.Complexity.toThreeSAT`. Both witness maps are explicit and certified
polynomial-time:

* forward (`Cslib.Complexity.toThreeSATWitness`): the assignment `σ` described by a certificate for
  `φ` is extended to the auxiliary variables of `φ.to3CNF` by
  `Cslib.Logic.PL.CNF.to3CNFAssignment`, the auxiliary variable `(i, k)` taking the value of the
  disjunction of the literals of clause `i` after position `k + 1`
  [Arora and Barak, Section 2.3.1][AroraBarak09], and listed along the occurrences of `φ.to3CNF`;
* backward (`Cslib.Complexity.ofThreeSATWitness`): the assignment described by a certificate for
  `toThreeSAT φ` is restricted to the original variables, which `toThreeSAT` numbers `2 * v`.

## Main definitions

* `Cslib.Complexity.ThreeSAT.npRelation`: the NP relation of `ThreeSAT`.
* `Cslib.Complexity.toThreeSATWitness`, `Cslib.Complexity.ofThreeSATWitness`: the witness maps.
* `Cslib.Complexity.toThreeSATLevinReduction`: the Levin reduction.

## Main results

* `Cslib.Complexity.ThreeSAT.language_npRelation`: the language of the relation is `ThreeSAT`.
* `Cslib.Complexity.isWitness_toThreeSATWitness`, `Cslib.Complexity.isWitness_ofThreeSATWitness`:
  the witness maps send witnesses to witnesses.
* `Cslib.Complexity.computableInPolyTime_toThreeSATWitness`,
  `Cslib.Complexity.computableInPolyTime_ofThreeSATWitness`: they are polynomial-time.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2008], Exercise
  2.28 (numbering of the author's online draft of 30 December 2006).
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

namespace ThreeSAT

/-- The NP relation of `ThreeSAT`: certificates as long as the encoded formula, checked by
`Cslib.Complexity.ThreeSAT.verifier`. -/
@[expose]
noncomputable def npRelation : NPRelation encCNF :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier⟩

/-- A witness of `ThreeSAT` is a witness of `SAT` for a formula of width at most three. -/
theorem isWitness_npRelation_iff {φ : CNF ℕ} {w : List Bool} :
    npRelation.IsWitness φ w ↔ (∀ c ∈ φ, c.length ≤ 3) ∧ SAT.npRelation.IsWitness φ w := by
  simp only [NPRelation.isWitness_iff, npRelation, SAT.npRelation, verifier, Bool.and_eq_true,
    List.all_eq_true, decide_eq_true_eq]
  tauto

/-- The language of the NP relation of `ThreeSAT` is `ThreeSAT`. -/
theorem language_npRelation : npRelation.language = ThreeSAT :=
  npRelation.language_eq_of_isVerifier isVerifier

end ThreeSAT

/-! ### The witness maps -/

/-- The forward witness map: the assignment described by a certificate `x.2` for `x.1`, extended
to the auxiliary variables of `x.1.to3CNF` and listed along its occurrences. -/
@[expose]
def toThreeSATWitness (x : CNF ℕ × List Bool) : List Bool :=
  SAT.padCertificate (toThreeSAT x.1)
    (x.1.to3CNF.vars.map (x.1.to3CNFAssignment (SAT.assignment x.1 x.2)))

/-- The backward witness map: the assignment described by a certificate `x.2` for
`toThreeSAT x.1`, restricted to the original variables and listed along the occurrences of
`x.1`. -/
@[expose]
def ofThreeSATWitness (x : CNF ℕ × List Bool) : List Bool :=
  SAT.padCertificate x.1
    (x.1.vars.map fun v => SAT.assignment (toThreeSAT x.1) x.2 (splitVarToNat (.inl v)))

/-- The forward witness map sends witnesses of `SAT` to witnesses of `ThreeSAT`. -/
theorem isWitness_toThreeSATWitness {φ : CNF ℕ} {w : List Bool}
    (h : SAT.npRelation.IsWitness φ w) :
    ThreeSAT.npRelation.IsWitness (toThreeSAT φ) (toThreeSATWitness (φ, w)) := by
  refine ThreeSAT.isWitness_npRelation_iff.2 ⟨fun c hc => ?_, ?_⟩
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    simpa using CNF.length_le_three_of_mem_to3CNF hd
  · exact SAT.isWitness_padCertificate_relabel splitVarToNat_injective
      (CNF.eval_to3CNF_to3CNFAssignment (SAT.eval_assignment_of_isWitness h))

/-- The backward witness map sends witnesses of `ThreeSAT` to witnesses of `SAT`. -/
theorem isWitness_ofThreeSATWitness {φ : CNF ℕ} {w : List Bool}
    (h : ThreeSAT.npRelation.IsWitness (toThreeSAT φ) w) :
    SAT.npRelation.IsWitness φ (ofThreeSATWitness (φ, w)) := by
  have hτ := SAT.eval_assignment_of_isWitness (ThreeSAT.isWitness_npRelation_iff.1 h).2
  rw [toThreeSAT, CNF.eval_relabel] at hτ
  exact SAT.isWitness_padCertificate (CNF.eval_comp_inl_of_eval_to3CNF hτ)

/-! ### Polynomial time -/

/-- The extended assignment, written by case analysis on the two kinds of variables. -/
private theorem to3CNFAssignment_eq_elim (φ : CNF ℕ) (σ : ℕ → Bool) (s : ℕ ⊕ (ℕ × ℕ)) :
    φ.to3CNFAssignment σ s =
      s.getLeft?.elim (s.getRight?.elim false fun q =>
        Clause.eval σ ((φ.getD q.1 []).drop (q.2 + 2))) σ := by
  rcases s with _ | ⟨_, _⟩ <;> rfl

/-- Evaluating the extended assignment of the certificate assignment is polynomial-time, with
auxiliary variables numbered in unary. -/
private theorem computableInPolyTime_to3CNFAssignment :
    ComputableInPolyTime
      (fun p : (CNF ℕ × List Bool) × (ℕ ⊕ (ℕ × ℕ)) =>
        p.1.1.to3CNFAssignment (SAT.assignment p.1.1 p.1.2) p.2)
      (encPair (encPair encCNF encBits) (encSum encNat (encPair encUnary encUnary))) encBool := by
  simp only [to3CNFAssignment_eq_elim]
  have hleft := (ComputableInO.getLeft?_deg encNat (encPair encUnary encUnary)).computableInPolyTime
  have hright :=
    (ComputableInO.getRight?_deg encNat (encPair encUnary encUnary)).computableInPolyTime
  refine ComputableInPolyTime.optionElimWithInput (hleft.comp (.snd _ _))
    (ComputableInPolyTime.optionElimWithInput (hright.comp (.snd _ _)) (.const false) ?_) ?_
  · have hclause : ComputableInPolyTime
        (fun p : ((CNF ℕ × List Bool) × (ℕ ⊕ (ℕ × ℕ))) × (ℕ × ℕ) =>
          (p.1.1.1.getD p.2.1 []).drop (p.2.2 + 2))
        (encPair (encPair (encPair encCNF encBits) (encSum encNat (encPair encUnary encUnary)))
          (encPair encUnary encUnary)) (encList (encPair encNat encBool)) := by
      have hφ : ComputableInPolyTime
          (fun p : ((CNF ℕ × List Bool) × (ℕ ⊕ (ℕ × ℕ))) × (ℕ × ℕ) => p.1.1.1)
          (encPair (encPair (encPair encCNF encBits)
            (encSum encNat (encPair encUnary encUnary))) (encPair encUnary encUnary))
          (encList (encList (encPair encNat encBool))) :=
        (ComputableInPolyTime.fst encCNF encBits).comp
          ((ComputableInPolyTime.fst _ _).comp (.fst _ _))
      have hi : ComputableInPolyTime
          (fun p : ((CNF ℕ × List Bool) × (ℕ ⊕ (ℕ × ℕ))) × (ℕ × ℕ) => p.2.1)
          (encPair (encPair (encPair encCNF encBits)
            (encSum encNat (encPair encUnary encUnary))) (encPair encUnary encUnary))
          encUnary := by fun_prop
      have hk : ComputableInPolyTime
          (fun p : ((CNF ℕ × List Bool) × (ℕ ⊕ (ℕ × ℕ))) × (ℕ × ℕ) => p.2.2 + 2)
          (encPair (encPair (encPair encCNF encBits)
            (encSum encNat (encPair encUnary encUnary))) (encPair encUnary encUnary))
          encUnary := by fun_prop
      exact (ComputableInPolyTime.dropUnary (encA := encPair encNat encBool)).comp
        ((ComputableInPolyTime.listGetDWithInput hφ hi []).prod hk)
    exact SAT.computableInPolyTime_clause.comp
      (((ComputableInPolyTime.fst _ _).comp (.fst _ _)).prod hclause)
  · fun_prop [SAT.assignment]

/-- The forward witness map is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_toThreeSATWitness :
    ComputableInPolyTime toThreeSATWitness (encPair encCNF encBits) encBits := by
  have hvars : ComputableInPolyTime (fun x : CNF ℕ × List Bool => x.1.to3CNF.vars)
      (encPair encCNF encBits) (encList (encSum encNat (encPair encUnary encUnary))) :=
    (CNF.computableInPolyTime_vars _).comp ((CNF.isPolyTime_to3CNF encNat).comp (.fst _ _))
  exact SAT.computableInPolyTime_padCertificate (computableInPolyTime_toThreeSAT.comp (.fst _ _))
    (ComputableInPolyTime.mapToBitsWithInput hvars computableInPolyTime_to3CNFAssignment)

/-- The backward witness map is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_ofThreeSATWitness :
    ComputableInPolyTime ofThreeSATWitness (encPair encCNF encBits) encBits := by
  have hvars : ComputableInPolyTime (fun x : CNF ℕ × List Bool => x.1.vars)
      (encPair encCNF encBits) (encList encNat) :=
    SAT.computableInPolyTime_vars.comp (.fst _ _)
  have hbody : ComputableInPolyTime
      (fun p : (CNF ℕ × List Bool) × ℕ =>
        SAT.assignment (toThreeSAT p.1.1) p.1.2 (splitVarToNat (.inl p.2)))
      (encPair (encPair encCNF encBits) encNat) encBool :=
    SAT.computableInPolyTime_assignment.comp
      (((computableInPolyTime_toThreeSAT.comp ((ComputableInPolyTime.fst _ _).comp (.fst _ _))).prod
        ((ComputableInPolyTime.snd _ _).comp (.fst _ _))).prod
        (computableInPolyTime_splitVarToNat.comp
          ((ComputableInPolyTime.sumInl _ (encPair encUnary encUnary)).comp (.snd _ _))))
  exact SAT.computableInPolyTime_padCertificate (.fst _ _)
    (ComputableInPolyTime.mapToBitsWithInput hvars hbody)

/-! ### The Levin reduction -/

/-- **SAT Levin-reduces to 3SAT.** The instance map splits the clauses (`toThreeSAT`); the forward
witness map extends a satisfying assignment explicitly to the auxiliary variables, and the backward
map restricts it to the original ones. -/
@[expose]
def toThreeSATLevinReduction : LevinReduction SAT.npRelation ThreeSAT.npRelation where
  toFun := toThreeSAT
  forwardWitness := toThreeSATWitness
  backwardWitness := ofThreeSATWitness
  computableInPolyTime_toFun := computableInPolyTime_toThreeSAT
  computableInPolyTime_forwardWitness := computableInPolyTime_toThreeSATWitness
  computableInPolyTime_backwardWitness := computableInPolyTime_ofThreeSATWitness
  isWitness_forwardWitness _ _ := isWitness_toThreeSATWitness
  isWitness_backwardWitness _ _ := isWitness_ofThreeSATWitness

end Cslib.Complexity
