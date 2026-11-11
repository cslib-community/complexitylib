/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.PrimitivePositive
public import Complexity.Computability.PolyTime.CSP.Boolean
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.List.Enum
import Mathlib.Data.List.GetD

/-!
# Certified fixed-gadget replacement

Each source constraint is replaced by a fixed equality-free gadget. Original variable `v`
becomes `2*v`; auxiliary port `j` at constraint index `i` becomes `2*(B*i+j)+1`, where
`B` bounds every gadget's auxiliary count. Repeated source variables are allowed.
A global exact-arity guard sends malformed inputs to an explicit rejecting target instance.
The rejection premise concerns only that fixed instance, not a solver or gadget theorem.

The native multitape polynomial-time certificate uses binary input/output variable indices,
unary local template indices and constraint indices, and a finite lookup for the fixed
source alphabet. This is the equality-free case of [Chen2006CSP], Proposition 3.9, arXiv v1,
p. 8, with the encoding and malformed-input behavior made explicit.

## Main definitions

* `Cslib.Logic.PL.CSP.PPGadget.template`: uniform local ports for a certified gadget.
* `Cslib.Logic.PL.CSP.replaceGadgetsGuarded`: exact-arity guarded fixed-gadget replacement.

## Main results

* `Cslib.Logic.PL.CSP.satisfiable_replaceGadgetsGuarded_iff`: total semantic correctness.
* `Cslib.Complexity.CSP.computableInPolyTime_replaceGadgetsGuarded`: native polynomial time
  for fixed finite source alphabets, with binary variable names.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
    {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}

namespace PPGadget

/-- Uniform local ports: `false` denotes a free port and `true` an auxiliary port.
The natural indices are bounded constants, encoded in unary. -/
@[expose] def template {n : ℕ} {R : Set (Fin n → Bool)} (g : PPGadget arity sem R) :
    CSP Rel (Bool × ℕ) :=
  g.body.relabel (Sum.elim (fun i => (false, i.val)) (fun i => (true, i.val)))

end PPGadget

/-- Instantiate a local template at one source scope and constraint index. -/
@[expose] def instantiate (B index : ℕ) (scope : List ℕ) (body : CSP Rel (Bool × ℕ)) : CSP Rel ℕ :=
  body.relabel fun p => if p.1 then 2 * (B * index + p.2) + 1
    else 2 * scope.getD p.2 0

/-- Replace every source constraint, with disjoint auxiliary namespaces. -/
@[expose] def replaceGadgets (B : ℕ) (templates : Src → CSP Rel (Bool × ℕ))
    (F : CSP Src ℕ) : CSP Rel ℕ :=
  F.zipIdx.flatMap fun ((r, scope), index) =>
    instantiate B index scope (templates r)

/-- Exact-arity guarded gadget replacement with an explicit reject instance. -/
@[expose] def replaceGadgetsGuarded (srcArity : Src → ℕ) (B : ℕ)
    (templates : Src → CSP Rel (Bool × ℕ)) (reject : CSP Rel ℕ)
    (F : CSP Src ℕ) : CSP Rel ℕ :=
  if validArity srcArity F then replaceGadgets B templates F else reject

/-- Uniform templates retain the well-formedness of the certified gadget. -/
theorem PPGadget.wellFormed_template {n : ℕ} {R : Set (Fin n → Bool)}
    (g : PPGadget arity sem R) : WellFormed arity g.template := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  simpa [Constraint.relabel] using g.wellFormed d hd

/-- Renaming a well-formed gadget preserves exact target arities. -/
theorem wellFormed_instantiate (B index : ℕ) (scope : List ℕ)
    (body : CSP Rel (Bool × ℕ)) (h : WellFormed arity body) :
    WellFormed arity (instantiate B index scope body) := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  simpa [Constraint.relabel] using h d hd

/-- Replacing with well-formed templates produces well-formed target constraints. -/
theorem wellFormed_replaceGadgets (B : ℕ) (templates : Src → CSP Rel (Bool × ℕ))
    (h : ∀ r, WellFormed arity (templates r)) (F : CSP Src ℕ) :
    WellFormed arity (replaceGadgets B templates F) := by
  intro c hc
  obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp hc
  exact wellFormed_instantiate B p.2 p.1.2 (templates p.1.1) (h _) c hp

/-- The guarded compiler produces a well-formed result if its fixed reject instance is
well formed. -/
theorem wellFormed_replaceGadgetsGuarded (srcArity : Src → ℕ) (B : ℕ)
    (templates : Src → CSP Rel (Bool × ℕ)) (h : ∀ r, WellFormed arity (templates r))
    (reject : CSP Rel ℕ) (hr : WellFormed arity reject) (F : CSP Src ℕ) :
    WellFormed arity (replaceGadgetsGuarded srcArity B templates reject F) := by
  unfold replaceGadgetsGuarded
  split
  · exact wellFormed_replaceGadgets B templates h F
  · exact hr

private theorem eval_instantiate {n : ℕ} {R : Set (Fin n → Bool)}
    (g : PPGadget arity sem R) (B index : ℕ) (scope : List ℕ) (σ : ℕ → Bool) :
    (instantiate B index scope g.template).eval sem σ =
      g.body.eval sem (Sum.elim (fun i => σ (2 * scope.getD i.val 0))
        (fun j => σ (2 * (B * index + j.val) + 1))) := by
  simp only [instantiate, PPGadget.template, eval_relabel]
  congr 1
  funext x
  cases x <;> rfl

/-- Correct gadgets preserve satisfiability on well-formed inputs.
Only a uniform bound on the number of auxiliary ports is required. -/
theorem satisfiable_replaceGadgets_iff
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (hB : ∀ r, (gadgets r).numAux ≤ B)
    (F : CSP Src ℕ) (hF : WellFormed srcArity F) :
    (replaceGadgets B (fun r => (gadgets r).template) F).Satisfiable sem ↔
      F.Satisfiable srcSem := by
  classical
  have hev (σ : ℕ → Bool) :
      (replaceGadgets B (fun r => (gadgets r).template) F).eval sem σ = true ↔
      ∀ (i : ℕ) (hi : i < F.length),
        ((gadgets F[i].1).body.eval sem
          (Sum.elim (fun j => σ (2 * F[i].2.getD j.val 0))
            (fun j => σ (2 * (B * i + j.val) + 1)))) = true := by
    rw [replaceGadgets, eval, List.all_flatMap]
    change F.zipIdx.all (fun p =>
      (instantiate B p.2 p.1.2 (gadgets p.1.1).template).eval sem σ) = true ↔ _
    simp only [List.all_eq_true, List.forall_mem_zipIdx', eval_instantiate]
  have scope_eq (σ : ℕ → Bool) (i : ℕ) (hi : i < F.length) :
      List.ofFn (fun j : Fin (srcArity F[i].1) => σ (F[i].2.getD j.val 0)) =
        F[i].2.map σ := by
    have hlen := hF F[i] (List.getElem_mem hi)
    apply List.ext_getElem
    · simp [hlen]
    · intro j hj hk
      simp only [List.getElem_ofFn, List.getElem_map]
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hk)]
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨fun v => τ (2 * v), ?_⟩
    rw [eval, List.all_eq_true, List.forall_mem_iff_getElem]
    intro i hi
    have hg := (gadgets F[i].1).correct (fun j => τ (2 * F[i].2.getD j.val 0))
    have hr := hg.mpr ⟨_, (hev τ).mp hτ i hi⟩
    change srcSem F[i].1 (List.ofFn _) = true at hr
    rw [scope_eq (fun v => τ (2 * v)) i hi] at hr
    exact hr
  · rintro ⟨σ, hσ⟩
    have hex : ∀ (i : ℕ) (hi : i < F.length), ∃ b : Fin (gadgets F[i].1).numAux → Bool,
        (gadgets F[i].1).body.eval sem
          (Sum.elim (fun j => σ (F[i].2.getD j.val 0)) b) = true := by
      intro i hi
      apply ((gadgets F[i].1).correct _).mp
      change srcSem F[i].1 (List.ofFn _) = true
      rw [scope_eq]
      exact (List.all_eq_true.mp hσ) F[i] (List.getElem_mem hi)
    choose b hb using hex
    let aux : ℕ → ℕ → Bool := fun i j =>
      if hi : i < F.length then
        if hj : j < (gadgets F[i].1).numAux then b i hi ⟨j, hj⟩ else false
      else false
    let τ : ℕ → Bool := fun v =>
      if v % 2 = 0 then σ (v / 2) else aux ((v / 2) / B) ((v / 2) % B)
    refine ⟨τ, (hev τ).mpr fun i hi => ?_⟩
    have hfree (v : ℕ) : τ (2 * v) = σ v := by simp [τ]
    have haux (j : Fin (gadgets F[i].1).numAux) :
        τ (2 * (B * i + j.val) + 1) = b i hi j := by
      have hj : j.val < B := j.isLt.trans_le (hB _)
      have hpos : 0 < B := by omega
      have hhalf : (2 * (B * i + j.val) + 1) / 2 = B * i + j.val := by omega
      have hodd : (2 * (B * i + j.val) + 1) % 2 ≠ 0 := by omega
      have hdiv : (B * i + j.val) / B = i := by
        rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hj, Nat.add_zero]
      have hmod : (B * i + j.val) % B = j.val := by
        simp [Nat.add_mod, Nat.mod_eq_of_lt hj]
      simp only [τ, ite_eq_right hodd, hhalf, hdiv, hmod]
      simp [aux, hi, j.isLt]
    simpa only [hfree, haux] using hb i hi

/-- The exact-arity guard gives total correctness, including malformed inputs.
The supplied reject instance must be unsatisfiable. -/
theorem satisfiable_replaceGadgetsGuarded_iff
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (hB : ∀ r, (gadgets r).numAux ≤ B)
    (reject : CSP Rel ℕ) (hreject : ¬ reject.Satisfiable sem) (F : CSP Src ℕ) :
    (replaceGadgetsGuarded srcArity B (fun r => (gadgets r).template) reject F).Satisfiable sem ↔
      WellFormed srcArity F ∧ F.Satisfiable srcSem := by
  by_cases h : WellFormed srcArity F
  · simp only [replaceGadgetsGuarded, (validArity_eq_true_iff _ _).mpr h,
      ↓reduceIte, h, true_and]
    exact satisfiable_replaceGadgets_iff gadgets B hB F h
  · have hv : validArity srcArity F = false := Bool.eq_false_iff.mpr fun hv =>
      h ((validArity_eq_true_iff _ _).mp hv)
    simp [replaceGadgetsGuarded, hv, h, hreject]

/-- Full guarded correctness for the exact-arity CSP decision predicate. A reject target
may fail either well-formedness or satisfiability, allowing a fixed malformed constraint. -/
theorem wellFormed_satisfiable_replaceGadgetsGuarded_iff
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (hB : ∀ r, (gadgets r).numAux ≤ B)
    (reject : CSP Rel ℕ) (hreject : ¬ (WellFormed arity reject ∧ reject.Satisfiable sem))
    (F : CSP Src ℕ) :
    (WellFormed arity (replaceGadgetsGuarded srcArity B
        (fun r => (gadgets r).template) reject F) ∧
      (replaceGadgetsGuarded srcArity B
        (fun r => (gadgets r).template) reject F).Satisfiable sem) ↔
      WellFormed srcArity F ∧ F.Satisfiable srcSem := by
  by_cases h : WellFormed srcArity F
  · have hv := (validArity_eq_true_iff srcArity F).mpr h
    have hw := wellFormed_replaceGadgets B (fun r => (gadgets r).template)
      (fun r => (gadgets r).wellFormed_template) F
    simp only [replaceGadgetsGuarded, hv, ↓reduceIte, hw, true_and, h]
    exact satisfiable_replaceGadgets_iff gadgets B hB F h
  · have hv : validArity srcArity F = false := Bool.eq_false_iff.mpr fun hv =>
      h ((validArity_eq_true_iff _ _).mp hv)
    simp [replaceGadgetsGuarded, hv, h, hreject]

/-- A fixed malformed target for rejecting invalid source scopes. Any target symbol suffices. -/
@[expose] def malformedReject (arity : Rel → ℕ) (r : Rel) : CSP Rel ℕ :=
  [(r, List.replicate (arity r + 1) 0)]

/-- The fixed reject target fails exact arity independently of its semantics. -/
theorem not_wellFormed_malformedReject (arity : Rel → ℕ) (r : Rel) :
    ¬ WellFormed arity (malformedReject arity r) := by
  simp [WellFormed, malformedReject]

end Cslib.Logic.PL.CSP

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime
open Cslib.Logic.PL.CSP

variable {Src Rel : Type}

/-- Instantiate a local template in native polynomial time. Local indices and the
constraint number are unary; scope variable names and output names are binary. -/
theorem computableInPolyTime_instantiate (encRel : Rel ↪ List Bool) (B : ℕ) :
    ComputableInPolyTime
      (fun p : (ℕ × List ℕ) × CSP Rel (Bool × ℕ) =>
        let ((index, scope), body) := p
        instantiate B index scope body)
      (encPair (encPair encUnary (encList encNat))
        (encCSP encRel (encPair encBool encUnary))) (encCSP encRel encNat) := by
  unfold instantiate relabel Constraint.relabel
  fun_prop

/-- Finite fixed gadget lookup and replacement are native polynomial time, with no
computability requirement on the process used to obtain the fixed gadgets. -/
theorem computableInPolyTime_replaceGadgets [Finite Src]
    (encSrc : Src ↪ List Bool) (encRel : Rel ↪ List Bool) (B : ℕ)
    (templates : Src → CSP Rel (Bool × ℕ)) :
    ComputableInPolyTime (replaceGadgets B templates)
      (encCSP encSrc encNat) (encCSP encRel encNat) := by
  have ht : ComputableInPolyTime templates encSrc
      (encCSP encRel (encPair encBool encUnary)) := of_finite _
  have hi := computableInPolyTime_instantiate encRel B
  have hz : ComputableInPolyTime (fun F : CSP Src ℕ => F.zipIdx)
      (encCSP encSrc encNat) (encList (encPair (encConstraint encSrc encNat) encUnary)) :=
    .of_tidy (ComputableTidilyInPolyTime.zipIdx _)
  unfold replaceGadgets
  apply flatMapWithInput hz
  exact hi.comp (g := fun p : CSP Src ℕ × (Constraint Src ℕ × ℕ) =>
    ((p.2.2, p.2.1.2), templates p.2.1.1)) (by fun_prop)

/-- A total native polynomial-time compiler with an explicit malformed-input reject target. -/
theorem computableInPolyTime_replaceGadgetsGuarded [Finite Src]
    (encSrc : Src ↪ List Bool) (encRel : Rel ↪ List Bool)
    (srcArity : Src → ℕ) (B : ℕ) (templates : Src → CSP Rel (Bool × ℕ))
    (reject : CSP Rel ℕ) :
    ComputableInPolyTime (replaceGadgetsGuarded srcArity B templates reject)
      (encCSP encSrc encNat) (encCSP encRel encNat) :=
  (computableInPolyTime_validArity encSrc srcArity).ite
    (computableInPolyTime_replaceGadgets encSrc encRel B templates) (const reject)

end Cslib.Complexity.CSP
