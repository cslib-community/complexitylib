/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.P.FirstOrder.ModelChecker
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Logics.FirstOrder.Ordered.LeastFixedPoint
import Complexity.Computability.Complexity.Fagin.Verifier
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-!
# Polynomial-time evaluation of ordered FO(LFP)

For each fixed formula, the finite evaluator is computed by a native multi-tape Turing machine
in polynomial time. The proof uses the library's certified closure rules for Boolean operations,
bounded quantification, table construction and iteration. A fixed point's working table has
exactly `n ^ k` bits after each step, so the loop calculus accounts for the size of intermediate
states as well as the number of iterations.

The input vocabulary and formula are fixed. Polynomial degrees may depend on the formula's
quantifier nesting and relation arities; no polynomial combined-complexity claim is made when
the formula itself is part of the input.

## Main results

* `Cslib.Logic.FO.LFP.ModelChecker.computableInPolyTime_eval`: the raw bounded evaluator has a
  native polynomial-time certificate, uniformly in polynomial-time input assignments.
* `Cslib.Logic.FO.LFP.ModelChecker.computableInPolyTime_modelChecker`: the sentence decider,
  including shape and universe-size checks, is polynomial time.
* `Cslib.Logic.FO.Ordered.LFPDefinable.encodedLanguage_mem_P`: every ordered FO(LFP)-definable
  query belongs to the existing native machine class `P` under `encStructure`.

## References

* [N. Immerman, *Relational queries computable in polynomial time*][Immerman1986], Section 2.
-/

public section

universe u v w

open FirstOrder Language Turing.MultiTapeTM

namespace Cslib.Logic.FO.LFP.ModelChecker

variable {L : Language.{u, v}} [L.IsRelational] (v : Vocabulary L)

open ComputableTidilyInPolyTime

private theorem termValue_poly {α : Type w} (t : (Ordered.language L).Term α)
    {γ : Type} {enc : γ ↪ List Bool} {n : γ → ℕ} {σ : γ → α → ℕ}
    (hn : ComputableTidilyInPolyTime n enc encUnary)
    (hσ : ∀ x, ComputableTidilyInPolyTime (fun a => σ a x) enc encUnary) :
    ComputableTidilyInPolyTime (fun a => termValue (n a) (σ a) t) enc encUnary := by
  cases t with
  | var x => exact hσ x
  | func f ts =>
    cases f with
    | inl f => exact isEmptyElim f
    | inr c =>
      cases c with
      | zero => exact const 0
      | one => exact const 1
      | max => exact unary_sub.comp (hn.prod (const 1))

private theorem valuesIndex_poly {k : ℕ} {γ : Type} {enc : γ ↪ List Bool}
    {n : γ → ℕ} {xs : γ → Fin k → ℕ}
    (hn : ComputableTidilyInPolyTime n enc encUnary)
    (hxs : ∀ j, ComputableTidilyInPolyTime (fun a => xs a j) enc encUnary) :
    ComputableTidilyInPolyTime (fun a => valuesIndex (n a) (xs a)) enc encUnary := by
  induction k with
  | zero => exact const 0
  | succ k ih =>
    exact unary_add.comp ((hxs 0).prod
      (unary_mul.comp (hn.prod (ih fun j => hxs j.succ))))

omit [L.IsRelational] in
private theorem relBit_poly {k : ℕ} (r : (Ordered.language L).Relations k)
    {γ : Type} {enc : γ ↪ List Bool} {a : γ → EncodedStructure} {xs : γ → Fin k → ℕ}
    (ha : ComputableTidilyInPolyTime a enc encStructure)
    (hxs : ∀ j, ComputableTidilyInPolyTime (fun x => xs x j) enc encUnary) :
    ComputableTidilyInPolyTime (fun x => relBit v (a x) r (xs x)) enc encBool := by
  cases r with
  | inl r =>
    exact bitsGetDWithInput
      (v.computableInPolyTime_table ⟨_, r⟩ ha.computableInPolyTime).tidy
      (valuesIndex_poly ha.fst' hxs) false
  | inr r =>
    cases r with
    | le => exact unary_le' (hxs 0) (hxs 1)
    | bit => exact binary_testBit (unary_to_binary.comp (hxs 0)) (hxs 1)

private theorem foEval_poly {α : Type w} {k : ℕ}
    (φ : (Ordered.language L).BoundedFormula α k) :
    ∀ {γ : Type} {enc : γ ↪ List Bool} {a : γ → EncodedStructure} {σ : γ → α → ℕ}
      {xs : γ → Fin k → ℕ},
      ComputableTidilyInPolyTime a enc encStructure →
      (∀ x, ComputableTidilyInPolyTime (fun y => σ y x) enc encUnary) →
      (∀ j, ComputableTidilyInPolyTime (fun y => xs y j) enc encUnary) →
      ComputableTidilyInPolyTime (fun y => foEval v (a y) (σ y) φ (xs y)) enc encBool := by
  induction φ with
  | falsum => intros; exact const false
  | equal s t =>
    intro γ enc a σ xs ha hσ hxs
    have hv (z) : ComputableTidilyInPolyTime
        (fun y => Sum.elim (σ y) (xs y) z) enc encUnary := by
      cases z with
      | inl x => exact hσ x
      | inr j => exact hxs j
    exact unary_beq (termValue_poly s ha.fst' hv) (termValue_poly t ha.fst' hv)
  | rel r ts =>
    intro γ enc a σ xs ha hσ hxs
    apply relBit_poly v r ha
    intro j
    apply termValue_poly (ts j) ha.fst'
    intro z
    cases z with
    | inl x => exact hσ x
    | inr j => exact hxs j
  | imp φ ψ ihφ ihψ =>
    intro γ enc a σ xs ha hσ hxs
    exact bool_or.comp ((bool_not.comp (ihφ ha hσ hxs)).prod (ihψ ha hσ hxs))
  | @all k φ ih =>
    intro γ enc a σ xs ha hσ hxs
    apply allWithInput (range.comp ha.fst')
    apply ih (ha.comp (fst enc encUnary)) (fun x => (hσ x).comp (fst enc encUnary))
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [Fin.snoc_last] using snd enc encUnary
    · simpa only [Fin.snoc_castSucc, Function.comp_def] using
        (hxs i).comp (fst enc encUnary)

private theorem eval_poly {Γ : List ℕ} {α : Type w}
    (φ : RawFormula (Ordered.language L) Γ α) :
    ∀ {γ : Type} {enc : γ ↪ List Bool} {a : γ → EncodedStructure}
      {tables : γ → List (List Bool)} {σ : γ → α → ℕ},
      ComputableTidilyInPolyTime a enc encStructure →
      ComputableTidilyInPolyTime tables enc (encList encBits) →
      (∀ x, ComputableTidilyInPolyTime (fun y => σ y x) enc encUnary) →
      ComputableTidilyInPolyTime (fun y => eval v φ (a y) (tables y) (σ y)) enc encBool := by
  induction φ with
  | ofFO φ =>
    intro γ enc a tables σ ha ht hσ
    exact foEval_poly v φ ha hσ (fun j => j.elim0)
  | rel r ts =>
    intro γ enc a tables σ ha ht hσ
    exact bitsGetDWithInput ((listGetD []).comp (ht.prod (const (relIndex r))))
      (valuesIndex_poly ha.fst' (fun j => termValue_poly (ts j) ha.fst' hσ)) false
  | neg φ ih =>
    intro γ enc a tables σ ha ht hσ
    exact bool_not.comp (ih ha ht hσ)
  | conj φ ψ ihφ ihψ =>
    intro γ enc a tables σ ha ht hσ
    exact bool_and.comp ((ihφ ha ht hσ).prod (ihψ ha ht hσ))
  | ex φ ih =>
    intro γ enc a tables σ ha ht hσ
    apply anyWithInput (range.comp ha.fst')
    apply ih (ha.comp (fst enc encUnary)) (ht.comp (fst enc encUnary))
    intro z
    cases z with
    | none => exact snd enc encUnary
    | some x => exact (hσ x).comp (fst enc encUnary)
  | @op Γ α k body ts ih =>
    intro γ enc a tables σ ha ht hσ
    let tableStep (x : γ) (table : List Bool) :=
      tableOf (a x).1 k (fun xs => eval v (body 0) (a x) (table :: tables x) (Sum.elim (σ x) xs))
    have hcount : ComputableTidilyInPolyTime (fun x => (a x).1 ^ k) enc encUnary :=
      (unary_pow k).comp ha.fst'
    have hstep : ComputableTidilyInPolyTime
        (fun p : γ × List Bool => tableStep p.1 p.2) (encPair enc encBits) encBits := by
      apply mapToBitsWithInput (range.comp (hcount.comp (fst enc encBits)))
      have hpar := fst (encPair enc encBits) encUnary
      have hinput := (fst enc encBits).comp hpar
      have hn := ha.fst'.comp hinput
      apply ih 0 (ha.comp hinput)
        (cons' ((snd enc encBits).comp hpar) (ht.comp hinput))
      intro z
      cases z with
      | inl x => exact (hσ x).comp hinput
      | inr j =>
        exact unary_mod.comp ((unary_div.comp
          ((snd (encPair enc encBits) encUnary).prod ((unary_pow j.val).comp hn))).prod hn)
    have hiter : ComputableTidilyInPolyTime
        (fun x => (tableStep x)^[(a x).1 ^ k] []) enc encBits := by
      apply iterateWithInput_of_bounded_growth hcount (const []) hstep
      refine ⟨hcount.polyBounded, ?_⟩
      intro x state
      simp [tableStep, encBits]
    exact bitsGetDWithInput hiter
      (valuesIndex_poly ha.fst' (fun j => termValue_poly (ts j) ha.fst' hσ)) false

/-- Every fixed raw formula's bounded evaluator has a native polynomial-time implementation.
The free variables may be any fixed family of polynomial-time numerical inputs. Formation is
needed for semantic correctness, and is not needed for the cost bound. -/
@[fun_prop]
theorem computableInPolyTime_eval {Γ : List ℕ} {α : Type w}
    (φ : RawFormula (Ordered.language L) Γ α) {γ : Type} {enc : γ ↪ List Bool}
    {a : γ → EncodedStructure} {tables : γ → List (List Bool)} {σ : γ → α → ℕ}
    (ha : ComputableInPolyTime a enc encStructure)
    (ht : ComputableInPolyTime tables enc (encList encBits))
    (hσ : ∀ x, ComputableInPolyTime (fun y => σ y x) enc encUnary) :
    ComputableInPolyTime (fun y => eval v φ (a y) (tables y) (σ y)) enc encBool :=
  .of_tidy (eval_poly v φ ha.tidy ht.tidy (fun x => (hσ x).tidy))

/-- Decide a fixed sentence, rejecting malformed relation tables and universes smaller than two. -/
@[expose] def modelChecker (φ : RawFormula (Ordered.language L) [] Empty)
    (a : EncodedStructure) : Bool :=
  v.checkShape a && (decide (2 ≤ a.1) && eval v φ a [] Empty.elim)

/-- The complete decision procedure, including its input checks, is native polynomial time. -/
@[fun_prop] theorem computableInPolyTime_modelChecker
    (φ : RawFormula (Ordered.language L) [] Empty) :
    ComputableInPolyTime (modelChecker v φ) encStructure encBool := by
  apply ComputableInPolyTime.bool_and' v.computableInPolyTime_checkShape
  apply ComputableInPolyTime.bool_and'
  · exact .of_tidy (unary_le' (const 2) (fst encUnary (encList encBits)))
  · exact computableInPolyTime_eval v φ .id' (.const []) (fun x => x.elim)

end Cslib.Logic.FO.LFP.ModelChecker

namespace Cslib.Logic.FO.Ordered

open Cslib.Complexity LFP.ModelChecker

/-- Every ordered FO(LFP)-definable query is in the native class `P`, using the existing
source-only structure encoding. The formula is uniform over all canonical finite structures. -/
theorem LFPDefinable.encodedLanguage_mem_P {L : Language} [L.IsRelational]
    {K : Query L} (hK : LFPDefinable K) (v : Vocabulary L) :
    K.encodedLanguage v ∈ P encStructure := by
  obtain ⟨φ, hφ⟩ := hK
  refine ⟨modelChecker v φ.val, computableInPolyTime_modelChecker v φ.val, fun a => ?_⟩
  simp only [Query.encodedLanguage, Set.mem_ofPred_eq, modelChecker, Bool.and_eq_true,
    Vocabulary.checkShape_eq_true_iff, decide_eq_true_eq]
  have hrels : @relations [] a.1 [] = @Operator.RelEnv.empty (Fin a.1) := by
    funext k r
    exact nomatch r
  have hempty : (fun x : Empty => (Empty.elim x : Fin a.1).val) = Empty.elim :=
    Subsingleton.elim _ _
  constructor
  · rintro ⟨hshape, hn, hmem⟩
    refine ⟨hshape, hn, ?_⟩
    have hreal := (hφ (decoded v a hn)).mp hmem
    have heval := eval_eq_true_iff v hn φ.val φ.property [] (Empty.elim : Empty → Fin a.1)
    rw [hrels, hempty] at heval
    exact heval.mpr hreal
  · rintro ⟨hshape, hn, heval⟩
    refine ⟨hshape, hn, (hφ (decoded v a hn)).mpr ?_⟩
    have hreal := eval_eq_true_iff v hn φ.val φ.property [] (Empty.elim : Empty → Fin a.1)
    rw [hrels, hempty] at hreal
    exact hreal.mp heval

end Cslib.Logic.FO.Ordered
