/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Optimality
public import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Size
public import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Blossom
public import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Optimality

/-!
# One improvement through blossom contraction

The whole algorithm of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6,
Algorithm 1 (printed p. 10) and Section 5.3 (printed pp. 11–13), organized to return
one improvement. Each call performs one fresh search and at most one recursive child call.
A child improvement is lifted and returned immediately. A child optimum transfers through
Lemma 42; the preparation has the original defect count. This arrangement avoids recursively
optimizing a contracted child before restarting a local optimization loop.

The explicit depth parameter makes the function total even on malformed input. For an edge
instance with even delta-matroid constraints and valid labels, a depth exceeding
`contractionMeasure` suffices. This module proves semantic correctness and termination;
encoded native resource bounds belong to the executable implementation.

The recursion organization and its bookkeeping are original; the search, preparation,
contraction and lifting are the existing constructions from the cited source.
-/

public section

namespace Cslib.Logic.PL.CSP.Solver

open Table

/-- Return one valid labeling with exactly two fewer defects, or certify optimality by
returning `none`. The latter interpretation requires the depth and model hypotheses of
`improve_spec`; depth exhaustion on arbitrary raw inputs simply returns `none`. -/
@[expose] def improve : (depth : ℕ) → (F : CSP Table ℕ) →
    OccurrenceLabeling F Bool → Option (OccurrenceLabeling F Bool)
  | 0, _, _ => none
  | depth + 1, _F, f =>
    match Forest.search sem f with
    | .exhausted _ => none
    | .augment m => some (m.walk.flip f)
    | .blossom m => do
      let b ← m.blossomData
      let prepared := b.prepare.flip f
      let comparison ← improve depth (Blossom.contract prepared (Blossom.internal b.cycle))
        (Blossom.reference prepared (Blossom.internal b.cycle))
      Blossom.liftComparison prepared b.cycle comparison

/-- An adequately funded call either certifies optimality or removes exactly two defects.
All contraction and lifting obligations are derived internally from the fresh search. -/
theorem improve_spec (depth : ℕ) (F : CSP Table ℕ) (f : OccurrenceLabeling F Bool)
    (hd : F.contractionMeasure < depth) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F) :
    match improve depth F f with
    | none => IsOptimalLabeling sem f
    | some g => ValidLabeling sem g ∧ (defects g).card + 2 = (defects f).card := by
  induction depth generalizing F with
  | zero => omega
  | succ depth ih =>
    cases hs : Forest.search sem f with
    | exhausted es =>
      simpa only [improve, hs] using
        Forest.search_exhausted_isOptimalLabeling sem f hF hf hM hs
    | augment m =>
      simpa only [improve, hs] using (Forest.search_augment_correct sem f hF hf hM hs).2
    | blossom m =>
      obtain ⟨b, hb, hblossom, hprepared, hcount⟩ :=
        Forest.search_blossom_correct sem f hF hf hM hs
      let prepared := b.prepare.flip f
      let vs := Blossom.internal b.cycle
      have hne := Blossom.touched_ne_nil b.cycle hblossom.steps_ne_nil
      have hdec := Blossom.contractionMeasure_contract_lt hF hblossom
      change (Blossom.contract prepared vs).contractionMeasure < F.contractionMeasure at hdec
      have hchild := ih (Blossom.contract prepared vs) (Blossom.reference prepared vs)
        (by omega) (Blossom.edge_contract hF prepared vs)
        (Blossom.valid_reference hprepared vs hne)
        (Blossom.even_contract hprepared hM vs hne)
      cases hc : improve depth (Blossom.contract prepared vs)
          (Blossom.reference prepared vs) with
      | none =>
        rw [hc] at hchild
        have ho := Blossom.isOptimal_of_reference hF hblossom hprepared hM hchild
        have horig : IsOptimalLabeling sem f :=
          ⟨hf, fun g hg => hcount ▸ ho.2 g hg⟩
        dsimp only [prepared, vs] at hc
        simpa only [improve, hs, hb, Option.bind_eq_bind, Option.bind_some,
          hc, Option.bind_none] using horig
      | some g =>
        rw [hc] at hchild
        have hlt : (defects g).card < (defects (Blossom.reference prepared vs)).card := by
          have := hchild.2
          omega
        obtain ⟨result, hr, hv, hn⟩ := Blossom.liftComparison_spec hF hblossom hprepared hM
          g hchild.1 hlt
        dsimp only [prepared, vs] at hc
        simpa only [improve, hs, hb, Option.bind_eq_bind, Option.bind_some,
          hc, hr, hcount] using And.intro hv hn

/-- Sufficient contraction budgets give exactly the same deterministic improvement, including
its outside changes. Depth affects only malformed or inadequately funded executions. -/
theorem improve_depth_eq (F : CSP Table ℕ) (f : OccurrenceLabeling F Bool)
    (hF : EdgeInstance F) (hf : ValidLabeling sem f)
    (hM : EdgeInstance.EvenConstraints sem F) (a b : ℕ)
    (ha : F.contractionMeasure < a) (hb : F.contractionMeasure < b) :
    improve a F f = improve b F f := by
  induction hm : F.contractionMeasure using Nat.strong_induction_on generalizing F a b with
  | ind measure ih =>
    cases a with
    | zero => omega
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        cases hs : Forest.search sem f with
        | exhausted log => simp only [improve, hs]
        | augment m => simp only [improve, hs]
        | blossom m =>
          obtain ⟨data, hd, hc, hv, _⟩ := Forest.search_blossom_correct sem f hF hf hM hs
          let prepared := data.prepare.flip f
          let vs := Blossom.internal data.cycle
          have hne := Blossom.touched_ne_nil data.cycle hc.steps_ne_nil
          have hlt := Blossom.contractionMeasure_contract_lt hF hc
          change (Blossom.contract prepared vs).contractionMeasure < F.contractionMeasure at hlt
          have he := ih _ (by omega) (Blossom.contract prepared vs)
            (Blossom.reference prepared vs) (Blossom.edge_contract hF prepared vs)
            (Blossom.valid_reference hv vs hne) (Blossom.even_contract hv hM vs hne)
            a b (by omega) (by omega) rfl
          simp only [improve, hs, hd, Option.bind_eq_bind, Option.bind_some]
          exact congrArg (fun r => r.bind (Blossom.liftComparison prepared data.cycle)) he

end Cslib.Logic.PL.CSP.Solver
