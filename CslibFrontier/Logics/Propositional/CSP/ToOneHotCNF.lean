/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.ExactlyOne
public import CslibFrontier.Logics.Propositional.CNF.ModelCount.Declared
public import CslibFrontier.Logics.Propositional.CNF.ModelCount
public import CslibFrontier.Logics.Propositional.CSP
import CslibFrontier.Foundations.Data.Nat.Div
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD

/-!
# One-hot CNF compilation for fixed-arity finite-domain CSPs

Given a finite-domain CSP instance `F : CSP Rel ℕ` over `Fin q` on declared variables `0, …, N - 1`,
`CSP.toOneHotCNF q N F sem` introduces `q` Boolean variables `v * q + a` (`a < q`) for each source
variable `v < N`:

* `CNF.exactlyOne` constraints enforce a unique value `a < q` for every `v < N`;
* for each constraint `(R, vs) ∈ F` and each disallowed tuple `ts : List (Fin q)` of length
  `vs.length` (`sem R ts = false`), the clause `(vs.zip ts).map (fun (v, a) => (v * q + a, false))`
  forbids that local assignment.

For fixed domain size `q ≥ 1` and arity bound `k`, the compiled formula uses `q * N` variables
(linear in `N`), clauses of width at most `max q (max k 2)`, and preserves exact solution counts
with an explicit assignment bijection (`CSP.toOneHotCNFEquiv`).

## Main definitions

* `Cslib.Logic.PL.CSP.finTuples`: all `Fin q`-valued lists of a given length.
* `Cslib.Logic.PL.Constraint.toOneHotCNF`, `Cslib.Logic.PL.Constraint.toOneHotCNFBounded`:
  per-constraint one-hot forbidden-tuple clauses and their width-guarded variant.
* `Cslib.Logic.PL.CSP.toOneHotCNF`, `Cslib.Logic.PL.CSP.toOneHotCNFBounded`,
  `Cslib.Logic.PL.CSP.toOneHotDeclaredCNF`: one-hot CNF compilation on `N * q` Boolean variables
  and its width-guarded declared-variable variants.
* `Cslib.Logic.PL.CSP.toOneHotCNFEquiv`: explicit bijection between satisfying assignments on
  `Finset.range (N * q)` and solutions of `F` on `Finset.range N`.

## Main results

* `Cslib.Logic.PL.CSP.length_clause_toOneHotCNF_le`,
  `Cslib.Logic.PL.CSP.length_clause_toOneHotCNFBounded_le`,
  `Cslib.Logic.PL.CSP.validDeclaredInput_toOneHotCNFBounded`: clause width at most
  `max q (max k 2)` and declared-variable bounds.
* `Cslib.Logic.PL.CSP.vars_toOneHotCNF_toFinset`: exact occurring variable set `range (N * q)`
  for `0 < q`.
* `Cslib.Logic.PL.CSP.eval_toOneHotCNF`, `Cslib.Logic.PL.CSP.modelCountOn_toOneHotCNF`,
  `Cslib.Logic.PL.CSP.modelCount_toOneHotCNF`,
  `Cslib.Logic.PL.CSP.modelCountOn_toOneHotDeclaredCNF`: exact evaluation and model-count
  preservation.

## References

* [M. Cygan et al., *Parameterized Algorithms*][CyganEtAl2015]
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Rel : Type*}

/-- All lists of length `r` over `Fin q`. -/
@[expose] def finTuples (q : ℕ) : ℕ → List (List (Fin q))
  | 0 => [[]]
  | r + 1 => (finTuples q r).flatMap fun ts => (List.finRange q).map fun a => a :: ts

/-- Membership in `finTuples q r` characterizes lists of length `r`. -/
@[simp]
theorem mem_finTuples {q r : ℕ} {ts : List (Fin q)} :
    ts ∈ finTuples q r ↔ ts.length = r := by
  induction r generalizing ts with
  | zero =>
    simp [finTuples, List.length_eq_zero_iff]
  | succ r ih =>
    cases ts with
    | nil => simp [finTuples]
    | cons a ts =>
      simp only [finTuples, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and,
        List.cons.injEq, List.length_cons, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨ts', hts', a', -, rfl, rfl⟩
        exact ih.mp hts'
      · intro hlen
        exact ⟨ts, ih.mpr hlen, a, rfl, rfl⟩

/-- `finTuples q r` has length `q ^ r`. -/
theorem length_finTuples (q r : ℕ) : (finTuples q r).length = q ^ r := by
  induction r with
  | zero => simp [finTuples]
  | succ r ih =>
    simp [finTuples, List.length_flatMap, ih, Nat.pow_succ', mul_comm]

/-- Clause forbidding local tuple `ts` on scope `vs` in the one-hot variable numbering. -/
@[expose] def forbidOneHotClause (q : ℕ) (vs : List ℕ) (ts : List (Fin q)) : Clause ℕ :=
  (vs.zip ts).map fun (v, a) => (v * q + a.1, false)

@[simp]
theorem length_forbidOneHotClause (q : ℕ) (vs : List ℕ) (ts : List (Fin q)) :
    (forbidOneHotClause q vs ts).length = min vs.length ts.length := by
  simp [forbidOneHotClause]

end Cslib.Logic.PL.CSP

namespace Cslib.Logic.PL.Constraint

variable {Rel : Type*}

/-- One-hot forbidden-tuple clauses for a single constraint `c` over `Fin q`. -/
@[expose] def toOneHotCNF (q : ℕ) (sem : Rel → List (Fin q) → Bool) (c : Constraint Rel ℕ) :
    CNF ℕ :=
  ((CSP.finTuples q c.2.length).filter fun ts => !sem c.1 ts).map (CSP.forbidOneHotClause q c.2)

/-- Width-guarded one-hot forbidden-tuple clauses: emits `toOneHotCNF` when `c.2.length ≤ k`, and
`[]` otherwise. -/
@[expose] def toOneHotCNFBounded (q k : ℕ) (sem : Rel → List (Fin q) → Bool)
    (c : Constraint Rel ℕ) : CNF ℕ :=
  if c.2.length ≤ k then toOneHotCNF q sem c else []

theorem toOneHotCNFBounded_eq_toOneHotCNF {q k : ℕ} {sem : Rel → List (Fin q) → Bool}
    {c : Constraint Rel ℕ} (hc : c.2.length ≤ k) :
    toOneHotCNFBounded q k sem c = toOneHotCNF q sem c := by
  simp [toOneHotCNFBounded, hc]

theorem length_clause_toOneHotCNFBounded_le {q k : ℕ} {sem : Rel → List (Fin q) → Bool}
    {c : Constraint Rel ℕ} {cl : Clause ℕ} (hcl : cl ∈ toOneHotCNFBounded q k sem c) :
    cl.length ≤ k := by
  dsimp only [toOneHotCNFBounded] at hcl
  split_ifs at hcl with hc
  · obtain ⟨ts, _, rfl⟩ := List.mem_map.mp hcl
    rw [CSP.length_forbidOneHotClause]
    exact (Nat.min_le_left _ _).trans hc
  · cases hcl

end Cslib.Logic.PL.Constraint

namespace Cslib.Logic.PL.CSP

variable {Rel : Type*}

/-- **One-hot CNF compilation** of a finite-domain CSP `F : CSP Rel ℕ` over `Fin q` on
declared variables `0, …, N - 1`. Uses Boolean variables `v * q + a` (`v < N`, `a < q`). -/
@[expose] def toOneHotCNF (q N : ℕ) (F : CSP Rel ℕ) (sem : Rel → List (Fin q) → Bool) : CNF ℕ :=
  ((List.range N).flatMap fun v => CNF.exactlyOne ((List.range q).map fun a => v * q + a)) ++
    F.flatMap (Constraint.toOneHotCNF q sem)

/-- If every constraint scope has length at most `k`, every clause of `toOneHotCNF q N F sem`
has width at most `max q (max k 2)`. -/
theorem length_clause_toOneHotCNF_le {q N k : ℕ} {F : CSP Rel ℕ}
    (sem : Rel → List (Fin q) → Bool) (hF : ∀ c ∈ F, c.2.length ≤ k)
    {cl : Clause ℕ} (hcl : cl ∈ toOneHotCNF q N F sem) :
    cl.length ≤ max q (max k 2) := by
  simp only [toOneHotCNF, Constraint.toOneHotCNF, List.mem_append, List.mem_flatMap,
    List.mem_map, List.mem_filter] at hcl
  rcases hcl with ⟨v, _, hc⟩ | ⟨c, hcF, ts, -, rfl⟩
  · rw [CNF.exactlyOne, List.mem_append] at hc
    rcases hc with hc | hc
    · rw [CNF.atLeastOne, List.mem_singleton] at hc
      subst hc
      simp
    · simp only [CNF.atMostOne, List.mem_flatMap, List.mem_map] at hc
      obtain ⟨_, _, _, _, rfl⟩ := hc
      exact (le_max_right k 2).trans (le_max_right q (max k 2))
  · rw [length_forbidOneHotClause]
    exact (Nat.min_le_left _ _).trans
      ((hF c hcF).trans ((le_max_left k 2).trans (le_max_right q (max k 2))))

private theorem oneHot_inj {v₁ v₂ q a₁ a₂ : ℕ} (ha₁ : a₁ < q) (ha₂ : a₂ < q)
    (heq : v₁ * q + a₁ = v₂ * q + a₂) : v₁ = v₂ ∧ a₁ = a₂ := by
  refine ⟨by rw [← Nat.mul_add_div_of_lt v₁ ha₁, heq, Nat.mul_add_div_of_lt v₂ ha₂], ?_⟩
  have hm := congrArg (· % q) heq
  simpa only [Nat.mul_comm _ q, Nat.mul_add_mod, Nat.mod_eq_of_lt ha₁,
    Nat.mod_eq_of_lt ha₂] using hm

/-- When all variables of `F` are `< N`, every variable of `toOneHotCNF q N F sem` is `< N * q`. -/
theorem vars_toOneHotCNF_subset_range {q N : ℕ} {F : CSP Rel ℕ}
    (sem : Rel → List (Fin q) → Bool) (hvars : ∀ v ∈ F.vars, v < N) {x : ℕ}
    (hx : x ∈ (toOneHotCNF q N F sem).vars) : x < N * q := by
  simp only [toOneHotCNF, Constraint.toOneHotCNF, CNF.vars, List.flatten_append, List.map_append,
    List.mem_append, List.mem_map, List.mem_flatten, List.mem_flatMap, List.mem_filter,
    List.mem_range] at hx
  rcases hx with ⟨l, ⟨c, ⟨v, hv, hc⟩, hl⟩, rfl⟩ |
      ⟨l, ⟨c, ⟨d, hd, ts, -, rfl⟩, hl⟩, rfl⟩
  · have hmem := CNF.fst_mem_of_mem_exactlyOne hc hl
    rw [List.mem_map] at hmem
    obtain ⟨a, ha, heqa⟩ := hmem
    have ha' := List.mem_range.mp ha
    rw [← heqa]
    exact (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt ha')).mp
      ((Nat.mul_add_div_of_lt v ha').trans_lt hv)
  · rw [forbidOneHotClause, List.mem_map] at hl
    obtain ⟨⟨v, a⟩, hva, rfl⟩ := hl
    have hv : v < N := hvars v (List.mem_flatMap.mpr ⟨d, hd, (List.of_mem_zip hva).1⟩)
    exact (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt a.isLt)).mp
      ((Nat.mul_add_div_fin v a).trans_lt hv)

/-- When `0 < q` and all variables of `F` are `< N`, the occurring variables of `toOneHotCNF` are
precisely `Finset.range (N * q)`. -/
@[simp]
theorem vars_toOneHotCNF_toFinset {q N : ℕ} (hq : 0 < q) {F : CSP Rel ℕ}
    (sem : Rel → List (Fin q) → Bool) (hvars : ∀ v ∈ F.vars, v < N) :
    (toOneHotCNF q N F sem).vars.toFinset = Finset.range (N * q) := by
  ext x
  rw [List.mem_toFinset, Finset.mem_range]
  refine ⟨vars_toOneHotCNF_subset_range sem hvars, fun hx => ?_⟩
  have hdiv : x / q < N := (Nat.div_lt_iff_lt_mul hq).mpr hx
  have hmod : x % q < q := Nat.mod_lt x hq
  have hxq : (x / q) * q + x % q = x := by
    rw [mul_comm, Nat.div_add_mod]
  rw [← hxq]
  simp only [toOneHotCNF, CNF.vars, List.flatten_append, List.map_append, List.mem_append,
    List.mem_map, List.mem_flatten, List.mem_flatMap, List.mem_range]
  refine Or.inl ⟨((x / q) * q + x % q, true),
    ⟨((List.range q).map fun a => (x / q) * q + a).map (·, true), ?_, ?_⟩, rfl⟩
  · refine ⟨x / q, hdiv, ?_⟩
    rw [CNF.exactlyOne, List.mem_append]
    exact Or.inl (by simp [CNF.atLeastOne])
  · exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨x % q, List.mem_range.mpr hmod, rfl⟩, rfl⟩

/-- Evaluation of `forbidOneHotClause`: when `σ` encodes `τ : ℕ → Fin q` via one-hot bits on
`v * q + a`, `forbidOneHotClause q vs ts` fails iff `vs.map τ = ts`. -/
private theorem eval_forbidOneHotClause_eq_false_iff {q : ℕ} (vs : List ℕ) (ts : List (Fin q))
    (hlen : ts.length = vs.length) (σ : ℕ → Bool) (τ : ℕ → Fin q)
    (hrep : ∀ v ∈ vs, ∀ a : Fin q, σ (v * q + a.1) = decide (τ v = a)) :
    (forbidOneHotClause q vs ts).eval σ = false ↔ vs.map τ = ts := by
  induction vs generalizing ts with
  | nil =>
    cases ts with
    | nil => simp [forbidOneHotClause]
    | cons _ _ => simp at hlen
  | cons v vs ih =>
    cases ts with
    | nil => simp at hlen
    | cons a ts =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hv := hrep v (List.mem_cons_self ..) a
      have ih' := ih ts hlen (fun u hu b => hrep u (List.mem_cons_of_mem _ hu) b)
      have hdef : forbidOneHotClause q (v :: vs) (a :: ts) =
          (v * q + a.1, false) :: forbidOneHotClause q vs ts := rfl
      rw [hdef, Clause.eval_cons, Bool.or_eq_false_iff, ih']
      simp [Literal.eval, hv]

/-- **Evaluation correctness of `toOneHotCNF`**: for `0 < q`, `σ` satisfies `toOneHotCNF q N F sem`
iff every `v < N` has a unique true one-hot bit `a < q` and the induced assignment satisfies `F`. -/
theorem eval_toOneHotCNF {q N : ℕ} {F : CSP Rel ℕ} (sem : Rel → List (Fin q) → Bool)
    (σ : ℕ → Bool) :
    (toOneHotCNF q N F sem).eval σ = true ↔
      (∀ v < N, (∃ a < q, σ (v * q + a) = true) ∧
        ∀ a₁ < q, ∀ a₂ < q, σ (v * q + a₁) = true → σ (v * q + a₂) = true → a₁ = a₂) ∧
      (∀ c ∈ F, ∀ ts : List (Fin q), ts.length = c.2.length → sem c.1 ts = false →
        (forbidOneHotClause q c.2 ts).eval σ = true) := by
  rw [toOneHotCNF, CNF.eval_append, Bool.and_eq_true, CNF.eval_flatMap_eq_true_iff,
    CNF.eval_flatMap_eq_true_iff]
  refine and_congr ?_ ?_
  · simp only [List.mem_range]
    refine forall₂_congr fun v _ => ?_
    rw [CNF.eval_exactlyOne]
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨⟨_, ⟨a, ha, rfl⟩, hsa⟩, huniq⟩
      refine ⟨⟨a, ha, hsa⟩, fun a₁ ha₁ a₂ ha₂ h1 h2 => ?_⟩
      have heq := huniq (v * q + a₁) ⟨a₁, ha₁, rfl⟩ (v * q + a₂) ⟨a₂, ha₂, rfl⟩ h1 h2
      exact (oneHot_inj ha₁ ha₂ heq).2
    · rintro ⟨⟨a, ha, hsa⟩, huniq⟩
      refine ⟨⟨v * q + a, ⟨a, ha, rfl⟩, hsa⟩, ?_⟩
      rintro _ ⟨a₁, ha₁, rfl⟩ _ ⟨a₂, ha₂, rfl⟩ h1 h2
      rw [huniq a₁ ha₁ a₂ ha₂ h1 h2]
  · simp only [Constraint.toOneHotCNF, CNF.eval_map_eq_true_iff, List.mem_filter, Bool.not_eq_true',
      mem_finTuples, and_imp]

private theorem eval_toOneHotEncode {q N : ℕ} (hq : 0 < q) (F : CSP Rel ℕ)
    (sem : Rel → List (Fin q) → Bool) (hvars : ∀ v ∈ F.vars, v < N)
    (τ : Finset.range N → Fin q)
    (hτ : F.eval sem (fun v => if hv : v ∈ Finset.range N then τ ⟨v, hv⟩ else ⟨0, hq⟩) = true) :
    let τExt (v : ℕ) : Fin q := if hv : v ∈ Finset.range N then τ ⟨v, hv⟩ else ⟨0, hq⟩
    (toOneHotCNF q N F sem).eval
      (fun x => if _ : x ∈ Finset.range (N * q) then
        decide (x % q = (τExt (x / q)).1) else false) = true := by
  let τExt (v : ℕ) : Fin q := if hv : v ∈ Finset.range N then τ ⟨v, hv⟩ else ⟨0, hq⟩
  have hrep : ∀ v < N, ∀ a : Fin q,
      (if hx : v * q + a.1 ∈ Finset.range (N * q)
        then decide ((v * q + a.1) % q = (τExt ((v * q + a.1) / q)).1) else false) =
        decide (τExt v = a) := by
    intro v hv a
    have hdiv := Nat.mul_add_div_fin v a
    have hlt : v * q + a.1 < N * q :=
      (Nat.div_lt_iff_lt_mul hq).mp (hdiv.trans_lt hv)
    have hmod : (v * q + a.1) % q = a.1 := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt a.isLt]
    simp only [Finset.mem_range.mpr hlt, ↓reduceDIte, hdiv, hmod, Fin.ext_iff]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    exact eq_comm
  rw [eval_toOneHotCNF]
  refine ⟨fun v hv => ?_, fun c hc ts hlen hfalse => ?_⟩
  · refine ⟨⟨(τExt v).1, (τExt v).isLt, ?_⟩, fun a₁ ha₁ a₂ ha₂ h1 h2 => ?_⟩
    · have h := hrep v hv (τExt v)
      simp only [decide_true] at h
      exact h
    · have ha1 := hrep v hv ⟨a₁, ha₁⟩
      have ha2 := hrep v hv ⟨a₂, ha₂⟩
      dsimp only [τExt] at ha1 ha2 h1 h2
      rw [ha1, decide_eq_true_eq] at h1
      rw [ha2, decide_eq_true_eq] at h2
      exact congrArg Fin.val (h1.symm.trans h2)
  · by_contra hcs
    have hcl : (forbidOneHotClause q c.2 ts).eval
        (fun x => if hx : x ∈ Finset.range (N * q)
          then decide (x % q = (τExt (x / q)).1) else false) = false :=
      Bool.eq_false_iff.mpr hcs
    have hf := (eval_forbidOneHotClause_eq_false_iff c.2 ts hlen _ τExt
      fun v hv a => hrep v (hvars v (List.mem_flatMap.mpr ⟨c, hc, hv⟩)) a).mp hcl
    have hsat := (List.all_eq_true.mp hτ) c hc
    rw [Constraint.eval, hf, hfalse] at hsat
    exact Bool.false_ne_true hsat

/-- **Explicit assignment bijection for `toOneHotCNF`**: when `0 < q` and all variables of `F`
are `< N`, declared solutions of `F` on `Finset.range N` biject with satisfying assignments of
`toOneHotCNF q N F sem` on `Finset.range (N * q)`. -/
noncomputable def toOneHotCNFEquiv {q N : ℕ} (hq : 0 < q) (F : CSP Rel ℕ)
    (sem : Rel → List (Fin q) → Bool) (hvars : ∀ v ∈ F.vars, v < N) :
    letI : Inhabited (Fin q) := ⟨⟨0, hq⟩⟩
    {τ : Finset.range N → Fin q //
      F.eval sem (fun v => if hv : v ∈ Finset.range N then τ ⟨v, hv⟩ else default) = true} ≃
      {σ : Finset.range (N * q) → Bool //
        (toOneHotCNF q N F sem).eval
          (fun x => if hx : x ∈ Finset.range (N * q) then σ ⟨x, hx⟩ else false) = true} where
  toFun τ :=
    letI : Inhabited (Fin q) := ⟨⟨0, hq⟩⟩
    let τExt (v : ℕ) : Fin q := if hv : v ∈ Finset.range N then τ.1 ⟨v, hv⟩ else default
    ⟨fun x => decide (x.1 % q = (τExt (x.1 / q)).1),
      eval_toOneHotEncode hq F sem hvars τ.1 τ.2⟩
  invFun σ :=
    letI : Inhabited (Fin q) := ⟨⟨0, hq⟩⟩
    let ext (x : ℕ) : Bool := if hx : x ∈ Finset.range (N * q) then σ.1 ⟨x, hx⟩ else false
    ⟨fun v =>
      let hex := ((eval_toOneHotCNF sem ext).mp σ.2).1 v.1 (Finset.mem_range.mp v.2)
      ⟨hex.1.choose, hex.1.choose_spec.1⟩, by
      rw [eval, List.all_eq_true]
      intro c hc
      let τExt (v : ℕ) : Fin q :=
        if hv : v ∈ Finset.range N then
          let hex := ((eval_toOneHotCNF sem ext).mp σ.2).1 v (Finset.mem_range.mp hv)
          ⟨hex.1.choose, hex.1.choose_spec.1⟩
        else default
      change Constraint.eval sem τExt c = true
      have hrep : ∀ v ∈ c.2, ∀ a : Fin q, ext (v * q + a.1) = decide (τExt v = a) := by
        intro v hv a
        have hvN := hvars v (List.mem_flatMap.mpr ⟨c, hc, hv⟩)
        have hmv : v ∈ Finset.range N := Finset.mem_range.mpr hvN
        have huniq := ((eval_toOneHotCNF sem ext).mp σ.2).1 v hvN
        have hspec := huniq.1.choose_spec
        dsimp only [τExt]
        simp only [hmv, ↓reduceDIte]
        rw [Bool.eq_iff_iff, decide_eq_true_eq, Fin.ext_iff]
        refine ⟨fun ha => (huniq.2 a.1 a.isLt huniq.1.choose hspec.1 ha hspec.2).symm,
          fun heq => by rw [← heq]; exact hspec.2⟩
      by_contra hcs
      have hfalse : sem c.1 (c.2.map τExt) = false := Bool.eq_false_iff.mpr hcs
      have hcl := ((eval_toOneHotCNF sem ext).mp σ.2).2 c hc (c.2.map τExt)
        (List.length_map _) hfalse
      have hclF := (eval_forbidOneHotClause_eq_false_iff c.2 (c.2.map τExt)
        (List.length_map _) ext τExt hrep).mpr rfl
      rw [hcl] at hclF
      exact Bool.noConfusion hclF⟩
  left_inv τ := by
    let : Inhabited (Fin q) := ⟨⟨0, hq⟩⟩
    obtain ⟨τ, hτ⟩ := τ
    ext v
    dsimp only
    have hvN := Finset.mem_range.mp v.2
    have hdiv := Nat.mul_add_div_fin v.1 (τ v)
    have hlt : v.1 * q + (τ v).1 < N * q :=
      (Nat.div_lt_iff_lt_mul hq).mp (hdiv.trans_lt hvN)
    have hmod : (v.1 * q + (τ v).1) % q = (τ v).1 := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (τ v).isLt]
    let τExt (u : ℕ) : Fin q := if hu : u ∈ Finset.range N then τ ⟨u, hu⟩ else default
    have hσ0 := eval_toOneHotEncode hq F sem hvars τ hτ
    have huniq := ((eval_toOneHotCNF sem _).mp hσ0).1 v.1 hvN
    have hspec := huniq.1.choose_spec
    have heq : (if hx : v.1 * q + (τ v).1 ∈ Finset.range (N * q)
        then decide ((v.1 * q + (τ v).1) % q = (τExt ((v.1 * q + (τ v).1) / q)).1)
        else false) = true := by
      simp [τExt, Finset.mem_range.mpr hlt, hdiv, hmod, hvN]
    exact huniq.2 _ hspec.1 (τ v).1 (τ v).isLt hspec.2 heq
  right_inv σ := by
    obtain ⟨σ, hσ⟩ := σ
    ext x
    dsimp only
    have hx := Finset.mem_range.mp x.2
    have hvN : x.1 / q < N := (Nat.div_lt_iff_lt_mul hq).mpr hx
    have hmod : x.1 % q < q := Nat.mod_lt x.1 hq
    have hmv : x.1 / q ∈ Finset.range N := Finset.mem_range.mpr hvN
    let ext (y : ℕ) : Bool := if hy : y ∈ Finset.range (N * q) then σ ⟨y, hy⟩ else false
    have huniq := ((eval_toOneHotCNF sem ext).mp hσ).1 (x.1 / q) hvN
    have hspec := huniq.1.choose_spec
    simp only [hmv, ↓reduceDIte]
    change decide (x.1 % q = huniq.1.choose) = σ x
    have hmul : (x.1 / q) * q + x.1 % q = x.1 := by rw [mul_comm, Nat.div_add_mod]
    by_cases hval : σ x = true
    · have hex : ext ((x.1 / q) * q + x.1 % q) = true := by
        dsimp only [ext]
        rw [hmul]
        simp only [x.2, ↓reduceDIte]
        exact hval
      have heq : x.1 % q = huniq.1.choose := huniq.2 (x.1 % q) hmod _ hspec.1 hex hspec.2
      simp [hval, heq]
    · have hne : x.1 % q ≠ huniq.1.choose := by
        intro heq
        apply hval
        have heq_x : (x.1 / q) * q + huniq.1.choose = x.1 := by rw [← heq, hmul]
        simpa only [ext, heq_x, x.2, ↓reduceDIte] using hspec.2
      have hfalse : σ x = false := Bool.eq_false_iff.mpr hval
      simp [hfalse, hne]

/-- **`toOneHotCNF` preserves exact declared-variable model counts.** -/
theorem modelCountOn_toOneHotCNF {q N : ℕ} (hq : 0 < q) (F : CSP Rel ℕ)
    (sem : Rel → List (Fin q) → Bool) (hvars : ∀ v ∈ F.vars, v < N) :
    letI : Inhabited (Fin q) := ⟨⟨0, hq⟩⟩
    (toOneHotCNF q N F sem).modelCountOn (Finset.range (N * q)) =
      F.modelCountOn sem (Finset.range N) := by
  classical
  let : Inhabited (Fin q) := ⟨⟨0, hq⟩⟩
  rw [CNF.modelCountOn, modelCountOn, ← Fintype.card_coe, ← Fintype.card_coe]
  symm
  exact Fintype.card_congr
    ((Equiv.subtypeEquivRight
      (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])).trans
      ((toOneHotCNFEquiv hq F sem hvars).trans
        (Equiv.subtypeEquivRight
          (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]))))

/-- **`toOneHotCNF` preserves exact occurring-variable model counts when all `v < N` appear**. -/
theorem modelCount_toOneHotCNF {q N : ℕ} (hq : 0 < q) (F : CSP Rel ℕ)
    (sem : Rel → List (Fin q) → Bool) (hvars : ∀ v ∈ F.vars, v < N) :
    letI : Inhabited (Fin q) := ⟨⟨0, hq⟩⟩
    (toOneHotCNF q N F sem).modelCount = F.modelCountOn sem (Finset.range N) := by
  let : Inhabited (Fin q) := ⟨⟨0, hq⟩⟩
  rw [← CNF.modelCountOn_vars, vars_toOneHotCNF_toFinset hq sem hvars,
    modelCountOn_toOneHotCNF hq F sem hvars]

/-! ### Width-guarded and declared-variable one-hot CNF compilation -/

/-- Width-guarded one-hot CNF compilation of a finite-domain CSP `F : CSP Rel ℕ` over `Fin q` on
declared variables `0, …, N - 1`. -/
@[expose] def toOneHotCNFBounded (q k N : ℕ) (F : CSP Rel ℕ)
    (sem : Rel → List (Fin q) → Bool) : CNF ℕ :=
  ((List.range N).flatMap fun v => CNF.exactlyOne ((List.range q).map fun a => v * q + a)) ++
    F.flatMap (Constraint.toOneHotCNFBounded q k sem)

/-- Declared-variable one-hot CNF compilation `(N * q, toOneHotCNFBounded q k N F sem)`. -/
@[expose] def toOneHotDeclaredCNF (q k : ℕ) (sem : Rel → List (Fin q) → Bool)
    (x : ℕ × CSP Rel ℕ) : ℕ × CNF ℕ :=
  (x.1 * q, toOneHotCNFBounded q k x.1 x.2 sem)

theorem toOneHotCNFBounded_eq_toOneHotCNF {q k N : ℕ} {F : CSP Rel ℕ}
    (sem : Rel → List (Fin q) → Bool) (hF : ∀ c ∈ F, c.2.length ≤ k) :
    toOneHotCNFBounded q k N F sem = toOneHotCNF q N F sem := by
  unfold toOneHotCNFBounded toOneHotCNF
  congr 1
  exact List.flatMap_congr fun c hc => Constraint.toOneHotCNFBounded_eq_toOneHotCNF (hF c hc)

theorem length_clause_toOneHotCNFBounded_le {q k N : ℕ} {F : CSP Rel ℕ}
    {sem : Rel → List (Fin q) → Bool} {cl : Clause ℕ}
    (hcl : cl ∈ toOneHotCNFBounded q k N F sem) :
    cl.length ≤ max q (max k 2) := by
  rw [toOneHotCNFBounded, List.mem_append] at hcl
  rcases hcl with hcl | hcl
  · obtain ⟨v, _, hc⟩ := List.mem_flatMap.mp hcl
    rw [CNF.exactlyOne, List.mem_append] at hc
    rcases hc with hc | hc
    · rw [CNF.atLeastOne, List.mem_singleton] at hc
      subst hc
      simp
    · simp only [CNF.atMostOne, List.mem_flatMap, List.mem_map] at hc
      obtain ⟨_, _, _, _, rfl⟩ := hc
      exact (le_max_right k 2).trans (le_max_right q (max k 2))
  · obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp hcl
    exact (Constraint.length_clause_toOneHotCNFBounded_le hc).trans
      ((le_max_left k 2).trans (le_max_right q (max k 2)))

theorem validDeclaredInput_toOneHotCNFBounded {q k N : ℕ} {F : CSP Rel ℕ}
    (sem : Rel → List (Fin q) → Bool) (hv : validDeclaredCSP k N F = true) :
    CNF.validDeclaredInput (max q (max k 2)) (N * q) (toOneHotCNFBounded q k N F sem) = true := by
  obtain ⟨hw, hsub⟩ := validDeclaredCSP_eq_true_iff.mp hv
  rw [toOneHotCNFBounded_eq_toOneHotCNF sem hw]
  refine CNF.validDeclaredInput_eq_true_iff.mpr ⟨fun _ hc =>
    length_clause_toOneHotCNF_le sem hw hc, ?_⟩
  intro x hx
  exact Finset.mem_range.mpr (vars_toOneHotCNF_subset_range sem
    (fun v hv' => Finset.mem_range.mp (hsub (List.mem_toFinset.mpr hv')))
    (List.mem_toFinset.mp hx))

theorem modelCountOn_toOneHotDeclaredCNF {q k : ℕ} (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) {x : ℕ × CSP Rel ℕ}
    (hv : validDeclaredCSP k x.1 x.2 = true) :
    letI : Inhabited (Fin q) := ⟨⟨0, hq⟩⟩
    (toOneHotDeclaredCNF q k sem x).2.modelCountOn
        (Finset.range (toOneHotDeclaredCNF q k sem x).1) =
      x.2.modelCountOn sem (Finset.range x.1) := by
  let : Inhabited (Fin q) := ⟨⟨0, hq⟩⟩
  obtain ⟨hw, hsub⟩ := validDeclaredCSP_eq_true_iff.mp hv
  dsimp only [toOneHotDeclaredCNF]
  rw [toOneHotCNFBounded_eq_toOneHotCNF sem hw]
  exact modelCountOn_toOneHotCNF hq x.2 sem fun v hv' =>
    Finset.mem_range.mp (hsub (List.mem_toFinset.mpr hv'))

end Cslib.Logic.PL.CSP
