/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.LocalMapCounting
public import CslibFrontier.Computability.Complexity.Problems.Graph.CountingCNF
public import CslibFrontier.Computability.Complexity.Problems.SetSplitting
public import CslibFrontier.Logics.Propositional.CSP.ToOneHotCNF
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Preprocess
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Runtime transfers and polynomial-time bounded-width CNF counting compilations

This module connects the six bounded-width CNF counting encodings to polynomial-time machine
certificates and conditional exponential/subexponential runtime transfers:

1. **General conditional runtime transfer** (`CountingTransfer.transfer_declaredCounter`,
   `CountingTransfer.declaredCounter_of_modelCounter`): any declared `k`-CNF counter (or plain
   `(max k 2)`-CNF model counter via tautology variable padding `CNF.padDeclaredVars`) running in
   time `2 ^ E N * poly(|x|)` and polynomial space transfers along any polynomial-time compilation
   `g : α → ℕ × CNF ℕ` satisfying `(g x).1 ≤ C * μ x + D` under a polynomial-time guard.
2. **Polynomial-time bounded one-hot CSP compilation** (`CSP.toOneHotCNFBounded`,
   `CSP.toOneHotDeclaredCNF`, `CSP.computableInPolyTime_toOneHotDeclaredCNF_of_forall`,
   `CSP.computableInPolyTime_toOneHotDeclaredCNF_of_finite`): compiles a finite-domain CSP over
   `Fin q` of arity `≤ k` on `N` declared variables into an equivalent CNF formula on `q * N`
   variables of clause width `≤ max q (max k 2)`.
3. **Explicit assignment bijection for constant-locality Boolean maps**
   (`LocalMap.preimageDeclaredEquiv`): pairs `LocalMap.toDeclaredCNF` with an explicit bijection
   between declared-range satisfying assignments and `n`-bit preimages.
4. **Six conditional counting runtime transfers**:
   independent sets (`width = 2`, parameter `|V|`), proper `q`-colourings (`width = max q 2`,
   parameter `|V|`), general-graph perfect matchings (`width = 3`, parameter `|V| + |E|`),
   fixed-arity finite-domain `#CSP` via one-hot encoding (`width = max q (max k 2)`, parameter `N`),
   `#k-SetSplitting` (`width = k`, parameter `|U|`), and constant-locality Boolean map preimage
   counting (`width = k`, parameter `numVars`).

## Main definitions

* `Cslib.Complexity.encDeclaredCNF`, `Cslib.Complexity.encDeclaredCSP`: framed encodings of
  declared-variable CNF and CSP instances.
* `Cslib.Logic.PL.CNF.padDeclaredVars`: width-`2` tautology padding fixing `numVars = N`.
* `Cslib.Logic.PL.CSP.toOneHotCNFBounded`, `Cslib.Logic.PL.CSP.toOneHotDeclaredCNF`: width-guarded
  one-hot CNF compilation for finite-domain CSPs.
* `Cslib.Complexity.LocalMap.preimageDeclaredEquiv`: explicit preimage bijection for
  `LocalMap.toDeclaredCNF`.

## Main results

* `Cslib.Complexity.CountingTransfer.transfer_declaredCounter`,
  `Cslib.Complexity.CountingTransfer.declaredCounter_of_modelCounter`: general conditional
  counting runtime and polynomial-space transfers.
* `Cslib.Complexity.CSP.computableInPolyTime_toOneHotDeclaredCNF_of_forall`,
  `Cslib.Complexity.CSP.computableInPolyTime_toOneHotDeclaredCNF_of_finite`: polynomial-time
  one-hot CSP compilation.
* `Cslib.Complexity.CountingTransfer.exists_indepSetCounter_of_declaredCounter`,
  `Cslib.Complexity.CountingTransfer.exists_coloringCounter_of_declaredCounter`,
  `Cslib.Complexity.CountingTransfer.exists_perfectMatchingCounter_of_declaredCounter`,
  `Cslib.Complexity.CountingTransfer.exists_oneHotCSPCounter_of_declaredCounter`,
  `Cslib.Complexity.CountingTransfer.exists_setSplittingCounter_of_declaredCounter`,
  `Cslib.Complexity.CountingTransfer.exists_localMapPreimageCounter_of_declaredCounter`:
  conditional runtime transfers for all six counting encodings.

## References

* [M. Cygan et al., *Parameterized Algorithms*][CyganEtAl2015]
* [G. S. Tseitin, *On the complexity of derivation in propositional calculus*][Tseitin1983]
* [L. G. Valiant, *The complexity of computing the permanent*][Valiant1979]
-/

public section

namespace Cslib.Logic.PL

/-! ### Tautology variable padding for declared-variable CNF formulas -/

namespace CNF

/-- Prepend width-`2` tautology clauses `(v ∨ ¬v)` for all `v < N` so that every declared variable
occurs explicitly without changing truth values on any assignment. -/
@[expose] def padDeclaredVars (N : ℕ) (φ : CNF ℕ) : CNF ℕ :=
  ((List.range N).map fun v => [(v, true), (v, false)]) ++ φ

@[simp]
theorem eval_padDeclaredVars (N : ℕ) (φ : CNF ℕ) (σ : ℕ → Bool) :
    (padDeclaredVars N φ).eval σ = φ.eval σ := by
  rw [padDeclaredVars, CNF.eval_append]
  have htaut : CNF.eval σ ((List.range N).map fun v => [(v, true), (v, false)]) = true := by
    rw [CNF.eval, List.all_eq_true]
    intro c hc
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hc
    rw [Clause.eval]
    cases σ v <;> simp [Literal.eval]
  rw [htaut, Bool.true_and]

theorem length_clause_padDeclaredVars_le {k N : ℕ} {φ : CNF ℕ}
    (hφ : ∀ cl ∈ φ, cl.length ≤ k) {cl : Clause ℕ} (hcl : cl ∈ padDeclaredVars N φ) :
    cl.length ≤ max k 2 := by
  rw [padDeclaredVars, List.mem_append] at hcl
  rcases hcl with hcl | hcl
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hcl
    exact le_max_right k 2
  · exact (hφ cl hcl).trans (le_max_left k 2)

theorem vars_padDeclaredVars_toFinset {N : ℕ} {φ : CNF ℕ}
    (hsub : φ.vars.toFinset ⊆ Finset.range N) :
    (padDeclaredVars N φ).vars.toFinset = Finset.range N := by
  ext v
  simp only [padDeclaredVars, CNF.vars, List.flatten_append, List.map_append, List.mem_toFinset,
    List.mem_append, Finset.mem_range]
  constructor
  · rintro (hv | hv)
    · simp only [List.mem_map, List.mem_flatten] at hv
      obtain ⟨l, ⟨c, hc, hl⟩, rfl⟩ := hv
      obtain ⟨u, hu, rfl⟩ := hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> exact List.mem_range.mp hu
    · exact Finset.mem_range.mp (hsub (List.mem_toFinset.mpr hv))
  · intro hv
    left
    simp only [List.mem_map, List.mem_flatten]
    exact ⟨(v, true), ⟨[(v, true), (v, false)],
      ⟨v, List.mem_range.mpr hv, rfl⟩,
      List.mem_cons_self⟩, rfl⟩

theorem numVars_padDeclaredVars {N : ℕ} {φ : CNF ℕ}
    (hsub : φ.vars.toFinset ⊆ Finset.range N) :
    (padDeclaredVars N φ).numVars = N := by
  rw [CNF.numVars, vars_padDeclaredVars_toFinset hsub, Finset.card_range]

theorem modelCount_padDeclaredVars {N : ℕ} {φ : CNF ℕ}
    (hsub : φ.vars.toFinset ⊆ Finset.range N) :
    (padDeclaredVars N φ).modelCount = φ.modelCountOn (Finset.range N) := by
  rw [← CNF.modelCountOn_vars, vars_padDeclaredVars_toFinset hsub]
  simp only [CNF.modelCountOn, eval_padDeclaredVars]

end CNF

/-! ### Width-guarded one-hot CNF compilation for finite-domain CSPs -/

namespace Constraint

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

end Constraint

namespace CSP

variable {Rel : Type*}

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

end CSP

end Cslib.Logic.PL

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM SubexponentialSAT

/-- Framed encoding of a declared-variable CNF instance `(N, φ) : ℕ × CNF ℕ`, with `N` in unary
and `φ` in binary `encCNF`. -/
abbrev encDeclaredCNF : ℕ × CNF ℕ ↪ List Bool :=
  encPair encUnary encCNF

/-- Framed encoding of a declared-variable CSP instance `(N, F) : ℕ × CSP Rel ℕ`, with `N` in
unary and `F` in binary `encCSP encRel encNat`. -/
abbrev encDeclaredCSP {Rel : Type} (encRel : Rel ↪ List Bool) : ℕ × CSP Rel ℕ ↪ List Bool :=
  encPair encUnary (encCSP encRel encNat)

/-! ### Row 6 explicit assignment bijection -/

/-- Explicit bijection between declared-range satisfying assignments of `LocalMap.toDeclaredCNF k q`
and `n`-bit preimages of `q.2` under `q.1` when `q.1.Valid k = true`. -/
@[expose] def LocalMap.preimageDeclaredEquiv {k : ℕ} {q : LocalMap × List Bool}
    (hq : q.1.Valid k = true) :
    {σ : Finset.range q.1.numVars → Bool //
      (LocalMap.toDeclaredCNF k q).2.eval
        (fun v => if hv : v ∈ Finset.range q.1.numVars then σ ⟨v, hv⟩ else false) = true} ≃
      {σ : Finset.range q.1.numVars → Bool //
        q.1.eval (fun v => if hv : v ∈ Finset.range q.1.numVars then σ ⟨v, hv⟩ else false) =
          q.2} :=
  Equiv.subtypeEquivRight fun σ => by
    rw [LocalMap.eval_toDeclaredCNF, hq, Bool.true_and, decide_eq_true_eq]

/-! ### Row 4 polynomial-time one-hot CSP compilation -/

namespace CSP

variable {Rel : Type}

open Cslib.Logic.PL.CSP ComputableInPolyTime

private theorem computableInPolyTime_forbidOneHot (q : ℕ) (ts : List (Fin q)) :
    ComputableInPolyTime (fun vs : List ℕ => forbidOneHotClause q vs ts)
      (encList encNat) (encClause encNat) := by
  induction ts with
  | nil =>
    refine (const (encOut := encClause encNat) []).of_enc_eq fun vs => ?_
    simp [forbidOneHotClause]
  | cons a ts ih =>
    have hemp : ComputableInPolyTime (fun vs : List ℕ => decide (vs.length = 0))
        (encList encNat) encBool := by
      fun_prop
    have hhd : ComputableInPolyTime (fun vs : List ℕ => vs.getD 0 0) (encList encNat) encNat :=
      listGetD_binary (encA := encNat) (encL := encList encNat) 0
        (id' (encIn := encList encNat)) (const 0)
    have hlit : ComputableInPolyTime (fun vs : List ℕ => (vs.getD 0 0 * q + a.1, false))
        (encList encNat) (encPair encNat encBool) :=
      (binary_add.comp ((binary_mul' hhd (const q)).prod (const a.1))).prod (const false)
    have htl : ComputableInPolyTime (fun vs : List ℕ => vs.tail)
        (encList encNat) (encList encNat) := by
      fun_prop
    refine (hemp.ite (const []) (hlit.cons' (ih.comp htl))).of_enc_eq fun vs =>
      congrArg (encClause encNat) ?_
    cases vs with
    | nil => rfl
    | cons v vs => simp [forbidOneHotClause]

private theorem computableInPolyTime_toOneHotCNFAt (encRel : Rel ↪ List Bool) (q r : ℕ)
    (sem : Rel → List (Fin q) → Bool)
    (hsem : ∀ ts ∈ finTuples q r,
      ComputableInPolyTime (fun R : Rel => sem R ts) encRel encBool) :
    ComputableInPolyTime
      (fun c : Constraint Rel ℕ =>
        ((finTuples q r).filter fun ts => !sem c.1 ts).map (forbidOneHotClause q c.2))
      (encConstraint encRel encNat) encCNF := by
  refine computableInPolyTime_mapFilterConst (finTuples q r)
    (test := fun (c : Constraint Rel ℕ) (ts : List (Fin q)) => !sem c.1 ts)
    (f := fun (c : Constraint Rel ℕ) (ts : List (Fin q)) => forbidOneHotClause q c.2 ts)
    (fun ts hts => ?_) (fun ts _ => ?_)
  · have hsemt := hsem ts hts
    fun_prop
  · exact (computableInPolyTime_forbidOneHot q ts).comp (snd encRel (encList encNat))

private theorem computableInPolyTime_constraintToOneHotCNFBounded
    (encRel : Rel ↪ List Bool) (q k : ℕ) (sem : Rel → List (Fin q) → Bool)
    (hsem : ∀ ts : List (Fin q), ts.length ≤ k →
      ComputableInPolyTime (fun R : Rel => sem R ts) encRel encBool) :
    ComputableInPolyTime (Constraint.toOneHotCNFBounded q k sem)
      (encConstraint encRel encNat) encCNF := by
  induction k with
  | zero =>
    have htest : ComputableInPolyTime
        (fun c : Constraint Rel ℕ => decide (c.2.length = 0))
        (encConstraint encRel encNat) encBool := by
      fun_prop
    refine (htest.ite (computableInPolyTime_toOneHotCNFAt encRel q 0 sem
        fun ts hts => hsem ts (by simp [(mem_finTuples.mp hts)]))
      (const [])).of_enc_eq fun c => ?_
    simp only [Constraint.toOneHotCNFBounded, Constraint.toOneHotCNF, Nat.le_zero]
    by_cases h : c.2.length = 0 <;> simp [h]
  | succ k ih =>
    have htest : ComputableInPolyTime
        (fun c : Constraint Rel ℕ => decide (c.2.length = k + 1))
        (encConstraint encRel encNat) encBool := by
      fun_prop
    refine (htest.ite (computableInPolyTime_toOneHotCNFAt encRel q (k + 1) sem
        fun ts hts => hsem ts (by simp [(mem_finTuples.mp hts)]))
      (ih fun ts hts => hsem ts (hts.trans (Nat.le_succ k)))).of_enc_eq fun c => ?_
    simp only [Constraint.toOneHotCNFBounded, Constraint.toOneHotCNF]
    by_cases h1 : c.2.length = k + 1
    · simp [h1]
    · have hle : (c.2.length ≤ k + 1) ↔ (c.2.length ≤ k) := by omega
      simp [h1, hle]

private theorem computableInPolyTime_exactlyOneBlock (q : ℕ) :
    ComputableInPolyTime
      (fun v : ℕ => CNF.exactlyOne ((List.range q).map fun a => v * q + a))
      encNat encCNF := by
  have hlist : ComputableInPolyTime
      (fun v : ℕ => (List.range q).map fun a => v * q + a) encNat (encList encNat) :=
    ComputableInPolyTime.mapWithInput (const (List.range q))
      (binary_add.comp ((binary_mul' (fst encNat encNat) (const q)).prod (snd encNat encNat)))
  have hex : ComputableInPolyTime (CNF.exactlyOne (V := ℕ)) (encList encNat) encCNF := by
    unfold CNF.exactlyOne CNF.atLeastOne CNF.atMostOne
    fun_prop
  exact hex.comp hlist

/-- Compiling `(N, F)` to its declared one-hot CNF `(N * q, toOneHotCNFBounded q k N F sem)` is
polynomial-time whenever `fun R => sem R ts` is polynomial-time on tuples of length `≤ k`. -/
theorem computableInPolyTime_toOneHotDeclaredCNF_of_forall (encRel : Rel ↪ List Bool) (q k : ℕ)
    (sem : Rel → List (Fin q) → Bool)
    (hsem : ∀ ts : List (Fin q), ts.length ≤ k →
      ComputableInPolyTime (fun R : Rel => sem R ts) encRel encBool) :
    ComputableInPolyTime (toOneHotDeclaredCNF q k sem)
      (encDeclaredCSP encRel) encDeclaredCNF := by
  have hN : ComputableInPolyTime (fun x : ℕ × CSP Rel ℕ => x.1 * q)
      (encDeclaredCSP encRel) encUnary :=
    unary_mul' (fst encUnary (encCSP encRel encNat)) (const q)
  have hex : ComputableInPolyTime
      (fun x : ℕ × CSP Rel ℕ =>
        (List.range x.1).flatMap fun v => CNF.exactlyOne ((List.range q).map fun a => v * q + a))
      (encDeclaredCSP encRel) encCNF := by
    have hb := computableInPolyTime_exactlyOneBlock q
    fun_prop
  have hforb : ComputableInPolyTime
      (fun x : ℕ × CSP Rel ℕ => x.2.flatMap (Constraint.toOneHotCNFBounded q k sem))
      (encDeclaredCSP encRel) encCNF := by
    have hc := computableInPolyTime_constraintToOneHotCNFBounded encRel q k sem hsem
    fun_prop
  exact hN.prod (listAppend' hex hforb)

/-- Over a finite relation alphabet `Rel`, `toOneHotDeclaredCNF q k sem` is polynomial-time. -/
theorem computableInPolyTime_toOneHotDeclaredCNF_of_finite [Finite Rel]
    (encRel : Rel ↪ List Bool) (q k : ℕ) (sem : Rel → List (Fin q) → Bool) :
    ComputableInPolyTime (toOneHotDeclaredCNF q k sem)
      (encDeclaredCSP encRel) encDeclaredCNF :=
  computableInPolyTime_toOneHotDeclaredCNF_of_forall encRel q k sem fun _ _ => of_finite _

end CSP

/-! ### General conditional counting runtime transfers -/

namespace CountingTransfer

open ComputableInPolyTime

@[fun_prop]
theorem computableInPolyTime_padDeclaredVars :
    ComputableInPolyTime (fun p : ℕ × CNF ℕ => CNF.padDeclaredVars p.1 p.2)
      encDeclaredCNF encCNF := by
  unfold CNF.padDeclaredVars
  fun_prop

/-- Convert any plain `(max k 2)`-CNF model counter on `encCNF` running in time
`2 ^ E φ.numVars * (|φ| + 1) ^ e₀` and polynomial space into a declared `k`-CNF counter on
`encDeclaredCNF` running in time `2 ^ E p.1 * (|p| + 1) ^ e` and polynomial space. -/
theorem declaredCounter_of_modelCounter {k : ℕ} {countCNF : CNF ℕ → ℕ} {T₀ S₀ : CNF ℕ → ℕ}
    {E : ℕ → ℕ} {e₀ b₀ : ℕ}
    (hcount : ComputableInO countCNF encCNF encNat T₀ S₀)
    (hspec : ∀ φ : CNF ℕ, (∀ cl ∈ φ, cl.length ≤ max k 2) → countCNF φ = φ.modelCount)
    (hT₀ : ∀ φ, T₀ φ ≤ 2 ^ E φ.numVars * ((encCNF φ).length + 1) ^ e₀)
    (hS₀ : ∀ φ, S₀ φ ≤ ((encCNF φ).length + 1) ^ b₀) :
    ∃ (countDecl : ℕ × CNF ℕ → ℕ) (e b : ℕ),
      (∀ p : ℕ × CNF ℕ, CNF.validDeclaredInput k p.1 p.2 = true →
        countDecl p = p.2.modelCountOn (Finset.range p.1)) ∧
      ComputableInO countDecl encDeclaredCNF encNat
        (fun p => 2 ^ E p.1 * ((encDeclaredCNF p).length + 1) ^ e)
        (fun p => ((encDeclaredCNF p).length + 1) ^ b) := by
  have hvalid : ComputableInPolyTime
      (fun p : ℕ × CNF ℕ => CNF.validDeclaredInput k p.1 p.2) encDeclaredCNF encBool := by
    unfold CNF.validDeclaredInput
    have hN := unary_to_binary.comp (fst encUnary encCNF)
    fun_prop
  set pad : ℕ × CNF ℕ → CNF ℕ := fun p =>
    if CNF.validDeclaredInput k p.1 p.2 then CNF.padDeclaredVars p.1 p.2
    else CNF.padDeclaredVars p.1 [[]]
  have hpad : ComputableInPolyTime pad encDeclaredCNF encCNF :=
    hvalid.ite computableInPolyTime_padDeclaredVars
      (computableInPolyTime_padDeclaredVars.comp
        ((fst encUnary encCNF).prod (const [[]])))
  have hnum (p : ℕ × CNF ℕ) : (pad p).numVars = p.1 := by
    dsimp only [pad]
    split_ifs with hp
    · exact CNF.numVars_padDeclaredVars (CNF.validDeclaredInput_eq_true_iff.mp hp).2
    · exact CNF.numVars_padDeclaredVars (by simp [CNF.vars])
  obtain ⟨e, b, hcomp⟩ := hcount.comp_polyTime hpad
    (E := fun p => E p.1)
    (fun p => by simpa only [hnum p] using hT₀ (pad p))
    (fun p => hS₀ (pad p))
  refine ⟨fun p => countCNF (pad p), e, b, fun p hp => ?_, hcomp⟩
  obtain ⟨hw, hsub⟩ := CNF.validDeclaredInput_eq_true_iff.mp hp
  simp only [pad, hp, ↓reduceIte]
  rw [hspec _ (fun _ hc => CNF.length_clause_padDeclaredVars_le hw hc),
    CNF.modelCount_padDeclaredVars hsub]

/-- **General conditional counting runtime transfer:** any declared `k`-CNF counter running in time
`2 ^ E N * (|p| + 1) ^ e₀` and polynomial space with monotone `E` transfers across any
polynomial-time compilation `g : α → ℕ × CNF ℕ` and guard `valid : α → Bool` satisfying
`(g x).1 ≤ C * μ x + D` under `valid x = true`. -/
theorem transfer_declaredCounter {α : Type} {encA : α ↪ List Bool} (k : ℕ)
    {countDecl : ℕ × CNF ℕ → ℕ} {T₀ S₀ : ℕ × CNF ℕ → ℕ} {E : ℕ → ℕ} (hE : Monotone E)
    {e₀ b₀ : ℕ}
    (hcount : ComputableInO countDecl encDeclaredCNF encNat T₀ S₀)
    (hspec : ∀ p : ℕ × CNF ℕ, CNF.validDeclaredInput k p.1 p.2 = true →
      countDecl p = p.2.modelCountOn (Finset.range p.1))
    (hT₀ : ∀ p, T₀ p ≤ 2 ^ E p.1 * ((encDeclaredCNF p).length + 1) ^ e₀)
    (hS₀ : ∀ p, S₀ p ≤ ((encDeclaredCNF p).length + 1) ^ b₀)
    {g : α → ℕ × CNF ℕ} (hg : ComputableInPolyTime g encA encDeclaredCNF)
    {valid : α → Bool} (hvalid : ComputableInPolyTime valid encA encBool)
    (μ : α → ℕ) (C D : ℕ)
    (hvalid_imp : ∀ x, valid x = true →
      CNF.validDeclaredInput k (g x).1 (g x).2 = true ∧ (g x).1 ≤ C * μ x + D) :
    ∃ (count : α → ℕ) (e b : ℕ),
      (∀ x, count x = if valid x then (g x).2.modelCountOn (Finset.range (g x).1) else 0) ∧
      ComputableInO count encA encNat
        (fun x => 2 ^ E (C * μ x + D) * ((encA x).length + 1) ^ e)
        (fun x => ((encA x).length + 1) ^ b) := by
  set g' : α → ℕ × CNF ℕ := fun x => if valid x then g x else (0, [[]])
  have hg' : ComputableInPolyTime g' encA encDeclaredCNF := hvalid.ite hg (const (0, [[]]))
  have hle (x : α) : (g' x).1 ≤ C * μ x + D := by
    dsimp only [g']
    split_ifs with hx
    · exact (hvalid_imp x hx).2
    · exact Nat.zero_le _
  obtain ⟨e, b, hcomp⟩ := hcount.comp_polyTime hg'
    (E := fun x => E (C * μ x + D))
    (fun x => (hT₀ (g' x)).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (hE (hle x)))))
    (fun x => hS₀ (g' x))
  refine ⟨fun x => countDecl (g' x), e, b, fun x => ?_, hcomp⟩
  dsimp only [g']
  split_ifs with hx
  · exact hspec (g x) (hvalid_imp x hx).1
  · have hv0 : CNF.validDeclaredInput k 0 ([[]] : CNF ℕ) = true := by
      rw [CNF.validDeclaredInput_eq_true_iff]
      simp [CNF.vars]
    rw [hspec (0, [[]]) hv0]
    simp only [CNF.modelCountOn, CNF.eval, Clause.eval, List.all_cons, List.any_nil,
      Bool.false_and, Bool.false_eq_true, Finset.filter_false, Finset.card_empty]

/-! ### Conditional runtime transfers for the six CNF counting encodings -/

/-- **Row 1 conditional transfer (`#IndependentSet`, width `2`, `n = |V|`)**: any declared `2`-CNF
counter with monotone exponent `E` yields an independent-set counter in time
`2 ^ E G.1.toFinset.card * (|G| + 1) ^ e` and polynomial space. -/
theorem exists_indepSetCounter_of_declaredCounter
    {countDecl : ℕ × CNF ℕ → ℕ} {T₀ S₀ : ℕ × CNF ℕ → ℕ} {E : ℕ → ℕ} (hE : Monotone E)
    {e₀ b₀ : ℕ}
    (hcount : ComputableInO countDecl encDeclaredCNF encNat T₀ S₀)
    (hspec : ∀ p : ℕ × CNF ℕ, CNF.validDeclaredInput 2 p.1 p.2 = true →
      countDecl p = p.2.modelCountOn (Finset.range p.1))
    (hT₀ : ∀ p, T₀ p ≤ 2 ^ E p.1 * ((encDeclaredCNF p).length + 1) ^ e₀)
    (hS₀ : ∀ p, S₀ p ≤ ((encDeclaredCNF p).length + 1) ^ b₀) :
    ∃ (count : Graph → ℕ) (e b : ℕ),
      (∀ G : Graph, count G =
        Nat.card {S : Finset {v : ℕ // v ∈ G.1} //
          G.induced.IsIndepSet (S : Set {v : ℕ // v ∈ G.1})}) ∧
      ComputableInO count encGraph encNat
        (fun G => 2 ^ E G.1.toFinset.card * ((encGraph G).length + 1) ^ e)
        (fun G => ((encGraph G).length + 1) ^ b) := by
  have hg : ComputableInPolyTime
      (fun G : Graph => (G.toIndepSetCNF.denseRelabel.numVars, G.toIndepSetCNF.denseRelabel))
      encGraph encDeclaredCNF := by
    have hdecl : ComputableInPolyTime (fun ψ : CNF ℕ => (ψ.numVars, ψ)) encCNF encDeclaredCNF := by
      fun_prop
    exact hdecl.comp
      (SAT.computableInPolyTime_denseRelabel.comp Graph.computableInPolyTime_toIndepSetCNF)
  obtain ⟨count, e, b, hcspec, hcinO⟩ :=
    transfer_declaredCounter 2 hE hcount hspec hT₀ hS₀ hg (const true)
      (fun G => G.1.toFinset.card) 1 0 fun G _ => by
        have hw : ∀ cl ∈ G.toIndepSetCNF.denseRelabel, cl.length ≤ 2 :=
          (CNF.all_length_le_denseRelabel G.toIndepSetCNF).mpr fun _ hc =>
            (Graph.length_clause_toIndepSetCNF hc).le
        refine ⟨CNF.validDeclaredInput_eq_true_iff.mpr
          ⟨hw, by rw [CNF.vars_denseRelabel_toFinset, CNF.numVars_denseRelabel]⟩, ?_⟩
        simp [CNF.numVars_denseRelabel, Graph.numVars_toIndepSetCNF]
  refine ⟨count, e, b, fun G => ?_, ?_⟩
  · simp only [hcspec G, ↓reduceIte, CNF.numVars_denseRelabel, CNF.modelCountOn_denseRelabel,
      Graph.modelCount_toIndepSetCNF]
  · simpa only [Nat.one_mul, Nat.add_zero] using hcinO

/-- **Row 2 conditional transfer (`#q-Coloring`, width `max q 2`, `n = q * |V|`)**: any declared
`(max q 2)`-CNF counter with monotone exponent `E` yields a proper `q`-colouring counter in time
`2 ^ E (q * G.1.toFinset.card) * (|G| + 1) ^ e` and polynomial space. -/
theorem exists_coloringCounter_of_declaredCounter (q : ℕ)
    {countDecl : ℕ × CNF ℕ → ℕ} {T₀ S₀ : ℕ × CNF ℕ → ℕ} {E : ℕ → ℕ} (hE : Monotone E)
    {e₀ b₀ : ℕ}
    (hcount : ComputableInO countDecl encDeclaredCNF encNat T₀ S₀)
    (hspec : ∀ p : ℕ × CNF ℕ, CNF.validDeclaredInput (max q 2) p.1 p.2 = true →
      countDecl p = p.2.modelCountOn (Finset.range p.1))
    (hT₀ : ∀ p, T₀ p ≤ 2 ^ E p.1 * ((encDeclaredCNF p).length + 1) ^ e₀)
    (hS₀ : ∀ p, S₀ p ≤ ((encDeclaredCNF p).length + 1) ^ b₀) :
    ∃ (count : Graph → ℕ) (e b : ℕ),
      (∀ G : Graph, count G = Nat.card (G.induced.Coloring (Fin q))) ∧
      ComputableInO count encGraph encNat
        (fun G => 2 ^ E (q * G.1.toFinset.card) * ((encGraph G).length + 1) ^ e)
        (fun G => ((encGraph G).length + 1) ^ b) := by
  have hg : ComputableInPolyTime
      (fun G : Graph => (q * G.distinctVertices.length, G.toColoringCNF q))
      encGraph encDeclaredCNF := by
    have hdv := Graph.computableInPolyTime_distinctVertices
    have hc := Graph.computableInPolyTime_toColoringCNF q
    fun_prop
  obtain ⟨count, e, b, hcspec, hcinO⟩ :=
    transfer_declaredCounter (max q 2) hE hcount hspec hT₀ hS₀ hg (const true)
      (fun G => G.1.toFinset.card) q 0 fun G _ =>
        ⟨Graph.validDeclaredInput_toColoringCNF q G,
          by simp [Graph.length_distinctVertices]⟩
  refine ⟨count, e, b, fun G => ?_, ?_⟩
  · simp only [hcspec G, ↓reduceIte, Graph.modelCountOn_toColoringCNF]
  · simpa only [Nat.add_zero] using hcinO

/-- Declared wire count `|E| + gates` of `Graph.toPerfectMatchingCNF` is polynomial-time in
unary. -/
theorem computableInPolyTime_perfectMatchingDeclaredVars :
    ComputableInPolyTime
      (fun G : Graph => G.edgeList.length + G.perfectMatchingCircuit.1.length)
      encGraph encUnary := by
  have hE := Graph.computableInPolyTime_edgeList
  have hW : ComputableInPolyTime Graph.perfectMatchingWires
      encGraph (encList (encList encUnary)) := by
    unfold Graph.perfectMatchingWires Graph.incident
    fun_prop
  have hfl : ComputableInPolyTime (fun G : Graph => G.perfectMatchingWires.flatten.length)
      encGraph encUnary := by
    fun_prop
  have hwl : ComputableInPolyTime (fun G : Graph => G.perfectMatchingWires.length)
      encGraph encUnary := by
    fun_prop
  have hexpr : ComputableInPolyTime
      (fun G : Graph => G.edgeList.length +
        (1 + (3 * G.perfectMatchingWires.flatten.length + 4 * G.perfectMatchingWires.length)))
      encGraph encUnary := by
    fun_prop
  refine hexpr.of_enc_eq fun G => congrArg encUnary ?_
  rw [Graph.perfectMatchingCircuit, Circuits.Boolean.length_seqExactlyOneAll,
    List.length_flatten]
  omega

/-- **Row 3 conditional transfer (`#PerfectMatching`, width `3`, `n ≤ 7 * (|V| + |E|) + 1`)**:
any declared `3`-CNF counter with monotone exponent `E` yields an exact perfect-matching counter on
general graphs in time `2 ^ E (7 * (|V| + |E|) + 1) * (|G| + 1) ^ e` and polynomial space. -/
theorem exists_perfectMatchingCounter_of_declaredCounter
    {countDecl : ℕ × CNF ℕ → ℕ} {T₀ S₀ : ℕ × CNF ℕ → ℕ} {E : ℕ → ℕ} (hE : Monotone E)
    {e₀ b₀ : ℕ}
    (hcount : ComputableInO countDecl encDeclaredCNF encNat T₀ S₀)
    (hspec : ∀ p : ℕ × CNF ℕ, CNF.validDeclaredInput 3 p.1 p.2 = true →
      countDecl p = p.2.modelCountOn (Finset.range p.1))
    (hT₀ : ∀ p, T₀ p ≤ 2 ^ E p.1 * ((encDeclaredCNF p).length + 1) ^ e₀)
    (hS₀ : ∀ p, S₀ p ≤ ((encDeclaredCNF p).length + 1) ^ b₀) :
    ∃ (count : Graph → ℕ) (e b : ℕ),
      (∀ G : Graph, count G = Nat.card {M : G.induced.Subgraph // M.IsPerfectMatching}) ∧
      ComputableInO count encGraph encNat
        (fun G => 2 ^ E (7 * (G.1.toFinset.card + G.edgeList.length) + 1) *
          ((encGraph G).length + 1) ^ e)
        (fun G => ((encGraph G).length + 1) ^ b) := by
  have hg : ComputableInPolyTime
      (fun G : Graph =>
        (G.edgeList.length + G.perfectMatchingCircuit.1.length, G.toPerfectMatchingCNF))
      encGraph encDeclaredCNF :=
    computableInPolyTime_perfectMatchingDeclaredVars.prod
      Graph.computableInPolyTime_toPerfectMatchingCNF
  obtain ⟨count, e, b, hcspec, hcinO⟩ :=
    transfer_declaredCounter 3 hE hcount hspec hT₀ hS₀ hg (const true)
      (fun G => G.1.toFinset.card + G.edgeList.length) 7 1 fun G _ => by
        refine ⟨Graph.validDeclaredInput_toPerfectMatchingCNF G, ?_⟩
        have h := Graph.length_perfectMatchingCircuit_le G
        omega
  refine ⟨count, e, b, fun G => ?_, hcinO⟩
  simp only [hcspec G, ↓reduceIte, Graph.modelCountOn_toPerfectMatchingCNF]

/-- **Row 4 conditional transfer (one-hot `#CSP` over `Fin q`, width `max q (max k 2)`,
`n = q * N`)**: any declared `(max q (max k 2))`-CNF counter with monotone exponent `E` transfers
to finite-domain `#CSP` in time `2 ^ E (q * N) * (|x| + 1) ^ e` and polynomial space. -/
theorem exists_oneHotCSPCounter_of_declaredCounter {Rel : Type} (encRel : Rel ↪ List Bool)
    {q : ℕ} (hq : 0 < q) (k : ℕ) (sem : Rel → List (Fin q) → Bool)
    (hsem : ∀ ts : List (Fin q), ts.length ≤ k →
      ComputableInPolyTime (fun R : Rel => sem R ts) encRel encBool)
    {countDecl : ℕ × CNF ℕ → ℕ} {T₀ S₀ : ℕ × CNF ℕ → ℕ} {E : ℕ → ℕ} (hE : Monotone E)
    {e₀ b₀ : ℕ}
    (hcount : ComputableInO countDecl encDeclaredCNF encNat T₀ S₀)
    (hspec : ∀ p : ℕ × CNF ℕ, CNF.validDeclaredInput (max q (max k 2)) p.1 p.2 = true →
      countDecl p = p.2.modelCountOn (Finset.range p.1))
    (hT₀ : ∀ p, T₀ p ≤ 2 ^ E p.1 * ((encDeclaredCNF p).length + 1) ^ e₀)
    (hS₀ : ∀ p, S₀ p ≤ ((encDeclaredCNF p).length + 1) ^ b₀) :
    letI : Inhabited (Fin q) := ⟨⟨0, hq⟩⟩
    ∃ (count : ℕ × CSP Rel ℕ → ℕ) (e b : ℕ),
      (∀ x, count x = if CSP.validDeclaredCSP k x.1 x.2 then
        x.2.modelCountOn sem (Finset.range x.1) else 0) ∧
      ComputableInO count (encDeclaredCSP encRel) encNat
        (fun x => 2 ^ E (q * x.1) * ((encDeclaredCSP encRel x).length + 1) ^ e)
        (fun x => ((encDeclaredCSP encRel x).length + 1) ^ b) := by
  let : Inhabited (Fin q) := ⟨⟨0, hq⟩⟩
  obtain ⟨count, e, b, hcspec, hcinO⟩ :=
    transfer_declaredCounter (max q (max k 2)) hE hcount hspec hT₀ hS₀
      (CSP.computableInPolyTime_toOneHotDeclaredCNF_of_forall encRel q k sem hsem)
      (CSP.computableInPolyTime_validDeclaredCSP encRel k)
      Prod.fst q 0 fun x hx =>
        ⟨CSP.validDeclaredInput_toOneHotCNFBounded sem hx, by simp [CSP.toOneHotDeclaredCNF,
          Nat.mul_comm]⟩
  refine ⟨count, e, b, fun x => ?_, ?_⟩
  · rw [hcspec x]
    split_ifs with hx
    · exact CSP.modelCountOn_toOneHotDeclaredCNF hq sem hx
    · rfl
  · simpa only [Nat.add_zero] using hcinO

/-- **Row 5 conditional transfer (`#k-SetSplitting`, width `k`, `n = |U|`)**: any declared `k`-CNF
counter with monotone exponent `E` counts ordered splitting bipartitions on valid instances of set
size `≤ k` in time `2 ^ E x.ground.toFinset.card * (|x| + 1) ^ e` and polynomial space. -/
theorem exists_setSplittingCounter_of_declaredCounter (k : ℕ)
    {countDecl : ℕ × CNF ℕ → ℕ} {T₀ S₀ : ℕ × CNF ℕ → ℕ} {E : ℕ → ℕ} (hE : Monotone E)
    {e₀ b₀ : ℕ}
    (hcount : ComputableInO countDecl encDeclaredCNF encNat T₀ S₀)
    (hspec : ∀ p : ℕ × CNF ℕ, CNF.validDeclaredInput k p.1 p.2 = true →
      countDecl p = p.2.modelCountOn (Finset.range p.1))
    (hT₀ : ∀ p, T₀ p ≤ 2 ^ E p.1 * ((encDeclaredCNF p).length + 1) ^ e₀)
    (hS₀ : ∀ p, S₀ p ≤ ((encDeclaredCNF p).length + 1) ^ b₀) :
    ∃ (count : SetSplittingInstance → ℕ) (e b : ℕ),
      (∀ x : SetSplittingInstance,
        count x = if x.maxSetSizeBool k then x.count else 0) ∧
      ComputableInO count encSetSplitting encNat
        (fun x => 2 ^ E x.ground.toFinset.card * ((encSetSplitting x).length + 1) ^ e)
        (fun x => ((encSetSplitting x).length + 1) ^ b) := by
  obtain ⟨count, e, b, hcspec, hcinO⟩ :=
    transfer_declaredCounter k hE hcount hspec hT₀ hS₀
      SetSplittingInstance.computableInPolyTime_toDeclaredCNF
      (SetSplittingInstance.computableInPolyTime_maxSetSizeBool k)
      (fun x => x.ground.toFinset.card) 1 0 fun x hx =>
        ⟨SetSplittingInstance.validDeclaredInput_toDeclaredCNF hx,
          by simp [SetSplittingInstance.toDeclaredCNF,
            SetSplittingInstance.length_distinctGround]⟩
  refine ⟨count, e, b, fun x => ?_, ?_⟩
  · rw [hcspec x]
    split_ifs with hx
    · exact SetSplittingInstance.modelCountOn_toDeclaredCNF
        ((SetSplittingInstance.maxSetSizeBool_eq_true_iff k x).mp hx).1
    · rfl
  · simpa only [Nat.one_mul, Nat.add_zero] using hcinO

/-- **Row 6 conditional transfer (constant-locality Boolean map preimage counting, width `k`,
`n = G.numVars`)**: any declared `k`-CNF counter with monotone exponent `E` counts preimages of
`k`-local Boolean maps in time `2 ^ E q.1.numVars * (|q| + 1) ^ e` and polynomial space. -/
theorem exists_localMapPreimageCounter_of_declaredCounter (k : ℕ)
    {countDecl : ℕ × CNF ℕ → ℕ} {T₀ S₀ : ℕ × CNF ℕ → ℕ} {E : ℕ → ℕ} (hE : Monotone E)
    {e₀ b₀ : ℕ}
    (hcount : ComputableInO countDecl encDeclaredCNF encNat T₀ S₀)
    (hspec : ∀ p : ℕ × CNF ℕ, CNF.validDeclaredInput k p.1 p.2 = true →
      countDecl p = p.2.modelCountOn (Finset.range p.1))
    (hT₀ : ∀ p, T₀ p ≤ 2 ^ E p.1 * ((encDeclaredCNF p).length + 1) ^ e₀)
    (hS₀ : ∀ p, S₀ p ≤ ((encDeclaredCNF p).length + 1) ^ b₀) :
    ∃ (count : LocalMap × List Bool → ℕ) (e b : ℕ),
      (∀ q : LocalMap × List Bool,
        count q = if q.1.Valid k then q.1.preimageCount q.2 else 0) ∧
      ComputableInO count encLocalMapQuery encNat
        (fun q => 2 ^ E q.1.numVars * ((encLocalMapQuery q).length + 1) ^ e)
        (fun q => ((encLocalMapQuery q).length + 1) ^ b) := by
  have hv : ComputableInPolyTime (fun q : LocalMap × List Bool => q.1.Valid k)
      encLocalMapQuery encBool :=
    (computableInPolyTime_localMap_valid k).comp (fst encLocalMap encBits)
  obtain ⟨count, e, b, hcspec, hcinO⟩ :=
    transfer_declaredCounter k hE hcount hspec hT₀ hS₀
      (LocalMap.computableInPolyTime_toDeclaredCNF k) hv
      (fun q => q.1.numVars) 1 0 fun q _ =>
        ⟨LocalMap.validDeclaredInput_toDeclaredCNF (le_refl k) q, by simp⟩
  refine ⟨count, e, b, fun q => ?_, ?_⟩
  · rw [hcspec q]
    split_ifs with hq
    · simp only [LocalMap.modelCountOn_toDeclaredCNF, hq, ↓reduceIte]
    · rfl
  · simpa only [Nat.one_mul, Nat.add_zero] using hcinO

end CountingTransfer

end Cslib.Complexity
