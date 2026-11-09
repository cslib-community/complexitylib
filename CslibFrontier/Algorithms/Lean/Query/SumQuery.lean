/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Algorithms.Lean.Query.FreeM

/-!
# Sums of Query Signatures

`SumQuery F G` is the disjoint sum of two query signatures `F G : Type → Type`: a program in
`FreeM (SumQuery F G)` may ask queries of either kind, and an oracle for the sum is a pair of
oracles (`SumQuery.combine`). The counters `countInl` and `countInr` charge the two kinds of
queries separately, and add up to `FreeM.countQueries`. This is used, for example, to charge
value-oracle and independence-oracle calls of constrained submodular maximization separately.

## Main definitions

* `Cslib.Query.SumQuery`: the sum of two query signatures.
* `Cslib.Query.SumQuery.combine`: the oracle for `SumQuery F G` built from oracles for `F` and `G`.
* `Cslib.Query.SumQuery.liftInl`, `Cslib.Query.SumQuery.liftInr`: lift single queries.
* `Cslib.Query.SumQuery.countInl`, `Cslib.Query.SumQuery.countInr`: the number of `F`-queries and
  of `G`-queries along an oracle path.

## Main results

* `SumQuery.countInl_add_countInr`: `countInl + countInr = countQueries`.
-/

public section

namespace Cslib.Query

/-- The sum of two query signatures: a query is either an `F`-query or a `G`-query. -/
inductive SumQuery (F G : Type → Type) : Type → Type where
  /-- An `F`-query. -/
  | inl {ι : Type} (q : F ι) : SumQuery F G ι
  /-- A `G`-query. -/
  | inr {ι : Type} (q : G ι) : SumQuery F G ι

namespace SumQuery

variable {F G : Type → Type}

/-- The oracle for `SumQuery F G` answering `F`-queries with `o₁` and `G`-queries with `o₂`. -/
@[expose] def combine (o₁ : {ι : Type} → F ι → ι) (o₂ : {ι : Type} → G ι → ι) :
    {ι : Type} → SumQuery F G ι → ι
  | _, .inl q => o₁ q
  | _, .inr q => o₂ q

@[simp] theorem combine_inl (o₁ : {ι : Type} → F ι → ι) (o₂ : {ι : Type} → G ι → ι)
    {ι : Type} (q : F ι) : combine o₁ o₂ (.inl q) = o₁ q := rfl

@[simp] theorem combine_inr (o₁ : {ι : Type} → F ι → ι) (o₂ : {ι : Type} → G ι → ι)
    {ι : Type} (q : G ι) : combine o₁ o₂ (.inr q) = o₂ q := rfl

/-- Lift an `F`-query into `FreeM (SumQuery F G)`. -/
abbrev liftInl {ι : Type} (q : F ι) : FreeM (SumQuery F G) ι := FreeM.lift (.inl q)

/-- Lift a `G`-query into `FreeM (SumQuery F G)`. -/
abbrev liftInr {ι : Type} (q : G ι) : FreeM (SumQuery F G) ι := FreeM.lift (.inr q)

/-- Unit weight on `F`-queries. -/
@[expose] def weightInl : {ι : Type} → SumQuery F G ι → ℕ
  | _, .inl _ => 1
  | _, .inr _ => 0

/-- Unit weight on `G`-queries. -/
@[expose] def weightInr : {ι : Type} → SumQuery F G ι → ℕ
  | _, .inl _ => 0
  | _, .inr _ => 1

/-- The number of `F`-queries along the path of `p` determined by `oracle`. -/
@[expose] def countInl {α : Type} (oracle : {ι : Type} → SumQuery F G ι → ι)
    (p : FreeM (SumQuery F G) α) : ℕ :=
  p.cost oracle weightInl

/-- The number of `G`-queries along the path of `p` determined by `oracle`. -/
@[expose] def countInr {α : Type} (oracle : {ι : Type} → SumQuery F G ι → ι)
    (p : FreeM (SumQuery F G) α) : ℕ :=
  p.cost oracle weightInr

variable {α β : Type} (oracle : {ι : Type} → SumQuery F G ι → ι)

@[simp] theorem countInl_pure (a : α) :
    countInl oracle (pure a : FreeM (SumQuery F G) α) = 0 := rfl

@[simp] theorem countInr_pure (a : α) :
    countInr oracle (pure a : FreeM (SumQuery F G) α) = 0 := rfl

@[simp] theorem countInl_bind (p : FreeM (SumQuery F G) α) (k : α → FreeM (SumQuery F G) β) :
    countInl oracle (p >>= k) = countInl oracle p + countInl oracle (k (p.eval oracle)) :=
  FreeM.cost_bind oracle weightInl p k

@[simp] theorem countInr_bind (p : FreeM (SumQuery F G) α) (k : α → FreeM (SumQuery F G) β) :
    countInr oracle (p >>= k) = countInr oracle p + countInr oracle (k (p.eval oracle)) :=
  FreeM.cost_bind oracle weightInr p k

@[simp] theorem countInl_map (p : FreeM (SumQuery F G) α) (g : α → β) :
    countInl oracle (g <$> p) = countInl oracle p :=
  FreeM.cost_map oracle weightInl p g

@[simp] theorem countInr_map (p : FreeM (SumQuery F G) α) (g : α → β) :
    countInr oracle (g <$> p) = countInr oracle p :=
  FreeM.cost_map oracle weightInr p g

@[simp] theorem countInl_liftInl {ι : Type} (q : F ι) :
    countInl oracle (liftInl q : FreeM (SumQuery F G) ι) = 1 :=
  FreeM.cost_lift oracle weightInl (.inl q)

@[simp] theorem countInl_liftInr {ι : Type} (q : G ι) :
    countInl oracle (liftInr q : FreeM (SumQuery F G) ι) = 0 :=
  FreeM.cost_lift oracle weightInl (.inr q)

@[simp] theorem countInr_liftInl {ι : Type} (q : F ι) :
    countInr oracle (liftInl q : FreeM (SumQuery F G) ι) = 0 :=
  FreeM.cost_lift oracle weightInr (.inl q)

@[simp] theorem countInr_liftInr {ι : Type} (q : G ι) :
    countInr oracle (liftInr q : FreeM (SumQuery F G) ι) = 1 :=
  FreeM.cost_lift oracle weightInr (.inr q)

/-- The two counters split the total query count. -/
theorem countInl_add_countInr (p : FreeM (SumQuery F G) α) :
    countInl oracle p + countInr oracle p = p.countQueries oracle := by
  induction p with
  | pure a => rfl
  | lift_bind op cont ih =>
    have h := ih (oracle op)
    simp only [countInl, countInr] at h
    simp only [FreeM.bind_eq_bind, countInl, countInr, FreeM.cost_liftBind,
      FreeM.countQueries_liftBind]
    cases op <;> simp only [weightInl, weightInr] <;> omega

end SumQuery

end Cslib.Query
