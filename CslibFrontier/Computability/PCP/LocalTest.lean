/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.ConstraintGraph
public import Mathlib.Algebra.BigOperators.Expect
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Local tests and their constraint graphs

A **local test** reads a proof `π : P → Γ`, a word over the alphabet `Γ` indexed by positions, at a
few positions chosen by a random string `r : R`, the positions `query r i` for `i : Q`, and decides
from the symbols read whether to accept. Its acceptance probability `acceptProb π` is taken over a
uniformly random string. This is the shape of the verifier of a probabilistically checkable proof
making `|Q|` queries, and of the testers of the Hadamard code
[Arora and Barak, Chapter 11][AroraBarak09].

Such a test becomes a constraint graph [Arora and Barak, Chapter 22][AroraBarak09]
(`LocalTest.toConstraintGraph`): a vertex for every position, carrying a symbol, and a vertex for
every random string, carrying the symbols the test is to read on it; for every random string `r`
and query `i`, an edge from the vertex of `r` to the position `query r i` holds when the symbols
claimed at `r` make the test accept and the `i`-th of them is the symbol at the position. On a
random string where the test rejects the proof read off the positions, the claimed symbols either
make the test reject or differ from the proof at some query, so one of the edges of the random
string is violated. A labelling therefore violates a proportion of the edges at least the rejection
probability of the test divided by `|Q|` (`LocalTest.one_sub_acceptProb_le_card_mul_unsatFrac`).

Local tests combine: `LocalTest.map` renames the positions, to run a test on part of a larger
proof; `LocalTest.and` runs two tests on independent random strings and accepts when both do;
`LocalTest.mix` runs a test of a family chosen uniformly at random.

## Main definitions

* `Cslib.PCP.LocalTest`: a test reading a proof at positions chosen by a random string.
* `Cslib.PCP.LocalTest.Passes`, `Cslib.PCP.LocalTest.acceptProb`: acceptance on a random string,
  and its probability.
* `Cslib.PCP.LocalTest.map`, `Cslib.PCP.LocalTest.and`, `Cslib.PCP.LocalTest.mix`: renaming the
  positions, conjunction, and random choice in a family.
* `Cslib.PCP.LocalTest.comapRand`, `Cslib.PCP.LocalTest.padQueries`: adapting coin and query
  layouts.
* `Cslib.PCP.LocalTest.toConstraintGraph`: the constraint graph of a local test.
* `Cslib.PCP.LocalTest.proofOf`: the proof that a labelling of that graph carries at the positions.
* `Cslib.PCP.LocalTest.labellingOf`: the labelling of that graph by a proof.

## Main results

* `Cslib.PCP.LocalTest.acceptProb_eq_one_iff`: a test accepts with probability one exactly when it
  passes on every random string.
* `Cslib.PCP.LocalTest.acceptProb_and_le_left`, `Cslib.PCP.LocalTest.acceptProb_and_le_right`,
  `Cslib.PCP.LocalTest.acceptProb_mix`: acceptance probabilities of combined tests.
* `Cslib.PCP.LocalTest.card_filter_not_passes_le_card_unsatEdges`,
  `Cslib.PCP.LocalTest.one_sub_acceptProb_le_card_mul_unsatFrac`: soundness of the constraint
  graph, every rejecting random string accounting for a violated edge.
* `Cslib.PCP.LocalTest.satisfiable_toConstraintGraph`: completeness of the constraint graph.
* `Cslib.PCP.LocalTest.unsatFrac_labellingOf`: its exact value on the labelling carried by a proof.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.PCP

open Finset
open scoped BigOperators

/-- A **local test** on proofs `π : P → Γ`, words over the alphabet `Γ` indexed by the positions
`P`: on a random string `r : R`, it reads the proof at the positions `query r i` for `i : Q`, and
accepts when `Accepts r` holds of the symbols read. -/
structure LocalTest (P R Q Γ : Type*) where
  /-- The position read by the query `i` on the random string `r`. -/
  query : R → Q → P
  /-- Whether the test accepts on the random string `r`, given the symbols read by its queries. -/
  Accepts : R → (Q → Γ) → Prop

namespace LocalTest

variable {P P' R R' Q Q' Γ E : Type*} (T : LocalTest P R Q Γ)

/-- The test **passes** the proof `π` on the random string `r` when it accepts the symbols of `π`
at the positions it queries. -/
def Passes (π : P → Γ) (r : R) : Prop :=
  T.Accepts r fun i ↦ π (T.query r i)

/-! ### Combining tests -/

/-- The test `T` run through the renaming `f : P → P'` of its positions: it reads `f (query r i)`.
On a proof indexed by `P'` it is `T` run on the part of the proof that `f` selects. -/
def map (f : P → P') : LocalTest P' R Q Γ where
  query r i := f (T.query r i)
  Accepts := T.Accepts

/-- Run a test using the random string extracted by `f`. This does not assert that `f`
preserves the uniform distribution. -/
def comapRand (f : R' → R) : LocalTest P R' Q Γ where
  query r := T.query (f r)
  Accepts r := T.Accepts (f r)

/-- Replace the query layout by `Q'`: `read` chooses the old query at each new position,
and `use` selects the answers consumed by the original predicate. A left inverse makes this
an exact padding or rearrangement, as expressed by `passes_reindexQueries`. -/
def reindexQueries (read : Q' → Q) (use : Q → Q') : LocalTest P R Q' Γ where
  query r i := T.query r (read i)
  Accepts r a := T.Accepts r (a ∘ use)

/-- Pad a nonempty query layout to length `m`, repeating the first query at unused positions.
The acceptance predicate ignores those additional answers. -/
def padQueries {n m : ℕ} (T : LocalTest P R (Fin (n + 1)) Γ) (h : n + 1 ≤ m) :
    LocalTest P R (Fin m) Γ :=
  T.reindexQueries (fun i ↦ if hi : i.val < n + 1 then ⟨i.val, hi⟩ else 0) (Fin.castLE h)

/-- The **conjunction** of two tests: on independent random strings `r` and `r'`, run both tests,
making the queries of both, and accept when both accept. -/
def and (T' : LocalTest P R' Q' Γ) : LocalTest P (R × R') (Q ⊕ Q') Γ where
  query r := Sum.elim (T.query r.1) (T'.query r.2)
  Accepts r a := T.Accepts r.1 (a ∘ Sum.inl) ∧ T'.Accepts r.2 (a ∘ Sum.inr)

/-- The test that runs a uniformly random test of the family `T`: on the random string `(e, r)`, it
runs `T e` on `r`. -/
def mix (T : E → LocalTest P R Q Γ) : LocalTest P (E × R) Q Γ where
  query r := (T r.1).query r.2
  Accepts r := (T r.1).Accepts r.2

variable {T}

@[simp]
theorem passes_map {f : P → P'} {π : P' → Γ} {r : R} : (T.map f).Passes π r ↔ T.Passes (π ∘ f) r :=
  Iff.rfl

@[simp]
theorem passes_comapRand (f : R' → R) (π : P → Γ) (r : R') :
    (T.comapRand f).Passes π r ↔ T.Passes π (f r) :=
  Iff.rfl

@[simp]
theorem passes_reindexQueries {read : Q' → Q} {use : Q → Q'}
    (h : Function.LeftInverse read use) (π : P → Γ) (r : R) :
    (T.reindexQueries read use).Passes π r ↔ T.Passes π r := by
  simp only [Passes, reindexQueries, Function.comp_def, h.eq]

@[simp]
theorem passes_padQueries {n m : ℕ} (T : LocalTest P R (Fin (n + 1)) Γ)
    (h : n + 1 ≤ m) (π : P → Γ) (r : R) :
    (T.padQueries h).Passes π r ↔ T.Passes π r := by
  apply passes_reindexQueries
  intro i
  change (if hi : i.val < n + 1 then (⟨i.val, hi⟩ : Fin (n + 1)) else 0) = i
  simp only [dite_eq_left i.isLt]

@[simp]
theorem passes_and {T' : LocalTest P R' Q' Γ} {π : P → Γ} {r : R × R'} :
    (T.and T').Passes π r ↔ T.Passes π r.1 ∧ T'.Passes π r.2 :=
  Iff.rfl

@[simp]
theorem passes_mix {T : E → LocalTest P R Q Γ} {π : P → Γ} {r : E × R} :
    (mix T).Passes π r ↔ (T r.1).Passes π r.2 :=
  Iff.rfl

/-! ### The acceptance probability -/

section Prob

variable (T) [Fintype R]

open Classical in
/-- The **acceptance probability** of the test on the proof `π`: the probability that it passes `π`
on a uniformly random string. -/
noncomputable def acceptProb (π : P → Γ) : ℝ :=
  𝔼 r, if T.Passes π r then 1 else 0

open Classical in
/-- The acceptance probability is the proportion of the random strings on which the test passes. -/
theorem acceptProb_eq_card_div (π : P → Γ) :
    T.acceptProb π = (#{r | T.Passes π r} : ℝ) / Fintype.card R := by
  classical
  rw [acceptProb, Fintype.expect_eq_sum_div_card, sum_boole]

open Classical in
/-- The rejection probability is the proportion of the random strings on which the test does not
pass. -/
theorem one_sub_acceptProb [Nonempty R] (π : P → Γ) :
    1 - T.acceptProb π = (#{r | ¬ T.Passes π r} : ℝ) / Fintype.card R := by
  classical
  have hR : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have h := card_filter_add_card_filter_not (s := univ) fun r ↦ T.Passes π r
  rw [card_univ] at h
  rw [acceptProb_eq_card_div, eq_div_iff hR.ne', sub_mul, div_mul_cancel₀ _ hR.ne', one_mul,
    sub_eq_iff_eq_add', ← Nat.cast_add, h]

theorem acceptProb_nonneg (π : P → Γ) : 0 ≤ T.acceptProb π := by
  rw [acceptProb_eq_card_div]
  positivity

theorem acceptProb_le_one (π : P → Γ) : T.acceptProb π ≤ 1 := by
  rw [acceptProb_eq_card_div]
  exact div_le_one_of_le₀ (by exact_mod_cast card_le_univ _) (Nat.cast_nonneg _)

/-- **A test accepts with probability one exactly when it passes on every random string.** -/
theorem acceptProb_eq_one_iff [Nonempty R] {π : P → Γ} :
    T.acceptProb π = 1 ↔ ∀ r, T.Passes π r := by
  classical
  have hR : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  rw [acceptProb_eq_card_div, div_eq_one_iff_eq hR.ne', Nat.cast_inj, ← card_univ,
    card_filter_eq_iff]
  simp

variable {T}

@[simp]
theorem acceptProb_map (f : P → P') (π : P' → Γ) : (T.map f).acceptProb π = T.acceptProb (π ∘ f) :=
  rfl

/-- The conjunction of two tests accepts at most as often as the first one. -/
theorem acceptProb_and_le_left [Fintype R'] [Nonempty R'] (T' : LocalTest P R' Q' Γ)
    (π : P → Γ) : (T.and T').acceptProb π ≤ T.acceptProb π := by
  classical
  simp only [acceptProb, Fintype.expect_prod_type, passes_and]
  calc 𝔼 r, 𝔼 r', (if T.Passes π r ∧ T'.Passes π r' then (1 : ℝ) else 0)
      ≤ 𝔼 r, 𝔼 _r' : R', (if T.Passes π r then (1 : ℝ) else 0) := by
        gcongr with r _ r' _
        split_ifs with h h' <;> first | exact absurd h.1 h' | norm_num
    _ = _ := by simp only [Fintype.expect_const]

/-- The conjunction of two tests accepts at most as often as the second one. -/
theorem acceptProb_and_le_right [Fintype R'] [Nonempty R] (T' : LocalTest P R' Q' Γ)
    (π : P → Γ) : (T.and T').acceptProb π ≤ T'.acceptProb π := by
  classical
  simp only [acceptProb, Fintype.expect_prod_type, passes_and]
  calc 𝔼 r, 𝔼 r', (if T.Passes π r ∧ T'.Passes π r' then (1 : ℝ) else 0)
      ≤ 𝔼 _r : R, 𝔼 r', (if T'.Passes π r' then (1 : ℝ) else 0) := by
        gcongr with r _ r' _
        split_ifs with h h' <;> first | exact absurd h.2 h' | norm_num
    _ = _ := by simp only [Fintype.expect_const]

/-- The acceptance probability of a random test of a family is the average of the acceptance
probabilities of its members. -/
theorem acceptProb_mix [Fintype E] (T : E → LocalTest P R Q Γ) (π : P → Γ) :
    (mix T).acceptProb π = 𝔼 e, (T e).acceptProb π := by
  classical
  simp only [acceptProb, Fintype.expect_prod_type, passes_mix]

/-- Selecting one of `|E|` checks loses at most a factor `|E|` in rejection compared with any
test implied by passing all the checks on the same random string. The checks may share coins;
independence is unnecessary. -/
theorem one_sub_acceptProb_le_card_mul_one_sub_acceptProb_mix
    [Nonempty R] [Fintype E] [Nonempty E] (S : LocalTest P R Q' Γ)
    (T : E → LocalTest P R Q Γ) (π : P → Γ)
    (h : ∀ r, (∀ e, (T e).Passes π r) → S.Passes π r) :
    1 - S.acceptProb π ≤ Fintype.card E * (1 - (mix T).acceptProb π) := by
  classical
  have hpoint (r : R) :
      (1 - if S.Passes π r then (1 : ℝ) else 0) ≤
        ∑ e, (1 - if (T e).Passes π r then (1 : ℝ) else 0) := by
    by_cases hs : S.Passes π r
    · simp only [ite_eq_left hs, sub_self]
      exact sum_nonneg fun e _ ↦ by split_ifs <;> norm_num
    · obtain ⟨e, he⟩ := not_forall.1 (mt (h r) hs)
      simpa only [ite_eq_right hs, ite_eq_right he, sub_zero] using
        (single_le_sum (f := fun e ↦ (1 - if (T e).Passes π r then (1 : ℝ) else 0))
          (fun e _ ↦ by split_ifs <;> norm_num) (mem_univ e))
  have hmean := expect_le_expect fun r (_ : r ∈ (univ : Finset R)) ↦ hpoint r
  simp only [expect_sum_comm, expect_sub_distrib, Fintype.expect_const] at hmean
  change 1 - S.acceptProb π ≤ ∑ e, (1 - (T e).acceptProb π) at hmean
  have hE : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    1 - S.acceptProb π ≤ ∑ e, (1 - (T e).acceptProb π) := hmean
    _ = Fintype.card E * (1 - (mix T).acceptProb π) := by
      rw [acceptProb_mix, Fintype.expect_eq_sum_div_card, mul_sub,
        mul_div_cancel₀ _ hE, sum_sub_distrib]
      simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]

end Prob

/-! ### The constraint graph of a local test -/

variable (T)

/-- The **constraint graph of a local test** [Arora and Barak, Chapter 22][AroraBarak09]. Its
vertices are the positions, labelled by a symbol, and the random strings, labelled by the symbols
the test is to read. For every random string `r` and query `i`, the edge `(r, i)` goes from the
vertex of `r` to the position `query r i`, and holds when the symbols claimed at `r` make the test
accept and the `i`-th of them is the symbol of the position. The alphabet `Γ × (Q → Γ)` serves both
kinds of vertices: positions use the first component and random strings the second one. -/
def toConstraintGraph : ConstraintGraph (P ⊕ R) (R × Q) (Γ × (Q → Γ)) where
  src x := .inr x.1
  dst x := .inl (T.query x.1 x.2)
  rel x a b := T.Accepts x.1 a.2 ∧ a.2 x.2 = b.1

/-- The proof carried by a labelling of the constraint graph of a test: the symbols of the
positions. -/
def proofOf (A : P ⊕ R → Γ × (Q → Γ)) (p : P) : Γ :=
  (A (.inl p)).1

variable {T}

/-- The edge `(r, i)` holds when the symbols claimed at `r` make the test accept and the `i`-th of
them is the symbol of the position read. -/
theorem satisfies_toConstraintGraph {A : P ⊕ R → Γ × (Q → Γ)} {x : R × Q} :
    T.toConstraintGraph.Satisfies A x ↔
      T.Accepts x.1 (A (.inr x.1)).2 ∧ (A (.inr x.1)).2 x.2 = proofOf A (T.query x.1 x.2) :=
  Iff.rfl

/-- A random string on which the test does not pass the proof carried by a labelling has a
violated edge. -/
theorem exists_not_satisfies_of_not_passes [Nonempty Q] {A : P ⊕ R → Γ × (Q → Γ)} {r : R}
    (h : ¬ T.Passes (proofOf A) r) : ∃ i, ¬ T.toConstraintGraph.Satisfies A (r, i) := by
  by_contra! hall
  have hans : (A (.inr r)).2 = fun i ↦ proofOf A (T.query r i) :=
    funext fun i ↦ (satisfies_toConstraintGraph.1 (hall i)).2
  have hacc := (satisfies_toConstraintGraph.1 (hall (Classical.arbitrary Q))).1
  rw [hans] at hacc
  exact h hacc

section Count

variable [Fintype R] [Fintype Q]

open Classical in
/-- **Soundness of the constraint graph of a test**, counting version: the random strings on which
the test does not pass the proof carried by a labelling are at most as many as the edges the
labelling violates. -/
theorem card_filter_not_passes_le_card_unsatEdges [Nonempty Q] (A : P ⊕ R → Γ × (Q → Γ)) :
    #{r | ¬ T.Passes (proofOf A) r} ≤ #(T.toConstraintGraph.unsatEdges A) := by
  classical
  choose! i hi using fun r (h : ¬ T.Passes (proofOf A) r) ↦ exists_not_satisfies_of_not_passes h
  refine card_le_card_of_injOn (fun r ↦ (r, i r)) (fun r hr ↦ ?_) fun r _ r' _ h ↦
    congrArg Prod.fst h
  simp only [coe_filter, mem_univ, true_and] at hr
  simpa using hi r hr

/-- **Soundness of the constraint graph of a test**: a labelling violates a proportion of the edges
at least the rejection probability of the test on the proof it carries, divided by the number of
queries. -/
theorem one_sub_acceptProb_le_card_mul_unsatFrac [Nonempty R] [Nonempty Q]
    (A : P ⊕ R → Γ × (Q → Γ)) :
    1 - T.acceptProb (proofOf A) ≤ Fintype.card Q * T.toConstraintGraph.unsatFrac A := by
  classical
  have hR : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have hQ : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
  have h : (#{r | ¬ T.Passes (proofOf A) r} : ℝ) ≤ #(T.toConstraintGraph.unsatEdges A) := by
    exact_mod_cast card_filter_not_passes_le_card_unsatEdges A
  rw [one_sub_acceptProb, ConstraintGraph.unsatFrac, Fintype.card_prod, Nat.cast_mul,
    mul_div_assoc', mul_comm (Fintype.card R : ℝ), mul_div_mul_left _ _ hQ.ne']
  gcongr

end Count

variable (T) in
/-- The labelling of the constraint graph of a test by a proof `π`: every position carries its
symbol, and every random string the symbols of `π` that the test reads on it. The symbol `γ` fills
the components that the constraints do not read. -/
def labellingOf (π : P → Γ) (γ : Γ) : P ⊕ R → Γ × (Q → Γ) :=
  Sum.elim (fun p ↦ (π p, fun _ ↦ γ)) fun r ↦ (γ, fun i ↦ π (T.query r i))

/-- The labelling of the constraint graph by a proof carries that proof. -/
@[simp]
theorem proofOf_labellingOf (π : P → Γ) (γ : Γ) : proofOf (T.labellingOf π γ) = π :=
  rfl

/-- The labelling by a proof satisfies the edges of the random strings on which the test passes
that proof. -/
theorem satisfies_labellingOf {π : P → Γ} {γ : Γ} {x : R × Q} (h : T.Passes π x.1) :
    T.toConstraintGraph.Satisfies (T.labellingOf π γ) x :=
  ⟨h, rfl⟩

/-- When the claimed answers are read from a proof, every edge at a random string is violated
exactly when the test rejects. The violated fraction is therefore the rejection probability. -/
theorem unsatFrac_labellingOf [Fintype R] [Fintype Q] [Nonempty R] [Nonempty Q]
    (π : P → Γ) (γ : Γ) :
    T.toConstraintGraph.unsatFrac (T.labellingOf π γ) = 1 - T.acceptProb π := by
  classical
  rw [← ConstraintGraph.expect_mem_unsatEdges, Fintype.expect_prod_type]
  simp only [ConstraintGraph.mem_unsatEdges, ConstraintGraph.Satisfies, toConstraintGraph,
    labellingOf, Sum.elim_inl, Sum.elim_inr, and_true, Fintype.expect_const]
  rw [acceptProb]
  conv_rhs => rw [← Fintype.expect_const (ι := R) (1 : ℝ), ← expect_sub_distrib]
  exact expect_congr rfl fun r _ ↦ by
    simp only [Fintype.expect_const]
    change (if ¬ T.Passes π r then (1 : ℝ) else 0) = 1 - if T.Passes π r then 1 else 0
    split_ifs <;> norm_num

/-- **Completeness of the constraint graph of a test**: if the test passes the proof `π` on every
random string, the labelling by `π` satisfies the constraint graph. -/
theorem satisfiable_toConstraintGraph [Nonempty Γ] {π : P → Γ} (h : ∀ r, T.Passes π r) :
    T.toConstraintGraph.Satisfiable :=
  ⟨T.labellingOf π (Classical.arbitrary Γ), fun x ↦ satisfies_labellingOf (h x.1)⟩

end LocalTest

end Cslib.PCP
