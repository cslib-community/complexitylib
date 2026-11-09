/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.TwoBoundary
public import CslibFrontier.Logics.Propositional.CNF.ExactOne
public import CslibFrontier.Foundations.LinearAlgebra.RowSelection
public import Mathlib.Data.Finset.Card
import Mathlib.Order.Prod.Lex.Basic

/-!
# Exact-one systems and ordinary counting queries

Actual clause compilation for [ChenJiangZhu2027], Theorem 1.2 and Section 5.3:
coverage is a disjunction of signed literals, and deduplicated pairwise exclusions
use only original variables. Every declared variable remains counted.

## Main definitions

* `signedClause`: the existing signed XSAT syntax with each scope variable once.
* `query`, `sideQuery`: ordinary unweighted CNFs with substituted path endpoints.

## Main results

* `exists_queries_of_two_rational_solutions`: rank-derived queries for the general signed
  system with binary side constraints, with at most $2r-2$ declared variables.
* `equation_iff`, `holds_iff_evalOne`: rational and existing XSAT semantics.
* `sideQuery_width`, `sideQuery_length`: width three and at most $13r^2$ clauses.
* `count_eq_zero_of_inconsistent`, `count_le_one_of_full_span`: direct-case facts.
* `coverScopes_iff`: parsimonious indexed Exact Cover transposition.

The scope/polarity form enforces the paper's distinct-variable convention and is
proved equivalent to the existing occurrence-sensitive `Clause.evalOne`. Counts
here include all declared bits; `CNF.oneModelCount` counts occurring variables instead.
The constructions below are finite-table constructions; no native polynomial-bit-time
elimination or external fixed-width counting runtime is asserted.

## References

* [ChenJiangZhu2027], Theorems 1.2 and 5.2, PDF pp. 5 and 15–17.
-/

public section

namespace Cslib.Logic.PL.ExactOne

variable {V I : Type*} [Fintype V] [LinearOrder V]

/-- Exactly one variable in a scope has its specified polarity. -/
@[expose] def Holds (S : Finset V) (p x : V → Bool) : Prop :=
  ∃ v ∈ S, x v = p v ∧ ∀ w ∈ S, x w = p w → w = v

instance (S : Finset V) (p x : V → Bool) : Decidable (Holds S p x) :=
  inferInstanceAs (Decidable (∃ v ∈ S, x v = p v ∧ ∀ w ∈ S, x w = p w → w = v))

omit [Fintype V] [LinearOrder V] in
/-- Preserve a local signed equation under an injective scope embedding. -/
theorem holds_map {W : Type*} (e : W ↪ V) (s : Finset W) (p : W → Bool) (x : V → Bool) :
    Holds (s.map e) (Function.extend e p (fun _ => false)) x ↔
      Holds s p (x ∘ e) := by
  classical
  simp only [Holds]
  constructor
  · rintro ⟨v, hv, hp, hu⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
    rw [e.injective.extend_apply] at hp
    refine ⟨i, hi, hp, fun j hj hpj => e.injective (hu (e j) ?_ ?_)⟩
    · exact Finset.mem_map.mpr ⟨j, hj, rfl⟩
    · simpa only [e.injective.extend_apply, Function.comp_apply] using hpj
  · rintro ⟨i, hi, hp, hu⟩
    refine ⟨e i, Finset.mem_map.mpr ⟨i, hi, rfl⟩, ?_, ?_⟩
    · simpa only [e.injective.extend_apply, Function.comp_apply] using hp
    · intro v hv hpv
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hv
      rw [e.injective.extend_apply] at hpv
      exact congrArg e (hu j hj hpv)

/-- A scope becomes a disjunction of singleton terms, with no auxiliary gates. -/
@[expose] def coverage (S : Finset V) (p : V → Bool) : DNF V :=
  (S.sort (· ≤ ·)).map fun v => [(v, p v)]

omit [Fintype V] in
/-- Coverage is precisely the existence of a true literal in the scope. -/
theorem coverage_eval (S : Finset V) (p x : V → Bool) :
    DNF.eval x (coverage S p) = true ↔ ∃ v ∈ S, x v = p v := by
  simp [coverage, DNF.eval, Term.eval, Literal.eval]

/-- Pairs of signed literals that must not both hold in any retained row. -/
@[expose] def forbidden [Fintype I] (S : I → Finset V) (p : I → V → Bool) :
    Finset ((V × Bool) × (V × Bool)) :=
  Finset.univ.filter fun ((v, a), (w, b)) =>
    v ≠ w ∧ ∃ j, v ∈ S j ∧ w ∈ S j ∧ p j v = a ∧ p j w = b

/-- Deduplicated binary exclusions; the enumeration has at most `4 * |V|²` entries. -/
@[expose] def exclusions [Fintype I] (S : I → Finset V) (p : I → V → Bool) : CNF V :=
  letI : LinearOrder (V × Bool) := LinearOrder.lift' toLex (fun _ _ h => h)
  let pairOrder : LinearOrder ((V × Bool) × (V × Bool)) :=
    LinearOrder.lift' toLex (fun _ _ h => h)
  ((forbidden S p).sort (@LE.le _ pairOrder.toLE)).map
    fun ((v, a), (w, b)) => [(v, !a), (w, !b)]

/-- The exclusions prohibit exactly the distinct simultaneously true row literals. -/
theorem exclusions_eval [Fintype I] (S : I → Finset V) (p : I → V → Bool)
    (x : V → Bool) :
    (exclusions S p).eval x = true ↔
      ∀ j v, v ∈ S j → ∀ w, w ∈ S j → x v = p j v → x w = p j w → v = w := by
  simp only [CNF.eval_eq_true_iff, exclusions, List.mem_map, Finset.mem_sort]
  constructor
  · intro h j v hv w hw hxv hxw
    by_contra hne
    have hm : ((v, p j v), (w, p j w)) ∈ forbidden S p := by
      simp only [forbidden, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hne, j, hv, hw, rfl, rfl⟩
    have hh := h _ ⟨_, hm, rfl⟩
    simp [Clause.eval, Literal.eval, hxv, hxw] at hh
  · intro h c hc
    obtain ⟨⟨⟨v, a⟩, ⟨w, b⟩⟩, hm, rfl⟩ := hc
    simp only [forbidden, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    obtain ⟨hne, j, hv, hw, ha, hb⟩ := hm
    have hn : ¬ (x v = a ∧ x w = b) := by
      rintro ⟨hxv, hxw⟩
      exact hne (h j v hv w hw (hxv.trans ha.symm) (hxw.trans hb.symm))
    cases hxv : x v <;> cases hxw : x w <;> cases a <;> cases b <;>
      simp_all [Clause.eval, Literal.eval]

/-- The compiled bounded CNF and wide coverages preserve every original solution. -/
theorem compilation_iff [Fintype I] (S : I → Finset V) (p : I → V → Bool)
    (x : V → Bool) :
    (exclusions S p).eval x = true ∧ (∀ j, DNF.eval x (coverage (S j) (p j)) = true) ↔
      ∀ j, Holds (S j) (p j) x := by
  simp only [exclusions_eval, coverage_eval, Holds]
  constructor
  · rintro ⟨he, hc⟩ j
    obtain ⟨v, hv, hxv⟩ := hc j
    exact ⟨v, hv, hxv, fun w hw hxw => he j w hw v hv hxw hxv⟩
  · intro h
    constructor
    · intro j v hv w hw hxv hxw
      obtain ⟨u, _, _, hu⟩ := h j
      exact (hu v hv hxv).trans (hu w hw hxw).symm
    · intro j
      obtain ⟨v, hv, hxv, _⟩ := h j
      exact ⟨v, hv, hxv⟩

/-- Each exclusion has width two. -/
theorem exclusions_width [Fintype I] (S : I → Finset V) (p : I → V → Bool)
    (c : Clause V) (hc : c ∈ exclusions S p) : c.length ≤ 2 := by
  obtain ⟨⟨⟨v, a⟩, ⟨w, b⟩⟩, _, rfl⟩ := List.mem_map.mp hc
  simp

/-- Deduplication bounds exclusions independently of the number of original rows. -/
theorem exclusions_length [Fintype I] (S : I → Finset V) (p : I → V → Bool) :
    (exclusions S p).length ≤ 4 * Fintype.card V ^ 2 := by
  have h := Finset.card_le_card (Finset.filter_subset
    (fun ((v, a), (w, b)) => v ≠ w ∧ ∃ j, v ∈ S j ∧ w ∈ S j ∧ p j v = a ∧ p j w = b)
    (Finset.univ : Finset ((V × Bool) × (V × Bool))))
  simpa [exclusions, forbidden, Fintype.card_prod, pow_two, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc] using h

/-- An actual pair of ordinary CNFs, determined before either count is requested. -/
@[expose] def query {k : ℕ} (S : Fin (k + 1) → Finset V)
    (p : Fin (k + 1) → V → Bool) (β : Bool) : CNF (V ⊕ Fin k) :=
  TwoBoundary.query (exclusions S p) k (fun j => coverage (S j) (p j)) β

/-- Exact unweighted counts for the compiled signed system, retaining unused variables. -/
theorem counting_identity {k : ℕ} (S : Fin (k + 1) → Finset V)
    (p : Fin (k + 1) → V → Bool) :
    Fintype.card {x : V → Bool // ∀ j, Holds (S j) (p j) x} =
      Fintype.card {x : V ⊕ Fin k → Bool // (query S p false).eval x = true} -
      Fintype.card {x : V ⊕ Fin k → Bool // (query S p true).eval x = true} := by
  classical
  unfold query
  rw [← TwoBoundary.counting_identity]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight fun x => (compilation_iff S p x).symm

/-- Both constructed queries have width at most three. -/
theorem query_width {k : ℕ} (S : Fin (k + 1) → Finset V)
    (p : Fin (k + 1) → V → Bool) (β : Bool) (c : Clause (V ⊕ Fin k))
    (hc : c ∈ query S p β) : c.length ≤ 3 := by
  apply TwoBoundary.query_width _ _ 2 1 (exclusions_width S p) _ β c hc
  intro j t ht
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp ht
  simp

/-- The total clause budget is quadratic when the selected row count is below `|V|`. -/
theorem query_length {k : ℕ} (S : Fin (k + 1) → Finset V)
    (p : Fin (k + 1) → V → Bool) (hk : k + 1 < Fintype.card V) (β : Bool) :
    (query S p β).length ≤ 6 * Fintype.card V ^ 2 := by
  have h := TwoBoundary.query_length (exclusions S p) (fun j => coverage (S j) (p j)) β
  have hs : (∑ j : Fin (k + 1), (coverage (S j) (p j)).length) ≤
      (k + 1) * Fintype.card V := by
    calc
      _ ≤ ∑ _j : Fin (k + 1), Fintype.card V := Finset.sum_le_sum fun j _ => by
        simpa [coverage] using (S j).card_le_univ
      _ = _ := by simp
  have he := exclusions_length S p
  have hm := Nat.mul_le_mul_right (Fintype.card V) (Nat.le_of_lt hk)
  change (TwoBoundary.query (exclusions S p) k (fun j => coverage (S j) (p j)) β).length ≤ _
  nlinarith [sq_nonneg (Fintype.card V : ℤ)]

omit [LinearOrder V] in
/-- The actual declared variable type satisfies the sharp path budget. -/
theorem query_variables {k : ℕ} (hk : k + 1 < Fintype.card V) :
    Fintype.card (V ⊕ Fin k) = Fintype.card V + k ∧
      Fintype.card (V ⊕ Fin k) ≤ 2 * Fintype.card V - 2 := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  constructor
  · trivial
  · omega

/-- All literals on the declared variables, enumerated without repetition. -/
@[expose] def literals : List (Literal V) :=
  ((Finset.univ : Finset V).sort (· ≤ ·)).flatMap fun v => [(v, false), (v, true)]

private theorem mem_literals (l : Literal V) : l ∈ literals (V := V) := by
  rcases l with ⟨v, b⟩
  cases b <;> simp [literals]

private theorem literals_length : (literals (V := V)).length = 2 * Fintype.card V := by
  simp [literals, List.length_flatMap, List.map_const', Nat.mul_comm]

/-- Exhaustive syntax universe for clauses of width at most two, including the empty clause. -/
@[expose] def binaryUniverse : CNF V :=
  [[]] ++ (literals (V := V)).map (fun l => [l]) ++
    (literals (V := V)).flatMap fun l => (literals (V := V)).map fun m => [l, m]

/-- Every clause of width at most two occurs in the finite syntax universe. -/
theorem mem_binaryUniverse (c : Clause V) (hc : c.length ≤ 2) :
    c ∈ binaryUniverse (V := V) := by
  cases c with
  | nil => simp [binaryUniverse]
  | cons l c =>
    cases c with
    | nil => simp [binaryUniverse, mem_literals]
    | cons m c =>
      have hc' : c = [] := by simpa using hc
      subst c
      simp [binaryUniverse, mem_literals]

private theorem binaryUniverse_length :
    (binaryUniverse (V := V)).length =
      1 + 2 * Fintype.card V + 4 * Fintype.card V ^ 2 := by
  simp [binaryUniverse, List.length_flatMap, List.map_const', literals_length,
    List.sum_replicate, pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
    Nat.add_comm, Nat.add_assoc]

/-- The syntax universe contains only clauses of width at most two. -/
theorem binaryUniverse_width (c : Clause V) (hc : c ∈ binaryUniverse (V := V)) :
    c.length ≤ 2 := by
  simp only [binaryUniverse, List.mem_append, List.mem_singleton, List.mem_map,
    List.mem_flatMap] at hc
  rcases hc with ((rfl | ⟨l, _, rfl⟩) | ⟨l, _, m, _, rfl⟩) <;> simp

/-- Removing duplicate binary clauses gives a global quadratic budget, even for
arbitrarily many input side constraints. Empty and repeated-literal clauses are retained. -/
theorem dedup_binary_length (B : CNF V) (hb : ∀ c ∈ B, c.length ≤ 2) :
    B.dedup.length ≤ 1 + 2 * Fintype.card V + 4 * Fintype.card V ^ 2 := by
  have hs : B.toFinset ⊆ (binaryUniverse (V := V)).toFinset := by
    intro c hc
    exact List.mem_toFinset.mpr (mem_binaryUniverse c (hb c (List.mem_toFinset.mp hc)))
  calc
    _ = B.toFinset.card := (List.toFinset_card_of_nodup (List.nodup_dedup B)).symm.trans
      (by simp)
    _ ≤ (binaryUniverse (V := V)).toFinset.card := Finset.card_le_card hs
    _ ≤ (binaryUniverse (V := V)).length := List.toFinset_card_le _
    _ = _ := binaryUniverse_length

/-- Binary side constraints and retained rows are compiled together on the same columns. -/
@[expose] def sideQuery {k : ℕ} (B : CNF V) (S : Fin (k + 1) → Finset V)
    (p : Fin (k + 1) → V → Bool) (β : Bool) : CNF (V ⊕ Fin k) :=
  TwoBoundary.query (B.dedup ++ exclusions S p) k (fun j => coverage (S j) (p j)) β

/-- Exact subtraction continues to count original solutions with binary side constraints. -/
theorem side_counting_identity {k : ℕ} (B : CNF V) (S : Fin (k + 1) → Finset V)
    (p : Fin (k + 1) → V → Bool) :
    Fintype.card {x : V → Bool // B.eval x = true ∧ ∀ j, Holds (S j) (p j) x} =
      Fintype.card {x : V ⊕ Fin k → Bool // (sideQuery B S p false).eval x = true} -
      Fintype.card {x : V ⊕ Fin k → Bool // (sideQuery B S p true).eval x = true} := by
  classical
  unfold sideQuery
  rw [← TwoBoundary.counting_identity]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  have hd : CNF.eval x B.dedup = B.eval x := by
    apply Bool.eq_iff_iff.mpr
    simp [CNF.eval_eq_true_iff]
  simp only [CNF.eval_append, Bool.and_eq_true, hd, and_assoc, compilation_iff]

/-- The side-constraint queries are still ordinary 3-CNFs. -/
theorem sideQuery_width {k : ℕ} (B : CNF V) (hb : ∀ c ∈ B, c.length ≤ 2)
    (S : Fin (k + 1) → Finset V) (p : Fin (k + 1) → V → Bool)
    (β : Bool) (c : Clause (V ⊕ Fin k)) (hc : c ∈ sideQuery B S p β) : c.length ≤ 3 := by
  apply TwoBoundary.query_width _ _ 2 1 _ _ β c hc
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hb a (List.mem_dedup.mp ha)
    · exact exclusions_width S p a ha
  · intro j t ht
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp ht
    simp

/-- A global quadratic clause budget includes deduplicated binary side constraints. -/
theorem sideQuery_length {k : ℕ} (B : CNF V) (hb : ∀ c ∈ B, c.length ≤ 2)
    (S : Fin (k + 1) → Finset V) (p : Fin (k + 1) → V → Bool)
    (hk : k + 1 < Fintype.card V) (β : Bool) :
    (sideQuery B S p β).length ≤ 13 * Fintype.card V ^ 2 := by
  have h := TwoBoundary.query_length (B.dedup ++ exclusions S p)
    (fun j => coverage (S j) (p j)) β
  have hs : (∑ j : Fin (k + 1), (coverage (S j) (p j)).length) ≤
      (k + 1) * Fintype.card V := by
    calc
      _ ≤ ∑ _j : Fin (k + 1), Fintype.card V := Finset.sum_le_sum fun j _ => by
        simpa [coverage] using (S j).card_le_univ
      _ = _ := by simp
  have he := exclusions_length S p
  have hd := dedup_binary_length B hb
  have hm := Nat.mul_le_mul_right (Fintype.card V) (Nat.le_of_lt hk)
  simp only [List.length_append] at h
  change (TwoBoundary.query _ k _ β).length ≤ _
  nlinarith [sq_nonneg (Fintype.card V : ℤ)]

/-- Rational embedding of a declared Boolean assignment. -/
@[expose] def rationalPoint (x : V → Bool) (v : V) : ℚ := if x v then 1 else 0

/-- Signed coefficient row, with zero outside its scope. -/
@[expose] def coefficients (S : Finset V) (p : V → Bool) (v : V) : ℚ :=
  if v ∈ S then if p v then 1 else -1 else 0

/-- Moving the negative literals' constants to the right-hand side. -/
@[expose] def rhs (S : Finset V) (p : V → Bool) : ℚ :=
  1 - ((S.filter fun v => p v = false).card : ℚ)

omit [Fintype V] [LinearOrder V] in
/-- Exact-one semantics can equivalently be read as a singleton true-literal set. -/
theorem holds_iff_card (S : Finset V) (p x : V → Bool) :
    Holds S p x ↔ (S.filter fun v => x v = p v).card = 1 := by
  classical
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨v, hv, hxv, hu⟩
    refine ⟨v, Finset.ext fun w => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => hu w h.1 h.2, fun h => h ▸ ⟨hv, hxv⟩⟩
  · rintro ⟨v, hv⟩
    have hm : v ∈ S.filter fun w => x w = p w := by rw [hv]; simp
    refine ⟨v, (Finset.mem_filter.mp hm).1, (Finset.mem_filter.mp hm).2, ?_⟩
    intro w hw hxw
    have : w ∈ S.filter fun w => x w = p w := Finset.mem_filter.mpr ⟨hw, hxw⟩
    simpa only [hv, Finset.mem_singleton] using this

/-- The original signed clause, using the library's occurrence-sensitive XSAT syntax.
A scope is a set, so each underlying variable occurs once. -/
@[expose] def signedClause (S : Finset V) (p : V → Bool) : Clause V :=
  (S.sort (· ≤ ·)).map fun v => (v, p v)

omit [Fintype V] in
/-- The scope/polarity presentation agrees with the existing occurrence-counted
exact-one API. It specializes that API to the paper's distinct-variable convention. -/
theorem holds_iff_evalOne (S : Finset V) (p x : V → Bool) :
    Holds S p x ↔ (signedClause S p).evalOne x = true := by
  rw [holds_iff_card, Clause.evalOne_eq_true_iff]
  have h := (Finset.sort_nodup S (· ≤ ·)).card_eq_countP (P := fun v => x v = p v)
  simpa [signedClause, List.countP_map, Literal.eval, Function.comp_def,
    Bool.beq_eq_decide_eq] using
    congrArg (fun n : ℕ => n = 1) h

/-- The signed rational equation is derived from literal truth, rather than assumed. -/
theorem equation_iff (S : Finset V) (p x : V → Bool) :
    dotProduct (coefficients S p) (rationalPoint x) = rhs S p ↔ Holds S p x := by
  classical
  have he (v : V) : coefficients S p v * rationalPoint x v =
      (if v ∈ S ∧ x v = p v then (1 : ℚ) else 0) -
      (if v ∈ S ∧ p v = false then (1 : ℚ) else 0) := by
    by_cases hv : v ∈ S <;> cases hp : p v <;> cases hx : x v <;>
      simp [coefficients, rationalPoint, hv, hp, hx]
  have hd : dotProduct (coefficients S p) (rationalPoint x) =
      ((S.filter fun v => x v = p v).card : ℚ) -
      ((S.filter fun v => p v = false).card : ℚ) := by
    simp only [dotProduct, he, Finset.sum_sub_distrib]
    congr 1 <;> simp only [Finset.sum_boole]
    all_goals congr 2; ext v; simp
  rw [hd, rhs, sub_left_inj, holds_iff_card]
  exact_mod_cast (Iff.rfl : (S.filter fun v => x v = p v).card = 1 ↔
    (S.filter fun v => x v = p v).card = 1)

omit [Fintype V] [LinearOrder V] in
/-- The Boolean-to-rational embedding loses no declared bits. -/
theorem rationalPoint_injective : Function.Injective (rationalPoint (V := V)) := by
  intro x y h
  funext v
  have hv := congrFun h v
  cases hx : x v <;> cases hy : y v <;> simp_all [rationalPoint]

/-- Original signed rows are selected by rational rank, then compiled into actual
ordinary queries. No queries or rank-reduced subsystem occur among the hypotheses.
The two distinct rational witnesses exclude the inconsistent/full-rank direct cases;
a nonempty input family excludes the empty-family direct case. This theorem is
an existence/correctness result, not a polynomial-time row-selection program. -/
theorem exists_queries_of_two_rational_solutions [Fintype I] [Nonempty I]
    (B : CNF V) (hb : ∀ c ∈ B, c.length ≤ 2) (S : I → Finset V) (p : I → V → Bool) (x z : V → ℚ)
    (hx : ∀ i, dotProduct (coefficients (S i) (p i)) x = rhs (S i) (p i))
    (hz : ∀ i, dotProduct (coefficients (S i) (p i)) z = rhs (S i) (p i)) (hne : x ≠ z) :
    ∃ k : ℕ, ∃ Q : Bool → CNF (V ⊕ Fin k),
      k + 1 < Fintype.card V ∧
      k + 1 = Module.finrank ℚ (Submodule.span ℚ (Set.range fun i => coefficients (S i) (p i))) ∧
      Fintype.card {u : V → Bool // B.eval u = true ∧ ∀ i, Holds (S i) (p i) u} =
        Fintype.card {u : V ⊕ Fin k → Bool // (Q false).eval u = true} -
        Fintype.card {u : V ⊕ Fin k → Bool // (Q true).eval u = true} ∧
      (∀ β c, c ∈ Q β → c.length ≤ 3) ∧
      (∀ β, (Q β).length ≤ 13 * Fintype.card V ^ 2) ∧
      (∀ β, Fintype.card {u : V ⊕ Fin k → Bool // (Q β).eval u = true} ≤
        2 ^ (2 * Fintype.card V - 2)) ∧
      Fintype.card (V ⊕ Fin k) ≤ 2 * Fintype.card V - 2 := by
  classical
  obtain ⟨s, hs, hrank, hsol⟩ := LinearSystem.exists_original_rows_of_two_solutions
    (fun i => coefficients (S i) (p i)) (fun i => rhs (S i) (p i))
    x z hx hz hne
  have hpos : s.card ≠ 0 := by
    intro hempty
    have hall (u : V → Bool) : ∀ i, Holds (S i) (p i) u := by
      have h := (hsol (rationalPoint u)).mp (by simp [Finset.card_eq_zero.mp hempty])
      exact fun i => (equation_iff _ _ _).mp (h i)
    let i : I := Classical.choice inferInstance
    obtain ⟨v, _, hv, _⟩ := hall (fun v => !(p i v)) i
    simp at hv
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  let e : Fin (k + 1) ≃ s := (finCongr (by simpa using hk.symm)).trans (Fintype.equivFin s).symm
  let T : Fin (k + 1) → Finset V := fun j => S (e j)
  let q : Fin (k + 1) → V → Bool := fun j => p (e j)
  have hequiv (u : V → Bool) : (∀ j, Holds (T j) (q j) u) ↔
      ∀ i, Holds (S i) (p i) u := by
    constructor
    · intro hu
      have hsystem : ∀ i, dotProduct (coefficients (S i) (p i)) (rationalPoint u) =
          rhs (S i) (p i) := (hsol (rationalPoint u)).mp (by
        intro i hi
        obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
        have h := hu j
        change Holds (S (e j)) (p (e j)) u at h
        rw [hj] at h
        exact (equation_iff _ _ _).mpr h)
      exact fun i => (equation_iff _ _ _).mp (hsystem i)
    · intro hu j
      exact hu (e j)
  have hcount : Fintype.card {u : V → Bool // B.eval u = true ∧ ∀ i, Holds (S i) (p i) u} =
      Fintype.card {u : V → Bool // B.eval u = true ∧ ∀ j, Holds (T j) (q j) u} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun u => and_congr_right fun _ => (hequiv u).symm)
  have hbound : k + 1 < Fintype.card V := by omega
  refine ⟨k, sideQuery B T q, hbound, ?_, ?_, sideQuery_width B hb T q,
    sideQuery_length B hb T q hbound, ?_, (query_variables hbound).2⟩
  · omega
  · rw [hcount]
    exact side_counting_identity B T q
  · intro β
    calc
      _ ≤ Fintype.card (V ⊕ Fin k → Bool) := Fintype.card_subtype_le _
      _ = 2 ^ Fintype.card (V ⊕ Fin k) := by simp
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (query_variables hbound).2

/-- An empty exact-one scope forces zero solutions, even with side constraints. -/
theorem count_eq_zero_of_empty_scope [Fintype I] (B : CNF V)
    (S : I → Finset V) (p : I → V → Bool) (i : I) (hi : S i = ∅) :
    Fintype.card {u : V → Bool // B.eval u = true ∧ ∀ j, Holds (S j) (p j) u} = 0 := by
  classical
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun u => ?_⟩
  obtain ⟨v, hv, _⟩ := u.property.2 i
  simp [hi] at hv

/-- Rational inconsistency is a direct zero-count branch for signed XSAT. -/
theorem count_eq_zero_of_inconsistent [Fintype I] (B : CNF V)
    (S : I → Finset V) (p : I → V → Bool)
    (hi : ¬ ∃ z : V → ℚ, ∀ i, dotProduct (coefficients (S i) (p i)) z = rhs (S i) (p i)) :
    Fintype.card {u : V → Bool // B.eval u = true ∧ ∀ j, Holds (S j) (p j) u} = 0 := by
  classical
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun u => hi ⟨rationalPoint u.val, ?_⟩⟩
  exact fun i => (equation_iff _ _ _).mpr (u.property.2 i)

/-- Full column span gives at most one Boolean candidate, including the side constraints. -/
theorem count_le_one_of_full_span [Fintype I] (B : CNF V)
    (S : I → Finset V) (p : I → V → Bool)
    (hfull : Submodule.span ℚ (Set.range fun i => coefficients (S i) (p i)) = ⊤) :
    Fintype.card {u : V → Bool // B.eval u = true ∧ ∀ j, Holds (S j) (p j) u} ≤ 1 := by
  classical
  let : Subsingleton {u : V → Bool // B.eval u = true ∧ ∀ j, Holds (S j) (p j) u} :=
    ⟨fun u v => Subtype.ext (rationalPoint_injective
      (LinearSystem.solution_eq_of_span_eq_top _ _ hfull
        (fun i => (equation_iff _ _ _).mpr (u.property.2 i))
        (fun i => (equation_iff _ _ _).mpr (v.property.2 i))))⟩
  exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance

/-- Read a rational candidate as bits; the separate Boolean test rejects other entries. -/
@[expose] def candidateBits (z : V → ℚ) (v : V) : Bool := decide (z v = 1)

/-- Direct evaluation of the sole rational candidate, including binary side constraints. -/
@[expose] def fullRankCount (B : CNF V) (z : V → ℚ) : ℕ :=
  if (∀ v, z v = 0 ∨ z v = 1) ∧ B.eval (candidateBits z) = true then 1 else 0

omit [Fintype V] [LinearOrder V] in
private theorem rational_candidate (z : V → ℚ) (hz : ∀ v, z v = 0 ∨ z v = 1) :
    rationalPoint (candidateBits z) = z := by
  funext v
  rcases hz v with h | h <;> simp [rationalPoint, candidateBits, h]

/-- The direct full-rank branch computes zero or one by checking the actual rational
candidate's entries and side clauses. It does not enumerate the source solutions. -/
theorem fullRankCount_correct [Fintype I] (B : CNF V)
    (S : I → Finset V) (p : I → V → Bool) (z : V → ℚ)
    (hz : ∀ i, dotProduct (coefficients (S i) (p i)) z = rhs (S i) (p i))
    (hfull : Submodule.span ℚ (Set.range fun i => coefficients (S i) (p i)) = ⊤) :
    fullRankCount B z =
      Fintype.card {u : V → Bool // B.eval u = true ∧ ∀ j, Holds (S j) (p j) u} := by
  classical
  have hle := count_le_one_of_full_span B S p hfull
  have heq (u : V → Bool) (hu : ∀ j, Holds (S j) (p j) u) : rationalPoint u = z :=
    LinearSystem.solution_eq_of_span_eq_top _ _ hfull
      (fun i => (equation_iff _ _ _).mpr (hu i)) hz
  unfold fullRankCount
  split_ifs with hb
  · have hpoint := rational_candidate z hb.1
    have hsol (i : I) : Holds (S i) (p i) (candidateBits z) := by
      apply (equation_iff _ _ _).mp
      rw [hpoint]
      exact hz i
    have hp : 0 < Fintype.card {u : V → Bool // B.eval u = true ∧ ∀ j, Holds (S j) (p j) u} :=
      Fintype.card_pos_iff.mpr ⟨⟨candidateBits z, hb.2, hsol⟩⟩
    omega
  · symm
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun u => hb ?_⟩
    have hpoint := heq u.val u.property.2
    have hbool : ∀ v, z v = 0 ∨ z v = 1 := by
      intro v
      rw [← hpoint]
      cases hv : u.val v <;> simp [rationalPoint, hv]
    have hbits : candidateBits z = u.val :=
      rationalPoint_injective ((rational_candidate z hbool).trans hpoint.symm)
    exact ⟨hbool, hbits ▸ u.property.1⟩

/-- Transpose an indexed Exact Cover instance. Equal or empty candidate sets retain
separate declared index bits, as required by the counting convention. -/
@[expose] def coverScopes [DecidableEq I] (A : V → Finset I) (i : I) : Finset V :=
  Finset.univ.filter fun v => i ∈ A v

omit [LinearOrder V] in
/-- Exact Cover transposition is pointwise parsimonious on the original index bits. -/
theorem coverScopes_iff [DecidableEq I] (A : V → Finset I) (x : V → Bool) :
    (∀ i, Holds (coverScopes A i) (fun _ => true) x) ↔
      ∀ i, ∃ v, i ∈ A v ∧ x v = true ∧
        ∀ w, i ∈ A w → x w = true → w = v := by
  simp [Holds, coverScopes]

end Cslib.Logic.PL.ExactOne
