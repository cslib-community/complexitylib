/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.Counting
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.Tree
public import Mathlib.Data.Finset.Powerset
import Complexity.Foundations.Data.List.Counting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Defs

/-!
# Recursive counting-sparsification tree

The decision sparsification tree (`BranchingRule` in
`Complexity/Logics/Propositional/ClauseSet/Sparsification/Tree.lean`) fixes its step to
`child`, whose branches cover the parent's satisfying assignments but may overlap. For exact model
counting (`Counting.lean`), `countingChild` refines the petal branch (`true`) by adjoining the unit
clauses `negatedHeartUnits H` requiring every literal of `H` to be false, matching equation (A.2)
in Appendix A.1 of [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (pp. 44–45).

Adding `negatedHeartUnits H` contributes up to `2 |H|` to the clause-width potential
`∑_{C ∈ ψ} 2 ^ |C|`. A single width-two clause (`z = 1`, `c = 2`, `|H| = 1`) can therefore be
replaced by one petal unit and one negated-heart unit of equal total potential `2 + 2 = 4`.
Whenever the selected flower has at least two clauses (`2 ≤ (flower ψ c H).card`), however,
removing the flower subtracts `z · 2 ^ c` while the petals and negated-heart units add at most
`z · 2 ^ (c - |H|) + 2 |H| < z · 2 ^ c` (`potential_countingChild_lt_of_two_le_card_flower`). Any
threshold schedule satisfying `2 ≤ θ j` for `1 ≤ j`—in particular the geometric schedule
`θ j = M ^ j` with `2 ≤ M` in Appendix A.1—guarantees `2 ≤ (flower ψ c H).card` at every heavy
heart (`potential_countingChild_lt`, `potential_countingChild_lt_pow`).

Using this strict potential decrease, `countingLeaves` recursively enumerates the finite list of
leaves obtained from `chooseBranch` and `countingChild`. Along the recursion we establish:
* leaf sparsity (`sparse_of_mem_countingLeaves`) whenever `2 ≤ θ j` for `1 ≤ j`;
* preservation of declared variable support (`support_of_mem_countingLeaves`), clause width
  (`card_le_of_mem_countingLeaves`), and reducedness (`reduced_of_mem_countingLeaves`);
* exact assignment partition: every satisfying assignment of the root satisfies a unique leaf
  occurrence (`countP_sat_countingLeaves`, `sat_iff_existsUnique_fin_countingLeaves`,
  `sat_iff_existsUnique_mem_countingLeaves`), while unsatisfying assignments satisfy none;
* exact additive conservation of `CNF.modelCountOn` on a single common declared variable set
  (`sum_modelCountOn_countingLeaves`, `sum_modelCountOn_countingLeaves_toClauseSet`), including
  unused declared variables, empty formulas, unit clauses, and contradictory formulas.

Quantitative insertion, path-length, and `2 ^ (σ n)` leaf-count bounds (Appendix A.2–A.3,
Lemmas A.1–A.3) are separate results not claimed in this module.

## Main definitions

* `Cslib.Logic.PL.ClauseSet.Sparsification.countingLeaves`: well-founded recursive leaf enumeration
  for disjoint counting sparsification.

## Main results

* `Cslib.Logic.PL.ClauseSet.Sparsification.potential_countingChild_lt_of_two_le_card_flower`:
  strict potential decrease when the flower has at least two clauses.
* `Cslib.Logic.PL.ClauseSet.Sparsification.potential_countingChild_lt`: strict potential decrease
  under `2 ≤ θ j` for `1 ≤ j`.
* `Cslib.Logic.PL.ClauseSet.Sparsification.potential_countingChild_lt_pow`: strict potential
  decrease for the geometric schedule `θ j = M ^ j` with `2 ≤ M`.
* `Cslib.Logic.PL.ClauseSet.Sparsification.sparse_of_mem_countingLeaves`: every leaf is sparse when
  `2 ≤ θ j` for `1 ≤ j`.
* `Cslib.Logic.PL.ClauseSet.Sparsification.support_of_mem_countingLeaves`: declared-variable
  support is preserved at every leaf.
* `Cslib.Logic.PL.ClauseSet.Sparsification.countP_sat_countingLeaves`: exact `0`/`1`
  leaf-occurrence multiplicity for every assignment.
* `Cslib.Logic.PL.ClauseSet.Sparsification.sum_modelCountOn_countingLeaves`: additive conservation
  of `CNF.modelCountOn` across all leaves on a common declared variable set.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*, Appendix A.1, pp. 44–45][OpenAI2026ETH]
* [C. Calabro, R. Impagliazzo, R. Paturi, *A duality between clause width and clause density for
  SAT*][CalabroImpagliazzoPaturi2006]
-/

@[expose] public section

namespace Cslib.Logic.PL.ClauseSet.Sparsification

open Finset

variable {V : Type*} [DecidableEq V]

/-! ### Negated-heart units and counting-child potential -/

private theorem mem_negatedHeartUnits {H : Finset (Literal V)} {C : Finset (Literal V)} :
    C ∈ negatedHeartUnits H ↔ ∃ l ∈ H, {Std.Sat.Literal.negate l} = C :=
  mem_image

/-- Each singleton clause in `negatedHeartUnits H` has cardinality `1`. -/
theorem card_of_mem_negatedHeartUnits {H : Finset (Literal V)} {C : Finset (Literal V)}
    (hC : C ∈ negatedHeartUnits H) : C.card = 1 := by
  obtain ⟨l, -, rfl⟩ := mem_negatedHeartUnits.mp hC
  exact card_singleton _

private theorem card_negatedHeartUnits (H : Finset (Literal V)) :
    (negatedHeartUnits H).card = H.card := by
  refine card_image_of_injective H fun a b hab => ?_
  have hneg : Std.Sat.Literal.negate a = Std.Sat.Literal.negate b := singleton_inj.mp hab
  rcases a with ⟨va, ba⟩
  rcases b with ⟨vb, bb⟩
  simp only [Std.Sat.Literal.negate, Prod.mk.injEq] at hneg
  exact Prod.ext hneg.1 (Bool.not_inj_iff.mp hneg.2)

private theorem potential_negatedHeartUnits (H : Finset (Literal V)) :
    potential (negatedHeartUnits H) = 2 * H.card := by
  unfold potential
  calc ∑ C ∈ negatedHeartUnits H, 2 ^ C.card
      = ∑ _C ∈ negatedHeartUnits H, 2 ^ 1 :=
        sum_congr rfl fun C hC => by rw [card_of_mem_negatedHeartUnits hC]
    _ = 2 * H.card := by
        rw [sum_const, card_negatedHeartUnits, smul_eq_mul, pow_one, Nat.mul_comm]

private theorem reduced_countingChild (ψ : ClauseSet V) (c : ℕ) (H : Finset (Literal V))
    (b : Bool) : Reduced (countingChild ψ c H b) := by
  cases b <;> exact reduced_reduce _

private theorem disjoint_flower_countingChild (ψ : ClauseSet V) {c : ℕ} {H : Finset (Literal V)}
    (h1 : 1 ≤ H.card) (hlt : H.card < c) (b : Bool) :
    Disjoint (flower ψ c H) (countingChild ψ c H b) := by
  rw [Finset.disjoint_left]
  intro C hC hCchild
  obtain ⟨-, hcard, hHC⟩ := mem_flower.mp hC
  cases b with
  | false =>
    have hmin := (mem_reduce.mp hCchild).2
    refine hmin H (mem_union_right _ (by simp only [intro, mem_singleton]))
      (ssubset_of_subset_of_ne hHC ?_)
    intro heq
    rw [heq, hcard] at hlt
    exact lt_irrefl _ hlt
  | true =>
    have hmin := (mem_reduce.mp hCchild).2
    refine hmin (C \ H) ?_ (sdiff_ssubset hHC (card_pos.mp h1))
    exact mem_union_left _ (mem_union_right _ (mem_petals.mpr ⟨C, hC, rfl⟩))

private theorem card_le_of_mem_countingChild {ψ : ClauseSet V} {c k : ℕ} {H : Finset (Literal V)}
    (h1 : 1 ≤ H.card) (hlt : H.card < c) (hF : (flower ψ c H).Nonempty)
    (hk : ∀ C ∈ ψ, C.card ≤ k) {b : Bool} {C : Finset (Literal V)}
    (hC : C ∈ countingChild ψ c H b) : C.card ≤ k := by
  obtain ⟨D₀, hD₀⟩ := hF
  have hck : c ≤ k := (mem_flower.mp hD₀).2.1 ▸ hk D₀ (flower_subset ψ c H hD₀)
  cases b with
  | false =>
    rcases mem_union.mp (child_subset ψ c H false hC) with hCψ | hCH
    · exact hk C hCψ
    · simp only [intro, mem_singleton] at hCH
      subst hCH
      omega
  | true =>
    rcases mem_union.mp (reduce_subset _ hC) with hC' | hCneg
    · rcases mem_union.mp hC' with hCψ | hCpet
      · exact hk C hCψ
      · have hp := card_of_mem_petals hCpet
        omega
    · have hu := card_of_mem_negatedHeartUnits hCneg
      omega

omit [DecidableEq V] in
private theorem potential_mono {α β : ClauseSet V} (h : α ⊆ β) :
    potential α ≤ potential β := by
  classical
  unfold potential
  have := sum_sdiff h (f := fun C : Finset (Literal V) => 2 ^ C.card)
  omega

private theorem potential_union_le (α β : ClauseSet V) :
    potential (α ∪ β) ≤ potential α + potential β := by
  unfold potential
  have := sum_union_inter (s₁ := α) (s₂ := β) (f := fun C : Finset (Literal V) => 2 ^ C.card)
  omega

private theorem petal_unit_potential_bound {c h z : ℕ} (h1 : 1 ≤ h) (hlt : h < c) (hz : 2 ≤ z) :
    z * 2 ^ (c - h) + 2 * h < z * 2 ^ c := by
  have hj_le : c - h ≤ c - 1 := by omega
  have hpow_j : 2 ^ (c - h) ≤ 2 ^ (c - 1) := Nat.pow_le_pow_right (by omega) hj_le
  have hh_lt : h < 2 ^ (c - 1) := lt_of_le_of_lt (by omega : h ≤ c - 1) Nat.lt_two_pow_self
  have hc_pow : 2 ^ c = 2 ^ (c - 1) + 2 ^ (c - 1) := by
    conv_lhs => rw [show c = (c - 1) + 1 by omega, Nat.pow_succ]
    omega
  calc z * 2 ^ (c - h) + 2 * h
      ≤ z * 2 ^ (c - 1) + 2 * h :=
        Nat.add_le_add_right (Nat.mul_le_mul_left z hpow_j) _
    _ < z * 2 ^ (c - 1) + 2 * 2 ^ (c - 1) :=
        Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left hh_lt (by omega)) _
    _ ≤ z * 2 ^ (c - 1) + z * 2 ^ (c - 1) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hz) _
    _ = z * 2 ^ c := by rw [hc_pow, Nat.mul_add]

/-- **Strict potential decrease for `countingChild`.** When `1 ≤ |H| < c` and `flower ψ c H` has at
least two clauses, both counting branches strictly decrease `potential`. On the petal branch
(`true`), removing `z ≥ 2` clauses of width `c` subtracts `z · 2 ^ c` while adding at most `z`
petals of width `c - |H|` and `|H|` negated units of width `1`, and
`z · 2 ^ (c - |H|) + 2 |H| < z · 2 ^ c`. -/
theorem potential_countingChild_lt_of_two_le_card_flower
    {ψ : ClauseSet V} {c : ℕ} {H : Finset (Literal V)}
    (h1 : 1 ≤ H.card) (hlt : H.card < c) (hz : 2 ≤ (flower ψ c H).card) (b : Bool) :
    potential (countingChild ψ c H b) < potential ψ := by
  set F := flower ψ c H
  have hFsplit : potential ψ = potential (ψ \ F) + potential F := by
    unfold potential
    rw [← sum_sdiff (flower_subset ψ c H)]
  have hF : potential F = F.card * 2 ^ c := by
    unfold potential
    rw [sum_congr rfl fun C hC => by rw [(mem_flower.mp hC).2.1], sum_const, smul_eq_mul]
  have hdisj := disjoint_flower_countingChild ψ h1 hlt b
  cases b with
  | false =>
    have hsub : countingChild ψ c H false ⊆ (ψ \ F) ∪ {H} := by
      intro C hC
      rcases mem_union.mp (child_subset ψ c H false hC) with hCψ | hCH
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hCψ, fun hCF => disjoint_left.mp hdisj hCF hC⟩)
      · simp only [intro] at hCH
        exact mem_union_right _ hCH
    have hHlt : potential ({H} : ClauseSet V) < F.card * 2 ^ c := by
      unfold potential
      rw [sum_singleton]
      calc 2 ^ H.card < 2 ^ c := Nat.pow_lt_pow_right (by omega) hlt
        _ ≤ F.card * 2 ^ c := Nat.le_mul_of_pos_left _ (by omega)
    calc potential (countingChild ψ c H false)
        ≤ potential ((ψ \ F) ∪ {H}) := potential_mono hsub
      _ ≤ potential (ψ \ F) + potential ({H} : ClauseSet V) := potential_union_le _ _
      _ < potential (ψ \ F) + potential F := by rw [hF]; exact Nat.add_lt_add_left hHlt _
      _ = potential ψ := hFsplit.symm
  | true =>
    have hsub : countingChild ψ c H true ⊆ (ψ \ F) ∪ (petals ψ c H ∪ negatedHeartUnits H) := by
      intro C hC
      rcases mem_union.mp (reduce_subset _ hC) with hC' | hCneg
      · rcases mem_union.mp hC' with hCψ | hCpet
        · exact mem_union_left _ (mem_sdiff.mpr ⟨hCψ, fun hCF => disjoint_left.mp hdisj hCF hC⟩)
        · exact mem_union_right _ (mem_union_left _ hCpet)
      · exact mem_union_right _ (mem_union_right _ hCneg)
    have hpet : potential (petals ψ c H) = F.card * 2 ^ (c - H.card) := by
      unfold potential
      calc ∑ C ∈ petals ψ c H, 2 ^ C.card
          = ∑ _C ∈ petals ψ c H, 2 ^ (c - H.card) :=
            sum_congr rfl fun C hC => by rw [card_of_mem_petals hC]
        _ = F.card * 2 ^ (c - H.card) := by rw [sum_const, card_petals, smul_eq_mul]
    have hnew : potential (petals ψ c H ∪ negatedHeartUnits H) < F.card * 2 ^ c := by
      calc potential (petals ψ c H ∪ negatedHeartUnits H)
          ≤ potential (petals ψ c H) + potential (negatedHeartUnits H) := potential_union_le _ _
        _ = F.card * 2 ^ (c - H.card) + 2 * H.card := by rw [hpet, potential_negatedHeartUnits]
        _ < F.card * 2 ^ c := petal_unit_potential_bound h1 hlt hz
    calc potential (countingChild ψ c H true)
        ≤ potential ((ψ \ F) ∪ (petals ψ c H ∪ negatedHeartUnits H)) := potential_mono hsub
      _ ≤ potential (ψ \ F) + potential (petals ψ c H ∪ negatedHeartUnits H) :=
          potential_union_le _ _
      _ < potential (ψ \ F) + potential F := by rw [hF]; exact Nat.add_lt_add_left hnew _
      _ = potential ψ := hFsplit.symm

/-- Any threshold schedule satisfying `2 ≤ θ j` for `1 ≤ j` guarantees at least two clauses in the
flower of every heavy heart. -/
theorem two_le_card_flower_of_heavy {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ j → 2 ≤ θ j)
    {ψ : ClauseSet V} {c : ℕ} {H : Finset (Literal V)} (h : Heavy θ ψ c H) :
    2 ≤ (flower ψ c H).card :=
  (hθ (c - H.card) (by have := h.2.1; omega)).trans h.2.2

/-- **Termination under `2 ≤ θ j` (`1 ≤ j`).** Every heavy heart has a flower of size at least `2`,
so both counting children strictly decrease `potential`. -/
theorem potential_countingChild_lt {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ j → 2 ≤ θ j)
    {ψ : ClauseSet V} {c : ℕ} {H : Finset (Literal V)} (h : Heavy θ ψ c H) (b : Bool) :
    potential (countingChild ψ c H b) < potential ψ :=
  potential_countingChild_lt_of_two_le_card_flower h.1 h.2.1
    (two_le_card_flower_of_heavy hθ h) b

/-- **Termination for geometric thresholds `θ j = M ^ j` (`2 ≤ M`)** (Appendix A.1, p. 44). -/
theorem potential_countingChild_lt_pow {M : ℕ} (hM : 2 ≤ M)
    {ψ : ClauseSet V} {c : ℕ} {H : Finset (Literal V)}
    (h : Heavy (M ^ ·) ψ c H) (b : Bool) :
    potential (countingChild ψ c H b) < potential ψ :=
  potential_countingChild_lt
    (fun _ hj => hM.trans
      (by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < M) hj))
    h b

/-! ### Finite characterization of sparsity and unique choices -/

/-- When `1 ≤ θ j` for `1 ≤ j`, sparsity depends only on nonempty proper subsets of clauses present
in `ψ`, giving a finite criterion on any variable type with decidable equality. -/
theorem sparse_iff_forall_mem_powerset {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ j → 1 ≤ θ j)
    (ψ : ClauseSet V) :
    Sparse θ ψ ↔ ∀ C ∈ ψ, ∀ H ∈ C.powerset, ¬ Heavy θ ψ C.card H := by
  refine ⟨fun hs C _ H _ => hs C.card H, fun h c H hheavy => ?_⟩
  have hpos : 0 < (flower ψ c H).card :=
    lt_of_lt_of_le (hθ (c - H.card) (by have := hheavy.2.1; omega)) hheavy.2.2
  obtain ⟨C, hC⟩ := card_pos.mp hpos
  obtain ⟨hCψ, hCcard, hHC⟩ := mem_flower.mp hC
  exact h C hCψ H (mem_powerset.mpr hHC) (hCcard ▸ hheavy)

/-- If `(c, H)` is a valid `Choice` and no other heavy heart at width `c` has size at least `|H|`,
`chooseBranch` must select `(c, H)`. -/
theorem chooseBranch_eq_of_choice_unique {θ : ℕ → ℕ} {ψ : ClauseSet V} {c : ℕ}
    {H : Finset (Literal V)} (hch : Choice θ ψ c H)
    (huniq : ∀ H', Heavy θ ψ c H' → H.card ≤ H'.card → H' = H) :
    chooseBranch θ ψ = (c, H) := by
  have hns : ¬ Sparse θ ψ := fun hs => hs c H hch.1
  have hcb : Choice θ ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2 := choice_chooseBranch hns
  have hc_eq : (chooseBranch θ ψ).1 = c :=
    le_antisymm (hcb.2.1 c H hch.1) (hch.2.1 _ _ hcb.1)
  have hH_heavy : Heavy θ ψ c (chooseBranch θ ψ).2 := hc_eq ▸ hcb.1
  have hH_le : H.card ≤ (chooseBranch θ ψ).2.card := (hc_eq ▸ hcb.2.2) H hch.1
  exact Prod.ext hc_eq (huniq _ hH_heavy hH_le)

/-! ### Recursive leaf enumeration -/

/-- Recursively enumerate the leaves of the disjoint counting-sparsification tree of `ψ` using
`chooseBranch θ` and `countingChild`. At any non-sparse state whose chosen flower has at least two
clauses (which holds automatically whenever `2 ≤ θ j` for `1 ≤ j`), `potential` strictly decreases
in both children. -/
noncomputable def countingLeaves (θ : ℕ → ℕ) (ψ : ClauseSet V) : List (ClauseSet V) :=
  open Classical in
  if ¬ Sparse θ ψ ∧ 2 ≤ (flower ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2).card then
    let ch := chooseBranch θ ψ
    countingLeaves θ (countingChild ψ ch.1 ch.2 false) ++
      countingLeaves θ (countingChild ψ ch.1 ch.2 true)
  else
    [ψ]
termination_by potential ψ
decreasing_by
  · rename_i h
    exact potential_countingChild_lt_of_two_le_card_flower
      (choice_chooseBranch h.1).1.1 (choice_chooseBranch h.1).1.2.1 h.2 false
  · rename_i h
    exact potential_countingChild_lt_of_two_le_card_flower
      (choice_chooseBranch h.1).1.1 (choice_chooseBranch h.1).1.2.1 h.2 true

/-- At a sparse clause set, `countingLeaves` terminates immediately with `[ψ]`. -/
theorem countingLeaves_of_sparse {θ : ℕ → ℕ} {ψ : ClauseSet V} (h : Sparse θ ψ) :
    countingLeaves θ ψ = [ψ] := by
  rw [countingLeaves]
  exact ite_eq_right fun h' => h'.1 h

/-- When `2 ≤ θ j` for `1 ≤ j` and `ψ` is not sparse, `countingLeaves` branches into the heart
(`false`) and petal-plus-negated-units (`true`) subtrees for `chooseBranch θ ψ`. -/
theorem countingLeaves_of_not_sparse {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ j → 2 ≤ θ j)
    {ψ : ClauseSet V} (h : ¬ Sparse θ ψ) :
    countingLeaves θ ψ =
      countingLeaves θ (countingChild ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2 false) ++
        countingLeaves θ (countingChild ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2 true) := by
  have hz : 2 ≤ (flower ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2).card :=
    two_le_card_flower_of_heavy hθ (choice_chooseBranch h).1
  rw [countingLeaves]
  exact ite_eq_left ⟨h, hz⟩

/-- Unfolding `countingLeaves` when the valid `Choice` at `ψ` is uniquely `(c, H)` and
`flower ψ c H` has at least two clauses. -/
theorem countingLeaves_of_choice_unique {θ : ℕ → ℕ} {ψ : ClauseSet V} {c : ℕ}
    {H : Finset (Literal V)} (hch : Choice θ ψ c H) (hz : 2 ≤ (flower ψ c H).card)
    (huniq : ∀ H', Heavy θ ψ c H' → H.card ≤ H'.card → H' = H) :
    countingLeaves θ ψ =
      countingLeaves θ (countingChild ψ c H false) ++
        countingLeaves θ (countingChild ψ c H true) := by
  have hns : ¬ Sparse θ ψ := fun hs => hs c H hch.1
  have hcb := chooseBranch_eq_of_choice_unique hch huniq
  have hcond : ¬ Sparse θ ψ ∧
      2 ≤ (flower ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2).card := by
    rw [hcb]
    exact ⟨hns, hz⟩
  rw [countingLeaves, ite_eq_left hcond, hcb]

/-- Finite criterion for unfolding `countingLeaves` at a unique valid choice `(c, H)` when
`1 ≤ θ j` for `1 ≤ j`, inspecting only clauses `C ∈ ψ` and subsets `H' ∈ C.powerset`. -/
theorem countingLeaves_of_mem_powerset_unique {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ j → 1 ≤ θ j)
    {ψ : ClauseSet V} {c : ℕ} {H : Finset (Literal V)}
    (hheavy : Heavy θ ψ c H) (hz : 2 ≤ (flower ψ c H).card)
    (hmin : ∀ C ∈ ψ, C.card < c → ∀ H' ∈ C.powerset, ¬ Heavy θ ψ C.card H')
    (huniq : ∀ C ∈ ψ, C.card = c → ∀ H' ∈ C.powerset,
      Heavy θ ψ c H' → H.card ≤ H'.card → H' = H) :
    countingLeaves θ ψ =
      countingLeaves θ (countingChild ψ c H false) ++
        countingLeaves θ (countingChild ψ c H true) := by
  have hex_clause : ∀ {c' : ℕ} {H' : Finset (Literal V)}, Heavy θ ψ c' H' →
      ∃ C ∈ ψ, C.card = c' ∧ H' ∈ C.powerset := by
    intro c' H' hh
    have hpos : 0 < (flower ψ c' H').card :=
      lt_of_lt_of_le (hθ (c' - H'.card) (by have := hh.2.1; omega)) hh.2.2
    obtain ⟨C, hC⟩ := card_pos.mp hpos
    obtain ⟨hCψ, hCcard, hHC⟩ := mem_flower.mp hC
    exact ⟨C, hCψ, hCcard, mem_powerset.mpr hHC⟩
  have huniq' : ∀ H', Heavy θ ψ c H' → H.card ≤ H'.card → H' = H := by
    intro H' hh hle
    obtain ⟨C, hCψ, hCcard, hH'pow⟩ := hex_clause hh
    exact huniq C hCψ hCcard H' hH'pow hh hle
  have hch : Choice θ ψ c H := by
    refine ⟨hheavy, fun c' H' hh => ?_, fun H' hh => ?_⟩
    · by_contra hlt
      obtain ⟨C, hCψ, hCcard, hH'pow⟩ := hex_clause hh
      exact hmin C hCψ (by omega) H' hH'pow (hCcard ▸ hh)
    · by_contra hlt
      have heq := huniq' H' hh (by omega)
      rw [heq] at hlt
      exact hlt le_rfl
  exact countingLeaves_of_choice_unique hch hz huniq'

/-- `countingLeaves` never returns the empty list. -/
theorem countingLeaves_ne_nil (θ : ℕ → ℕ) (ψ : ClauseSet V) :
    countingLeaves θ ψ ≠ [] := by
  induction hp : potential ψ using Nat.strong_induction_on generalizing ψ with
  | _ n ih =>
    rw [countingLeaves]
    by_cases h : ¬ Sparse θ ψ ∧ 2 ≤ (flower ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2).card
    · rw [ite_eq_left h]
      have hlt := potential_countingChild_lt_of_two_le_card_flower
        (choice_chooseBranch h.1).1.1 (choice_chooseBranch h.1).1.2.1 h.2 false
      exact List.append_ne_nil_of_left_ne_nil (ih _ (hp ▸ hlt) _ rfl) _
    · rw [ite_eq_right h]
      exact List.cons_ne_nil _ _

/-! ### Structural invariants along the recursion -/

/-- **Leaf sparsity.** Whenever `2 ≤ θ j` for `1 ≤ j`, every clause set in `countingLeaves θ ψ` is
`θ`-sparse. -/
theorem sparse_of_mem_countingLeaves {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ j → 2 ≤ θ j)
    {ψ L : ClauseSet V} (hL : L ∈ countingLeaves θ ψ) : Sparse θ L := by
  suffices ∀ n (ψ : ClauseSet V), potential ψ = n → L ∈ countingLeaves θ ψ → Sparse θ L from
    this (potential ψ) ψ rfl hL
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ψ hp hL
    by_cases hs : Sparse θ ψ
    · rw [countingLeaves_of_sparse hs, List.mem_singleton] at hL
      exact hL ▸ hs
    · rw [countingLeaves_of_not_sparse hθ hs, List.mem_append] at hL
      have hch := (choice_chooseBranch hs).1
      rcases hL with hL | hL
      · exact ih _ (hp ▸ potential_countingChild_lt hθ hch false) _ rfl hL
      · exact ih _ (hp ▸ potential_countingChild_lt hθ hch true) _ rfl hL

/-- **Leaf sparsity for geometric thresholds `θ j = M ^ j` (`2 ≤ M`).** -/
theorem sparse_of_mem_countingLeaves_pow {M : ℕ} (hM : 2 ≤ M)
    {ψ L : ClauseSet V} (hL : L ∈ countingLeaves (M ^ ·) ψ) : Sparse (M ^ ·) L :=
  sparse_of_mem_countingLeaves
    (fun _ hj => hM.trans
      (by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < M) hj))
    hL

/-- **Variable-support preservation.** If all variables occurring in `ψ` belong to `declared`, then
all variables occurring in every leaf `L ∈ countingLeaves θ ψ` belong to `declared`. -/
theorem support_of_mem_countingLeaves {θ : ℕ → ℕ} {ψ L : ClauseSet V} {declared : Finset V}
    (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 ∈ declared) (hL : L ∈ countingLeaves θ ψ) :
    ∀ C ∈ L, ∀ l ∈ C, l.1 ∈ declared := by
  suffices ∀ n (ψ : ClauseSet V), potential ψ = n →
      (∀ C ∈ ψ, ∀ l ∈ C, l.1 ∈ declared) → L ∈ countingLeaves θ ψ →
      ∀ C ∈ L, ∀ l ∈ C, l.1 ∈ declared from
    this (potential ψ) ψ rfl hψ hL
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ψ hp hψ hL
    rw [countingLeaves] at hL
    by_cases h : ¬ Sparse θ ψ ∧ 2 ≤ (flower ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2).card
    · rw [ite_eq_left h, List.mem_append] at hL
      set ch := chooseBranch θ ψ
      have hch := (choice_chooseBranch h.1).1
      obtain ⟨D, hD⟩ := card_pos.mp (lt_of_lt_of_le (by omega : 0 < 2) h.2)
      obtain ⟨hDψ, -, hHD⟩ := mem_flower.mp hD
      have hH : ∀ l ∈ ch.2, l.1 ∈ declared := fun l hl => hψ D hDψ l (hHD hl)
      rcases hL with hL | hL
      · have hlt := potential_countingChild_lt_of_two_le_card_flower hch.1 hch.2.1 h.2 false
        exact ih _ (hp ▸ hlt) _ rfl (support_countingChild ψ ch.1 ch.2 declared hψ hH false) hL
      · have hlt := potential_countingChild_lt_of_two_le_card_flower hch.1 hch.2.1 h.2 true
        exact ih _ (hp ▸ hlt) _ rfl (support_countingChild ψ ch.1 ch.2 declared hψ hH true) hL
    · rw [ite_eq_right h, List.mem_singleton] at hL
      exact hL ▸ hψ

/-- **Clause-width preservation.** If every clause of `ψ` has width at most `k`, then every clause
of every leaf `L ∈ countingLeaves θ ψ` has width at most `k`. -/
theorem card_le_of_mem_countingLeaves {θ : ℕ → ℕ} {ψ L : ClauseSet V} {k : ℕ}
    (hk : ∀ C ∈ ψ, C.card ≤ k) (hL : L ∈ countingLeaves θ ψ) :
    ∀ C ∈ L, C.card ≤ k := by
  suffices ∀ n (ψ : ClauseSet V), potential ψ = n →
      (∀ C ∈ ψ, C.card ≤ k) → L ∈ countingLeaves θ ψ → ∀ C ∈ L, C.card ≤ k from
    this (potential ψ) ψ rfl hk hL
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ψ hp hk hL
    rw [countingLeaves] at hL
    by_cases h : ¬ Sparse θ ψ ∧ 2 ≤ (flower ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2).card
    · rw [ite_eq_left h, List.mem_append] at hL
      set ch := chooseBranch θ ψ
      have hch := (choice_chooseBranch h.1).1
      have hne : (flower ψ ch.1 ch.2).Nonempty :=
        card_pos.mp (lt_of_lt_of_le (by omega : 0 < 2) h.2)
      rcases hL with hL | hL
      · have hlt := potential_countingChild_lt_of_two_le_card_flower hch.1 hch.2.1 h.2 false
        exact ih _ (hp ▸ hlt) _ rfl
          (fun C hC => card_le_of_mem_countingChild hch.1 hch.2.1 hne hk hC) hL
      · have hlt := potential_countingChild_lt_of_two_le_card_flower hch.1 hch.2.1 h.2 true
        exact ih _ (hp ▸ hlt) _ rfl
          (fun C hC => card_le_of_mem_countingChild hch.1 hch.2.1 hne hk hC) hL
    · rw [ite_eq_right h, List.mem_singleton] at hL
      exact hL ▸ hk

/-- **Reducedness preservation.** From a reduced root `ψ`, every leaf in `countingLeaves θ ψ` is
reduced. -/
theorem reduced_of_mem_countingLeaves {θ : ℕ → ℕ} {ψ L : ClauseSet V}
    (hred : Reduced ψ) (hL : L ∈ countingLeaves θ ψ) : Reduced L := by
  suffices ∀ n (ψ : ClauseSet V), potential ψ = n →
      Reduced ψ → L ∈ countingLeaves θ ψ → Reduced L from
    this (potential ψ) ψ rfl hred hL
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ψ hp hred hL
    rw [countingLeaves] at hL
    by_cases h : ¬ Sparse θ ψ ∧ 2 ≤ (flower ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2).card
    · rw [ite_eq_left h, List.mem_append] at hL
      set ch := chooseBranch θ ψ
      have hch := (choice_chooseBranch h.1).1
      rcases hL with hL | hL
      · have hlt := potential_countingChild_lt_of_two_le_card_flower hch.1 hch.2.1 h.2 false
        exact ih _ (hp ▸ hlt) _ rfl (reduced_countingChild ψ ch.1 ch.2 false) hL
      · have hlt := potential_countingChild_lt_of_two_le_card_flower hch.1 hch.2.1 h.2 true
        exact ih _ (hp ▸ hlt) _ rfl (reduced_countingChild ψ ch.1 ch.2 true) hL
    · rw [ite_eq_right h, List.mem_singleton] at hL
      exact hL ▸ hred

/-! ### Exact assignment partition and model-count conservation -/

/-- **Exact assignment partition (multiplicity form).** For every assignment `x : V → Bool`, the
number of leaf occurrences in `countingLeaves θ ψ` satisfied by `x` is `1` when `ψ.Sat x` holds and
`0` otherwise. -/
theorem countP_sat_countingLeaves (θ : ℕ → ℕ) (ψ : ClauseSet V) (x : V → Bool) :
    (countingLeaves θ ψ).countP (fun L => decide (L.Sat x)) =
      if ψ.Sat x then 1 else 0 := by
  induction hp : potential ψ using Nat.strong_induction_on generalizing ψ with
  | _ n ih =>
    rw [countingLeaves]
    by_cases h : ¬ Sparse θ ψ ∧ 2 ≤ (flower ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2).card
    · rw [ite_eq_left h]
      set ch := chooseBranch θ ψ
      have hch := (choice_chooseBranch h.1).1
      have hlt₀ := potential_countingChild_lt_of_two_le_card_flower hch.1 hch.2.1 h.2 false
      have hlt₁ := potential_countingChild_lt_of_two_le_card_flower hch.1 hch.2.1 h.2 true
      rw [List.countP_append, ih _ (hp ▸ hlt₀) _ rfl, ih _ (hp ▸ hlt₁) _ rfl]
      by_cases hsat : ψ.Sat x
      · by_cases hH : ∃ l ∈ ch.2, x l.1 = l.2
        · have h₀ : (countingChild ψ ch.1 ch.2 false).Sat x :=
            (sat_countingChild_false_iff ψ ch.1 ch.2 x).mpr ⟨hsat, hH⟩
          have h₁ : ¬ (countingChild ψ ch.1 ch.2 true).Sat x := fun ht =>
            not_sat_both_countingChild ψ ch.1 ch.2 x ⟨h₀, ht⟩
          rw [ite_eq_left hsat, ite_eq_left h₀, ite_eq_right h₁]
        · have h₁ : (countingChild ψ ch.1 ch.2 true).Sat x :=
            (sat_countingChild_true_iff ψ ch.1 ch.2 x).mpr ⟨hsat, hH⟩
          have h₀ : ¬ (countingChild ψ ch.1 ch.2 false).Sat x := fun hf =>
            not_sat_both_countingChild ψ ch.1 ch.2 x ⟨hf, h₁⟩
          rw [ite_eq_left hsat, ite_eq_right h₀, ite_eq_left h₁]
      · have h₀ : ¬ (countingChild ψ ch.1 ch.2 false).Sat x := fun hf =>
          hsat ((sat_countingChild_false_iff ψ ch.1 ch.2 x).mp hf).1
        have h₁ : ¬ (countingChild ψ ch.1 ch.2 true).Sat x := fun ht =>
          hsat ((sat_countingChild_true_iff ψ ch.1 ch.2 x).mp ht).1
        rw [ite_eq_right hsat, ite_eq_right h₀, ite_eq_right h₁]
    · rw [ite_eq_right h]
      let p : ClauseSet V → Bool := fun L => decide (L.Sat x)
      change [ψ].countP p = if ψ.Sat x then 1 else 0
      by_cases hsat : ψ.Sat x
      · rw [List.countP_cons_of_pos (p := p) (decide_eq_true hsat), List.countP_nil,
          ite_eq_left hsat]
      · rw [List.countP_cons_of_neg (p := p) (by simpa only [p, decide_eq_true_eq] using hsat),
          List.countP_nil, ite_eq_right hsat]

/-- **Exact assignment partition (indexed leaf occurrence form).** An assignment `x` satisfies `ψ`
if and only if there is a unique index `i` into `countingLeaves θ ψ` whose leaf is satisfied by
`x`. -/
theorem sat_iff_existsUnique_fin_countingLeaves (θ : ℕ → ℕ) (ψ : ClauseSet V) (x : V → Bool) :
    ψ.Sat x ↔ ∃! i : Fin (countingLeaves θ ψ).length, ((countingLeaves θ ψ)[i]).Sat x := by
  have hc := countP_sat_countingLeaves θ ψ x
  constructor
  · intro hsat
    rw [ite_eq_left hsat] at hc
    obtain ⟨i, hi, huniq⟩ := List.existsUnique_fin_of_countP_eq_one hc
    exact Exists.intro i (And.intro (of_decide_eq_true hi) fun j hj => huniq j (decide_eq_true hj))
  · rintro ⟨i, hi, -⟩
    by_contra hnsat
    rw [ite_eq_right hnsat, List.countP_eq_zero] at hc
    exact hc ((countingLeaves θ ψ)[i]) (List.getElem_mem i.isLt) (decide_eq_true hi)

/-- **Exact assignment partition (leaf membership form).** Because any satisfiable leaf occurs at
most once in `countingLeaves θ ψ`, `x` satisfies `ψ` if and only if there is a unique clause set
`L` satisfying `L ∈ countingLeaves θ ψ ∧ L.Sat x`. -/
theorem sat_iff_existsUnique_mem_countingLeaves (θ : ℕ → ℕ) (ψ : ClauseSet V) (x : V → Bool) :
    ψ.Sat x ↔ ∃! L, L ∈ countingLeaves θ ψ ∧ L.Sat x := by
  have hc := countP_sat_countingLeaves θ ψ x
  constructor
  · intro hsat
    rw [ite_eq_left hsat] at hc
    obtain ⟨L, ⟨hLm, hLs⟩, huniq⟩ := List.existsUnique_mem_of_countP_eq_one hc
    exact Exists.intro L (And.intro ⟨hLm, of_decide_eq_true hLs⟩ fun L' ⟨hL'm, hL's⟩ =>
      huniq L' ⟨hL'm, decide_eq_true hL's⟩)
  · rintro ⟨L, ⟨hLm, hLs⟩, -⟩
    by_contra hnsat
    rw [ite_eq_right hnsat, List.countP_eq_zero] at hc
    exact hc L hLm (decide_eq_true hLs)

/-- **Additive model-count conservation.** Summing `CNF.modelCountOn declared` over all leaves in
`countingLeaves θ ψ` recovers `ψ.toCNF.modelCountOn declared` on the same declared variable set,
preserving free choices for unused declared variables and handling empty or contradictory clause
sets without extra premises. -/
theorem sum_modelCountOn_countingLeaves (θ : ℕ → ℕ) (ψ : ClauseSet V) (declared : Finset V) :
    ((countingLeaves θ ψ).map fun L => L.toCNF.modelCountOn declared).sum =
      ψ.toCNF.modelCountOn declared := by
  induction hp : potential ψ using Nat.strong_induction_on generalizing ψ with
  | _ n ih =>
    rw [countingLeaves]
    by_cases h : ¬ Sparse θ ψ ∧ 2 ≤ (flower ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2).card
    · rw [ite_eq_left h]
      set ch := chooseBranch θ ψ
      have hch := (choice_chooseBranch h.1).1
      have hlt₀ := potential_countingChild_lt_of_two_le_card_flower hch.1 hch.2.1 h.2 false
      have hlt₁ := potential_countingChild_lt_of_two_le_card_flower hch.1 hch.2.1 h.2 true
      rw [List.map_append, List.sum_append, ih _ (hp ▸ hlt₀) _ rfl, ih _ (hp ▸ hlt₁) _ rfl]
      exact (modelCountOn_countingChild ψ ch.1 ch.2 declared).symm
    · rw [ite_eq_right h]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

/-! ### Bridges to `CNF` formulas and `CNF.modelCountOn` -/

/-- Clause-set reduction `reduce` preserves `modelCountOn` on any declared variable set. -/
@[simp]
theorem modelCountOn_toCNF_reduce (ψ : ClauseSet V) (declared : Finset V) :
    (reduce ψ).toCNF.modelCountOn declared = ψ.toCNF.modelCountOn declared := by
  unfold CNF.modelCountOn
  congr 1
  ext σ
  simp only [mem_filter, mem_univ, true_and, ClauseSet.eval_toCNF_eq_true_iff, sat_reduce_iff]

/-- **CNF assignment partition.** Evaluating `L.toCNF` across `countingLeaves θ φ.toClauseSet`
accepts each assignment `x` at `1` leaf occurrence when `φ.eval x = true` and `0` otherwise. -/
theorem countP_eval_toCNF_countingLeaves (θ : ℕ → ℕ) (φ : CNF V) (x : V → Bool) :
    ((countingLeaves θ φ.toClauseSet).map ClauseSet.toCNF).countP (fun F => F.eval x) =
      if φ.eval x then 1 else 0 := by
  rw [List.countP_map]
  have hcongr : (Function.comp (fun F : CNF V => F.eval x) ClauseSet.toCNF) =
      fun L : ClauseSet V => decide (L.Sat x) := by
    funext L
    exact Bool.eq_iff_iff.mpr
      ((ClauseSet.eval_toCNF_eq_true_iff L x).trans decide_eq_true_iff.symm)
  rw [hcongr, countP_sat_countingLeaves]
  by_cases hev : φ.eval x = true
  · rw [ite_eq_left ((CNF.sat_toClauseSet_iff φ x).mpr hev), ite_eq_left hev]
  · have hnsat : ¬ φ.toClauseSet.Sat x := fun hs => hev ((CNF.sat_toClauseSet_iff φ x).mp hs)
    rw [ite_eq_right hnsat, ite_eq_right hev]

/-- **CNF declared-variable support preservation.** If `φ.vars.toFinset ⊆ declared`, then every
leaf formula `L.toCNF` produced from `φ.toClauseSet` has its occurring variables contained in
`declared`. -/
theorem vars_toCNF_subset_of_mem_countingLeaves {θ : ℕ → ℕ} {φ : CNF V} {declared : Finset V}
    (hvars : φ.vars.toFinset ⊆ declared) {L : ClauseSet V}
    (hL : L ∈ countingLeaves θ φ.toClauseSet) :
    L.toCNF.vars.toFinset ⊆ declared := by
  have hroot : ∀ C ∈ φ.toClauseSet, ∀ l ∈ C, l.1 ∈ declared := by
    intro C hC l hl
    simp only [CNF.toClauseSet, List.mem_toFinset, List.mem_map] at hC
    obtain ⟨c, hc, rfl⟩ := hC
    exact hvars (List.mem_toFinset.mpr (CNF.mem_vars.mpr ⟨c, hc, l.2, List.mem_toFinset.mp hl⟩))
  have hleaf := support_of_mem_countingLeaves hroot hL
  intro v hv
  obtain ⟨c, hc, b, hvb⟩ := CNF.mem_vars.mp (List.mem_toFinset.mp hv)
  simp only [ClauseSet.toCNF, List.mem_map, Finset.mem_toList] at hc
  obtain ⟨C, hC, rfl⟩ := hc
  exact hleaf C hC (v, b) (Finset.mem_toList.mp hvb)

/-- **CNF additive model-count conservation.** Summing `modelCountOn declared` over the leaf
formulas of `countingLeaves θ φ.toClauseSet` recovers `φ.modelCountOn declared`. -/
theorem sum_modelCountOn_countingLeaves_toClauseSet (θ : ℕ → ℕ) (φ : CNF V)
    (declared : Finset V) :
    ((countingLeaves θ φ.toClauseSet).map fun L => L.toCNF.modelCountOn declared).sum =
      φ.modelCountOn declared := by
  rw [sum_modelCountOn_countingLeaves, modelCountOn_toCNF_toClauseSet]

/-- **Reduced CNF additive model-count conservation.** Normalizing the root clause set with
`reduce` before enumerating `countingLeaves` likewise preserves `φ.modelCountOn declared`. -/
theorem sum_modelCountOn_countingLeaves_reduce_toClauseSet (θ : ℕ → ℕ) (φ : CNF V)
    (declared : Finset V) :
    ((countingLeaves θ (reduce φ.toClauseSet)).map fun L => L.toCNF.modelCountOn declared).sum =
      φ.modelCountOn declared := by
  rw [sum_modelCountOn_countingLeaves, modelCountOn_toCNF_reduce, modelCountOn_toCNF_toClauseSet]

end Cslib.Logic.PL.ClauseSet.Sparsification
