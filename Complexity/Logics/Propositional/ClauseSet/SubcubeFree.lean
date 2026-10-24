/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Sparsification
public import Complexity.Foundations.Data.BitString.Flip
import Complexity.Logics.Propositional.CNF.Coding
import Mathlib.Order.Interval.Finset.Nat

/-!
# Formulas without large subcubes of solutions have few solutions

A *move* of a solution `x` of a clause set `ψ` is a nonempty set `T` of variables such that `x`
with the bits in `T` flipped (`BitString.flipOn`) is again a solution; two moves are *separated*
when no clause meets both. Separated moves combine freely
(`ClauseSet.flipOn_biUnion_mem_solutions_of_separated`), so in a clause set whose variables have at
most `Δ` neighbours in the co-occurrence graph and whose solutions contain no subcube of dimension
`D` (`ContainsSubcube`), every solution has at most `(D - 1)(Δ + 1)` directions in which it is not
isolated (`ClauseSet.card_compl_isolatedDirections_le`). The satisfiability coding lemma then
bounds the solutions (`ClauseSet.card_solutions_le_of_neighbors`), and after sparsification every
formula of width `k` is a union of at most `2 ^ (ε N)` such pieces: a formula of width `k` over `N`
variables whose solutions contain no subcube of dimension `D` has at most
`2 ^ ((1 - 1 / k + ε) N + C D)` solutions (`ClauseSet.card_solutions_le_of_not_containsSubcube`).

The exponent `1 - 1 / k` cannot be improved, already for `D = 1`: requiring even parity on each of
`N / k` disjoint blocks of `k` variables gives `2 ^ ((1 - 1 / k) N)` solutions, no two of which
are neighbours (see `Complexity/Logics/Propositional/Parity/DepthThree.lean`).

## Main definitions

* `Cslib.Logic.PL.ContainsSubcube`: a set of words contains a subcube of a given dimension.
* `Cslib.Logic.PL.isolatedDirections`, `Cslib.Logic.PL.ClauseSet.neighbors`.
* `Cslib.Logic.PL.ClauseSet.Meets`: whether a clause mentions a variable from a given set.

## Main results

* `Cslib.Logic.PL.ClauseSet.card_compl_isolatedDirections_le`: few non-isolated directions.
* `Cslib.Logic.PL.ClauseSet.card_solutions_le_of_neighbors`: the bound in bounded degree.
* `Cslib.Logic.PL.ClauseSet.card_solutions_le_of_not_containsSubcube`: the bound.

## References

* [R. Paturi, P. Pudlák, F. Zane, *Satisfiability coding lemma*][PaturiPudlakZane1999]
* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
-/

@[expose] public section

namespace Cslib

open Finset


namespace Logic.PL

open BitString

variable {N : ℕ}

/-- The set `S` contains a *subcube of dimension `d`*: all the words obtained from one word by
flipping bits in a fixed set of `d` positions. -/
def ContainsSubcube (S : Set (BitString N)) (d : ℕ) : Prop :=
  ∃ (a : BitString N) (J : Finset (Fin N)), J.card = d ∧ ∀ T ⊆ J, flipOn T a ∈ S

/-- `ContainsSubcube` is monotone in the set of words. -/
theorem ContainsSubcube.mono {S T : Set (BitString N)} (hST : S ⊆ T) {d : ℕ}
    (h : ContainsSubcube S d) : ContainsSubcube T d := by
  obtain ⟨a, J, hJ, hsub⟩ := h
  exact ⟨a, J, hJ, fun U hU => hST (hsub U hU)⟩

/-- The *isolated directions* of `x` in `S`: the positions whose flip leaves `S`. -/
def isolatedDirections (S : Finset (BitString N)) (x : BitString N) : Finset (Fin N) :=
  {i | flipOn {i} x ∉ S}

namespace ClauseSet

/-- The variables `w ≠ u` that share a clause of `ψ` with `u`: the neighbours of `u` in the
co-occurrence graph. -/
def neighbors (ψ : ClauseSet (Fin N)) (u : Fin N) : Finset (Fin N) :=
  {w | w ≠ u ∧ ∃ C ∈ ψ, (∃ l ∈ C, l.1 = u) ∧ ∃ l ∈ C, l.1 = w}

/-- The clause `C` mentions a variable of `T`. -/
def Meets (C : Finset (Literal (Fin N))) (T : Finset (Fin N)) : Prop :=
  ∃ l ∈ C, l.1 ∈ T

/-- A word satisfies every clause of `ψ` that a solution agreeing with it on the variables of the
clause satisfies. -/
private theorem mem_solutions_of_agree {ψ : ClauseSet (Fin N)} {w : BitString N}
    (h : ∀ C ∈ ψ, ∃ z ∈ ψ.solutions, ∀ l ∈ C, z l.1 = w l.1) : w ∈ ψ.solutions := by
  rw [mem_solutions]
  intro C hC
  obtain ⟨z, hz, hagree⟩ := h C hC
  obtain ⟨l, hl, htrue⟩ := mem_solutions.mp hz C hC
  exact ⟨l, hl, (hagree l hl).symm.trans htrue⟩

/-- **Closed parts of moves are moves**: if flipping `T` keeps `x` a solution and no clause meets
both `T' ⊆ T` and `T \ T'`, flipping `T'` keeps it a solution. -/
private theorem flipOn_mem_solutions_of_closed {ψ : ClauseSet (Fin N)} {x : BitString N}
    {T T' : Finset (Fin N)} (hx : x ∈ ψ.solutions) (hT : flipOn T x ∈ ψ.solutions)
    (hsub : T' ⊆ T) (hclosed : ∀ C ∈ ψ, Meets C T' → ¬ Meets C (T \ T')) :
    flipOn T' x ∈ ψ.solutions := by
  refine mem_solutions_of_agree fun C hC => ?_
  by_cases hmeet : Meets C T'
  · refine ⟨flipOn T x, hT, fun l hl => flipOn_apply_eq_of_iff ⟨fun hlT => ?_, fun h => hsub h⟩⟩
    by_contra hlT'
    exact hclosed C hC hmeet ⟨l, hl, mem_sdiff.mpr ⟨hlT, hlT'⟩⟩
  · exact ⟨x, hx, fun l hl => (flipOn_apply_of_notMem fun h => hmeet ⟨l, hl, h⟩).symm⟩

/-- **Separated moves combine**: if the moves `T j`, `j ∈ s`, of a solution `x` are pairwise
separated (no clause meets two of them), flipping the union of any of them keeps `x` a
solution. -/
theorem flipOn_biUnion_mem_solutions_of_separated {ι : Type*} {ψ : ClauseSet (Fin N)}
    {x : BitString N} {s : Finset ι} {T : ι → Finset (Fin N)} (hx : x ∈ ψ.solutions)
    (hmove : ∀ j ∈ s, flipOn (T j) x ∈ ψ.solutions)
    (hsep : ∀ C ∈ ψ, ∀ j ∈ s, ∀ j' ∈ s, j ≠ j' → Meets C (T j) → ¬ Meets C (T j'))
    {J : Finset ι} (hJ : J ⊆ s) : flipOn (J.biUnion T) x ∈ ψ.solutions := by
  classical
  refine mem_solutions_of_agree fun C hC => ?_
  by_cases hmeet : ∃ j ∈ J, Meets C (T j)
  · obtain ⟨j, hj, hjmeet⟩ := hmeet
    refine ⟨flipOn (T j) x, hmove j (hJ hj), fun l hl => flipOn_apply_eq_of_iff ?_⟩
    refine ⟨fun h => mem_biUnion.mpr ⟨j, hj, h⟩, fun h => ?_⟩
    obtain ⟨j', hj', hlj'⟩ := mem_biUnion.mp h
    by_contra hlj
    exact hsep C hC j (hJ hj) j' (hJ hj') (fun hjj => hlj (hjj ▸ hlj')) hjmeet ⟨l, hl, hlj'⟩
  · push Not at hmeet
    refine ⟨x, hx, fun l hl => (flipOn_apply_of_notMem fun h => ?_).symm⟩
    obtain ⟨j, hj, hlj⟩ := mem_biUnion.mp h
    exact hmeet j hj ⟨l, hl, hlj⟩

/-- Pairwise non-adjacent single-bit moves span a subcube of solutions. -/
private theorem flipOn_mem_solutions_of_independent {ψ : ClauseSet (Fin N)} {x : BitString N}
    {M : Finset (Fin N)} (hx : x ∈ ψ.solutions) (hmove : ∀ i ∈ M, flipOn {i} x ∈ ψ.solutions)
    (hind : ∀ u ∈ M, ∀ w ∈ M, u ≠ w → w ∉ ψ.neighbors u) {T : Finset (Fin N)} (hT : T ⊆ M) :
    flipOn T x ∈ ψ.solutions := by
  have h := flipOn_biUnion_mem_solutions_of_separated (T := fun i => {i}) hx hmove
    (fun C hC j hj j' hj' hne hmeet hmeet' => by
      obtain ⟨l, hl, hlj⟩ := hmeet
      obtain ⟨l', hl', hlj'⟩ := hmeet'
      rw [mem_singleton] at hlj hlj'
      apply hind j hj j' hj' hne
      simp only [neighbors, mem_filter, mem_univ, true_and]
      exact ⟨Ne.symm hne, C, hC, ⟨l, hl, hlj⟩, l', hl', hlj'⟩) hT
  simpa using h

/-- Co-occurrence adjacency in `neighbors` is symmetric. -/
theorem mem_neighbors_comm {ψ : ClauseSet (Fin N)} {u w : Fin N} :
    w ∈ ψ.neighbors u ↔ u ∈ ψ.neighbors w := by
  simp only [neighbors, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hne, C, hC, hu, hw⟩
    exact ⟨Ne.symm hne, C, hC, hw, hu⟩
  · rintro ⟨hne, C, hC, hw, hu⟩
    exact ⟨Ne.symm hne, C, hC, hu, hw⟩

/-- **Few non-isolated directions**: if every variable has at most `Δ` neighbours and the
solutions contain no subcube of dimension `D`, every solution has at most `(D - 1)(Δ + 1)`
directions in which it is not isolated. A largest set of pairwise non-adjacent non-isolated
directions spans a subcube of solutions, and its closed neighbourhood holds every non-isolated
direction. -/
theorem card_compl_isolatedDirections_le {ψ : ClauseSet (Fin N)} {Δ D : ℕ}
    (hdeg : ∀ u, (ψ.neighbors u).card ≤ Δ)
    (hfree : ¬ ContainsSubcube (ψ.solutions : Set (BitString N)) D) {x : BitString N}
    (hx : x ∈ ψ.solutions) :
    (univ \ isolatedDirections ψ.solutions x).card ≤ (D - 1) * (Δ + 1) := by
  set NI := univ \ isolatedDirections ψ.solutions x with hNI
  have hmemNI : ∀ i, i ∈ NI ↔ flipOn {i} x ∈ ψ.solutions := by
    intro i
    simp [hNI, isolatedDirections]
  let Ind : Finset (Finset (Fin N)) := NI.powerset.filter fun M =>
    ∀ u ∈ M, ∀ w ∈ M, u ≠ w → w ∉ ψ.neighbors u
  have hInd : (∅ : Finset (Fin N)) ∈ Ind := by simp [Ind]
  obtain ⟨M, hM, hmax⟩ := Ind.exists_max_image card ⟨∅, hInd⟩
  simp only [Ind, mem_filter, mem_powerset] at hM
  obtain ⟨hMNI, hMind⟩ := hM
  have hmove : ∀ i ∈ M, flipOn {i} x ∈ ψ.solutions := fun i hi => (hmemNI i).mp (hMNI hi)
  -- the independent set is small
  have hMcard : M.card ≤ D - 1 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨J, hJM, hJcard⟩ := exists_subset_card_eq (s := M) (n := D) (by omega)
    exact hfree ⟨x, J, hJcard, fun T hT =>
      flipOn_mem_solutions_of_independent hx hmove hMind (hT.trans hJM)⟩
  -- every non-isolated direction is in its closed neighbourhood
  have hcover : NI ⊆ M ∪ M.biUnion ψ.neighbors := by
    intro i hi
    by_cases hiM : i ∈ M
    · exact mem_union_left _ hiM
    · refine mem_union_right _ (mem_biUnion.mpr ?_)
      by_contra hnone
      push Not at hnone
      have hins : insert i M ∈ Ind := by
        simp only [Ind, mem_filter, mem_powerset]
        refine ⟨insert_subset hi hMNI, fun u hu w hw hne => ?_⟩
        rw [mem_insert] at hu hw
        by_cases hui : u = i
        · subst hui
          rcases hw with hwi | hwM
          · exact absurd hwi.symm hne
          · exact fun h => hnone w hwM (mem_neighbors_comm.mp h)
        · have huM : u ∈ M := hu.resolve_left hui
          by_cases hwi : w = i
          · subst hwi
            exact hnone u huM
          · exact hMind u huM w (hw.resolve_left hwi) hne
      have := hmax _ hins
      rw [card_insert_of_notMem hiM] at this
      omega
  calc NI.card ≤ (M ∪ M.biUnion ψ.neighbors).card := card_le_card hcover
    _ ≤ M.card + (M.biUnion ψ.neighbors).card := card_union_le _ _
    _ ≤ M.card + ∑ m ∈ M, (ψ.neighbors m).card := by gcongr; exact card_biUnion_le
    _ ≤ M.card + ∑ _m ∈ M, Δ := by gcongr with m; exact hdeg m
    _ = M.card * (Δ + 1) := by rw [sum_const, smul_eq_mul]; ring
    _ ≤ (D - 1) * (Δ + 1) := Nat.mul_le_mul_right _ hMcard

/-- In a clause set of width at most `k`, a variable in `c` clauses has at most `c (k - 1)`
neighbours. -/
theorem card_neighbors_le {ψ : ClauseSet (Fin N)} {k : ℕ} (hk : ∀ C ∈ ψ, C.card ≤ k)
    (u : Fin N) : (ψ.neighbors u).card ≤ ψ.occurrences u * (k - 1) := by
  let Cu := ψ.filter fun C => ∃ l ∈ C, l.1 = u
  have hsub : ψ.neighbors u ⊆ Cu.biUnion fun C => (C.image Prod.fst).erase u := by
    intro w hw
    simp only [neighbors, mem_filter, mem_univ, true_and] at hw
    obtain ⟨hne, C, hC, hu, l, hl, hlw⟩ := hw
    exact mem_biUnion.mpr ⟨C, mem_filter.mpr ⟨hC, hu⟩, mem_erase.mpr ⟨hne, mem_image.mpr
      ⟨l, hl, hlw⟩⟩⟩
  calc (ψ.neighbors u).card
      ≤ (Cu.biUnion fun C => (C.image Prod.fst).erase u).card := card_le_card hsub
    _ ≤ ∑ C ∈ Cu, ((C.image Prod.fst).erase u).card := card_biUnion_le
    _ ≤ ∑ _C ∈ Cu, (k - 1) := by
        refine sum_le_sum fun C hC => ?_
        obtain ⟨hCψ, l, hl, hlu⟩ := mem_filter.mp hC
        rw [card_erase_of_mem (mem_image.mpr ⟨l, hl, hlu⟩)]
        exact Nat.sub_le_sub_right (card_image_le.trans (hk C hCψ)) 1
    _ = ψ.occurrences u * (k - 1) := by rw [sum_const, smul_eq_mul]; rfl

/-- **The coding lemma for clause sets**: if every clause has at most `k ≥ 1` literals,
`∑ₓ 2 ^ (ι(x) / k) ≤ 2 ^ N` over the solutions `x`, where `ι(x)` is the number of isolated
directions of `x`. -/
private theorem sum_two_rpow_card_isolatedDirections_div_le {ψ : ClauseSet (Fin N)} {k : ℕ}
    (hk1 : 1 ≤ k) (hk : ∀ C ∈ ψ, C.card ≤ k) :
    ∑ x ∈ ψ.solutions, (2 : ℝ) ^ (((isolatedDirections ψ.solutions x).card : ℝ) / k) ≤
      2 ^ N := by
  have h := CNF.sum_two_rpow_card_isolated_div_le (φ := ψ.toCNF) hk1
    fun c hc => ClauseSet.length_le_of_mem_toCNF hk hc
  have hsol : ψ.solutions = ({x | ψ.toCNF.eval x = true} : Finset (BitString N)) := by
    ext x
    simp [eval_toCNF_eq_true_iff]
  refine le_of_eq_of_le (sum_congr hsol fun x _ => ?_) h
  have hiso : isolatedDirections ψ.solutions x =
      ({i | ψ.toCNF.eval (Function.update x i (!x i)) = false} : Finset (Fin N)) := by
    ext i
    simp only [isolatedDirections, flipOn_singleton, mem_filter, mem_univ, true_and,
      mem_solutions, ← eval_toCNF_eq_true_iff, Bool.not_eq_true]
  rw [hiso]

/-- **Few solutions in bounded degree**: if every clause of `ψ` has at most `k ≥ 1` literals, every
variable has at most `Δ` neighbours, and the solutions contain no subcube of dimension `D`, then
`ψ` has at most `2 ^ ((1 - 1 / k) N + (D - 1)(Δ + 1) / k)` solutions. -/
theorem card_solutions_le_of_neighbors {ψ : ClauseSet (Fin N)} {k Δ D : ℕ} (hk1 : 1 ≤ k)
    (hk : ∀ C ∈ ψ, C.card ≤ k) (hdeg : ∀ u, (ψ.neighbors u).card ≤ Δ)
    (hfree : ¬ ContainsSubcube (ψ.solutions : Set (BitString N)) D) :
    (ψ.solutions.card : ℝ) ≤
      (2 : ℝ) ^ ((1 - 1 / (k : ℝ)) * N + (((D - 1) * (Δ + 1) : ℕ) : ℝ) / k) := by
  set m : ℕ := (D - 1) * (Δ + 1)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  -- each solution has at least `N - m` isolated directions
  have hiso : ∀ x ∈ ψ.solutions,
      ((N : ℝ) - m) / k ≤ ((isolatedDirections ψ.solutions x).card : ℝ) / k := by
    intro x hx
    refine div_le_div_of_nonneg_right ?_ hkpos.le
    have hle := card_compl_isolatedDirections_le hdeg hfree hx
    have hsplit : (univ \ isolatedDirections ψ.solutions x).card +
        (isolatedDirections ψ.solutions x).card = N := by
      rw [card_sdiff_add_card_eq_card (subset_univ _), card_univ, Fintype.card_fin]
    have : (N : ℝ) = ((univ \ isolatedDirections ψ.solutions x).card : ℝ) +
        (isolatedDirections ψ.solutions x).card := by exact_mod_cast hsplit.symm
    have hle' : ((univ \ isolatedDirections ψ.solutions x).card : ℝ) ≤ m := by
      exact_mod_cast hle
    linarith
  have hlower : (ψ.solutions.card : ℝ) * (2 : ℝ) ^ (((N : ℝ) - m) / k) ≤ 2 ^ N := by
    calc (ψ.solutions.card : ℝ) * (2 : ℝ) ^ (((N : ℝ) - m) / k)
        = ∑ _x ∈ ψ.solutions, (2 : ℝ) ^ (((N : ℝ) - m) / k) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ ψ.solutions,
            (2 : ℝ) ^ (((isolatedDirections ψ.solutions x).card : ℝ) / k) :=
          sum_le_sum fun x hx => Real.rpow_le_rpow_of_exponent_le (by norm_num) (hiso x hx)
      _ ≤ 2 ^ N := sum_two_rpow_card_isolatedDirections_div_le hk1 hk
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (((N : ℝ) - m) / k) := by positivity
  rw [← le_div_iff₀ hpos, ← Real.rpow_natCast, ← Real.rpow_sub (by norm_num)] at hlower
  refine hlower.trans (le_of_eq ?_)
  congr 1
  field_simp
  ring

/-- **Formulas without large subcubes of solutions have few solutions**: for every width `k ≥ 1`
and every `ε > 0` there is a constant `C` such that every clause set of width `k` over `N`
variables whose solutions contain no subcube of dimension `D` has at most
`2 ^ ((1 - 1 / k + ε) N + C D)` solutions. -/
theorem card_solutions_le_of_not_containsSubcube (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (φ : ClauseSet (Fin N)) (D : ℕ), (∀ C ∈ φ, C.card ≤ k) →
      ¬ ContainsSubcube (φ.solutions : Set (BitString N)) D →
      (φ.solutions.card : ℝ) ≤ 2 ^ ((1 - 1 / (k : ℝ) + ε) * N + C * D) := by
  obtain ⟨c, hc⟩ := ClauseSet.sparsification.{0} k hε
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨((c * (k - 1) + 1 : ℕ) : ℝ) / k, by positivity, fun N φ D hφ hfree => ?_⟩
  obtain ⟨Ψ, hcard, hleaves, hcover⟩ := hc (Fin N) φ hφ
  rw [Fintype.card_fin] at hcard
  set E : ℝ := (1 - 1 / (k : ℝ)) * N + ((c * (k - 1) + 1 : ℕ) : ℝ) / k * D
  have hpiece : ∀ ψ ∈ Ψ, (ψ.solutions.card : ℝ) ≤ 2 ^ E := by
    intro ψ hψ
    obtain ⟨hwidth, hocc, hsol⟩ := hleaves ψ hψ
    have hdeg : ∀ u, (ψ.neighbors u).card ≤ c * (k - 1) := fun u =>
      (card_neighbors_le hwidth u).trans (Nat.mul_le_mul_right _ (hocc u))
    have hfree' : ¬ ContainsSubcube (ψ.solutions : Set (BitString N)) D :=
      fun h => hfree (h.mono (by exact_mod_cast hsol))
    refine (card_solutions_le_of_neighbors hk hwidth hdeg hfree').trans ?_
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    simp only [E]
    gcongr
    rw [div_mul_eq_mul_div]
    gcongr
    have : (D - 1) * (c * (k - 1) + 1) ≤ (c * (k - 1) + 1) * D := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.sub_le D 1)
    exact_mod_cast this
  calc (φ.solutions.card : ℝ) ≤ ((Ψ.biUnion solutions).card : ℝ) := by
        exact_mod_cast card_le_card hcover
    _ ≤ ∑ ψ ∈ Ψ, (ψ.solutions.card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _ψ ∈ Ψ, (2 : ℝ) ^ E := sum_le_sum hpiece
    _ = (Ψ.card : ℝ) * 2 ^ E := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ (ε * N) * 2 ^ E := by gcongr
    _ = 2 ^ ((1 - 1 / (k : ℝ) + ε) * N + ((c * (k - 1) + 1 : ℕ) : ℝ) / k * D) := by
        rw [← Real.rpow_add (by norm_num)]
        congr 1
        simp only [E]
        ring

end ClauseSet

/-- **Formulas without large subcubes of solutions have few solutions**: for every width `k ≥ 1`
and every `ε > 0` there is a constant `C` such that every formula in conjunctive normal form of
width `k` over `N` variables whose solutions contain no subcube of dimension `D` has at most
`2 ^ ((1 - 1 / k + ε) N + C D)` solutions. -/
theorem CNF.card_filter_eval_le_of_not_containsSubcube (k : ℕ) (hk : 1 ≤ k) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (φ : CNF (Fin N)) (D : ℕ), (∀ c ∈ φ, c.length ≤ k) →
      ¬ ContainsSubcube {x : BitString N | φ.eval x = true} D →
      (#{x : BitString N | φ.eval x = true} : ℝ) ≤ 2 ^ ((1 - 1 / (k : ℝ) + ε) * N + C * D) := by
  obtain ⟨C, hC, h⟩ := ClauseSet.card_solutions_le_of_not_containsSubcube k hk hε
  refine ⟨C, hC, fun N φ D hφ hfree => ?_⟩
  have hsol : φ.toClauseSet.solutions = ({x | φ.eval x = true} : Finset (BitString N)) := by
    ext x
    simp [CNF.sat_toClauseSet_iff]
  rw [← hsol]
  refine h N φ.toClauseSet D (fun C hC => ?_) ?_
  · obtain ⟨c, hc, hle⟩ := CNF.exists_card_le_of_mem_toClauseSet hC
    exact hle.trans (hφ c hc)
  · rw [hsol, coe_filter]
    simpa using hfree

end Logic.PL

end Cslib
