/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Query.Select.MinMax.Basic
public import Complexity.Algorithms.Lean.Query.Sort.LEQuery.Fooling
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Extension.Linear

/-!
# Comparison lower bounds for the minimum, and for the minimum and maximum

In cslib's comparison-query model `FreeM (LEQuery α)`:

* every correct algorithm for the minimum (`Cslib.Query.IsMinAlg`) makes at least `n - 1`
  comparisons on every list of `n` distinct elements, against **every** oracle implementing a
  linear order (`Cslib.Query.IsMinAlg.length_sub_one_le_countQueries`);
* every correct algorithm for the minimum and maximum together (`Cslib.Query.IsMinMaxAlg`) makes
  at least `⌈3n/2⌉ - 2` comparisons on every list of `n` distinct elements, against **some**
  oracle implementing a linear order (`Cslib.Query.IsMinMaxAlg.exists_le_countQueries`).

Both bounds are attained, by `Cslib.Query.findMin` and `Cslib.Query.findMinMax`.

## Proof

Call `x` *found above* by a run if some comparison `a ≤ b` of the run with `a ≠ b` has `x` on its
strictly larger side: `x = b` and the answer is true, or `x = a` and the answer is false
(`Cslib.Query.FoundAbove`). In a linear order, moving an element that was never found above to
the bottom (`Cslib.Query.moveToBot`) does not change any answer of the run
(`Cslib.Query.agreeOn_moveToBot`, `Cslib.Query.eval_moveToBot_eq`), so a correct algorithm cannot
tell the two orders apart, and its answer must be a least element of both. Hence every element
except the reported minimum is found above by the run, and since each comparison finds at most
one element above, a run of a correct minimum algorithm has at least `n - 1` comparisons. The dual
argument (`Cslib.Query.moveToTop`) shows that every element except the reported maximum is *found
below* (`Cslib.Query.FoundBelow`) by a run of a correct minimum-and-maximum algorithm.

For the minimum and maximum, the adversary answers each comparison by moving one of the two
elements to the top or the bottom of its current linear order, which keeps every earlier answer.
An element that has only been found above moves to the top and wins, one that has only been found
below moves to the bottom and loses, and otherwise the adversary keeps its order. Let an element
weigh `1` if it has been found neither above nor below, `2` if it has been found exactly one way,
and `4` if both. Then the total weight of the input grows by at most `2` per comparison, from `n`
at the start to at least `4n - 4` at the end. This is the classical argument of Pohl ([Pohl1972];
see [Knuth1998], Section 5.3.3, and [CLRS2009], Section 9.1), with the element states recorded as
facts about the run.

## Main results

* `Cslib.Query.IsMinAlg.card_toFinset_sub_one_le_countQueries`,
  `Cslib.Query.IsMinAlg.length_sub_one_le_countQueries`: `n - 1` comparisons against every linear
  order.
* `Cslib.Query.IsMinAlg.lowerBound_infinite`: the `n - 1` bound as a `Cslib.Query.LowerBound`.
* `Cslib.Query.IsMinAlg.countQueries_findMin_le`: `findMin` is optimal on every input.
* `Cslib.Query.IsMinMaxAlg.exists_card_toFinset_le_countQueries`,
  `Cslib.Query.IsMinMaxAlg.exists_le_countQueries`: `⌈3n/2⌉ - 2` comparisons against some linear
  order.
* `Cslib.Query.IsMinMaxAlg.lowerBound_infinite`: the `⌈3n/2⌉ - 2` bound as a
  `Cslib.Query.LowerBound`.
* `Cslib.Query.IsMinMaxAlg.exists_countQueries_findMinMax_le`: `findMinMax` is optimal on every
  input.

## References

* [I. Pohl, *A sorting problem and its complexity*][Pohl1972].
* [D. E. Knuth, *The Art of Computer Programming, Volume 3: Sorting and Searching*][Knuth1998],
  Section 5.3.3.
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Section 9.1.
-/

public section

namespace Cslib.Query

variable {α γ : Type}

/-! ## The minimum -/

/-- **Lower bound for the minimum, per input.** Against every oracle implementing a linear order,
a correct algorithm for the minimum makes at least `n - 1` comparisons on a list with `n` distinct
entries: every entry except the reported minimum must be found above by some comparison, and each
comparison finds at most one entry above. -/
theorem IsMinAlg.card_toFinset_sub_one_le_countQueries [DecidableEq α]
    {alg : List α → FreeM (LEQuery α) (Option α)} (halg : IsMinAlg alg)
    (r : α → α → Prop) [DecidableRel r] [IsLinearOrder α r]
    (oracle : {ι : Type} → LEQuery α ι → ι) (horacle : ∀ a b, oracle (.le a b) = decide (r a b))
    (xs : List α) : xs.toFinset.card - 1 ≤ (alg xs).countQueries oracle := by
  classical
  rcases eq_or_ne xs [] with rfl | hxs
  · simp
  obtain ⟨m, hm, -, hmin⟩ := halg.correct r oracle horacle xs hxs
  set Q := LEQuery.queriedPairs oracle (alg xs)
  have habove : ∀ x ∈ xs, x ≠ m → FoundAbove r Q x := by
    intro x hx hxm
    by_contra hnot
    have := isLinearOrder_moveToBot r x
    obtain ⟨m', hm', -, hmin'⟩ := halg.correct (moveToBot r x)
      (LEQuery.oracleOf fun a b => decide (moveToBot r x a b)) (fun _ _ => rfl) xs hxs
    rw [eval_moveToBot_eq oracle horacle (alg xs) hnot, hm, Option.some.injEq] at hm'
    subst hm'
    rcases moveToBot_iff.mp (hmin' x hx) with h | ⟨h, -⟩
    · exact hxm h.symm
    · exact h rfl
  have hsub : xs.toFinset.erase m ⊆
      Q.toFinset.image fun ab => if r ab.1 ab.2 then ab.2 else ab.1 := by
    intro x hx
    obtain ⟨hxm, hx⟩ := Finset.mem_erase.mp hx
    obtain ⟨a, b, hab, -, h⟩ := foundAbove_iff.mp (habove x (List.mem_toFinset.mp hx) hxm)
    refine Finset.mem_image.mpr ⟨(a, b), List.mem_toFinset.mpr hab, ?_⟩
    rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp [h]
  calc xs.toFinset.card - 1
      ≤ (xs.toFinset.erase m).card := Finset.pred_card_le_card_erase
    _ ≤ (Q.toFinset.image fun ab => if r ab.1 ab.2 then ab.2 else ab.1).card :=
        Finset.card_le_card hsub
    _ ≤ Q.toFinset.card := Finset.card_image_le
    _ ≤ Q.length := List.toFinset_card_le Q
    _ = (alg xs).countQueries oracle := LEQuery.length_queriedPairs oracle (alg xs)

/-- **Lower bound for the minimum.** Against every oracle implementing a linear order, a correct
algorithm for the minimum makes at least `n - 1` comparisons on every list of `n` distinct
elements. -/
theorem IsMinAlg.length_sub_one_le_countQueries {alg : List α → FreeM (LEQuery α) (Option α)}
    (halg : IsMinAlg alg) (r : α → α → Prop) [DecidableRel r] [IsLinearOrder α r]
    (oracle : {ι : Type} → LEQuery α ι → ι) (horacle : ∀ a b, oracle (.le a b) = decide (r a b))
    {xs : List α} (hxs : xs.Nodup) : xs.length - 1 ≤ (alg xs).countQueries oracle := by
  classical
  rw [← List.toFinset_card_of_nodup hxs]
  exact halg.card_toFinset_sub_one_le_countQueries r oracle horacle xs

/-- Every type carries a linear order. -/
private theorem exists_isLinearOrder (α : Type) : ∃ r : α → α → Prop, IsLinearOrder α r := by
  have : IsPartialOrder α (· = ·) :=
    { refl := fun _ => rfl, trans := fun _ _ _ => Eq.trans, antisymm := fun _ _ h _ => h }
  obtain ⟨r, hr, -⟩ := extend_partialOrder (α := α) (· = ·)
  exact ⟨r, hr⟩

/-- Some list of `n` distinct elements of an infinite type. -/
private theorem exists_nodup_length (α : Type) [Infinite α] (n : ℕ) :
    ∃ xs : List α, xs.Nodup ∧ xs.length = n := by
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq α n
  exact ⟨s.toList, s.nodup_toList, by rw [Finset.length_toList, hs]⟩

/-- **Lower bound for the minimum**, as a query lower bound: on an infinite type, every correct
algorithm for the minimum makes at least `n - 1` comparisons on some list of length `n`. -/
theorem IsMinAlg.lowerBound_infinite [Infinite α] {alg : List α → FreeM (LEQuery α) (Option α)}
    (halg : IsMinAlg alg) : LowerBound alg List.length (· - 1) := by
  classical
  intro n
  obtain ⟨xs, hnodup, hlen⟩ := exists_nodup_length α n
  obtain ⟨r, hr⟩ := exists_isLinearOrder α
  refine ⟨xs, hlen.le, LEQuery.oracleOf fun a b => decide (r a b), ?_⟩
  rw [← hlen]
  exact halg.length_sub_one_le_countQueries r _ (fun _ _ => rfl) hnodup

/-- The linear scan is optimal on every input: on a list of distinct elements, a correct algorithm
for the minimum makes, against every oracle implementing a linear order, at least as many
comparisons as `findMin` makes against any oracle. -/
theorem IsMinAlg.countQueries_findMin_le {alg : List α → FreeM (LEQuery α) (Option α)}
    (halg : IsMinAlg alg) (r : α → α → Prop) [DecidableRel r] [IsLinearOrder α r]
    (oracle : {ι : Type} → LEQuery α ι → ι) (horacle : ∀ a b, oracle (.le a b) = decide (r a b))
    {xs : List α} (hxs : xs.Nodup) (oracle' : {ι : Type} → LEQuery α ι → ι) :
    (findMin xs).countQueries oracle' ≤ (alg xs).countQueries oracle :=
  (countQueries_findMin oracle' xs).trans_le
    (halg.length_sub_one_le_countQueries r oracle horacle hxs)

/-! ## The adversary for the minimum and maximum -/

open Classical in
/-- The weight of an element that is found above (`A`) or below (`B`): `1`, `2`, `2` or `4`. -/
private noncomputable def wt (A B : Prop) : ℕ := (if A then 2 else 1) * (if B then 2 else 1)

/-- The potential of the comparisons `T` against `r` on the elements `S`: the total weight of the
elements of `S`. -/
private noncomputable def potential (S : Finset α) (r : α → α → Prop) (T : List (α × α)) : ℕ :=
  ∑ x ∈ S, wt (FoundAbove r T x) (FoundBelow r T x)

private theorem potential_nil (S : Finset α) (r : α → α → Prop) : potential S r [] = S.card := by
  simp [potential, wt]

private theorem potential_congr {S : Finset α} {r r' : α → α → Prop} {T : List (α × α)}
    (h : AgreeOn r r' T) : potential S r T = potential S r' T := by
  unfold potential
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [propext (foundAbove_congr h x), propext (foundBelow_congr h x)]

/-- The total weight grows by at most `2` when `w` becomes found above and `l` found below,
provided `w` was found above already if `l` was only found above, and `l` was found below already
if `w` was only found below. -/
private theorem sum_wt_le (S : Finset α) (A B A' B' : α → Prop) {w l : α}
    (hwl : w ≠ l) (hA : ∀ x, A' x ↔ A x ∨ x = w) (hB : ∀ x, B' x ↔ B x ∨ x = l)
    (h1 : B w ∧ ¬ A w → B l) (h2 : A l ∧ ¬ B l → A w) :
    ∑ x ∈ S, wt (A' x) (B' x) ≤ ∑ x ∈ S, wt (A x) (B x) + 2 := by
  classical
  set d : α → ℕ := fun x => wt (A' x) (B' x) - wt (A x) (B x)
  have hpt : ∀ x, wt (A' x) (B' x) ≤ wt (A x) (B x) + (if x = w then d w else 0) +
      (if x = l then d l else 0) := by
    intro x
    by_cases hxw : x = w
    · subst hxw
      simp only [d, ↓reduceIte, hwl]
      omega
    by_cases hxl : x = l
    · subst hxl
      simp only [d, hxw, ↓reduceIte]
      omega
    have hA' : A' x ↔ A x := by rw [hA]; simp [hxw]
    have hB' : B' x ↔ B x := by rw [hB]; simp [hxl]
    simp [hxw, hxl, propext hA', propext hB']
  have hd : d w + d l ≤ 2 := by
    have hAw : A' w := (hA w).mpr (Or.inr rfl)
    have hBl : B' l := (hB l).mpr (Or.inr rfl)
    have hBw : B' w ↔ B w := by rw [hB]; simp [hwl]
    have hAl : A' l ↔ A l := by rw [hA]; simp [Ne.symm hwl]
    simp only [d, wt, hAw, hBl, propext hBw, propext hAl, ↓reduceIte]
    by_cases haw : A w <;> by_cases hbw : B w <;> by_cases hal : A l <;> by_cases hbl : B l <;>
      simp only [haw, hbw, hal, hbl, ↓reduceIte] <;> first | omega | tauto
  calc ∑ x ∈ S, wt (A' x) (B' x)
      ≤ ∑ x ∈ S, (wt (A x) (B x) + (if x = w then d w else 0) + (if x = l then d l else 0)) :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = ∑ x ∈ S, wt (A x) (B x) + (if w ∈ S then d w else 0) + (if l ∈ S then d l else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
          Finset.sum_ite_eq']
    _ ≤ ∑ x ∈ S, wt (A x) (B x) + 2 := by split_ifs <;> omega

/-- **One adversary step.** Before a comparison `a ≤ b`, the adversary can move to a linear order
that keeps the earlier answers `T` and lets the potential grow by at most `2`: it raises an
element only found above, lowers an element only found below, and keeps `r` otherwise. -/
private theorem exists_step (S : Finset α) (r : α → α → Prop) [IsLinearOrder α r]
    (T : List (α × α)) (a b : α) :
    ∃ r' : α → α → Prop, IsLinearOrder α r' ∧ AgreeOn r r' T ∧
      potential S r' (T ++ [(a, b)]) ≤ potential S r T + 2 := by
  classical
  by_cases hab : a = b
  · subst hab
    refine ⟨r, inferInstance, AgreeOn.refl r T, ?_⟩
    unfold potential
    simp only [propext (foundAbove_append_singleton_self a _),
      propext (foundBelow_append_singleton_self a _)]
    omega
  -- The potential bound for any linear order `r'` keeping the answers `T`, under the two
  -- conditions on the winner and the loser of `a ≤ b` against `r'`.
  have key : ∀ r' : α → α → Prop, AgreeOn r r' T →
      (r' a b → ((FoundBelow r T b ∧ ¬ FoundAbove r T b → FoundBelow r T a) ∧
        (FoundAbove r T a ∧ ¬ FoundBelow r T a → FoundAbove r T b))) →
      (¬ r' a b → ((FoundBelow r T a ∧ ¬ FoundAbove r T a → FoundBelow r T b) ∧
        (FoundAbove r T b ∧ ¬ FoundBelow r T b → FoundAbove r T a))) →
      potential S r' (T ++ [(a, b)]) ≤ potential S r T + 2 := by
    intro r' hagree hyes hno
    rw [potential_congr hagree]
    have hA := foundAbove_congr hagree
    have hB := foundBelow_congr hagree
    by_cases h : r' a b
    · obtain ⟨h1, h2⟩ := hyes h
      refine sum_wt_le S (FoundAbove r' T) (FoundBelow r' T) _ _ (Ne.symm hab)
        (foundAbove_append_singleton_of_rel hab h) (foundBelow_append_singleton_of_rel hab h) ?_ ?_
      · rw [← hA, ← hB, ← hB]; exact h1
      · rw [← hA, ← hB, ← hA]; exact h2
    · obtain ⟨h1, h2⟩ := hno h
      refine sum_wt_le S (FoundAbove r' T) (FoundBelow r' T) _ _ hab
        (foundAbove_append_singleton_of_not_rel hab h)
        (foundBelow_append_singleton_of_not_rel hab h) ?_ ?_
      · rw [← hA, ← hB, ← hB]; exact h1
      · rw [← hA, ← hB, ← hA]; exact h2
  by_cases hUa : FoundAbove r T a ∧ ¬ FoundBelow r T a
  · -- `a` has only been found above: raise it, so that `a ≤ b` is false.
    refine ⟨moveToTop r a, isLinearOrder_moveToTop r a, agreeOn_moveToTop hUa.2,
      key _ (agreeOn_moveToTop hUa.2) (fun h => ?_)
        fun _ => ⟨fun h => absurd h.1 hUa.2, fun _ => hUa.1⟩⟩
    rcases moveToTop_iff.mp h with h | ⟨h, -⟩
    · exact absurd h.symm hab
    · exact absurd rfl h
  by_cases hUb : FoundAbove r T b ∧ ¬ FoundBelow r T b
  · -- `b` has only been found above: raise it, so that `a ≤ b` is true.
    refine ⟨moveToTop r b, isLinearOrder_moveToTop r b, agreeOn_moveToTop hUb.2,
      key _ (agreeOn_moveToTop hUb.2) (fun _ => ⟨fun h => absurd h.1 hUb.2, fun _ => hUb.1⟩)
        fun h => absurd (moveToTop_top r b a) h⟩
  by_cases hDa : FoundBelow r T a ∧ ¬ FoundAbove r T a
  · -- `a` has only been found below: lower it, so that `a ≤ b` is true.
    refine ⟨moveToBot r a, isLinearOrder_moveToBot r a, agreeOn_moveToBot hDa.2,
      key _ (agreeOn_moveToBot hDa.2) (fun _ => ⟨fun _ => hDa.1, fun h => absurd h.1 hDa.2⟩)
        fun h => absurd (moveToBot_bot r a b) h⟩
  by_cases hDb : FoundBelow r T b ∧ ¬ FoundAbove r T b
  · -- `b` has only been found below: lower it, so that `a ≤ b` is false.
    refine ⟨moveToBot r b, isLinearOrder_moveToBot r b, agreeOn_moveToBot hDb.2,
      key _ (agreeOn_moveToBot hDb.2) (fun h => ?_)
        fun _ => ⟨fun _ => hDb.1, fun h => absurd h.1 hDb.2⟩⟩
    rcases moveToBot_iff.mp h with h | ⟨h, -⟩
    · exact absurd h hab
    · exact absurd rfl h
  -- Otherwise keep `r`.
  exact ⟨r, inferInstance, AgreeOn.refl r T, key r (AgreeOn.refl r T)
    (fun _ => ⟨fun h => absurd ⟨h.1, h.2⟩ hDb, fun h => absurd ⟨h.1, h.2⟩ hUa⟩)
    fun _ => ⟨fun h => absurd ⟨h.1, h.2⟩ hDa, fun h => absurd ⟨h.1, h.2⟩ hUb⟩⟩

/-- **The adversary.** Starting from a linear order `r` that answers the comparisons `T`, there is
a linear order `r'` that keeps those answers and against which `p` raises the potential by at most
`2` per comparison. -/
private theorem exists_adversary (S : Finset α) (p : FreeM (LEQuery α) γ) :
    ∀ (T : List (α × α)) (r : α → α → Prop), IsLinearOrder α r →
      ∃ r' : α → α → Prop, IsLinearOrder α r' ∧ AgreeOn r r' T ∧
        potential S r' (T ++ LEQuery.queriedPairs
          (LEQuery.oracleOf fun a b => @decide (r' a b) (Classical.propDecidable _)) p) ≤
          potential S r T + 2 * p.countQueries
            (LEQuery.oracleOf fun a b => @decide (r' a b) (Classical.propDecidable _)) := by
  induction p with
  | pure x =>
    intro T r hr
    exact ⟨r, hr, AgreeOn.refl r T, by simp⟩
  | lift_bind op cont ih =>
    cases op with
    | le a b =>
      intro T r hr
      obtain ⟨r₁, hr₁, hagree₁, hstep⟩ := exists_step S r T a b
      obtain ⟨r₂, hr₂, hagree₂, hbound⟩ :=
        ih (@decide (r₁ a b) (Classical.propDecidable _)) (T ++ [(a, b)]) r₁ hr₁
      refine ⟨r₂, hr₂, hagree₁.trans (hagree₂.mono fun q hq => List.mem_append_left _ hq), ?_⟩
      have hans : @decide (r₂ a b) (Classical.propDecidable _) =
          @decide (r₁ a b) (Classical.propDecidable _) :=
        decide_eq_decide.mpr
          (hagree₂.iff (List.mem_append_right _ (List.mem_singleton_self _))).symm
      rw [FreeM.bind_eq_bind, LEQuery.queriedPairs_liftBind, FreeM.countQueries_liftBind,
        LEQuery.oracleOf_le, hans]
      rw [List.append_assoc, List.singleton_append] at hbound
      omega

/-- If every element of `S` except `m` is found above and every element except `M` is found
below, then the potential is at least `4 |S| - 4`. -/
private theorem potential_ge (S : Finset α) (r : α → α → Prop)
    (T : List (α × α)) (m M : α) (habove : ∀ x ∈ S, x ≠ m → FoundAbove r T x)
    (hbelow : ∀ x ∈ S, x ≠ M → FoundBelow r T x) : 4 * S.card ≤ potential S r T + 4 := by
  classical
  have hpt : ∀ x ∈ S, 4 ≤ wt (FoundAbove r T x) (FoundBelow r T x) + (if x = m then 2 else 0) +
      (if x = M then 2 else 0) := by
    intro x hx
    unfold wt
    by_cases hxm : x = m <;> by_cases hxM : x = M
    · split_ifs <;> omega
    · have := hbelow x hx hxM
      split_ifs <;> omega
    · have := habove x hx hxm
      split_ifs <;> omega
    · have hA := habove x hx hxm
      have hB := hbelow x hx hxM
      simp only [hxm, hxM, hA, hB, ↓reduceIte]
      omega
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
    Finset.sum_const, smul_eq_mul] at hsum
  unfold potential
  split_ifs at hsum <;> omega

/-! ## The minimum and maximum -/

/-- **Lower bound for the minimum and maximum, per input.** For every correct algorithm for the
minimum and maximum and every list `xs` with `n` distinct entries, some oracle implementing a
linear order makes the algorithm use at least `⌈3n/2⌉ - 2 = (3n + 1) / 2 - 2` comparisons on
`xs`. -/
theorem IsMinMaxAlg.exists_card_toFinset_le_countQueries [DecidableEq α]
    {alg : List α → FreeM (LEQuery α) (Option (α × α))} (halg : IsMinMaxAlg alg) (xs : List α) :
    ∃ f : α → α → Bool, IsLinearOrder α (fun a b => f a b = true) ∧
      (3 * xs.toFinset.card + 1) / 2 - 2 ≤ (alg xs).countQueries (LEQuery.oracleOf f) := by
  classical
  obtain ⟨r₀, hr₀⟩ := exists_isLinearOrder α
  set S := xs.toFinset
  obtain ⟨r, hr, -, hpot⟩ := exists_adversary S (alg xs) [] r₀ hr₀
  set f : α → α → Bool := fun a b => @decide (r a b) (Classical.propDecidable _)
  have hfr : (fun a b => f a b = true) = r := by
    funext a b
    simp [f]
  refine ⟨f, by rw [hfr]; exact hr, ?_⟩
  set oracle : {ι : Type} → LEQuery α ι → ι := LEQuery.oracleOf f
  rw [List.nil_append, potential_nil] at hpot
  rcases eq_or_ne xs [] with rfl | hxs
  · simp [S]
  have horacle : ∀ a b, oracle (.le a b) = decide (r a b) := fun a b => by
    simp only [oracle, LEQuery.oracleOf_le, f]
  obtain ⟨m, M, hmM, -, -, hbound⟩ := halg.correct r oracle horacle xs hxs
  set Q := LEQuery.queriedPairs oracle (alg xs)
  have habove : ∀ x ∈ S, x ≠ m → FoundAbove r Q x := by
    intro x hx hxm
    by_contra hnot
    have := isLinearOrder_moveToBot r x
    obtain ⟨m', M', hmM', -, -, hbound'⟩ := halg.correct (moveToBot r x)
      (LEQuery.oracleOf fun a b => decide (moveToBot r x a b)) (fun _ _ => rfl) xs hxs
    rw [eval_moveToBot_eq oracle horacle (alg xs) hnot, hmM, Option.some.injEq,
      Prod.mk.injEq] at hmM'
    obtain ⟨rfl, -⟩ := hmM'
    rcases moveToBot_iff.mp (hbound' x (List.mem_toFinset.mp hx)).1 with h | ⟨h, -⟩
    · exact hxm h.symm
    · exact h rfl
  have hbelow : ∀ x ∈ S, x ≠ M → FoundBelow r Q x := by
    intro x hx hxM
    by_contra hnot
    have := isLinearOrder_moveToTop r x
    obtain ⟨m', M', hmM', -, -, hbound'⟩ := halg.correct (moveToTop r x)
      (LEQuery.oracleOf fun a b => decide (moveToTop r x a b)) (fun _ _ => rfl) xs hxs
    rw [eval_moveToTop_eq oracle horacle (alg xs) hnot, hmM, Option.some.injEq,
      Prod.mk.injEq] at hmM'
    obtain ⟨-, rfl⟩ := hmM'
    rcases moveToTop_iff.mp (hbound' x (List.mem_toFinset.mp hx)).2 with h | ⟨h, -⟩
    · exact hxM h.symm
    · exact h rfl
  have hge := potential_ge S r Q m M habove hbelow
  have hpot' : potential S r Q ≤ S.card + 2 * (alg xs).countQueries oracle := hpot
  omega

/-- **Lower bound for the minimum and maximum** (Pohl). For every correct algorithm for the
minimum and maximum and every list of `n` distinct elements, some oracle implementing a linear
order makes the algorithm use at least `⌈3n/2⌉ - 2 = (3n + 1) / 2 - 2` comparisons. -/
theorem IsMinMaxAlg.exists_le_countQueries {alg : List α → FreeM (LEQuery α) (Option (α × α))}
    (halg : IsMinMaxAlg alg) {xs : List α} (hxs : xs.Nodup) :
    ∃ f : α → α → Bool, IsLinearOrder α (fun a b => f a b = true) ∧
      (3 * xs.length + 1) / 2 - 2 ≤ (alg xs).countQueries (LEQuery.oracleOf f) := by
  classical
  rw [← List.toFinset_card_of_nodup hxs]
  exact halg.exists_card_toFinset_le_countQueries xs

/-- **Lower bound for the minimum and maximum**, as a query lower bound: on an infinite type,
every correct algorithm for the minimum and maximum makes at least `⌈3n/2⌉ - 2` comparisons on
some list of length `n`. -/
theorem IsMinMaxAlg.lowerBound_infinite [Infinite α]
    {alg : List α → FreeM (LEQuery α) (Option (α × α))} (halg : IsMinMaxAlg alg) :
    LowerBound alg List.length (fun n => (3 * n + 1) / 2 - 2) := by
  intro n
  obtain ⟨xs, hnodup, hlen⟩ := exists_nodup_length α n
  obtain ⟨f, -, h⟩ := halg.exists_le_countQueries hnodup
  refine ⟨xs, hlen.le, LEQuery.oracleOf f, ?_⟩
  rw [← hlen]
  exact h

/-- Pairwise comparison is optimal on every input: on a list of distinct elements, a correct
algorithm for the minimum and maximum makes, against some oracle implementing a linear order, at
least as many comparisons as `findMinMax` makes against any oracle. -/
theorem IsMinMaxAlg.exists_countQueries_findMinMax_le
    {alg : List α → FreeM (LEQuery α) (Option (α × α))} (halg : IsMinMaxAlg alg) {xs : List α}
    (hxs : xs.Nodup) (oracle : {ι : Type} → LEQuery α ι → ι) :
    ∃ f : α → α → Bool, IsLinearOrder α (fun a b => f a b = true) ∧
      (findMinMax xs).countQueries oracle ≤ (alg xs).countQueries (LEQuery.oracleOf f) := by
  obtain ⟨f, hf, h⟩ := halg.exists_le_countQueries hxs
  exact ⟨f, hf, (countQueries_findMinMax oracle xs).trans_le h⟩

end Cslib.Query
