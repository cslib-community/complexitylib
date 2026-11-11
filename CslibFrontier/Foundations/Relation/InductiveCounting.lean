/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Relation.RelatesWithinSteps
import Mathlib.Data.Set.Finite.Lattice

/-!
# The rounds of breadth-first search and inductive counting

Round `n` of the breadth-first search of a relation `r` from `a` is the set
`Relation.reachableWithin r a n` of elements reached within `n` steps. The rounds grow, each is
the previous one together with its successors, and once a round adds nothing it is the set of all
reachable elements; on a finite type with `N` elements, round `N - 1` already is.

The method of inductive counting of Immerman and Szelepcsényi certifies that an element is
*not* reachable, using only the sizes of the rounds. Its principle is that a subset of a finite
set with at least as many elements is the whole set (`Set.eq_of_subset_of_ncard_le`). So a list
of distinct members of round `n`, with at least as many entries as the round has members,
contains every member of the round (`Relation.IsRoundList`), and an element missing from such a
list is outside the round. Membership of each entry is itself certified by a walk of exactly `n`
steps that may stay put (`Relation.relatesWithinSteps_iff_relatesInSteps_reflGen`). A
nondeterministic machine guesses such a list one entry at a time and only counts the entries, so
it needs to store just the size of the round, never the round.

The statements about all reachable elements come in two forms: for a finite type, and for any
type on which few elements are reachable from `a` (`..._of_encard_le`), as for the configurations
of a space-bounded machine.

Nothing here mentions a machine; these are the facts about the configuration graph that the
inductive counting algorithm relies on.

## Main definitions

* `Relation.reachableWithin`: round `n` of the breadth-first search, as a set.
* `Relation.IsRoundList`: a list certifying the contents of round `n` by its length.

## Main results

* `Relation.reachableWithin_succ`, `Relation.reachableWithin_mono`: the round recursion.
* `Relation.reachableWithin_eq_of_succ_eq`, `Relation.reachableWithin_eq_of_card_le`: a round
  that adds nothing, or the round with index one less than the number of elements, is the set of
  all reachable elements.
* `Relation.IsRoundList.mem_iff`, `Relation.exists_isRoundList`: soundness and completeness of
  round lists.
* `Relation.not_relatesWithinSteps_succ_iff`: the inductive counting step, which certifies that an
  element is outside round `n + 1` by a list for round `n`.
* `Relation.forall_reflTransGen_iff_exists_isRoundList`,
  `Relation.not_reflTransGen_iff_exists_isRoundList`: on a finite type, unreachability as a
  certificate.

## References

* [N. Immerman, *Nondeterministic Space Is Closed under Complementation*][Immerman1988]
* [R. Szelepcsényi, *The Method of Forcing for Nondeterministic Automata*][Szelepcsenyi1987]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
* [C. H. Papadimitriou, *Computational Complexity*, Section 7.3][Papadimitriou94]
-/

@[expose] public section

namespace Relation

variable {α : Type*} {r : α → α → Prop} {a b c : α} {n N : ℕ}

/-! ### The rounds of breadth-first search -/

/-- Round `n` of the breadth-first search of `r` from `a`: the elements that `r` relates to `a`
within `n` steps. -/
def reachableWithin (r : α → α → Prop) (a : α) (n : ℕ) : Set α :=
  {b | RelatesWithinSteps r a b n}

/-- An element is in round `n` exactly when `r` relates `a` to it within `n` steps. -/
@[simp]
theorem mem_reachableWithin : b ∈ reachableWithin r a n ↔ RelatesWithinSteps r a b n :=
  Iff.rfl

/-- Round `0` consists of the starting element. -/
@[simp]
theorem reachableWithin_zero : reachableWithin r a 0 = {a} := by
  ext b
  simp [eq_comm]

/-- An element is in round `n + 1` exactly when it is at most one step away from round `n`. -/
theorem mem_reachableWithin_succ :
    c ∈ reachableWithin r a (n + 1) ↔ ∃ b ∈ reachableWithin r a n, ReflGen r b c :=
  RelatesWithinSteps.succ_iff

/-- **The round recursion.** Round `n + 1` is round `n` together with the successors of its
members. -/
theorem reachableWithin_succ :
    reachableWithin r a (n + 1) =
      reachableWithin r a n ∪ {c | ∃ b ∈ reachableWithin r a n, r b c} := by
  ext c
  rw [mem_reachableWithin_succ, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨b, hb, _ | hbc⟩
    exacts [.inl hb, .inr ⟨b, hb, hbc⟩]
  · rintro (hc | ⟨b, hb, hbc⟩)
    exacts [⟨c, hc, .refl⟩, ⟨b, hb, .single hbc⟩]

/-- The rounds grow. -/
theorem reachableWithin_mono : Monotone (reachableWithin r a) :=
  fun _ _ hmn _ hb => RelatesWithinSteps.mono hmn hb

/-- Every round consists of reachable elements. -/
theorem reachableWithin_subset_setOf_reflTransGen :
    reachableWithin r a n ⊆ {b | ReflTransGen r a b} :=
  fun _ hb => RelatesWithinSteps.reflTransGen hb

/-- Every reachable element is in some round. -/
theorem iUnion_reachableWithin : ⋃ n, reachableWithin r a n = {b | ReflTransGen r a b} := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun _ => reachableWithin_subset_setOf_reflTransGen)
    fun b hb => ?_
  obtain ⟨n, hn⟩ := ReflTransGen.relatesInSteps hb
  exact Set.mem_iUnion.mpr ⟨n, RelatesWithinSteps.of_relatesInSteps hn⟩

/-- **A round that adds nothing is final.** Once round `n + 1` equals round `n`, round `n`
contains every reachable element, so breadth-first search may stop. -/
theorem reachableWithin_eq_of_succ_eq (h : reachableWithin r a (n + 1) = reachableWithin r a n) :
    reachableWithin r a n = {b | ReflTransGen r a b} := by
  refine Set.Subset.antisymm reachableWithin_subset_setOf_reflTransGen
    fun b (hb : ReflTransGen r a b) => ?_
  induction hb with
  | refl => exact reachableWithin_mono (Nat.zero_le n) (by simp)
  | tail _ hbc ih => exact h ▸ reachableWithin_succ ▸ Or.inr ⟨_, ih, hbc⟩

/-- Round `N` contains every reachable element once at most `N + 1` elements are reachable. -/
theorem reachableWithin_eq_of_encard_le (hN : {x | ReflTransGen r a x}.encard ≤ N + 1) :
    reachableWithin r a N = {b | ReflTransGen r a b} :=
  Set.ext fun _ => (reflTransGen_iff_relatesWithinSteps_of_encard_le hN).symm

/-- Round `N` is finite once at most `N + 1` elements are reachable. -/
theorem finite_reachableWithin_of_encard_le (hN : {x | ReflTransGen r a x}.encard ≤ N + 1) :
    (reachableWithin r a N).Finite :=
  reachableWithin_eq_of_encard_le hN ▸ Set.finite_of_encard_le_coe (k := N + 1) (mod_cast hN)

/-- **On a finite type, the round with index one less than the number of elements contains every
reachable element.** -/
theorem reachableWithin_eq_of_card_le [Finite α] (hN : Nat.card α ≤ N + 1) :
    reachableWithin r a N = {b | ReflTransGen r a b} :=
  Set.ext fun _ => (reflTransGen_iff_relatesWithinSteps hN).symm

/-- If every element has finitely many successors, every round is finite. -/
theorem finite_reachableWithin (hr : ∀ b, {c | r b c}.Finite) (n : ℕ) :
    (reachableWithin r a n).Finite := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [reachableWithin_succ]
    refine ih.union ((Set.Finite.biUnion ih fun b _ => hr b).subset ?_)
    rintro c ⟨b, hb, hbc⟩
    exact Set.mem_biUnion hb hbc

/-! ### Round lists -/

/-- A list certifying the contents of round `n` of the search from `a`: distinct members of the
round, at least as many as the round has. The counting principle makes the list exhaustive
(`Relation.IsRoundList.mem_iff`), so that an element missing from it is outside the round; this is
the certificate that the inductive counting algorithm guesses one entry at a time
[Sipser, Theorem 8.27][Sipser2013]. -/
structure IsRoundList (r : α → α → Prop) (a : α) (n : ℕ) (l : List α) : Prop where
  /-- The entries are distinct. -/
  nodup : l.Nodup
  /-- Every entry is in round `n`. -/
  relatesWithinSteps : ∀ b ∈ l, RelatesWithinSteps r a b n
  /-- There are at least as many entries as members of round `n`. -/
  encard_le : (reachableWithin r a n).encard ≤ l.length

/-- A list of distinct members of a finite round, as many as the round has, is a round list:
the form in which the count is a natural number. -/
theorem IsRoundList.of_ncard_le {l : List α} (hfin : (reachableWithin r a n).Finite)
    (hnodup : l.Nodup) (hl : ∀ b ∈ l, RelatesWithinSteps r a b n)
    (hcard : (reachableWithin r a n).ncard ≤ l.length) : IsRoundList r a n l :=
  ⟨hnodup, hl, hfin.cast_ncard_eq ▸ mod_cast hcard⟩

/-- **Round lists are sound.** By the counting principle, a round list contains every member of
the round. -/
theorem IsRoundList.setOf_mem_eq {l : List α} (hl : IsRoundList r a n l) :
    {b | b ∈ l} = reachableWithin r a n := by
  classical
  have hl' : {b | b ∈ l} = (l.toFinset : Set α) := by
    ext
    simp
  rw [hl']
  refine l.toFinset.finite_toSet.eq_of_subset_of_encard_le
    (fun b hb => hl.relatesWithinSteps b (by simpa using hb)) ?_
  rw [Set.encard_coe_eq_coe_finsetCard, List.toFinset_card_of_nodup hl.nodup]
  exact hl.encard_le

/-- A round list contains exactly the members of the round. -/
theorem IsRoundList.mem_iff {l : List α} (hl : IsRoundList r a n l) :
    b ∈ l ↔ RelatesWithinSteps r a b n := by
  rw [← mem_reachableWithin, ← hl.setOf_mem_eq, Set.mem_ofPred_eq]

/-- The length of a round list is the size of the round: the count that the inductive counting
algorithm carries from one round to the next. -/
theorem IsRoundList.length_eq {l : List α} (hl : IsRoundList r a n l) :
    l.length = (reachableWithin r a n).ncard := by
  classical
  rw [← hl.setOf_mem_eq, ← List.toFinset_card_of_nodup hl.nodup, ← Set.ncard_coe_finset]
  congr 1
  ext
  simp

/-- **Round lists are complete.** A finite round can always be listed. -/
theorem exists_isRoundList (hfin : (reachableWithin r a n).Finite) :
    ∃ l, IsRoundList r a n l :=
  ⟨hfin.toFinset.toList, hfin.toFinset.nodup_toList, fun b hb => by simpa using hb, by
    rw [Finset.length_toList, hfin.encard_eq_coe_toFinset_card]⟩

/-- **Universal statements about a finite round are certified by a round list.** A property
holds throughout round `n` exactly when some round list consists of elements with the
property. -/
theorem forall_relatesWithinSteps_iff_exists_isRoundList
    (hfin : (reachableWithin r a n).Finite) {p : α → Prop} :
    (∀ b, RelatesWithinSteps r a b n → p b) ↔ ∃ l, IsRoundList r a n l ∧ ∀ b ∈ l, p b := by
  refine ⟨fun h => ?_, fun ⟨l, hl, hp⟩ b hb => hp b (hl.mem_iff.mpr hb)⟩
  obtain ⟨l, hl⟩ := exists_isRoundList hfin
  exact ⟨l, hl, fun b hb => h b (hl.relatesWithinSteps b hb)⟩

/-- An element is outside a finite round exactly when some round list does not contain it. -/
theorem not_relatesWithinSteps_iff_exists_isRoundList (hfin : (reachableWithin r a n).Finite) :
    ¬ RelatesWithinSteps r a b n ↔ ∃ l, IsRoundList r a n l ∧ b ∉ l := by
  refine ⟨fun h => ?_, fun ⟨l, hl, hbl⟩ hb => hbl (hl.mem_iff.mpr hb)⟩
  obtain ⟨l, hl⟩ := exists_isRoundList hfin
  exact ⟨l, hl, fun hbl => h (hl.relatesWithinSteps b hbl)⟩

/-- **The inductive counting step.** An element `c` is outside round `n + 1` exactly when some
round list for round `n` contains neither `c` nor a predecessor of `c`. Checking such a list needs
only the size of round `n`, which is how the size of round `n + 1` is computed from it. -/
theorem not_relatesWithinSteps_succ_iff (hfin : (reachableWithin r a n).Finite) :
    ¬ RelatesWithinSteps r a c (n + 1) ↔
      ∃ l, IsRoundList r a n l ∧ ∀ b ∈ l, ¬ ReflGen r b c := by
  rw [← forall_relatesWithinSteps_iff_exists_isRoundList hfin, RelatesWithinSteps.succ_iff]
  exact ⟨fun h b hb hbc => h ⟨b, hb, hbc⟩, fun h ⟨b, hb, hbc⟩ => h b hb hbc⟩

/-! ### Unreachability as a certificate -/

/-- A property of every reachable element is certified by a round list for round `N`, once at most
`N + 1` elements are reachable. -/
theorem forall_reflTransGen_iff_exists_isRoundList_of_encard_le
    (hN : {x | ReflTransGen r a x}.encard ≤ N + 1) {p : α → Prop} :
    (∀ b, ReflTransGen r a b → p b) ↔ ∃ l, IsRoundList r a N l ∧ ∀ b ∈ l, p b := by
  simp only [reflTransGen_iff_relatesWithinSteps_of_encard_le (b := _) hN]
  exact forall_relatesWithinSteps_iff_exists_isRoundList (finite_reachableWithin_of_encard_le hN)

/-- Unreachability is certified by a round list for round `N`, once at most `N + 1` elements are
reachable. -/
theorem not_reflTransGen_iff_exists_isRoundList_of_encard_le
    (hN : {x | ReflTransGen r a x}.encard ≤ N + 1) :
    ¬ ReflTransGen r a b ↔ ∃ l, IsRoundList r a N l ∧ b ∉ l := by
  rw [reflTransGen_iff_relatesWithinSteps_of_encard_le hN]
  exact not_relatesWithinSteps_iff_exists_isRoundList (finite_reachableWithin_of_encard_le hN)

/-- **A property of every reachable element is certified by a round list.** On a finite type with
at most `N + 1` elements, every element reachable from `a` has property `p` exactly when some round
list for round `N` consists of elements with property `p`. With `p` the property of not being
accepting, this is what a nondeterministic machine certifies to accept the complement of a
language decided by reachability [Sipser, Theorem 8.27][Sipser2013]. -/
theorem forall_reflTransGen_iff_exists_isRoundList [Finite α] (hN : Nat.card α ≤ N + 1)
    {p : α → Prop} :
    (∀ b, ReflTransGen r a b → p b) ↔ ∃ l, IsRoundList r a N l ∧ ∀ b ∈ l, p b := by
  simp only [reflTransGen_iff_relatesWithinSteps (r := r) (a := a) hN]
  exact forall_relatesWithinSteps_iff_exists_isRoundList (Set.toFinite _)

/-- **Unreachability is certified by a round list.** On a finite type with at most `N + 1`
elements, `b` is not reachable from `a` exactly when some round list for round `N` does not
contain `b`. -/
theorem not_reflTransGen_iff_exists_isRoundList [Finite α] (hN : Nat.card α ≤ N + 1) :
    ¬ ReflTransGen r a b ↔ ∃ l, IsRoundList r a N l ∧ b ∉ l := by
  rw [reflTransGen_iff_relatesWithinSteps hN]
  exact not_relatesWithinSteps_iff_exists_isRoundList (Set.toFinite _)

end Relation
