/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, beside `Nat.rfindOpt` in `Mathlib/Computability/Partrec.lean`)

public import Complexity.Init
public import Mathlib.Computability.Partrec
public import Mathlib.Data.Set.Card
import Mathlib.Computability.Primrec.List

/-!
# Enumerating the distinct values of a sequence of partial outputs

A sequence `f : ℕ → Option β` lists, possibly with repetitions and gaps, the elements of its range
`{b | ∃ n, f n = some b}`. Typically `f n` decodes `n` as a program and a time bound and reports
the output of the program if it halts in time, so the range is a computably enumerable set.
`Nat.distinctValues f n` lists the distinct values among `f 0, …, f (n - 1)` in order of first
appearance, and `Nat.nthDistinctValue f i` is the `i`-th distinct value of the whole sequence,
found by an unbounded search over `n`. When the range is finite, every element has an index below
the size of the range. When `f` depends primitive recursively on a parameter, both are
computable in the parameter: this is the enumeration step in counting arguments of Kolmogorov
complexity, which describe an element of a computably enumerable set by its index.

## Main definitions

* `Nat.distinctValues`: the distinct values of a sequence up to a bound, in order of first
  appearance.
* `Nat.nthDistinctValue`: the `i`-th distinct value of a sequence, if there is one.

## Main results

* `Nat.mem_distinctValues`, `Nat.nodup_distinctValues`, `Nat.distinctValues_prefix`: the lists
  contain exactly the values seen so far, without repetitions, and grow by extension.
* `Nat.length_distinctValues_le_ncard`, `Nat.exists_length_distinctValues_eq_ncard`: for a finite
  range, the lists are no longer than the range and eventually as long as it.
* `Nat.mem_nthDistinctValue_iff`, `Nat.exists_eq_some_of_mem_nthDistinctValue`,
  `Nat.exists_mem_nthDistinctValue_of_finite`: the `i`-th distinct value is in the range, and, for
  a finite range, every element of it is the `i`-th distinct value for some `i` below its size.
* `Primrec.distinctValues`, `Partrec.nthDistinctValue`: computability in a parameter.
-/

public section

namespace Nat

variable {α β : Type*} [DecidableEq β]

/-- The distinct values among `f 0, …, f (n - 1)`, in order of first appearance. The body is
exposed so that concrete lists can be evaluated by `decide`. -/
@[expose] def distinctValues (f : ℕ → Option β) : ℕ → List β
  | 0 => []
  | n + 1 =>
    match f n with
    | none => distinctValues f n
    | some b => if b ∈ distinctValues f n then distinctValues f n else distinctValues f n ++ [b]

/-- Fold a partial output into a list of distinct values. -/
private def insertNew (L : List β) : Option β → List β
  | none => L
  | some b => if b ∈ L then L else L ++ [b]

private theorem distinctValues_succ_eq_insertNew (f : ℕ → Option β) (n : ℕ) :
    distinctValues f (n + 1) = insertNew (distinctValues f n) (f n) := by
  rw [distinctValues]
  cases f n <;> rfl

private theorem prefix_insertNew (L : List β) (o : Option β) : L <+: insertNew L o := by
  cases o with
  | none => exact List.prefix_refl L
  | some b =>
    simp only [insertNew]
    split_ifs
    · exact List.prefix_refl L
    · exact List.prefix_append L [b]

private theorem mem_insertNew {L : List β} {o : Option β} {b : β} :
    b ∈ insertNew L o ↔ b ∈ L ∨ o = some b := by
  cases o with
  | none => simp [insertNew]
  | some c =>
    simp only [insertNew]
    split_ifs with hc
    · refine ⟨Or.inl, ?_⟩
      rintro (h | h)
      · exact h
      · cases h
        exact hc
    · simp [eq_comm]

private theorem nodup_insertNew {L : List β} (hL : L.Nodup) (o : Option β) :
    (insertNew L o).Nodup := by
  cases o with
  | none => exact hL
  | some c =>
    simp only [insertNew]
    split_ifs with hc
    · exact hL
    · exact hL.append (List.nodup_singleton c) (by simpa using hc)

@[simp]
theorem distinctValues_zero (f : ℕ → Option β) : distinctValues f 0 = [] := rfl

/-- The lists of distinct values grow by extension. -/
theorem distinctValues_prefix (f : ℕ → Option β) {m n : ℕ} (h : m ≤ n) :
    distinctValues f m <+: distinctValues f n := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih =>
    rw [distinctValues_succ_eq_insertNew]
    exact ih.trans (prefix_insertNew _ _)

/-- The distinct values up to `n` are the values `f j = some b` with `j < n`. -/
theorem mem_distinctValues {f : ℕ → Option β} {n : ℕ} {b : β} :
    b ∈ distinctValues f n ↔ ∃ j < n, f j = some b := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [distinctValues_succ_eq_insertNew, mem_insertNew, ih]
    constructor
    · rintro (⟨j, hj, h⟩ | h)
      · exact ⟨j, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨j, hj, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact Or.inl ⟨j, hj, h⟩
      · exact Or.inr h

theorem nodup_distinctValues (f : ℕ → Option β) (n : ℕ) : (distinctValues f n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ n ih =>
    rw [distinctValues_succ_eq_insertNew]
    exact nodup_insertNew ih _

/-- For a finite range, the lists of distinct values are no longer than the range. -/
theorem length_distinctValues_le_ncard {f : ℕ → Option β} (hf : {b | ∃ n, f n = some b}.Finite)
    (n : ℕ) : (distinctValues f n).length ≤ {b | ∃ n, f n = some b}.ncard := by
  have hsub : (distinctValues f n).toFinset ⊆ hf.toFinset := fun c hc => by
    obtain ⟨j, -, hj⟩ := mem_distinctValues.mp (List.mem_toFinset.mp hc)
    exact hf.mem_toFinset.mpr ⟨j, hj⟩
  rw [← List.toFinset_card_of_nodup (nodup_distinctValues f n), Set.ncard_eq_toFinset_card _ hf]
  exact Finset.card_le_card hsub

/-- For a finite range, the list of distinct values eventually contains the whole range. -/
theorem exists_length_distinctValues_eq_ncard {f : ℕ → Option β}
    (hf : {b | ∃ n, f n = some b}.Finite) :
    ∃ N, (distinctValues f N).length = {b | ∃ n, f n = some b}.ncard := by
  have key : ∀ t : Finset β, (∀ b ∈ t, ∃ n, f n = some b) →
      ∃ N, ∀ b ∈ t, b ∈ distinctValues f N := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact fun _ => ⟨0, by simp⟩
    | @insert b t hb ih =>
      intro h
      obtain ⟨N, hN⟩ := ih fun c hc => h c (Finset.mem_insert_of_mem hc)
      obtain ⟨n, hn⟩ := h b (Finset.mem_insert_self b t)
      refine ⟨max N (n + 1), fun c hc => ?_⟩
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact (distinctValues_prefix f (le_max_right _ _)).subset
          (mem_distinctValues.mpr ⟨n, by omega, hn⟩)
      · exact (distinctValues_prefix f (le_max_left _ _)).subset (hN c hc)
  obtain ⟨N, hN⟩ := key hf.toFinset fun b hb => hf.mem_toFinset.mp hb
  refine ⟨N, le_antisymm (length_distinctValues_le_ncard hf N) ?_⟩
  rw [← List.toFinset_card_of_nodup (nodup_distinctValues f N), Set.ncard_eq_toFinset_card _ hf]
  exact Finset.card_le_card fun b hb => List.mem_toFinset.mpr (hN b hb)

/-- The `i`-th distinct value of the sequence `f`, in order of first appearance: the search for a
bound `n` such that `distinctValues f n` has an `i`-th entry. -/
def nthDistinctValue (f : ℕ → Option β) (i : ℕ) : Part β :=
  Nat.rfindOpt fun n => (distinctValues f n)[i]?

theorem mem_nthDistinctValue_iff {f : ℕ → Option β} {i : ℕ} {b : β} :
    b ∈ nthDistinctValue f i ↔ ∃ n, (distinctValues f n)[i]? = some b := by
  refine Nat.rfindOpt_mono fun {b m n} hmn h => ?_
  obtain ⟨t, ht⟩ := distinctValues_prefix f hmn
  rw [← ht, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- The distinct values of `f` are in its range. -/
theorem exists_eq_some_of_mem_nthDistinctValue {f : ℕ → Option β} {i : ℕ} {b : β}
    (h : b ∈ nthDistinctValue f i) : ∃ n, f n = some b := by
  obtain ⟨n, hn⟩ := mem_nthDistinctValue_iff.mp h
  obtain ⟨j, -, hj⟩ := mem_distinctValues.mp (List.mem_of_getElem? hn)
  exact ⟨j, hj⟩

/-- For a finite range, the indices of the distinct values are below the size of the range. -/
theorem lt_ncard_of_mem_nthDistinctValue {f : ℕ → Option β} (hf : {b | ∃ n, f n = some b}.Finite)
    {i : ℕ} {b : β} (h : b ∈ nthDistinctValue f i) : i < {b | ∃ n, f n = some b}.ncard := by
  obtain ⟨n, hn⟩ := mem_nthDistinctValue_iff.mp h
  exact (List.getElem?_eq_some_iff.mp hn).1.trans_le (length_distinctValues_le_ncard hf n)

/-- For a finite range, every element of the range is the `i`-th distinct value for some `i` below
the size of the range. -/
theorem exists_mem_nthDistinctValue_of_finite {f : ℕ → Option β}
    (hf : {b | ∃ n, f n = some b}.Finite) {b : β} {n : ℕ} (hb : f n = some b) :
    ∃ i < {b | ∃ n, f n = some b}.ncard, b ∈ nthDistinctValue f i := by
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem (mem_distinctValues.mpr ⟨n, n.lt_succ_self, hb⟩)
  exact ⟨i, hi.trans_le (length_distinctValues_le_ncard hf _),
    mem_nthDistinctValue_iff.mpr ⟨n + 1, List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩⟩⟩

end Nat

variable {α β : Type*} [Primcodable α] [Primcodable β] [DecidableEq β]

private theorem primrec₂_insertNew : Primrec₂ (Nat.insertNew : List β → Option β → List β) := by
  have hmem : PrimrecRel fun (L : List β) (b : β) => b ∈ L :=
    (PrimrecRel.exists_mem_list Primrec.eq).of_eq fun L b => by simp
  refine Primrec₂.mk ?_
  refine (Primrec.option_casesOn Primrec.snd Primrec.fst
    (Primrec₂.mk (f := fun (p : List β × Option β) (b : β) => if b ∈ p.1 then p.1 else p.1 ++ [b])
      (Primrec.ite (hmem.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
      (Primrec.list_concat.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)))).of_eq ?_
  rintro ⟨L, _ | b⟩ <;> rfl

/-- The distinct values of a sequence depending primitive recursively on a parameter are primitive
recursive in the parameter and the bound. -/
theorem Primrec.distinctValues {f : α → ℕ → Option β} (hf : Primrec₂ f) :
    Primrec₂ fun a n => Nat.distinctValues (f a) n := by
  refine (Primrec.nat_rec (f := fun _ => ([] : List β))
    (g := fun a (p : ℕ × List β) => Nat.insertNew p.2 (f a p.1)) (Primrec.const [])
    (primrec₂_insertNew.comp₂ (Primrec.snd.comp₂ Primrec₂.right)
      (hf.comp₂ Primrec₂.left (Primrec.fst.comp₂ Primrec₂.right)))).of_eq fun a n => ?_
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.distinctValues_succ_eq_insertNew, ← ih]

/-- The `i`-th distinct value of a sequence depending primitive recursively on a parameter is
partial recursive in the parameter and `i`. -/
theorem Partrec.nthDistinctValue {f : α → ℕ → Option β} (hf : Primrec₂ f) :
    Partrec₂ fun a i => Nat.nthDistinctValue (f a) i := by
  have h : Computable₂ fun (ai : α × ℕ) (n : ℕ) => (Nat.distinctValues (f ai.1) n)[ai.2]? :=
    (Primrec.list_getElem?.comp ((Primrec.distinctValues hf).comp (Primrec.fst.comp Primrec.fst)
      Primrec.snd) (Primrec.snd.comp Primrec.fst)).to_comp
  exact (Partrec.rfindOpt h).of_eq fun _ => rfl
