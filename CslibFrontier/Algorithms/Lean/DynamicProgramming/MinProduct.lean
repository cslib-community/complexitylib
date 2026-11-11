/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Minimum-product dynamic programming

An executable table retains a minimum rational score for each natural-number key.
The table is a list, so insertion scans only the stored keys. No powerset is
constructed by the implementation. This is the pruning step of [Wang2027],
Theorem 2(2), PDF p. 8. The generic interface also permits witnesses to be retained.

## Main results

* `prune_sound`: every retained witness was an input witness.
* `prune_dominates`: every input has a retained witness with the same key and no larger score.
* `prune_nodup`: retained keys are distinct.
* `run_sound`, `run_dominates`: the compressed select/omit recurrence is exact per key.
* `run_length_le`, `runWork_le`: actual table-size and rational-operation bounds.
* `choices_product`: reconstruction identifies the omitted-item product.
* `run_map`: relabeling preserves the exact table, its order and reconstructed choices.
-/

public section
namespace Cslib.Algorithms.Lean.DynamicProgramming.MinProduct

variable {α : Type*} (key : α → ℕ) (score : α → ℚ)

/-- Insert a witness, replacing the witness of the same key only if its score improves. -/
@[expose] def insert (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if key x = key y then
      (if score x ≤ score y then x else y) :: ys
    else y :: insert x ys

/-- Compress a list into one minimum-score witness per key. -/
@[expose] def prune : List α → List α
  | [] => []
  | x :: xs => insert key score x (prune xs)

/-- Retained witnesses are genuine inputs. -/
theorem mem_insert {x z : α} {xs : List α} (h : z ∈ insert key score x xs) :
    z = x ∨ z ∈ xs := by
  induction xs with
  | nil => simpa [insert] using h
  | cons y ys ih =>
    simp only [insert] at h
    split_ifs at h with hk hs
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · exact Or.inr h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (List.mem_cons_self ..)
      · rcases ih h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

/-- Insertion represents the new witness with an equal key and no larger score. -/
theorem insert_dominates_new (x : α) (xs : List α) :
    ∃ z ∈ insert key score x xs, key z = key x ∧ score z ≤ score x := by
  induction xs with
  | nil => exact ⟨x, by simp [insert], rfl, le_rfl⟩
  | cons y ys ih =>
    simp only [insert]
    split_ifs with hk hs
    · exact ⟨x, List.mem_cons_self .., rfl, le_rfl⟩
    · exact ⟨y, List.mem_cons_self .., hk.symm, le_of_not_ge hs⟩
    · obtain ⟨z,hz,hk,hs⟩ := ih
      exact ⟨z,List.mem_cons_of_mem _ hz,hk,hs⟩

/-- Insertion preserves representation of every old witness. -/
theorem insert_dominates_old (x : α) {y : α} {xs : List α} (hy : y ∈ xs) :
    ∃ z ∈ insert key score x xs, key z = key y ∧ score z ≤ score y := by
  induction xs with
  | nil => simp at hy
  | cons a as ih =>
    simp only [insert]
    split_ifs with hk hs
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨x,List.mem_cons_self ..,hk,hs⟩
      · exact ⟨y,List.mem_cons_of_mem _ hy,rfl,le_rfl⟩
    · exact ⟨y,hy,rfl,le_rfl⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨y,List.mem_cons_self ..,rfl,le_rfl⟩
      · obtain ⟨z,hz,hk,hs⟩ := ih hy
        exact ⟨z,List.mem_cons_of_mem _ hz,hk,hs⟩

/-- Every retained witness was supplied to the table. -/
theorem prune_sound {x : α} {xs : List α} (hx : x ∈ prune key score xs) : x ∈ xs := by
  induction xs with
  | nil => simp [prune] at hx
  | cons a as ih =>
    rcases mem_insert key score hx with h | h
    · exact List.mem_cons.mpr (Or.inl h)
    · exact List.mem_cons_of_mem _ (ih h)

/-- Every input has a retained witness of the same key and no larger score. -/
theorem prune_dominates {x : α} {xs : List α} (hx : x ∈ xs) :
    ∃ y ∈ prune key score xs, key y = key x ∧ score y ≤ score x := by
  induction xs with
  | nil => simp at hx
  | cons a as ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact insert_dominates_new key score x (prune key score as)
    · obtain ⟨y,hy,hk,hs⟩ := ih hx
      obtain ⟨z,hz,hzk,hzs⟩ := insert_dominates_old key score a hy
      exact ⟨z,hz,hzk.trans hk,hzs.trans hs⟩

private theorem insert_nodup (x : α) {xs : List α} (h : (xs.map key).Nodup) :
    ((insert key score x xs).map key).Nodup := by
  induction xs with
  | nil => simp [insert]
  | cons y ys ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    simp only [insert]
    split_ifs with hk hs
    · simpa [hk] using h
    · simpa using h
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_,ih h.2⟩
      intro hm
      obtain ⟨z,hz,hzk⟩ := List.mem_map.mp hm
      rcases mem_insert key score hz with rfl | hz
      · exact hk hzk
      · exact h.1 (List.mem_map.mpr ⟨z,hz,hzk⟩)

/-- There is at most one retained witness per key. -/
theorem prune_nodup (xs : List α) : ((prune key score xs).map key).Nodup := by
  induction xs with
  | nil => simp [prune]
  | cons x xs ih => exact insert_nodup key score x ih

/-- A bounded key gives a bounded table, irrespective of the number of candidates. -/
theorem prune_length_le {xs : List α} {M : ℕ} (h : ∀ x ∈ xs, key x ≤ M) :
    (prune key score xs).length ≤ M + 1 := by
  have hs : (prune key score xs).map key ⊆ List.range (M + 1) := by
    intro j hj
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hj
    exact List.mem_range.mpr (Nat.lt_succ_of_le (h x (prune_sound key score hx)))
  have := List.Nodup.length_le_of_subset (prune_nodup key score xs) hs
  simpa using this

/-- Count key/score comparisons and list-cell work in insertion. Rational
comparisons are single operations in this count; their bit costs are separate. -/
@[expose] def insertWork (x : α) : List α → ℕ
  | [] => 1
  | y :: ys => if key x = key y then 3 else 3 + insertWork x ys

/-- Count the actual recursive pruning work, including its insertion scans. -/
@[expose] def pruneWork : List α → ℕ
  | [] => 1
  | x :: xs => pruneWork xs + insertWork key x (prune key score xs) + 1

/-- Insertion adds at most one table entry. -/
theorem insert_length_le (x : α) (xs : List α) :
    (insert key score x xs).length ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [insert]
  | cons y ys ih =>
    simp only [insert]
    split_ifs <;> simp_all

/-- Compression never increases the number of supplied candidates. -/
theorem prune_length_le_input (xs : List α) : (prune key score xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [prune]
  | cons x xs ih =>
    exact (insert_length_le key score x _).trans (Nat.succ_le_succ ih)

private theorem insertWork_le (x : α) (xs : List α) :
    insertWork key x xs ≤ 3 * (xs.length + 1) := by
  induction xs with
  | nil => simp [insertWork]
  | cons y ys ih =>
    simp only [insertWork, List.length_cons]
    split_ifs <;> omega

/-- A quadratic bound for the insertion scans performed by pruning. -/
theorem pruneWork_le (xs : List α) :
    pruneWork key score xs ≤ 4 * (xs.length + 1) ^ 2 := by
  have stronger : pruneWork key score xs ≤ 2 * xs.length ^ 2 + 2 * xs.length + 1 := by
    induction xs with
    | nil => simp [pruneWork]
    | cons x xs ih =>
      have hi := insertWork_le key x (prune key score xs)
      have hl := prune_length_le_input key score xs
      simp only [pruneWork, List.length_cons]
      nlinarith
  nlinarith

/-- One table witness, with the selected items retained for reconstruction. -/
structure Entry (ι : Type*) where
  /-- Sum of rounded selected costs. -/
  rounded : ℕ
  /-- Product of failure factors of omitted items. -/
  product : ℚ
  /-- Selected items, in reverse processing order. -/
  selected : List ι
  deriving DecidableEq

/-- Select an item: add its rounded cost and remember it. -/
@[expose] def Entry.take {ι : Type*} (i : ι) (z : ℕ) (e : Entry ι) : Entry ι :=
  ⟨e.rounded + z, e.product, i :: e.selected⟩

/-- Omit an item: multiply its failure probability. -/
@[expose] def Entry.skip {ι : Type*} (q : ℚ) (e : Entry ι) : Entry ι :=
  ⟨e.rounded, q * e.product, e.selected⟩

/-- All one-step candidates before compression. -/
@[expose] def extend {ι : Type*} (i : ι) (z : ℕ) (q : ℚ)
    (table : List (Entry ι)) : List (Entry ι) :=
  table.map (Entry.skip q) ++ table.map (Entry.take i z)

/-- The actual dynamic program. Each item doubles the current table and then
retains one witness per rounded sum; it never enumerates all subsets. -/
@[expose] def run {ι : Type*} (z : ι → ℕ) (q : ι → ℚ)
    (initial : Entry ι) : List ι → List (Entry ι)
  | [] => [initial]
  | i :: is => prune Entry.rounded Entry.product (extend i (z i) (q i) (run z q initial is))

/-- Relabel a reconstructed witness, preserving its key, product and order. -/
@[expose] def Entry.map {κ ι : Type*} (f : ι → κ) (e : Entry ι) : Entry κ :=
  ⟨e.rounded,e.product,e.selected.map f⟩

private theorem insert_map {κ ι : Type*} (f : ι → κ) (x : Entry ι)
    (xs : List (Entry ι)) :
    (insert Entry.rounded Entry.product x xs).map (Entry.map f) =
      insert Entry.rounded Entry.product (x.map f) (xs.map (Entry.map f)) := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [insert, List.map_cons, Entry.map]
    split_ifs <;> simp_all [Entry.map]

private theorem prune_map {κ ι : Type*} (f : ι → κ) (xs : List (Entry ι)) :
    (prune Entry.rounded Entry.product xs).map (Entry.map f) =
      prune Entry.rounded Entry.product (xs.map (Entry.map f)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [prune, insert_map, ih, List.map_cons, prune]

private theorem extend_map {κ ι : Type*} (f : ι → κ) (i : ι) (z : ℕ) (q : ℚ)
    (xs : List (Entry ι)) :
    (extend i z q xs).map (Entry.map f) = extend (f i) z q (xs.map (Entry.map f)) := by
  simp only [extend, List.map_append, List.map_map, Function.comp_def]
  congr 1

/-- Relabeling the runtime indices preserves the exact compressed table, including
its order, ties and reconstructed choices. Field equality is needed only on the
processed population, allowing bounded implementations outside that population. -/
theorem run_map {κ ι : Type*} (f : ι → κ) (z : ι → ℕ) (q : ι → ℚ)
    (z' : κ → ℕ) (q' : κ → ℚ) (initial : Entry ι) (items : List ι)
    (hz : ∀ i ∈ items, z' (f i) = z i) (hq : ∀ i ∈ items, q' (f i) = q i) :
    run z' q' (initial.map f) (items.map f) =
      (run z q initial items).map (Entry.map f) := by
  induction items with
  | nil => rfl
  | cons i is ih =>
    have hi := hz i (List.mem_cons_self ..)
    have hqi := hq i (List.mem_cons_self ..)
    rw [List.map_cons, run, ih (fun j hj => hz j (List.mem_cons_of_mem _ hj))
      (fun j hj => hq j (List.mem_cons_of_mem _ hj)), hi, hqi, run,
      prune_map, extend_map]

/-- Exhaustive choices, used only as a correctness specification. -/
@[expose] def choices {ι : Type*} (z : ι → ℕ) (q : ι → ℚ)
    (initial : Entry ι) : List ι → List (Entry ι)
  | [] => [initial]
  | i :: is => extend i (z i) (q i) (choices z q initial is)

variable {ι : Type*} (z : ι → ℕ) (q : ι → ℚ) (initial : Entry ι)

/-- Every dynamic-program witness is an actual select/omit choice. -/
theorem run_sound (items : List ι) : run z q initial items ⊆ choices z q initial items := by
  induction items with
  | nil => exact fun _ h => h
  | cons i is ih =>
    intro e he
    have h := prune_sound Entry.rounded Entry.product he
    change e ∈ extend i (z i) (q i) (choices z q initial is)
    simp only [extend, List.mem_append, List.mem_map] at h ⊢
    rcases h with ⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩
    · exact Or.inl ⟨a,ih ha,rfl⟩
    · exact Or.inr ⟨a,ih ha,rfl⟩

/-- Compression preserves the minimum product for every attainable rounded sum. -/
theorem run_dominates (hq : ∀ i, 0 ≤ q i) (items : List ι)
    {e : Entry ι} (he : e ∈ choices z q initial items) :
    ∃ d ∈ run z q initial items, d.rounded = e.rounded ∧ d.product ≤ e.product := by
  induction items generalizing e with
  | nil => exact ⟨e,he,rfl,le_rfl⟩
  | cons i is ih =>
    change e ∈ extend i (z i) (q i) (choices z q initial is) at he
    simp only [extend, List.mem_append, List.mem_map] at he
    have hex : ∃ a ∈ extend i (z i) (q i) (run z q initial is),
        a.rounded = e.rounded ∧ a.product ≤ e.product := by
      rcases he with ⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩
      · obtain ⟨d,hd,hk,hs⟩ := ih ha
        exact ⟨d.skip (q i), List.mem_append_left _ (List.mem_map.mpr ⟨d,hd,rfl⟩),
          hk, mul_le_mul_of_nonneg_left hs (hq i)⟩
      · obtain ⟨d,hd,hk,hs⟩ := ih ha
        exact ⟨d.take i (z i), List.mem_append_right _ (List.mem_map.mpr ⟨d,hd,rfl⟩),
          congrArg (· + z i) hk, hs⟩
    obtain ⟨a,ha,hk,hs⟩ := hex
    obtain ⟨d,hd,hdk,hds⟩ := prune_dominates Entry.rounded Entry.product ha
    exact ⟨d,hd,hdk.trans hk,hds.trans hs⟩

/-- Every exhaustive choice has key at most the initial key plus all item keys. -/
theorem choices_rounded_le (items : List ι) {e : Entry ι}
    (he : e ∈ choices z q initial items) :
    e.rounded ≤ initial.rounded + (items.map z).sum := by
  induction items generalizing e with
  | nil =>
    have : e = initial := by simpa [choices] using he
    subst e
    simp
  | cons i is ih =>
    change e ∈ extend i (z i) (q i) (choices z q initial is) at he
    simp only [extend, List.mem_append, List.mem_map] at he
    rcases he with ⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩
    · have := ih ha
      simp only [Entry.skip, List.map_cons, List.sum_cons]
      omega
    · have := ih ha
      simp only [Entry.take, List.map_cons, List.sum_cons]
      omega

/-- The number of stored states is at most one plus the total rounded cost,
including the initial mandatory selection. This bounds the actual table. -/
theorem run_length_le (items : List ι) :
    (run z q initial items).length ≤ initial.rounded + (items.map z).sum + 1 := by
  cases items with
  | nil => simp [run]
  | cons i is =>
    apply prune_length_le Entry.rounded Entry.product
    intro e he
    have he' : e ∈ choices z q initial (i :: is) := by
      change e ∈ extend i (z i) (q i) (choices z q initial is)
      simp only [extend, List.mem_append, List.mem_map] at he ⊢
      rcases he with ⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩
      · exact Or.inl ⟨a,run_sound z q initial is ha,rfl⟩
      · exact Or.inr ⟨a,run_sound z q initial is ha,rfl⟩
    exact choices_rounded_le z q initial (i :: is) he'

/-- Operation count of the actual select/omit/compress recurrence. Each of the
two maps and the concatenation is charged for its list-cell traversal. Rational
multiplication and comparison are unit operations here, not uncharged oracles. -/
@[expose] def runWork : List ι → ℕ
  | [] => 1
  | i :: is =>
    let table := run z q initial is
    runWork is + 3 * table.length +
      pruneWork Entry.rounded Entry.product (extend i (z i) (q i) table) + 1

/-- A polynomial operation bound on the implemented recurrence. `M` bounds the
sum of rounded costs, not the original binary costs. Binary arithmetic and
scaling must be accounted for separately when using this as an FPTAS. -/
theorem runWork_le (items : List ι) (M : ℕ)
    (hM : initial.rounded + (items.map z).sum ≤ M) :
    runWork z q initial items ≤ 1 + items.length * (32 * (M + 2) ^ 2) := by
  induction items with
  | nil => simp [runWork]
  | cons i is ih =>
    have htail : initial.rounded + (is.map z).sum ≤ M := by
      simp only [List.map_cons, List.sum_cons] at hM
      omega
    have hi := ih htail
    have hl := (run_length_le z q initial is).trans (Nat.succ_le_succ htail)
    have hp := pruneWork_le Entry.rounded Entry.product
      (extend i (z i) (q i) (run z q initial is))
    have hext : (extend i (z i) (q i) (run z q initial is)).length =
        (run z q initial is).length + (run z q initial is).length := by
      simp [extend]
    rw [hext] at hp
    simp only [runWork, List.length_cons]
    have hstep : 3 * (run z q initial is).length +
        pruneWork Entry.rounded Entry.product
          (extend i (z i) (q i) (run z q initial is)) + 1 ≤ 32 * (M + 2) ^ 2 := by
      nlinarith [Nat.mul_self_le_mul_self hl]
    nlinarith

/-- Every reconstructed selection is a subsequence of the processed items
followed by the initial mandatory selection. -/
theorem choices_selected_sublist (items : List ι) {e : Entry ι}
    (he : e ∈ choices z q initial items) : e.selected.Sublist (items ++ initial.selected) := by
  induction items generalizing e with
  | nil =>
    have : e = initial := by simpa [choices] using he
    subst e
    exact List.Sublist.refl _
  | cons i is ih =>
    change e ∈ extend i (z i) (q i) (choices z q initial is) at he
    simp only [extend, List.mem_append, List.mem_map] at he
    rcases he with ⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩
    · exact (ih ha).cons _
    · exact (ih ha).cons_cons _

/-- Every choice keeps the initial mandatory selection. -/
theorem choices_initial_sublist (items : List ι) {e : Entry ι}
    (he : e ∈ choices z q initial items) : initial.selected.Sublist e.selected := by
  induction items generalizing e with
  | nil =>
    have : e = initial := by simpa [choices] using he
    subst e
    exact List.Sublist.refl _
  | cons i is ih =>
    change e ∈ extend i (z i) (q i) (choices z q initial is) at he
    simp only [extend, List.mem_append, List.mem_map] at he
    rcases he with ⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩
    · change initial.selected.Sublist a.selected
      exact ih ha
    · exact (ih ha).cons _

variable [DecidableEq ι]

/-- A specified subset determines an actual sequence of select/omit choices. -/
@[expose] def select (B : Finset ι) : List ι → Entry ι
  | [] => initial
  | i :: is => if i ∈ B then (select B is).take i (z i) else (select B is).skip (q i)

/-- Every specified subset is considered by the exhaustive correctness specification. -/
theorem select_mem_choices (B : Finset ι) (items : List ι) :
    select z q initial B items ∈ choices z q initial items := by
  induction items with
  | nil => simp [select, choices]
  | cons i is ih =>
    simp only [select, choices, extend, List.mem_append, List.mem_map]
    split_ifs
    · exact Or.inr ⟨_,ih,rfl⟩
    · exact Or.inl ⟨_,ih,rfl⟩

/-- Reconstruction retains precisely the selected processed items and mandatory items. -/
theorem select_selected (B : Finset ι) (items : List ι) :
    (select z q initial B items).selected = items.filter (· ∈ B) ++ initial.selected := by
  induction items with
  | nil => simp [select]
  | cons i is ih =>
    simp only [select]
    split_ifs with hi <;> simp [Entry.take, Entry.skip, hi, ih]

/-- The product is precisely the product of the omitted-item factors. -/
theorem select_product (B : Finset ι) (items : List ι) :
    (select z q initial B items).product =
      initial.product * ((items.filter (· ∉ B)).map q).prod := by
  induction items with
  | nil => simp [select]
  | cons i is ih =>
    simp only [select]
    split_ifs with hi
    · simpa [Entry.take, List.filter_cons, hi] using ih
    · simp only [Entry.skip, ih, List.filter_cons, hi, not_false_eq_true,
        decide_true, ite_true, List.map_cons, List.prod_cons]
      ring

/-- With distinct processed and mandatory items, any choice's product can be
read directly from its reconstructed subset. -/
theorem choices_product (items : List ι) (hn : (items ++ initial.selected).Nodup)
    {e : Entry ι} (he : e ∈ choices z q initial items) :
    e.product = initial.product * ((items.filter (· ∉ e.selected)).map q).prod := by
  induction items generalizing e with
  | nil =>
    have : e = initial := by simpa [choices] using he
    subst e
    simp
  | cons i is ih =>
    have hn' := (List.nodup_cons.mp hn).2
    have hi := (List.nodup_cons.mp hn).1
    change e ∈ extend i (z i) (q i) (choices z q initial is) at he
    simp only [extend, List.mem_append, List.mem_map] at he
    rcases he with ⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩
    · have hia : i ∉ a.selected := fun h => hi
        ((choices_selected_sublist z q initial is ha).subset h)
      simp only [Entry.skip, List.filter_cons, hia, not_false_eq_true, decide_true, ite_true,
        List.map_cons, List.prod_cons]
      rw [ih hn' ha]
      ring_nf
      rfl
    · have hfilter : is.filter (· ∉ i :: a.selected) = is.filter (· ∉ a.selected) := by
        apply List.filter_congr
        intro j hj
        have hji : j ≠ i := fun h => hi (List.mem_append_left _ (h ▸ hj))
        simp [hji]
      change a.product = initial.product *
        (((i :: is).filter (· ∉ i :: a.selected)).map q).prod
      have hhead : (i :: is).filter (· ∉ i :: a.selected) =
          is.filter (· ∉ a.selected) := by
        simpa only [List.filter_cons, List.mem_cons_self, not_true_eq_false,
          decide_false, Bool.false_eq_true, ite_false] using hfilter
      rw [hhead]
      exact ih hn' ha

end Cslib.Algorithms.Lean.DynamicProgramming.MinProduct
