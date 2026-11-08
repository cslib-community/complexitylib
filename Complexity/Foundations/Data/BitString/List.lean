/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Block
public import Mathlib.Data.List.OfFn

/-!
# Bit strings represented by lists

Fixed-width views of ordinary lists pad missing bits with `false`. A flat list can also be read
as a specified number of fixed-width rows. The representation uses the existing `blocksEquiv`;
row extraction is ordinary dropping, padding and taking, including on short or empty lists.

## Main definitions

* `Cslib.BitString.ofList`: a fixed-width view of a list.
* `Cslib.BitString.listRow`, `Cslib.BitString.listRows`: fixed-width rows of a flat list.
* `Cslib.BitString.replaceRow`: replace one fixed-width row of a flat list.

## Main results

* `Cslib.BitString.ofList_ofFn`, `Cslib.BitString.ofFn_ofList`: representation round trips.
* `Cslib.BitString.ofList_append_of_le`, `Cslib.BitString.ofList_ofFn_append`: fixed-width views
  ignore bits beyond their width.
* `Cslib.BitString.exists_take_ofFn_iff`, `Cslib.BitString.forall_take_ofFn_iff`: quantifying over
  longer strings through their prefixes.
* `Cslib.BitString.ofFn_ofList_eq_take`: the fixed-width view pads with `false` or truncates.
* `Cslib.BitString.getElem_listRow`, `Cslib.BitString.getD_listRow`: row indexing, including
  false padding on short words.
* `Cslib.BitString.listRow_flatMap_append`, `Cslib.BitString.listRow_flatten`: recover
  equal-width rows from concatenated words.
* `Cslib.BitString.listRow_replaceRow`: reading rows after replacing one row.
* `Cslib.BitString.listRows_eq_ofFn`, `Cslib.BitString.listRows_ofFn`: agreement with the finite
  block representation.
* `Cslib.BitString.listRows_succ_append`: the rows of a word whose first row is given.

Packing fixed-width rows is list concatenation by `Cslib.BitString.ofFn_blocksEquiv_symm`, in
`Complexity.Foundations.Data.BitString.Block`.

## References

Adapted from Probability/WordBits.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, reusing the shared bit-string block equivalence.
-/

@[expose] public section

namespace Cslib.BitString

/-- View a list as `n` bits, padding missing bits with `false`. -/
def ofList (n : ℕ) (word : List Bool) : BitString n := fun i => word.getD i.val false

/-- Viewing `List.ofFn bits` as an `n`-bit string recovers `bits`. -/
@[simp] theorem ofList_ofFn {n : ℕ} (bits : BitString n) :
    ofList n (List.ofFn bits) = bits := by
  funext i
  simp [ofList]

/-- A list of the declared width loses no data through the finite representation. -/
theorem ofFn_ofList {n : ℕ} {word : List Bool} (hlen : word.length = n) :
    List.ofFn (ofList n word) = word := by
  subst n
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp [ofList, List.getD, List.getElem?_eq_getElem hi']

/-- Concatenating words of the declared widths agrees with concatenating their bit strings. -/
theorem ofList_append {n m : ℕ} {u v : List Bool} (hu : u.length = n) (hv : v.length = m) :
    ofList (n + m) (u ++ v) = Fin.append (ofList n u) (ofList m v) := by
  have h : List.ofFn (Fin.append (ofList n u) (ofList m v)) = u ++ v := by
    rw [List.ofFn_fin_append, ofFn_ofList hu, ofFn_ofList hv]
  rw [← h, ofList_ofFn]

/-- The fixed-width view of a word does not see bits beyond its width. -/
theorem ofList_append_of_le {n : ℕ} {u : List Bool} (hu : n ≤ u.length) (v : List Bool) :
    ofList n (u ++ v) = ofList n u := by
  funext i
  simp only [ofList, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by omega)]

/-- Reading `n` bits of a word that starts with `n` given bits returns them. -/
theorem ofList_ofFn_append {n : ℕ} (bits : BitString n) (word : List Bool) :
    ofList n (List.ofFn bits ++ word) = bits := by
  rw [ofList_append_of_le (by simp), ofList_ofFn]

/-- The `n`-bit view of a word reads only its first `n` bits. -/
theorem ofList_take (n : ℕ) (word : List Bool) : ofList n (word.take n) = ofList n word := by
  funext i
  simp [ofList, i.isLt]

/-- Reading a word into a bit string pads it with `false` or truncates it. -/
theorem ofFn_ofList_eq_take (n : ℕ) (word : List Bool) :
    List.ofFn (ofList n word) = (word ++ List.replicate n false).take n := by
  refine List.ext_getElem (by simp) fun i hi _ => ?_
  simp only [List.length_ofFn] at hi
  simp only [List.getElem_ofFn, List.getElem_take, ofList, List.getD_eq_getElem?_getD,
    List.getElem_append]
  split_ifs with hw
  · simp [List.getElem?_eq_getElem hw]
  · simp [List.getElem?_eq_none (by omega : word.length ≤ i)]

/-- A string of `k ≤ K` bits padded with `false` to `K` bits has the original string as its
prefix of length `k`. -/
theorem take_ofFn_ofList {k K : ℕ} (h : k ≤ K) (y : BitString k) :
    (List.ofFn (ofList K (List.ofFn y))).take k = List.ofFn y := by
  rw [ofFn_ofList_eq_take, List.take_take, Nat.min_eq_left h, List.take_left' List.length_ofFn]

/-- **Prefixes and existential quantifiers.** For `k ≤ K`, some string of `K` bits has a prefix of
length `k` satisfying `g` iff some string of `k` bits does. -/
theorem exists_take_ofFn_iff {k K : ℕ} (h : k ≤ K) {g : List Bool → Prop} :
    (∃ y : BitString K, g ((List.ofFn y).take k)) ↔ ∃ y : BitString k, g (List.ofFn y) :=
  ⟨fun ⟨y, hy⟩ => ⟨ofList k ((List.ofFn y).take k), by
      rwa [ofFn_ofList (by simp [h])]⟩,
    fun ⟨y, hy⟩ => ⟨ofList K (List.ofFn y), by rwa [take_ofFn_ofList h]⟩⟩

/-- **Prefixes and universal quantifiers.** For `k ≤ K`, every string of `K` bits has a prefix of
length `k` satisfying `g` iff every string of `k` bits does. -/
theorem forall_take_ofFn_iff {k K : ℕ} (h : k ≤ K) {g : List Bool → Prop} :
    (∀ y : BitString K, g ((List.ofFn y).take k)) ↔ ∀ y : BitString k, g (List.ofFn y) := by
  simpa only [not_exists, not_not] using (exists_take_ofFn_iff h (g := fun w => ¬g w)).not

/-- Reading fewer rows agrees with restricting the longer fixed-width view. -/
theorem block_ofList_prefix {count rows width : ℕ} (h : rows ≤ count) (word : List Bool) :
    block (ofList (rows * width) word) =
      block (ofList (count * width) word) ∘ Fin.castLE h := rfl

/-- Read one fixed-width row, using `false` beyond the end of the supplied list. -/
def listRow (width row : ℕ) (word : List Bool) : List Bool :=
  (word.drop (row * width) ++ List.replicate width false).take width

/-- Every extracted row has length `width`. -/
@[simp] theorem length_listRow (width row : ℕ) (word : List Bool) :
    (listRow width row word).length = width := by
  simp [listRow]

/-- Entry `i` of row `row` is bit `row * width + i` of the word, or `false` beyond its end. -/
theorem getElem_listRow {width row i : ℕ} {word : List Bool} (hi : i < width) :
    (listRow width row word)[i]'(by simpa using hi) = word.getD (row * width + i) false := by
  simp only [listRow, List.getElem_take, List.getElem_append, List.length_drop,
    List.getElem_drop, List.getElem_replicate, List.getD_eq_getElem?_getD]
  split
  · rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  · rw [List.getElem?_eq_none (by omega), Option.getD_none]

/-- Below the row width, defaulted indexing reads the corresponding word bit, even when the
word is too short and the row is padded with `false`. -/
theorem getD_listRow {width row i : ℕ} {word : List Bool} (hi : i < width) :
    (listRow width row word).getD i false = word.getD (row * width + i) false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi), Option.getD_some]
  exact getElem_listRow hi

/-- Row zero is the fixed-width view of the word. -/
theorem listRow_zero (width : ℕ) (word : List Bool) :
    listRow width 0 word = List.ofFn (ofList width word) := by
  simpa only [listRow, Nat.zero_mul, List.drop_zero] using (ofFn_ofList_eq_take width word).symm

/-- Reading an existing row from concatenated equal-width words recovers that row, regardless
of the appended suffix. Width zero is allowed. -/
theorem listRow_flatMap_append {α : Type*} {width : ℕ} (f : α → List Bool) (l : List α)
    (hf : ∀ a ∈ l, (f a).length = width) (rest : List Bool) (j : ℕ) (hj : j < l.length) :
    listRow width j (l.flatMap f ++ rest) = f l[j] := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
    have ha := hf a (List.mem_cons_self ..)
    cases j with
    | zero =>
      simp only [listRow, Nat.zero_mul, List.drop_zero, List.flatMap_cons,
        List.append_assoc, List.getElem_cons_zero]
      exact List.take_left' ha
    | succ j =>
      have := ih (fun b hb => hf b (List.mem_cons_of_mem _ hb)) j (by simpa using hj)
      simp only [listRow, List.flatMap_cons, List.append_assoc,
        List.getElem_cons_succ] at this ⊢
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm, ← List.drop_drop, List.drop_left' ha]
      exact this

/-- Reading an existing row of a flattened list of equal-width words recovers that word. -/
theorem listRow_flatten {width : ℕ} {words : List (List Bool)}
    (hwords : ∀ w ∈ words, w.length = width) {i : ℕ} (hi : i < words.length) :
    listRow width i words.flatten = words.getD i [] := by
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using
    listRow_flatMap_append id words hwords [] i hi

/-- List slicing agrees with the finite block representation, even on short input lists. -/
theorem listRow_eq_ofFn {count : ℕ} (width : ℕ) (row : Fin count) (word : List Bool) :
    listRow width row.val word = List.ofFn (block (ofList (count * width) word) row) := by
  apply List.ext_getElem (by simp)
  intro column hleft hright
  simp only [length_listRow] at hleft
  by_cases h : column + width * row.val < word.length <;>
    simp [listRow, ofList, block, List.getElem_take, List.getElem_append,
      List.getElem_drop, List.getD, Nat.lt_sub_iff_add_lt,
      Nat.add_comm, Nat.mul_comm, h]

/-- Read a specified number of rows, retaining empty rows when the width is zero. -/
def listRows (count width : ℕ) (word : List Bool) : List (List Bool) :=
  (List.range count).map (fun row => listRow width row word)

/-- Extracting `count` rows produces a list of length `count`. -/
@[simp] theorem length_listRows (count width : ℕ) (word : List Bool) :
    (listRows count width word).length = count := by
  simp [listRows]

/-- Every extracted row has the declared width. -/
theorem length_of_mem_listRows {count width : ℕ} {word row : List Bool}
    (hrow : row ∈ listRows count width word) : row.length = width := by
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp hrow
  simp

/-- Extracting rows gives the list representation of the existing finite block view. -/
theorem listRows_eq_ofFn (count width : ℕ) (word : List Bool) :
    listRows count width word =
      List.ofFn (fun row => List.ofFn (block (ofList (count * width) word) row)) := by
  apply List.ext_getElem (by simp)
  intro row hleft hright
  simpa only [listRows, List.getElem_map, List.getElem_range, List.getElem_ofFn] using
    listRow_eq_ofFn width ⟨row, by simpa using hright⟩ word

/-- The rows of a word of `k * m` bits are its blocks. -/
theorem listRows_ofFn {k m : ℕ} (x : BitString (k * m)) :
    listRows k m (List.ofFn x) = List.ofFn fun i => List.ofFn (block x i) := by
  rw [listRows_eq_ofFn, ofList_ofFn]

/-- The rows of a word starting with a full row `u` are `u` followed by the rows of the rest. -/
theorem listRows_succ_append (count width : ℕ) {u : List Bool} (hu : u.length = width)
    (v : List Bool) : listRows (count + 1) width (u ++ v) = u :: listRows count width v := by
  simp only [listRows, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp [listRow, ← hu]
  · refine List.map_congr_left fun row _ => ?_
    simp only [Function.comp_apply, listRow, Nat.succ_mul, ← List.drop_drop, Nat.add_comm _ width]
    rw [← hu, List.drop_left]

/-- Replace row `j` of a `count × width` bit string `word` with `x`. -/
def replaceRow (width count j : ℕ) (x word : List Bool) : List Bool :=
  (List.range count).flatMap (fun i => if i = j then x else listRow width i word)

/-- Reading row `i < count` from `replaceRow width count j x word` returns `x` when `i = j` and
`listRow width i word` otherwise. -/
theorem listRow_replaceRow {width count j : ℕ} {x : List Bool} (hx : x.length = width)
    (word : List Bool) {i : ℕ} (hi : i < count) :
    listRow width i (replaceRow width count j x word) =
      if i = j then x else listRow width i word := by
  have h := listRow_flatMap_append
    (width := width)
    (fun r => if r = j then x else listRow width r word)
    (List.range count)
    (fun r _ => by split_ifs <;> simp [hx])
    [] i (by simpa using hi)
  simpa [replaceRow] using h

end Cslib.BitString
