/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.FusionTree.Tree
public import Complexity.Computability.WordRAM.Heap

/-!
# Contiguous static fusion-tree records

Every record has an 18-word header. Leaves store tag `0`, presence, and key (zero when
absent), followed by fifteen zero words. Internal nodes have tag `1`, followed by exactly
`n` interleaved pairs of full child minima and absolute child pointers, and the recursively
encoded children in order. No capacity-sized arrays are allocated. The header indices are:
tag 0, child count 1, minimum 2, compression
mask C 3, multiplier digits 4--6, D 7, copies 8, packed complements 9, packed normal 10,
guards 11, bits 12, middle 13, radix 14, maximum 15, width-dependent global offset 16,
and reserved 17. `Parameters` supplies indices 3--17; it asserts no node-search oracle.

This is a static representation, with explicit arena/address and stored-word fit contracts.
It asserts neither preprocessing time nor a query running time.

## Main definitions

* `span`, `encode`: allocation length and concrete list of RAM words.
* `Rep`: actual memory realizes that list using `WordRAM.Block.Realizes`.
* `ArenaFits`, `ContentFits`: separate address/frontier and stored-content contracts.

## Main results

* `encode_length`: the concrete list has precisely the claimed allocation length.
* `Rep.node_header`, `Rep.child`: literal loads and recursive child representations.
* `child_span_le`, `access_owned`, `child_access_owned`: allocation safety.
* `decode_encode`: the concrete memory round-trips through a load-based decoder.
* `span_build_le`: at most `126n + 18` allocated words, uniformly in branching capacity.
* `encoding_exists`: a fitting concrete memory, decoder and linear allocation bound together.

## References

* [FredmanWillard1993]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree

open Cslib.WordRAM
open Cslib.Algorithms.Lean.FusionTree

/-- The fifteen preprocessing words in header slots 3 through 17, for each internal node.
The final two slots accommodate a width-dependent global offset and one reserved word. -/
abbrev Parameters := Tree → Fin 15 → ℕ

/-- Fixed record header length, independent of branching capacity. -/
def headerWords : ℕ := 18

/-! Stable offsets within internal headers. The fifteen parameter words are named here so
node-search implementations can use the layout without duplicating numerical indices. -/
namespace HeaderOffset

/-- Record tag: 0 for leaves, 1 for internal nodes. -/
def tag : ℕ := 0
/-- Number of actual children (presence for a leaf). -/
def count : ℕ := 1
/-- Cached minimum (the key for a leaf). -/
def minimum : ℕ := 2
/-- Compression mask C. -/
def compression : ℕ := 3
/-- First multiplier digit. -/
def multiplierLow : ℕ := 4
/-- Second multiplier digit. -/
def multiplierMiddle : ℕ := 5
/-- Third multiplier digit. -/
def multiplierHigh : ℕ := 6
/-- Compression mask D. -/
def maskD : ℕ := 7
/-- Copies constant. -/
def copies : ℕ := 8
/-- Packed complement sketches. -/
def packedComplements : ℕ := 9
/-- Packed ordinary sketches. -/
def packedNormal : ℕ := 10
/-- Packed field guards. -/
def guards : ℕ := 11
/-- Sketch bit count. -/
def bits : ℕ := 12
/-- Middle-field constant. -/
def middle : ℕ := 13
/-- Packed field radix. -/
def radix : ℕ := 14
/-- Maximum compressed payload. -/
def maximum : ℕ := 15
/-- Width-dependent global offset. -/
def globalOffset : ℕ := 16
/-- Reserved preprocessing word. -/
def reserved : ℕ := 17

end HeaderOffset

/-- Actual allocated words, without any padding to the maximum branching capacity. -/
def span : Tree → ℕ
  | .leaf _ => headerWords
  | .node _ cs => headerWords + 2 * cs.length + (cs.map span).sum

/-- Starting address of child `i`, after the parent's actual tables and earlier children. -/
def childAddress (base : ℕ) (cs : List Tree) (i : ℕ) : ℕ :=
  base + headerWords + 2 * cs.length + ((cs.take i).map span).sum

/-- The concrete internal header. -/
def header (p : Parameters) (m : ℕ) (cs : List Tree) : List ℕ :=
  [1, cs.length, m] ++ List.ofFn (p (.node m cs))

/-- Stride-two child table: a full minimum followed by its absolute pointer. -/
def childTable (base : ℕ) (cs : List Tree) : List ℕ :=
  List.ofFn fun j : Fin (2 * cs.length) =>
    if j.val % 2 = 0 then (cs[j.val / 2]'(by omega)).minimum
    else childAddress base cs (j.val / 2)

private theorem childTable_minimum (base : ℕ) (cs : List Tree) (i : Fin cs.length) :
    (childTable base cs)[2 * i.val]'(by simp [childTable]) = cs[i].minimum := by
  have hd : 2 * i.val / 2 = i.val := by omega
  have hm : 2 * i.val % 2 = 0 := by omega
  simp [childTable, hd, hm]

private theorem childTable_pointer (base : ℕ) (cs : List Tree) (i : Fin cs.length) :
    (childTable base cs)[2 * i.val + 1]'(by simp [childTable]; omega) =
      childAddress base cs i := by
  have hd : (2 * i.val + 1) / 2 = i.val := by omega
  simp [childTable, hd]

mutual
  /-- Serialize a tree at its absolute address. Invalid nonsingleton leaves are truncated;
  `decode_encode` requires `Tree.Valid`, which excludes them. -/
  def encode (p : Parameters) (base : ℕ) : Tree → List ℕ
    | .leaf xs => [0, if xs.isEmpty then 0 else 1, xs.headD 0] ++ List.replicate 15 0
    | .node m cs => header p m cs ++ (childTable base cs ++
        encodeForest p (base + headerWords + 2 * cs.length) cs)

  /-- Serialize consecutive child records; the next record starts at the previous one's end. -/
  def encodeForest (p : Parameters) (base : ℕ) : List Tree → List ℕ
    | [] => []
    | t :: ts => encode p base t ++ encodeForest p (base + span t) ts
end

/-- Every serialized tree occupies exactly its claimed span. -/
theorem encode_length (p : Parameters) (base : ℕ) (t : Tree) :
    (encode p base t).length = span t := by
  revert base
  induction t using Tree.rec
      (motive_2 := fun cs => ∀ base,
        (encodeForest p base cs).length = (cs.map span).sum) with
  | leaf xs => intro base; simp [encode, span, headerWords]
  | node m cs ih =>
    intro base
    simp only [encode, header, span, List.length_append, List.length_cons, List.length_nil,
      List.length_ofFn, childTable, ih, headerWords]
    omega
  | nil => simp [encodeForest]
  | cons t ts iht ihs => simp [encodeForest, iht, ihs]

/-- The concrete child-record list has the sum of the child spans as its length. -/
theorem encodeForest_length (p : Parameters) (base : ℕ) (cs : List Tree) :
    (encodeForest p base cs).length = (cs.map span).sum := by
  induction cs generalizing base with
  | nil => simp [encodeForest]
  | cons t ts ih => simp [encodeForest, encode_length, ih]

/-- Actual RAM contents of a contiguous list, using the existing allocation API. -/
abbrev Stores (xs : List ℕ) (base : ℕ) (mem : ℕ → ℕ) : Prop :=
  (Block.mk base xs.length).Realizes mem (fun i => xs[i])

private theorem stores_iff (xs : List ℕ) (base : ℕ) (mem : ℕ → ℕ) :
    Stores xs base mem ↔ ∀ i, (hi : i < xs.length) → mem (base + i) = xs[i] := by
  exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i i.isLt⟩

private theorem stores_append {xs ys : List ℕ} {base : ℕ} {mem : ℕ → ℕ} :
    Stores (xs ++ ys) base mem ↔
      Stores xs base mem ∧ Stores ys (base + xs.length) mem := by
  simp only [stores_iff]
  constructor
  · intro h
    constructor
    · intro i hi
      have hh := h i (by simp only [List.length_append]; omega)
      rw [List.getElem_append_left hi] at hh
      exact hh
    · intro i hi
      have hh := h (xs.length + i) (by simp only [List.length_append]; omega)
      rw [List.getElem_append_right (by omega : xs.length ≤ xs.length + i)] at hh
      simpa only [Nat.add_sub_cancel_left, Nat.add_assoc] using hh
  · rintro ⟨hx, hy⟩ i hi
    by_cases hix : i < xs.length
    · rw [List.getElem_append_left hix]; exact hx i hix
    · rw [List.getElem_append_right (by omega)]
      have hh := hy (i - xs.length) (by simp only [List.length_append] at hi; omega)
      convert hh using 1
      congr 1
      omega

/-- Memory represents the concrete serialized tree, with arbitrary memory outside its block. -/
def Rep (p : Parameters) (t : Tree) (base : ℕ) (mem : ℕ → ℕ) : Prop :=
  Stores (encode p base t) base mem

/-- The existing heap assertion for the serialized arena, including exactly its allocated cells. -/
def arena (p : Parameters) (t : Tree) (base : ℕ) : HeapAssertion :=
  HeapAssertion.array base (encode p base t).length (fun i => (encode p base t)[i])

/-- The heap assertion's contents are exactly the representation predicate. -/
theorem arena_holds (p : Parameters) (t : Tree) (base : ℕ) (mem : ℕ → ℕ) :
    (arena p t base).holds mem ↔ Rep p t base mem := Iff.rfl

/-- The heap footprint counts actual allocated words, including each fixed header. -/
theorem arena_footprint (p : Parameters) (t : Tree) (base : ℕ) :
    (arena p t base).footprint = (Block.mk base (span t)).footprint := by
  simp only [arena, HeapAssertion.array, encode_length]

/-- Writes disjoint from the contiguous arena preserve the complete tree representation. -/
theorem Rep.frame {p : Parameters} {t : Tree} {base : ℕ} {mem mem' : ℕ → ℕ}
    {writes : Finset ℕ} (hr : Rep p t base mem)
    (hd : Disjoint (Block.mk base (span t)).footprint writes)
    (hm : Modifies writes mem mem') : Rep p t base mem' :=
  HeapAssertion.frame (P := arena p t base) hr (by rwa [arena_footprint]) hm

/-- A concrete total memory obtained by placing the serialized words into an otherwise zero RAM. -/
def memory (p : Parameters) (t : Tree) (base : ℕ) : ℕ → ℕ :=
  fun a => if base ≤ a then (encode p base t)[a - base]?.getD 0 else 0

/-- The explicit list encoding has an actual RAM realization. -/
theorem rep_memory (p : Parameters) (t : Tree) (base : ℕ) :
    Rep p t base (memory p t base) := by
  rw [Rep, stores_iff]
  intro i hi
  simp [memory, List.getElem?_eq_getElem hi]

/-- A represented internal node exposes its header, minima, pointers and child-record interval. -/
private theorem Rep.node_parts {p : Parameters} {m base : ℕ} {cs : List Tree} {mem : ℕ → ℕ}
    (hr : Rep p (.node m cs) base mem) :
    Stores (header p m cs) base mem ∧
    Stores (childTable base cs) (base + headerWords) mem ∧
    Stores (encodeForest p (base + headerWords + 2 * cs.length) cs)
      (base + headerWords + 2 * cs.length) mem := by
  simp only [Rep, encode, stores_append] at hr
  simpa [header, List.length_append, List.length_cons, List.length_nil, List.length_ofFn,
    List.length_map, childTable, headerWords, Nat.add_assoc] using hr

/-- The first three internal header words and all fifteen preprocessing words decode literally. -/
theorem Rep.node_header {p : Parameters} {m base : ℕ} {cs : List Tree} {mem : ℕ → ℕ}
    (hr : Rep p (.node m cs) base mem) :
    mem base = 1 ∧ mem (base + 1) = cs.length ∧ mem (base + 2) = m ∧
      ∀ j : Fin 15, mem (base + 3 + j) = p (.node m cs) j := by
  have hh := stores_append.mp hr.node_parts.1
  have hh0 := (stores_iff _ _ _).mp hh.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hh0 0 (by simp)
  · simpa using hh0 1 (by simp)
  · simpa using hh0 2 (by simp)
  · intro j
    have hj := (stores_iff _ _ _).mp hh.2 j (by simp only [List.length_ofFn]; exact j.isLt)
    simpa only [List.length_cons, List.length_nil, List.getElem_ofFn] using hj

/-- The three leaf words decode as tag, presence and key. -/
theorem Rep.leaf_fields {p : Parameters} {base : ℕ} {xs : List ℕ} {mem : ℕ → ℕ}
    (hr : Rep p (.leaf xs) base mem) :
    mem base = 0 ∧ mem (base + 1) = (if xs.isEmpty then 0 else 1) ∧
      mem (base + 2) = xs.headD 0 := by
  have hh := (stores_iff _ _ _).mp (stores_append.mp hr).1
  exact ⟨by simpa using hh 0 (by simp),
    by simpa using hh 1 (by simp),
    by simpa using hh 2 (by simp)⟩

private theorem forest_child {p : Parameters} {base : ℕ} {cs : List Tree} {mem : ℕ → ℕ}
    (hr : Stores (encodeForest p base cs) base mem) (i : ℕ) (hi : i < cs.length) :
    Rep p cs[i] (base + ((cs.take i).map span).sum) mem := by
  induction cs generalizing base i with
  | nil => simp at hi
  | cons t ts ih =>
    have hh := stores_append.mp hr
    cases i with
    | zero => simpa [Rep] using hh.1
    | succ i =>
      have hh' : Stores (encodeForest p (base + span t) ts) (base + span t) mem := by
        simpa only [encode_length] using hh.2
      simpa [List.take_succ_cons, Nat.add_assoc] using ih hh' i (by simpa using hi)

/-- Following a stored child pointer gives the representation of precisely that child. -/
theorem Rep.child {p : Parameters} {m base : ℕ} {cs : List Tree} {mem : ℕ → ℕ}
    (hr : Rep p (.node m cs) base mem) (i : Fin cs.length) :
    mem (base + headerWords + 2 * i.val) = cs[i].minimum ∧
    mem (base + headerWords + (2 * i.val + 1)) = childAddress base cs i ∧
    Rep p cs[i] (childAddress base cs i) mem := by
  have hh := hr.node_parts
  refine ⟨?_, ?_, ?_⟩
  · exact ((stores_iff _ _ _).mp hh.2.1 _ (by simp [childTable])).trans
      (childTable_minimum base cs i)
  · exact ((stores_iff _ _ _).mp hh.2.1 _ (by simp [childTable]; omega)).trans
      (childTable_pointer base cs i)
  · exact forest_child hh.2.2 i i.isLt

private theorem prefix_span_le (cs : List Tree) (i : ℕ) (hi : i < cs.length) :
    ((cs.take i).map span).sum + span cs[i] ≤ (cs.map span).sum := by
  induction cs generalizing i with
  | nil => simp at hi
  | cons t ts ih =>
    cases i with
    | zero => simp
    | succ i =>
      have hh := ih i (by simpa using hi)
      simpa [List.take_succ_cons, Nat.add_assoc] using Nat.add_le_add_left hh (span t)

/-- Every record is nonempty, including the empty leaf. -/
private theorem span_pos (t : Tree) : 0 < span t := by
  cases t <;> simp [span, headerWords]

/-- A whole child allocation lies inside its parent's allocation. -/
theorem child_span_le (base m : ℕ) (cs : List Tree) (i : Fin cs.length) :
    base + headerWords + 2 * cs.length ≤ childAddress base cs i ∧
    childAddress base cs i + span cs[i] ≤ base + span (.node m cs) := by
  have hh := prefix_span_le cs i i.isLt
  simp only [childAddress, span, Fin.getElem_fin]
  omega

/-- Every valid offset denotes an allocated cell, including the full leaf header. -/
theorem access_owned (base : ℕ) (t : Tree) (a : ℕ) (ha : a < span t) :
    (Block.mk base (span t)).Owns (base + a) :=
  ⟨Nat.le_add_right _ _, Nat.add_lt_add_left ha _⟩

/-- Every direct header/table read is an owned parent word. Tables use their actual lengths. -/
private theorem node_access_owned (base m : ℕ) (cs : List Tree) (a : ℕ)
    (ha : a < headerWords + 2 * cs.length) :
    (Block.mk base (span (.node m cs))).Owns (base + a) := by
  simp only [Block.Owns, span]
  omega

/-- Each of the eighteen header loads lies inside the record, including for empty leaves. -/
theorem header_access_owned (base : ℕ) (t : Tree) (j : Fin 18) :
    (Block.mk base (span t)).Owns (base + j) := by
  apply access_owned
  cases t <;> simp only [span, headerWords] <;> omega

/-- Both stride-two table loads are inside the parent's allocation. -/
theorem child_entry_access_owned (base m : ℕ) (cs : List Tree) (i : Fin cs.length) :
    (Block.mk base (span (.node m cs))).Owns (base + headerWords + 2 * i.val) ∧
    (Block.mk base (span (.node m cs))).Owns (base + headerWords + (2 * i.val + 1)) := by
  constructor <;> simpa only [Nat.add_assoc] using
    node_access_owned base m cs _ (by omega)

/-- Every word read inside a child record is owned by the parent allocation. Repeated use
provides the same guarantee at arbitrary descendant depth. -/
theorem child_access_owned (base m : ℕ) (cs : List Tree) (i : Fin cs.length) (a : ℕ)
    (ha : a < span cs[i]) :
    (Block.mk base (span (.node m cs))).Owns (childAddress base cs i + a) := by
  have hh := child_span_le base m cs i
  dsimp only [Block.Owns]
  omega

/-- The concrete allocation is at most nine times the structural scalar-slot count. -/
private theorem span_le_slots (t : Tree) : span t ≤ 9 * t.slots := by
  induction t using Tree.rec
      (motive_2 := fun cs => (cs.map span).sum ≤ 9 * (cs.map Tree.slots).sum) with
  | leaf xs => simp only [span, Tree.slots, headerWords]; omega
  | node m cs ih => simp only [span, Tree.slots, headerWords]; omega
  | nil => simp
  | cons t ts iht ihs =>
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Uniform linear allocated RAM words, with constants independent of branching capacity
and word width. This counts the actual serialized words, including all preprocessing headers. -/
theorem span_build_le {B : ℕ} (hB : 2 ≤ B) (xs : List ℕ) :
    span (Tree.build B xs) ≤ 126 * xs.length + 18 := by
  have hh := span_le_slots (Tree.build B xs)
  have hs := Tree.slots_build_le hB xs
  omega

/-- A single absolute constant works for both terms in the usual `C * n + C` bound. -/
theorem span_build_le_uniform {B : ℕ} (hB : 2 ≤ B) (xs : List ℕ) :
    span (Tree.build B xs) ≤ 126 * xs.length + 126 :=
  (span_build_le hB xs).trans (by omega)

/-- Recover the functional tree by loads of tags, fields and absolute child pointers.
Fuel bounds recursive depth, not the number of machine instructions. The zero-fuel result
is a default; correctness requires fuel strictly larger than the tree height. -/
def decode : ℕ → (ℕ → ℕ) → ℕ → Tree
  | 0, _, _ => .leaf []
  | fuel + 1, mem, base =>
    if mem base = 0 then
      .leaf (if mem (base + 1) = 0 then [] else [mem (base + 2)])
    else
      .node (mem (base + 2)) (List.ofFn fun i : Fin (mem (base + 1)) =>
        decode fuel mem (mem (base + headerWords + (2 * i.val + 1))))

/-- Concrete RAM decoding recovers every valid tree. In particular, empty and singleton
leaves remain distinct even when the stored key is zero. -/
theorem decode_rep {B fuel base : ℕ} {p : Parameters} {t : Tree} {mem : ℕ → ℕ}
    (ht : Tree.Valid B t) (hr : Rep p t base mem) (hf : t.height < fuel) :
    decode fuel mem base = t := by
  induction fuel generalizing t base with
  | zero => omega
  | succ fuel ih =>
    cases t with
    | leaf xs =>
      have hh := hr.leaf_fields
      simp only [decode, hh.1, ↓reduceIte, hh.2.1, hh.2.2]
      have hl : xs.length ≤ 1 := by simpa only [Tree.Valid] using ht
      rcases xs with _ | ⟨x, _ | ⟨y, ys⟩⟩ <;> simp_all
    | node m cs =>
      simp only [Tree.Valid] at ht
      have hh := hr.node_header
      simp only [decode, hh.1, Nat.one_ne_zero, ↓reduceIte, hh.2.1, hh.2.2.1]
      congr 1
      conv_rhs => rw [← List.ofFn_getElem (xs := cs)]
      apply congrArg List.ofFn
      funext i
      have hc := hr.child i
      simp only [Fin.val_cast]
      rw [hc.2.1]
      apply ih (ht.2.2.2 cs[i] (List.getElem_mem i.isLt)).1 hc.2.2
      have hh' := Tree.height_lt_node_of_mem (m := m) (List.getElem_mem i.isLt)
      simp only [Fin.getElem_fin]
      omega

/-- The explicit serializer and total RAM realization round-trip through the load-based decoder. -/
theorem decode_encode {B fuel : ℕ} {t : Tree} (ht : Tree.Valid B t)
    (hf : t.height < fuel) (p : Parameters) (base : ℕ) :
    decode fuel (memory p t base) base = t :=
  decode_rep ht (rep_memory p t base) hf

/-- Every owned address and the one-past-end allocation frontier fit a word. This strict
frontier condition also suffices for the existing `WordRAM.alloc` execution contract. -/
def ArenaFits (w base : ℕ) (t : Tree) : Prop := Fits w (base + span t)

/-- A numerical sufficient arena contract, using only input length and the allocation base.
It bounds the entire one-past-end frontier, rather than only the input key values. -/
theorem arenaFits_build_of_bound {B w base : ℕ} (hB : 2 ≤ B) (xs : List ℕ)
    (hw : Fits w (base + 126 * xs.length + 18)) :
    ArenaFits w base (Tree.build B xs) :=
  hw.of_le (by have hs := span_build_le hB xs; omega)

/-- Allocation size, base address and tag one all fit under the arena contract. Together
with the fitting frontier, these are the numerical inputs to `WordRAM.alloc_exec`. -/
theorem ArenaFits.allocation {w base : ℕ} {t : Tree} (ha : ArenaFits w base t) :
    Fits w base ∧ Fits w (span t) ∧ Fits w 1 := by
  have hp := span_pos t
  exact ⟨ha.of_le (by omega), ha.of_le (by omega), ha.of_le (by omega)⟩

/-- Explicit key and preprocessing-word assumptions. Child counts and addresses are instead
bounded by `ArenaFits`; fitting input keys alone does not imply either contract. -/
def ContentFits (w : ℕ) (p : Parameters) : Tree → Prop
  | .leaf xs => ∀ x ∈ xs, Fits w x
  | .node m cs => Fits w m ∧ (∀ j, Fits w (p (.node m cs) j)) ∧
      ∀ t ∈ cs, ContentFits w p t

/-- Cached child minima fit whenever all explicit tree contents fit. -/
theorem ContentFits.minimum {w : ℕ} {p : Parameters} {t : Tree} (ht : ContentFits w p t) :
    Fits w t.minimum := by
  cases t with
  | leaf xs =>
    cases xs with
    | nil => exact fits_zero w
    | cons x xs =>
      simp only [ContentFits] at ht
      exact ht x (by simp)
  | node m cs =>
    simp only [ContentFits] at ht
    exact ht.1

/-- The fit assumption for the arena bounds every owned access address. -/
theorem ArenaFits.address {w base a : ℕ} {t : Tree} (ha : ArenaFits w base t)
    (ho : (Block.mk base (span t)).Owns a) : Fits w a :=
  ha.of_le (by exact Nat.le_of_lt ho.2)

/-- The child's whole allocation also fits; in particular following its pointer cannot wrap. -/
theorem ArenaFits.child {w base m : ℕ} {cs : List Tree}
    (ha : ArenaFits w base (.node m cs)) (i : Fin cs.length) :
    ArenaFits w (childAddress base cs i) cs[i] :=
  ha.of_le (child_span_le base m cs i).2

/-- Every serialized data word fits under explicit content and arena assumptions. -/
private theorem encode_fits {w : ℕ} {p : Parameters} (t : Tree) :
    ∀ base, ArenaFits w base t → ContentFits w p t →
      ∀ v ∈ encode p base t, Fits w v := by
  induction t using Tree.rec
      (motive_2 := fun cs => ∀ base, Fits w (base + (cs.map span).sum) →
        (∀ t ∈ cs, ContentFits w p t) → ∀ v ∈ encodeForest p base cs, Fits w v) with
  | leaf xs =>
    intro base ha ht v hv
    have h1 : Fits w 1 := ha.of_le (by simp [span, headerWords])
    simp only [encode, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_replicate] at hv
    rcases hv with (rfl | rfl | rfl) | ⟨_, rfl⟩
    · exact fits_zero w
    · split
      · exact fits_zero w
      · exact h1
    · exact ContentFits.minimum ht
    · exact fits_zero w
  | node m cs ih =>
    intro base ha ht v hv
    simp only [ContentFits] at ht
    have h1 : Fits w 1 := ha.of_le (by simp [span, headerWords]; omega)
    have hn : Fits w cs.length := ha.of_le (by simp only [span]; omega)
    simp only [encode, List.mem_append, header, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_ofFn] at hv
    rcases hv with ((rfl | rfl | rfl) | ⟨j, rfl⟩) | hv | hv
    · exact h1
    · exact hn
    · exact ht.1
    · exact ht.2.1 j
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
      split
      · exact (ht.2.2 _ (List.getElem_mem (by omega))).minimum
      · exact (ha.child ⟨j.val / 2, by omega⟩).of_le (Nat.le_add_right _ _)
    · apply ih _ _ ht.2.2 v hv
      simpa only [ArenaFits, Nat.add_assoc, span] using ha
  | nil =>
    rename_i base ha ht v hv
    simp [encodeForest] at hv
  | cons t ts iht ihs =>
    rename_i base ha ht v hv
    have hbound : Fits w (base + span t + (ts.map span).sum) := by
      simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using ha
    rcases List.mem_append.mp hv with hv | hv
    · exact iht base (hbound.of_le (by omega)) (ht t (by simp)) v hv
    · exact ihs (base + span t) hbound (fun u hu => ht u (by simp [hu])) v hv

/-- The concrete memory consists entirely of fitting words, including its zero exterior. -/
theorem memory_fits {w base : ℕ} {p : Parameters} {t : Tree}
    (ha : ArenaFits w base t) (ht : ContentFits w p t) (a : ℕ) :
    Fits w (memory p t base a) := by
  simp only [memory]
  split
  · cases he : (encode p base t)[a - base]? with
    | none => exact fits_zero w
    | some v =>
      simp only [Option.getD_some]
      exact encode_fits t base ha ht v (List.mem_of_getElem? he)
  · exact fits_zero w

/-- A fitting contiguous encoding exists for every built tree whose explicit address and
content assumptions hold. The decoder uses depth fuel; no preprocessing-time claim is made. -/
theorem encoding_exists {B w base : ℕ} (hB : 2 ≤ B) (xs : List ℕ) (p : Parameters)
    (ha : ArenaFits w base (Tree.build B xs)) (ht : ContentFits w p (Tree.build B xs)) :
    ∃ mem : ℕ → ℕ, Rep p (Tree.build B xs) base mem ∧ (∀ a, Fits w (mem a)) ∧
      decode ((Tree.build B xs).height + 1) mem base = Tree.build B xs ∧
      (encode p base (Tree.build B xs)).length ≤ 126 * xs.length + 18 := by
  refine ⟨memory p (Tree.build B xs) base, rep_memory _ _ _, memory_fits ha ht, ?_, ?_⟩
  · exact decode_encode (Tree.valid_build hB xs) (by omega) p base
  · rw [encode_length]
    exact span_build_le hB xs

end Cslib.Algorithms.WordRAM.FusionTree
