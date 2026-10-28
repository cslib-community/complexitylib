/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalModel
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalChildren
public import Mathlib.Data.List.Nodup

/-!
# Semantic entries of the native Chan–He work stack

An entry pairs the seven unsigned stack words with the three signed integer lists stored at
their bases. Memory readback reuses `Block.Realizes`; set contents use `List.toFinset`; and the
mathematical task is the existing Chan–He recursion. This is a proof invariant for native code,
not an additional machine or execution semantics.

## Main definitions

* `Entry`: fuel, three native bases and their represented integer lists.
* `Entry.words`, `Entry.task`: native serialization and the existing mathematical task.
* `Entry.Stored`, `Entry.Loaded`: block readback and the current record's register ABI.

## Main results

* `Entry.image_read`: the injective-array API represents exactly the listed finite set.
* `Entry.read_injOn`: duplicate-free lists meet the actual modulus/node call premise.
* `Entry.Stored.input`: exact signed-encoded native array readback.
* `Entry.loaded_words`: the seven register words match the pending entry's serialization.

The native worklist invariants and composition proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM

/-- One pending native record and the integer arrays represented by its pointers and lengths. -/
structure Entry where
  /-- Remaining recursion levels. -/
  fuel : ℕ
  /-- The three data bases. -/
  source : Fin 3 → ℕ
  /-- The lists stored at those bases, in their actual enumeration order. -/
  data : Fin 3 → List ℤ

/-- Seven unsigned stack words in the exact native pop order. -/
def Entry.words (e : Entry) : List ℕ :=
  [e.fuel, e.source 0, (e.data 0).length, e.source 1, (e.data 1).length,
    e.source 2, (e.data 2).length]

/-- The unchanged finite recursion task represented by an entry. -/
def Entry.task (e : Entry) : Math.Task := ⟨e.fuel, fun j => (e.data j).toFinset⟩

/-- Total extension of the compact list for the existing native array APIs. -/
def Entry.read (e : Entry) (j : Fin 3) (i : ℕ) : ℤ := (e.data j).getD i 0

/-- Each signed-encoded list occupies its concrete block, using the generic memory API. -/
def Entry.Stored (e : Entry) (mem : ℕ → ℕ) : Prop :=
  ∀ j, (Block.mk (e.source j) (e.data j).length).Realizes mem
    (fun i => Signed.encode (e.data j)[i.val])

/-- The current seven record registers contain this entry's actual unsigned metadata. -/
def Entry.Loaded (e : Entry) (x : Data 128) : Prop :=
  x.regs (slot 0) = e.fuel ∧
    (∀ j, x.regs (arraySource j) = e.source j) ∧
    ∀ j, x.regs (arrayLength j) = (e.data j).length

/-- Replace exactly one column by its actual compact heavy list and decrease the fuel. -/
def Entry.child (e : Entry) (j : Fin 3) (base : ℕ) (zs : List ℤ) : Entry :=
  ⟨e.fuel - 1, Function.update e.source j base, Function.update e.data j zs⟩

/-- A pending entry always occupies seven physical stack cells, including empty arrays. -/
theorem Entry.length_words (e : Entry) : e.words.length = 7 := rfl

/-- Inside its valid range the total read function is the actual list element. -/
theorem Entry.read_eq (e : Entry) (j : Fin 3) (i : ℕ) (hi : i < (e.data j).length) :
    e.read j i = (e.data j)[i] := by
  simp only [Entry.read, List.getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- The finite-set input of each existing array kernel is exactly the entry's listed set. -/
theorem Entry.image_read (e : Entry) (j : Fin 3) :
    (Finset.range (e.data j).length).image (e.read j) = (e.data j).toFinset := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have hi' := Finset.mem_range.mp hi
    rw [e.read_eq j i hi', List.mem_toFinset]
    exact List.getElem_mem hi'
  · intro hz
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hz)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, (e.read_eq j i hi).trans he⟩

/-- A duplicate-free compact list meets the actual native collision-counting premise. -/
theorem Entry.read_injOn (e : Entry) (j : Fin 3) (h : (e.data j).Nodup) :
    Set.InjOn (e.read j) (↑(Finset.range (e.data j).length) : Set ℕ) := by
  intro i hi k hk he
  have hi' := Finset.mem_range.mp hi
  have hk' := Finset.mem_range.mp hk
  rw [e.read_eq j i hi', e.read_eq j k hk'] at he
  exact h.getElem_inj_iff.mp he

/-- Exact readback in the native array-call format, derived from the generic block realization. -/
theorem Entry.Stored.input {e : Entry} {mem : ℕ → ℕ} (h : e.Stored mem)
    (j : Fin 3) (i : ℕ) (hi : i < (e.data j).length) :
    mem (e.source j + i) = Signed.encode (e.read j i) := by
  rw [e.read_eq j i hi]
  exact h j ⟨i, hi⟩

/-- Readback transfers along a memory equality on the three live blocks. -/
theorem Entry.Stored.congr {e : Entry} {before after : ℕ → ℕ} (h : e.Stored before)
    (hf : ∀ j i, i < (e.data j).length → after (e.source j + i) = before (e.source j + i)) :
    e.Stored after := by
  intro j i
  exact (hf j i.val i.isLt).trans (h j i)

/-- A prefix frame preserves every pending list whose block ends before the fresh allocation. -/
theorem Entry.Stored.of_prefix {e : Entry} {before after : ℕ → ℕ} (h : e.Stored before)
    {frontier : ℕ} (hsrc : ∀ j, e.source j + (e.data j).length ≤ frontier)
    (hf : ∀ a < frontier, after a = before a) : e.Stored after := by
  apply h.congr
  intro j i hi
  exact hf _ (by have := hsrc j; omega)

/-- The seven actual register words match the exact work-stack serialization. -/
theorem Entry.loaded_words {e : Entry} {x : Data 128} (h : e.Loaded x) :
    [x.regs (slot 0), x.regs (slot 1), x.regs (slot 2), x.regs (slot 3),
      x.regs (slot 4), x.regs (slot 5), x.regs (slot 6)] = e.words := by
  rcases h with ⟨hf, hs, hn⟩
  change [x.regs (slot 0), x.regs (arraySource 0), x.regs (arrayLength 0),
      x.regs (arraySource 1), x.regs (arrayLength 1),
      x.regs (arraySource 2), x.regs (arrayLength 2)] = _
  simp only [hf, hs, hn, Entry.words]

/-- Replacing a native column changes exactly the corresponding mathematical set. -/
theorem Entry.task_child (e : Entry) (j : Fin 3) (base : ℕ) (zs : List ℤ) :
    (e.child j base zs).task =
      ⟨e.fuel - 1, Function.update e.task.sets j zs.toFinset⟩ := by
  unfold Entry.child Entry.task
  congr 1
  funext k
  by_cases he : k = j
  · subst k
    simp only [Function.update_self]
  · simp only [Function.update_of_ne he]

/-- The native child-record words represent exactly the changed data block, with the two
other columns and their original enumeration orders preserved. -/
theorem Entry.child_words {e : Entry} {x : Data 128} (h : e.Loaded x)
    (bases : Fin 3 → ℕ) (zs : Fin 3 → List ℤ)
    (hb : ∀ j, x.regs (heavyBase j) = bases j)
    (hn : ∀ j, x.regs (heavyLength j) = (zs j).length) (j : Fin 3) :
    childWords x j = (e.child j (bases j) (zs j)).words := by
  obtain ⟨hf, hs, hl⟩ := h
  have hs₀ : x.regs (slot 1) = e.source 0 := hs 0
  have hs₁ : x.regs (slot 3) = e.source 1 := hs 1
  have hs₂ : x.regs (slot 5) = e.source 2 := hs 2
  have hl₀ : x.regs (slot 2) = (e.data 0).length := hl 0
  have hl₁ : x.regs (slot 4) = (e.data 1).length := hl 1
  have hl₂ : x.regs (slot 6) = (e.data 2).length := hl 2
  fin_cases j <;> simp +decide [childWords, Entry.child, Entry.words, hf,
    hs₀, hs₁, hs₂, hl₀, hl₁, hl₂, hb, hn]

/-- The size and magnitude assumptions are the existing finite three-set admissibility notion;
duplicate-free enumeration is the additional native-array obligation. -/
def Entry.Valid (e : Entry) (n U : ℕ) : Prop :=
  (∀ j, (e.data j).Nodup) ∧ Cslib.Algorithms.ThreeSum.ChanHe.Admissible n U
    (e.data 0).toFinset (e.data 1).toFinset (e.data 2).toFinset

/-- Native input lengths equal finite-set cardinalities under the duplicate-free obligation. -/
theorem Entry.Valid.length_le {e : Entry} {n U : ℕ} (h : e.Valid n U) (j : Fin 3) :
    (e.data j).length ≤ n := by
  have he := List.toFinset_card_of_nodup (h.1 j)
  rw [← he]
  fin_cases j
  · exact h.2.card₁
  · exact h.2.card₂
  · exact h.2.card₃

/-- The existing finite-set magnitude promise bounds every actual native array element. -/
theorem Entry.Valid.natAbs_le {e : Entry} {n U : ℕ} (h : e.Valid n U)
    (j : Fin 3) (i : ℕ) (hi : i < (e.data j).length) : (e.read j i).natAbs ≤ U := by
  have hz : e.read j i ∈ (e.data j).toFinset := by
    rw [e.read_eq j i hi, List.mem_toFinset]
    exact List.getElem_mem hi
  have hb : |e.read j i| ≤ (U : ℤ) := by
    fin_cases j
    · exact h.2.bdd₁ _ hz
    · exact h.2.bdd₂ _ hz
    · exact h.2.bdd₃ _ hz
  rw [← Int.natCast_natAbs] at hb
  exact_mod_cast hb

/-- Replacing a column by a duplicate-free subset preserves the existing size/magnitude promises. -/
theorem Entry.Valid.child {e : Entry} {n U : ℕ} (h : e.Valid n U)
    (j : Fin 3) (base : ℕ) (zs : List ℤ) (hnd : zs.Nodup)
    (hsub : zs.toFinset ⊆ (e.data j).toFinset) : (e.child j base zs).Valid n U := by
  refine ⟨?_, ?_⟩
  · intro k
    by_cases he : k = j
    · subst k
      simpa only [Entry.child, Function.update_self] using hnd
    · simpa only [Entry.child, Function.update_of_ne he] using h.1 k
  · fin_cases j
    · change Cslib.Algorithms.ThreeSum.ChanHe.Admissible n U zs.toFinset
        (e.data 1).toFinset (e.data 2).toFinset
      exact ⟨(Finset.card_le_card hsub).trans h.2.card₁, h.2.card₂, h.2.card₃,
        h.2.bdd₁.mono hsub, h.2.bdd₂, h.2.bdd₃⟩
    · change Cslib.Algorithms.ThreeSum.ChanHe.Admissible n U (e.data 0).toFinset
        zs.toFinset (e.data 2).toFinset
      exact ⟨h.2.card₁, (Finset.card_le_card hsub).trans h.2.card₂, h.2.card₃,
        h.2.bdd₁, h.2.bdd₂.mono hsub, h.2.bdd₃⟩
    · change Cslib.Algorithms.ThreeSum.ChanHe.Admissible n U (e.data 0).toFinset
        (e.data 1).toFinset zs.toFinset
      exact ⟨h.2.card₁, h.2.card₂, (Finset.card_le_card hsub).trans h.2.card₃,
        h.2.bdd₁, h.2.bdd₂, h.2.bdd₃.mono hsub⟩

/-- A child reuses both untouched data blocks and the actual newly written heavy block. -/
theorem Entry.Stored.child {e : Entry} {mem : ℕ → ℕ} (h : e.Stored mem)
    (j : Fin 3) (base : ℕ) (zs : List ℤ)
    (hz : (Block.mk base zs.length).Realizes mem (fun i => Signed.encode zs[i.val])) :
    (e.child j base zs).Stored mem := by
  intro k i
  by_cases he : k = j
  · subst k
    have hi : i.val < zs.length := by
      simpa only [Entry.child, Function.update_self] using i.isLt
    simpa only [Entry.child, Block.read, Function.update_self] using hz ⟨i.val, hi⟩
  · have hi : i.val < (e.data k).length := by
      simpa only [Entry.child, Function.update_of_ne he] using i.isLt
    simpa only [Entry.child, Block.read, Function.update_of_ne he] using h k ⟨i.val, hi⟩

/-- Actual heavy lists and bases give exactly the existing ordered three-child worklist. -/
theorem Entry.task_children (e : Entry) (Q : Finset ℕ) (Λ : ℕ)
    (bases : Fin 3 → ℕ) (zs : Fin 3 → List ℤ)
    (hz : ∀ j, (zs j).toFinset = Cslib.Algorithms.ThreeSum.ChanHe.heavy
      (e.task.sets j) (e.task.node Q Λ).M) :
    [(e.child 0 (bases 0) (zs 0)).task, (e.child 1 (bases 1) (zs 1)).task,
      (e.child 2 (bases 2) (zs 2)).task] = e.task.children Q Λ (e.fuel - 1) := by
  let M := (e.task.node Q Λ).M
  have h₀ : Function.update e.task.sets 0
      (Cslib.Algorithms.ThreeSum.ChanHe.heavy (e.task.sets 0) M) =
      ![Cslib.Algorithms.ThreeSum.ChanHe.heavy (e.task.sets 0) M,
        e.task.sets 1, e.task.sets 2] := by
    funext j
    fin_cases j <;> rfl
  have h₁ : Function.update e.task.sets 1
      (Cslib.Algorithms.ThreeSum.ChanHe.heavy (e.task.sets 1) M) =
      ![e.task.sets 0, Cslib.Algorithms.ThreeSum.ChanHe.heavy (e.task.sets 1) M,
        e.task.sets 2] := by
    funext j
    fin_cases j <;> rfl
  have h₂ : Function.update e.task.sets 2
      (Cslib.Algorithms.ThreeSum.ChanHe.heavy (e.task.sets 2) M) =
      ![e.task.sets 0, e.task.sets 1,
        Cslib.Algorithms.ThreeSum.ChanHe.heavy (e.task.sets 2) M] := by
    funext j
    fin_cases j <;> rfl
  rw [Entry.task_child, Entry.task_child, Entry.task_child, hz 0, hz 1, hz 2, h₀, h₁, h₂]
  rfl

/-- The native word-stack length records exactly seven cells per pending entry. -/
theorem length_serialized (es : List Entry) : (es.flatMap Entry.words).length = 7 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons, List.length_append, Entry.length_words, ih, List.length_cons]
    omega

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
