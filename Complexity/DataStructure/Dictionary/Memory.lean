/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.Spec
public import Complexity.DataStructure.Memory.Frame
public import Complexity.DataStructure.Memory.Triple

/-!
# A direct-address table over the memory oracle

The dictionary `Dictionary.spec U V n_max` on the keys `Fin U` is implemented as a direct-address
table: a field `T` of `U` cells, one per key, holding `0` for an absent key and `v + 1` for the
value `v` (`decode`). A lookup reads the key's cell and an insertion writes it, one memory unit
each (`amortized`). The table has a cell for every key, so the capacity `n_max` never binds.
Values below `V` are stored, so `V` must fit a word.

The table is framed by its field (`framed`), so it shares memory with other structures. Allocated
in memory that is zero above the frontier, it starts empty at the cost of one memory unit
(`inv_alloc`).

## Main definitions

* `decode`: the value of a cell, `0` for absent.
* `get`, `insert`, `ops`, `methods`: the operations as memory programs.
* `abs`, `Inv`, `Valid`: the abstraction function, the implementation invariant and the static
  well-formedness of the field.
* `refinement`, `framed`: the table as a refinement of the dictionary, framed by its field.

## Main results

* `amortized`: every operation costs one memory unit.
* `inv_alloc`: a field allocated in memory that is zero above the frontier is an empty table.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 11.1][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.Dictionary.Memory

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory

/-- The value stored in a cell: `0` is an absent key, and `v + 1` the value `v`. This is the
word encoding of `Option ℕ` that the word-RAM dictionaries use. -/
def decode : ℕ → Option ℕ
  | 0 => none
  | v + 1 => some v

@[simp] theorem decode_zero : decode 0 = none := rfl

@[simp] theorem decode_succ (v : ℕ) : decode (v + 1) = some v := rfl

variable {U : ℕ} (T : Block)

/-- Look up a key: read its cell. -/
def get (u : Fin U) : Prog (Option ℕ) := do
  let x ← T.get u
  pure (decode x)

/-- Store the value `v` for a key: write `v + 1` to its cell. -/
def insert (u : Fin U) (v : ℕ) : Prog Unit := T.set u (v + 1)

/-- The dictionary operations as memory programs. -/
def ops : (o : Dictionary.Op U) → Prog o.Result
  | .get u => get T u
  | .insert u v => insert T u v

/-- The operations as methods of `Dictionary.spec U V n_max` over `Memory.spec w`. -/
abbrev methods (w V n_max : ℕ) : Methods (Dictionary.spec U V n_max) (Memory.spec w) := ops T

/-- The represented dictionary: the decoded cell of each key. -/
def abs (s : Memory.State) : Dictionary.State U := fun u => decode (s.mem (T.base + u))

/-- The implementation invariant: the field is allocated. -/
abbrev Inv (s : Memory.State) : Prop := T.Allocated s

/-- Static well-formedness for `U` keys and values below `V` at word size `w`: one cell per key,
and `V` fits a word, so every stored `v + 1` does. -/
structure Valid (T : Block) (w U V : ℕ) : Prop where
  /-- One cell per key. -/
  length_eq : T.length = U
  /-- The value bound fits a word. -/
  value_fits : Fits w V

variable {T} {w V n_max : ℕ}

/-- The cell of a key is allocated. -/
theorem cell_lt (hT : Valid T w U V) {s : Memory.State} (hs : Inv T s) (u : Fin U) :
    T.base + u < s.frontier :=
  Block.Allocated.lt_frontier hs (by rw [hT.length_eq]; exact u.isLt)

/-- The cell of a key belongs to the field. -/
theorem mem_footprint (hT : Valid T w U V) (u : Fin U) : T.base + u ∈ T.footprint :=
  Block.mem_footprint.mpr (Block.owns_add (by rw [hT.length_eq]; exact u.isLt))

/-- An owned cell of an allocated field is allocated. -/
theorem lt_of_owns {s : Memory.State} (hs : Inv T s) {a : ℕ} (ha : T.Owns a) : a < s.frontier := by
  unfold Block.Owns at ha
  unfold Inv Block.Allocated at hs
  omega

variable (T) in
/-- What a run of the operation `o` from `s` establishes: the specified step, the invariant, and
no change to the frontier or to any cell outside the field. -/
def Post (s : Memory.State) (o : Dictionary.Op U) (r : o.Result) (s' : Memory.State) : Prop :=
  Dictionary.step (abs T s) o = (abs T s', r) ∧ Inv T s' ∧ s'.frontier = s.frontier ∧
    ∀ a ∉ T.footprint, s'.mem a = s.mem a

/-- **Each operation realizes the specified step** with one memory operation. -/
theorem ops_triple (hT : Valid T w U V) {s : Memory.State} (hs : Inv T s) (o : Dictionary.Op U)
    (hv : (Dictionary.spec U V n_max).valid (abs T s) o) : Triple w s (ops T o) 1 (Post T s o) := by
  cases o with
  | get u =>
    exact Triple.read_bind (cell_lt hT hs u)
      (Triple.pure ⟨rfl, hs, rfl, fun _ _ => rfl⟩)
  | insert u v =>
    refine Triple.write_bind (cell_lt hT hs u) (hT.value_fits.of_le hv.2) <|
      Triple.pure ⟨?_, hs, rfl, fun a ha => Function.update_of_ne
        (fun h => ha (by rw [h]; exact mem_footprint hT u)) _ _⟩
    refine Prod.ext (funext fun u' => ?_) rfl
    by_cases hu : u' = u
    · subst hu
      simp [abs]
    · have : (T.base + u' : ℕ) ≠ T.base + u := by
        have := Fin.val_ne_of_ne hu
        omega
      simp [abs, hu, Function.update_of_ne this]

/-- The run of an operation, by `ops_triple`. -/
theorem ops_run (hT : Valid T w U V) {s : Memory.State} (hs : Inv T s) (o : Dictionary.Op U)
    (hv : (Dictionary.spec U V n_max).valid (abs T s) o) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (ops T o)) ∧
      (Memory.spec w).totalCost charge s ((Memory.spec w).clientHistory s (ops T o)) ≤ 1 ∧
      Post T s o ((Memory.spec w).clientResult s (ops T o))
        ((Memory.spec w).clientState s (ops T o)) :=
  triple_iff.mp (ops_triple hT hs o hv)

/-- The direct-address table implements the dictionary. -/
def refinement (hT : Valid T w U V) : Refinement (Dictionary.spec U V n_max) (Memory.spec w) :=
  Refinement.ofFn (methods T w V n_max) (Inv T) (abs T)
    (fun o hs hv => (ops_run hT hs o hv).1)
    (fun o hs hv => by
      obtain ⟨-, -, hstep, hinv, -⟩ := ops_run hT hs o hv
      exact ⟨hstep, hinv⟩)

/-- The abstraction reads only the field. -/
theorem abs_congr (hT : Valid T w U V) {s s' : Memory.State}
    (h : ∀ a ∈ T.footprint, s'.mem a = s.mem a) : abs (U := U) T s' = abs T s :=
  funext fun u => by simp only [abs, h _ (mem_footprint hT u)]

/-- The table, framed by its field. -/
def framed (hT : Valid T w U V) : Memory.Framed (Dictionary.spec U V n_max) w :=
  .ofStatic (refinement hT) T.footprint (fun hs ha => lt_of_owns hs (Block.mem_footprint.mp ha))
    (fun hs h hf => ⟨Block.Allocated.mono hs hf, abs_congr hT h⟩)
    (fun o hs hv b _ hb => by
      obtain ⟨-, -, -, -, -, h⟩ := ops_run hT hs o hv
      exact h b hb)

/-- The footprint of a table is its field. -/
@[simp] theorem framed_footprint (hT : Valid T w U V) (s : Memory.State) :
    (framed (n_max := n_max) hT).footprint s = T.footprint := rfl

/-- **Every operation costs one memory unit.** -/
theorem amortized (hT : Valid T w U V) :
    (framed (n_max := n_max) hT).Amortized charge (fun _ _ => 1) fun _ => 0 :=
  Refinement.Amortized.ofFn fun {_} o hs hv => by
    obtain ⟨-, hc, -⟩ := ops_run (w := w) hT hs o hv
    exact Nat.add_le_add_right hc 0

/-- A field allocated without clearing in memory that is zero above the frontier is an empty
table. -/
theorem inv_alloc {s : Memory.State} (hz : ZeroAbove s) :
    Inv ⟨s.frontier, U⟩ ⟨s.mem, s.frontier + U⟩ ∧
      abs ⟨s.frontier, U⟩ ⟨s.mem, s.frontier + U⟩ = Dictionary.empty U := by
  refine ⟨le_rfl, funext fun u => ?_⟩
  change decode (s.mem (s.frontier + u)) = none
  rw [hz _ (Nat.le_add_right _ _), decode_zero]

end Cslib.DataStructure.Dictionary.Memory
