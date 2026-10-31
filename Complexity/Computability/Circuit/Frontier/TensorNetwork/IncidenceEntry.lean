/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceNetwork
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.TruncatedRing
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.VertexDesc
public import Complexity.Computability.GenericRAM.Native.SubsetPairFold
public import Complexity.Computability.PolyTime.ParityFactorEval
public import Complexity.Foundations.Data.BitString.Enumeration

/-!
# The entries of the incidence network of Lemma D.2

The incidence network of Lemma D.2 of [OpenAI2026ETH] (pp. 55–56,
`Cslib.Circuits.Frontier.IncidenceNetwork.network`) has three kinds of vertices: a row for each
test group, a column for each variable group, and fixed tables for padding. This file gives the
entry procedure `incEntry` of all three, with values in `B_{P,ℓ} = (ℤ / 2 ^ P)[V] / (V ^ ℓ)` as
coefficient lists (`GaloisRingArith` at the modulus `truncFl ℓ`, see
`Complexity/Computability/Circuit/Frontier/TensorNetwork/TruncatedRing.lean`), and the encoding
`encDesc` of the descriptors.

**Indices.** The ports of a group vertex are the index wires of its blocks, in order. A block of
`N` incidences with `d` selected has `blockWires = ⌈log₂ C(N, d)⌉` wires. The entry reads the
bits block by block (`blockIndices`), each chunk as an index `ι` in little-endian order
(`BitString.lsbValue`). An index `ι < C(N, d)` names the weight-`d` subset of the block's
incidences at the `true` positions of the combination of rank `ι`
(`GenericRAM.SubsetPairFold.pureUnrankComb`, `selectBlock`). The selected incidences of all
blocks are `selected`.

**Rows** (`rowEntry`, p. 56). For the test group with tests `t`, an index `ι ≥ C(N, d)` in any
block gives the entry `0`. Otherwise let `S_t` be the variables selected for test `t`. The entry
is `∏_t c_t(S_t)` with `c_t(S) = ∑_{T ⊆ S} (-1) ^ (|S| - |T|) B(m_t(T); V)`, where `m_t(T)` is the
number of monomials of test `t` inside `T` (`monomialsIn`) and `B(y; V)` is the parity factor
`Polynomial.parityFactor ℓ y`, whose coefficient list modulo `2 ^ P` is `factorCoeffs` (from
`parityLinearCoeffs`, the linear remainders `e_j` of Lemma 5.1). The product of the subset sums
is one sum over the subsets of all selected incidences of the group: a word `w` on them
(`chosenBy`) contributes `(-1) ^ (|sel| - |w|) ∏_t B(m_t(T_t(w)); V)` (`rowTerm`, `rowBody`), and
the entry is the sum over all `2 ^ |sel|` words (`rowSum`), which the native machine streams.

**Columns** (`colEntry`). For the variable group with variables `X_h`, the entry is the constant
`2 ^ u` modulo `2 ^ P`, for `u` the number of variables of `X_h` selected by no test
(`unselectedCount`). Columns read invalid indices too; the rows make those terms zero.

**Tables** are read by `tableEntry`.

The correctness of the contraction against the incidence expansion and the native certificate are
separate.

## Main definitions

* `Cslib.Circuits.Frontier.IncidenceNetwork.blockIndices`: the indices of the blocks.
* `Cslib.Circuits.Frontier.IncidenceNetwork.selected`: the selected incidences.
* `Cslib.Circuits.Frontier.IncidenceNetwork.factorCoeffs`: the parity factor in `B_{P,ℓ}`.
* `Cslib.Circuits.Frontier.IncidenceNetwork.rowEntry`, `colEntry`: the group entries.
* `Cslib.Circuits.Frontier.IncidenceNetwork.incEntry`: the entry procedure.
* `Cslib.Circuits.Frontier.IncidenceNetwork.encDesc`: the encoding of the descriptors.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Lemma 5.1 (p. 36) and
  Lemma D.2 (pp. 54–56).
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open GaloisRingArith Cslib.BitString Cslib.GenericRAM Turing.MultiTapeTM

/-! ### Reading the indices -/

/-- **The number of index wires of a block** of `N` incidences with `d` selected:
`⌈log₂ C(N, d)⌉`. -/
@[expose] def blockWires (b : Block) : ℕ := Nat.clog 2 (b.1.length.choose b.2)

/-- One step of reading the indices: the next `blockWires b` bits, read little-endian. -/
@[expose] def indexStep (st : List Bool × List ℕ) (b : Block) : List Bool × List ℕ :=
  (st.1.drop (blockWires b), st.2 ++ [lsbValue (st.1.take (blockWires b))])

/-- **The indices of the blocks**, read from consecutive chunks of the bits. -/
@[expose] def blockIndices (blocks : List Block) (bs : List Bool) : List ℕ :=
  (blocks.foldl indexStep (bs, [])).2

/-- **The incidences of a block selected by an index**: those at the `true` positions of the
combination of that rank. -/
@[expose] def selectBlock (b : Block) (ι : ℕ) : List (ℕ × ℕ) :=
  ((b.1.zip (SubsetPairFold.pureUnrankComb b.1.length b.2 ι)).filter (·.2)).map (·.1)

/-- **The selected incidences** of the blocks at the indices. -/
@[expose] def selected (blocks : List Block) (idx : List ℕ) : List (ℕ × ℕ) :=
  (blocks.zip idx).flatMap fun p => selectBlock p.1 p.2

/-- **Valid indices**: the index of every block of `N` incidences with `d` selected is below
`C(N, d)`. -/
@[expose] def validIndices (blocks : List Block) (idx : List ℕ) : Bool :=
  (blocks.zip idx).all fun p => decide (p.2 < p.1.1.length.choose p.1.2)

/-! ### Rows -/

/-- **The parity factor `B(x; V)` in `B_{P,ℓ}`** at a natural `x`: coefficient `j < ℓ` is
`(a_j + b_j x) (x (x - 1)) ^ j` modulo `2 ^ P`, for the linear remainders `a_j + b_j Y` of
`parityLinearCoeffs ℓ`. -/
@[expose] def factorCoeffs (P ℓ x : ℕ) : List ℕ :=
  (List.range ℓ).map fun j =>
    ((((parityLinearCoeffs ℓ).getD j (0, 0)).1 % ((2 ^ P : ℕ) : ℤ)).toNat +
        (((parityLinearCoeffs ℓ).getD j (0, 0)).2 % ((2 ^ P : ℕ) : ℤ)).toNat * x) *
      (x * (x - 1)) ^ j % 2 ^ P

/-- **The monomials of a test inside its chosen variables**: the number of monomials of `test`
all of whose variables `v` have `(t, v)` chosen. -/
@[expose] def monomialsIn (test : List (List ℕ)) (t : ℕ) (chosen : List (ℕ × ℕ)) : ℕ :=
  test.countP fun M => M.all fun v => decide ((t, v) ∈ chosen)

/-- **The product of the parity factors** of the tests at the chosen incidences, in `B_{P,ℓ}`:
`∏_t B(m_t; V)`, for `m_t` the monomials of test `t` inside its chosen variables. -/
@[expose] def rowTerm (P ℓ : ℕ) (tests : List (List (List ℕ))) (chosen : List (ℕ × ℕ)) :
    List ℕ :=
  (List.range tests.length).foldl
    (fun acc t => mul P (truncFl ℓ) acc (factorCoeffs P ℓ (monomialsIn (tests.getD t []) t chosen)))
    (one (truncFl ℓ))

/-- The incidences chosen by a word on the selected incidences: those at its `true` positions. -/
@[expose] def chosenBy (sel : List (ℕ × ℕ)) (w : List Bool) : List (ℕ × ℕ) :=
  ((sel.zip w).filter (·.2)).map (·.1)

/-- The descriptor of a row: the precision `P`, the truncation order `ℓ`, the tests of its group
and its blocks. -/
abbrev RowDesc : Type := ℕ × ℕ × List (List (List ℕ)) × List Block

/-- The context of the sum of a row: `P`, `ℓ`, the tests and the selected incidences. -/
abbrev RowCtx : Type := ℕ × ℕ × List (List (List ℕ)) × List (ℕ × ℕ)

/-- **One term of the sum of a row**, at a word `w` on the selected incidences: add
`(-1) ^ (|sel| - |w|) ∏_t B(m_t; V)` to the accumulator, keeping the context. -/
@[expose] def rowBody (q : (ℕ × List Bool) × RowCtx × List ℕ) : RowCtx × List ℕ :=
  (q.2.1,
    if (q.2.1.2.2.2.length - q.1.2.count true) % 2 = 0 then
      add q.2.1.1 (truncFl q.2.1.2.1) q.2.2
        (rowTerm q.2.1.1 q.2.1.2.1 q.2.1.2.2.1 (chosenBy q.2.1.2.2.2 q.1.2))
    else
      sub q.2.1.1 (truncFl q.2.1.2.1) q.2.2
        (rowTerm q.2.1.1 q.2.1.2.1 q.2.1.2.2.1 (chosenBy q.2.1.2.2.2 q.1.2)))

/-- **The sum of a row** over all words on its selected incidences, in enumeration order. -/
@[expose] def rowSum (ctx : RowCtx) : List ℕ :=
  ((enumList ctx.2.2.2.length).foldl (fun st w => rowBody ((ctx.2.2.2.length, w), st))
    (ctx, zero (truncFl ctx.2.1))).2

/-- The context of a row at the bits on its ports: its `P`, `ℓ` and tests, and the incidences
selected by the indices. -/
@[expose] def rowContext (row : RowDesc) (bs : List Bool) : RowCtx :=
  (row.1, row.2.1, row.2.2.1, selected row.2.2.2 (blockIndices row.2.2.2 bs))

/-- **The entry of a row**: zero (the empty list) at an invalid index, and the sum of the row
otherwise. -/
@[expose] def rowEntry (row : RowDesc) (bs : List Bool) : List ℕ :=
  if validIndices row.2.2.2 (blockIndices row.2.2.2 bs) then rowSum (rowContext row bs) else []

/-! ### Columns -/

/-- The descriptor of a column: the precision `P`, the variables of its group and its blocks. -/
abbrev ColDesc : Type := ℕ × List ℕ × List Block

/-- The number of variables selected by no incidence. -/
@[expose] def unselectedCount (vars : List ℕ) (sel : List (ℕ × ℕ)) : ℕ :=
  vars.countP fun v => decide (v ∉ sel.map Prod.snd)

/-- **The entry of a column**: the constant `2 ^ u` modulo `2 ^ P`, for `u` the number of its
variables selected by no incidence. -/
@[expose] def colEntry (col : ColDesc) (bs : List Bool) : List ℕ :=
  [2 ^ unselectedCount col.2.1 (selected col.2.2 (blockIndices col.2.2 bs)) % 2 ^ col.1]

/-! ### The entry procedure -/

/-- **The entry procedure of the incidence network**: rows, columns and tables. -/
@[expose] def incEntry : Desc → List Bool → List ℕ
  | .inl row, bs => rowEntry row bs
  | .inr (.inl col), bs => colEntry col bs
  | .inr (.inr table), bs => tableEntry table bs

@[simp] theorem incEntry_inl (row : RowDesc) (bs : List Bool) :
    incEntry (.inl row) bs = rowEntry row bs := rfl

@[simp] theorem incEntry_inr_inl (col : ColDesc) (bs : List Bool) :
    incEntry (.inr (.inl col)) bs = colEntry col bs := rfl

@[simp] theorem incEntry_inr_inr (table : List ℕ) (bs : List Bool) :
    incEntry (.inr (.inr table)) bs = tableEntry table bs := rfl

/-! ### Encoding -/

/-- The encoding of a block: its incidences in binary and its selected number in unary. -/
abbrev encBlock : Block ↪ List Bool := encPair (encList (encPair encNat encNat)) encUnary

/-- The encoding of a row descriptor: `P` and `ℓ` in unary, then the tests and the blocks. -/
abbrev encRowDesc : RowDesc ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair (encList (encList (encList encNat)))
    (encList encBlock)))

/-- The encoding of a column descriptor: `P` in unary, then the variables and the blocks. -/
abbrev encColDesc : ColDesc ↪ List Bool :=
  encPair encUnary (encPair (encList encNat) (encList encBlock))

/-- **The encoding of the descriptors**: a tag, then a row, a column or a table. -/
abbrev encDesc : Desc ↪ List Bool := encSum encRowDesc (encSum encColDesc (encList encNat))

/-! ### Basic facts -/

/-- The rows of an invalid index have entry zero. -/
theorem rowEntry_of_not_valid {row : RowDesc} {bs : List Bool}
    (h : validIndices row.2.2.2 (blockIndices row.2.2.2 bs) = false) : rowEntry row bs = [] := by
  simp [rowEntry, h]

@[simp] theorem length_factorCoeffs (P ℓ x : ℕ) : (factorCoeffs P ℓ x).length = ℓ := by
  simp [factorCoeffs]

theorem lt_of_mem_factorCoeffs {P ℓ x y : ℕ} (hy : y ∈ factorCoeffs P ℓ x) : y < 2 ^ P := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
  exact Nat.mod_lt _ (Nat.two_pow_pos P)

/-- The indices of the blocks: one per block. -/
theorem length_blockIndices (blocks : List Block) (bs : List Bool) :
    (blockIndices blocks bs).length = blocks.length := by
  have h (st : List Bool × List ℕ) :
      (blocks.foldl indexStep st).2.length = st.2.length + blocks.length := by
    induction blocks generalizing st with
    | nil => simp
    | cons b blocks ih =>
      rw [List.foldl_cons, ih]
      simp [indexStep]
      omega
  simpa [blockIndices] using h (bs, [])

/-- A block selects at most its incidences. -/
theorem length_selectBlock_le (b : Block) (ι : ℕ) : (selectBlock b ι).length ≤ b.1.length := by
  rw [selectBlock, List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

/-- The selected incidences are at most the incidences of the blocks. -/
theorem length_selected_le (blocks : List Block) (idx : List ℕ) :
    (selected blocks idx).length ≤ (blocks.map fun b => b.1.length).sum := by
  induction blocks generalizing idx with
  | nil => simp [selected]
  | cons b blocks ih =>
    cases idx with
    | nil => simp [selected]
    | cons ι idx =>
      have := ih idx
      simp only [selected, List.zip_cons_cons, List.flatMap_cons, List.length_append,
        List.map_cons, List.sum_cons] at this ⊢
      exact Nat.add_le_add (length_selectBlock_le b ι) this

end Cslib.Circuits.Frontier.IncidenceNetwork
