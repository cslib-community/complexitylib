/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Computability.Circuit.Boolean.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Feature
public import Mathlib.Tactic.DeriveFintype

/-!
# Block and wire layout of the uniform tableau circuit

For a multi-tape Turing machine with `k` work tapes and state type `State` running for `T` steps on
inputs of length `n`, the uniform tableau circuit
(`Complexity/Computability/Circuit/Boolean/Tableau/Basic.lean`) has `n` input wires, two
constant gates (`false` at wire `n` and `true` at wire `n + 1`), and `T + 1` blocks of
`blockSize k State T` gates. Work-tape cells `-T, …, T` and input positions `0, …, n + 1` share
`numCols T = 2 T + 1` columns. Within each block, gates are arranged into four regions:

* the *scan* (`ScanLoc`), repeated across the `2 T + 1` columns;
* the *global* gates (`GlobLoc`): conjunctions for situations and disjunctions for action
  attributes (`Attr`);
* the *global feature* gadgets (`GFeat`), sixteen gates per state or output view;
* the *column feature* gadgets (`ColFeat`), sixteen gates per column feature in each column.

Gates refer to earlier wires symbolically (`Ref`, `ColSel`, `Guard`), and `Ref.resolve` translates
each symbolic reference to a concrete wire index via `wire`. Every region position has an index
(`idx`, `Loc.offset`) and an arithmetic decoder (`ofIdx`, `gadgetB`, `gadgetJ`) that invert each
other on valid indices, so every gate index `2 ≤ g < numGates k State T` sits at a unique admissible
block position (`div_mod_wire`, `exists_wire_eq`).

## Main definitions

* `Cslib.Circuits.Boolean.Tableau.Attr`, `Cslib.Circuits.Boolean.Tableau.ColFeat`,
  `Cslib.Circuits.Boolean.Tableau.GFeat`, `Cslib.Circuits.Boolean.Tableau.ScanQ`,
  `Cslib.Circuits.Boolean.Tableau.ScanLoc`, `Cslib.Circuits.Boolean.Tableau.numSit`,
  `Cslib.Circuits.Boolean.Tableau.GlobLoc`, `Cslib.Circuits.Boolean.Tableau.Loc`,
  `Cslib.Circuits.Boolean.Tableau.Loc.ColOK`: positions within a tableau block.
* `Cslib.Circuits.Boolean.Tableau.ColSel`, `Cslib.Circuits.Boolean.Tableau.ColSel.apply`,
  `Cslib.Circuits.Boolean.Tableau.Guard`, `Cslib.Circuits.Boolean.Tableau.Guard.test`,
  `Cslib.Circuits.Boolean.Tableau.Ref`, `Cslib.Circuits.Boolean.Tableau.Ref.toData`,
  `Cslib.Circuits.Boolean.Tableau.colF`, `Cslib.Circuits.Boolean.Tableau.gfF`,
  `Cslib.Circuits.Boolean.Tableau.act`, `Cslib.Circuits.Boolean.Tableau.halted`,
  `Cslib.Circuits.Boolean.Tableau.scanAt`: symbolic wire references relative to a block and column.
* `Cslib.Circuits.Boolean.Tableau.symIdx`, `Cslib.Circuits.Boolean.Tableau.attrIdx`,
  `Cslib.Circuits.Boolean.Tableau.gadgetIdx`, `Cslib.Circuits.Boolean.Tableau.scanWidth`,
  `Cslib.Circuits.Boolean.Tableau.globWidth`, `Cslib.Circuits.Boolean.Tableau.gfWidth`,
  `Cslib.Circuits.Boolean.Tableau.colWidth`, `Cslib.Circuits.Boolean.Tableau.numCols`,
  `Cslib.Circuits.Boolean.Tableau.globStart`, `Cslib.Circuits.Boolean.Tableau.gfStart`,
  `Cslib.Circuits.Boolean.Tableau.colStart`, `Cslib.Circuits.Boolean.Tableau.blockSize`,
  `Cslib.Circuits.Boolean.Tableau.numGates`, `Cslib.Circuits.Boolean.Tableau.Loc.offset`,
  `Cslib.Circuits.Boolean.Tableau.wire`, `Cslib.Circuits.Boolean.Tableau.Ref.resolve`,
  `Cslib.Circuits.Boolean.Tableau.argsOf`: numerical layout and wire resolution.
* `Cslib.Circuits.Boolean.Tableau.symOf`, `Cslib.Circuits.Boolean.Tableau.ScanQ.ofIdx`,
  `Cslib.Circuits.Boolean.Tableau.ScanLoc.ofIdx`, `Cslib.Circuits.Boolean.Tableau.GlobLoc.ofIdx`,
  `Cslib.Circuits.Boolean.Tableau.GFeat.ofIdx`, `Cslib.Circuits.Boolean.Tableau.ColFeat.ofIdx`:
  arithmetic decoders for block offsets.

## Main results

* `Cslib.Circuits.Boolean.Tableau.Loc.offset_lt`: every admissible position lies within its block.
* `Cslib.Circuits.Boolean.Tableau.div_mod_wire`: dividing and reducing a wire index modulo
  `blockSize` recovers its time block and intra-block offset.
* `Cslib.Circuits.Boolean.Tableau.exists_wire_eq`: every gate index after the two constants is the
  wire of an admissible block position.

## References

* [R. E. Ladner, *The circuit value problem is log space complete for P*][Ladner1975]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Sections 6.1 and 6.7][AroraBarak09]
* [C. H. Papadimitriou, *Computational Complexity*, Theorem 8.1][Papadimitriou94]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Tableau

open Turing MultiTapeTM

/-! ### Positions within a block -/

/-- One aspect of an action: the next state, the move of the input head, what is written on a work
tape, the move of a work head, and the output symbol. -/
inductive Attr (k : ℕ) (State : Type) where
  /-- The next state is `q` (`none` to halt). -/
  | state (q : Option State)
  /-- The input head moves by `m`. -/
  | inMove (m : SignType)
  /-- Work tape `i` is written `w` (`none` to leave the cell). -/
  | write (i : Fin k) (w : Option (Option Bool))
  /-- Work head `i` moves by `m`. -/
  | move (i : Fin k) (m : SignType)
  /-- The output symbol is `e`. -/
  | out (e : Option Bool)
  deriving DecidableEq, Fintype

/-- The features held in each column: the input head, a work head and a work cell. -/
inductive ColFeat (k : ℕ) where
  /-- The input head is at the position of the column. -/
  | inPos
  /-- Work head `i` is at the cell of the column. -/
  | head (i : Fin k)
  /-- The cell of the column on work tape `i` holds `s`. -/
  | cell (i : Fin k) (s : Option Bool)
  deriving DecidableEq, Fintype

/-- The global features: the state and the view of the output. -/
inductive GFeat (State : Type) where
  /-- The state is `q` (`none` once halted). -/
  | state (q : Option State)
  /-- The output written so far has the view `o`. -/
  | out (o : OutView)
  deriving DecidableEq, Fintype

/-- The quantities accumulated by the scan across the columns: the symbol under the input head and
the symbols under the work heads. -/
inductive ScanQ (k : ℕ) where
  /-- The input head reads `s`. -/
  | inRead (s : Option Bool)
  /-- Work head `i` reads `s`. -/
  | read (i : Fin k) (s : Option Bool)
  deriving DecidableEq, Fintype

/-- The gates of a column of the scan. -/
inductive ScanLoc (k : ℕ) where
  /-- Work head `i` is not at the cell of the column. -/
  | nh (i : Fin k)
  /-- The negated input bit of the column. -/
  | nx
  /-- The contribution of the column to a scanned quantity. -/
  | term (q : ScanQ k)
  /-- The disjunction of the contributions of the columns so far. -/
  | acc (q : ScanQ k)
  deriving DecidableEq, Fintype

/-- The number of situations of a machine. -/
abbrev numSit (k : ℕ) (State : Type) [Fintype State] : ℕ := Fintype.card (Situation k State)

/-- The global gates: the situations, as chains of conjunctions, and the attributes, as chains of
disjunctions over the situations. -/
inductive GlobLoc (k : ℕ) (State : Type) [Fintype State] where
  /-- The conjunction of the first `i + 1` conditions of situation number `j`. -/
  | sit (j : Fin (numSit k State)) (i : Fin (k + 1))
  /-- The disjunction of the first `j` situations having the attribute `v`. -/
  | attr (v : Attr k State) (j : Fin (numSit k State + 1))
  deriving DecidableEq, Fintype

/-- The position of a gate within its block: a gate of the scan, a global gate, or one of the
sixteen gates computing a feature from its terms (the conjunction `false` and the running
disjunction `true` of term `j`). -/
inductive Loc (k : ℕ) (State : Type) [Fintype State] where
  /-- A gate of the scan. -/
  | scan (l : ScanLoc k)
  /-- A global gate. -/
  | glob (l : GlobLoc k State)
  /-- A gate computing a global feature. -/
  | gf (f : GFeat State) (b : Bool) (j : Fin 8)
  /-- A gate computing a column feature. -/
  | col (f : ColFeat k) (b : Bool) (j : Fin 8)
  deriving DecidableEq, Fintype

/-! ### References to wires -/

/-- The column of a reference, relative to the column `c` of the gate: `c`, `c - 1`, `c + 1`, or
the last column. -/
inductive ColSel where
  /-- The column `c`. -/
  | same
  /-- The column `c - 1`. -/
  | prev
  /-- The column `c + 1`. -/
  | next
  /-- The last column. -/
  | last
  deriving DecidableEq

/-- Finite enumeration of column selectors. -/
instance : Fintype ColSel where
  elems := {.same, .prev, .next, .last}
  complete x := by cases x <;> simp

/-- A condition on the column `c` of a gate, under which a reference is used; otherwise it reads
`false`. -/
inductive Guard where
  /-- Always. -/
  | always
  /-- `1 ≤ c`. -/
  | pos
  /-- `c` is not the last column. -/
  | ltLast
  /-- `1 ≤ c ≤ n`: the column holds an input bit. -/
  | inRange
  /-- The column holds no input bit. -/
  | outRange
  /-- `c = 0`. -/
  | isZero
  /-- `c = n + 1`. -/
  | isEnd
  /-- `1 ≤ c ≤ n + 1`. -/
  | leEnd
  deriving DecidableEq

/-- Finite enumeration of column guards. -/
instance : Fintype Guard where
  elems := {.always, .pos, .ltLast, .inRange, .outRange, .isZero, .isEnd, .leEnd}
  complete x := by cases x <;> simp

/-- A reference to a wire, relative to the block and the column of the gate: the constant wires,
the input bit of the column, or a position of the current or the previous block. -/
inductive Ref (k : ℕ) (State : Type) [Fintype State] where
  /-- The constant `false`. -/
  | fls
  /-- The constant `true`. -/
  | tru
  /-- The input bit of the column, if it holds one. -/
  | inp
  /-- The position `l` of the previous block (`prev = true`) or the current one, in the column
  selected by `cs`, under the guard `g`. -/
  | node (prev : Bool) (l : Loc k State) (cs : ColSel) (g : Guard)
  deriving DecidableEq

variable {k : ℕ} {State : Type} [Fintype State]

/-- References as data. -/
def Ref.toData : Ref k State → Option (Option (Option (Bool × Loc k State × ColSel × Guard)))
  | .fls => none
  | .tru => some none
  | .inp => some (some none)
  | .node p l cs g => some (some (some (p, l, cs, g)))

/-- Finiteness of symbolic wire references. -/
instance : Finite (Ref k State) :=
  Finite.of_injective Ref.toData fun a b h => by cases a <;> cases b <;> simp_all [Ref.toData]

/-- A column feature of the previous block, in the column selected by `cs`, under the guard `g`. -/
def colF (f : ColFeat k) (cs : ColSel) (g : Guard) : Ref k State := .node true (.col f true 7) cs g

/-- A global feature of the previous block. -/
def gfF (f : GFeat State) : Ref k State := .node true (.gf f true 7) .same .always

/-- The attribute `v` of the action of the current step. -/
def act (v : Attr k State) : Ref k State :=
  .node false (.glob (.attr v (Fin.last _))) .same .always

/-- The previous configuration has halted. -/
abbrev halted : Ref k State := gfF (.state none)

/-- A gate of the scan of the current block. -/
def scanAt (l : ScanLoc k) (cs : ColSel) (g : Guard) : Ref k State := .node false (.scan l) cs g

/-! ### The layout -/

/-- The number of a cell symbol: blank, `false`, `true`. -/
def symIdx : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

/-- The number of a scanned quantity. -/
def ScanQ.idx : ScanQ k → ℕ
  | .inRead s => symIdx s
  | .read i s => 3 + 3 * i + symIdx s

/-- The position of a gate within a column of the scan. -/
def ScanLoc.idx : ScanLoc k → ℕ
  | .nh i => i
  | .nx => k
  | .term q => k + 1 + 2 * q.idx
  | .acc q => k + 2 + 2 * q.idx

/-- The number of gates of a column of the scan. -/
def scanWidth (k : ℕ) : ℕ := 7 + 7 * k

/-- The number of an attribute. -/
noncomputable def attrIdx (v : Attr k State) : ℕ := Fintype.equivFin (Attr k State) v

/-- The position of a global gate. -/
noncomputable def GlobLoc.idx : GlobLoc k State → ℕ
  | .sit j i => j * (k + 1) + i
  | .attr v j => numSit k State * (k + 1) + attrIdx v * (numSit k State + 1) + j

/-- The number of global gates. -/
def globWidth (k : ℕ) (State : Type) [Fintype State] : ℕ :=
  numSit k State * (k + 1) + Fintype.card (Attr k State) * (numSit k State + 1)

/-- The number of a global feature. -/
noncomputable def GFeat.idx : GFeat State → ℕ
  | .state q => Fintype.equivFin (Option State) q
  | .out o => Fintype.card (Option State) + o.index

/-- The number of a column feature. -/
def ColFeat.idx : ColFeat k → ℕ
  | .inPos => 0
  | .head i => 1 + i
  | .cell i s => 1 + k + 3 * i + symIdx s

/-- The position of gate `j` of kind `b` within the sixteen gates computing feature number `fi`. -/
def gadgetIdx (fi : ℕ) (b : Bool) (j : Fin 8) : ℕ := 16 * fi + 8 * b.toNat + j

/-- The number of gates computing the global features. -/
def gfWidth (State : Type) [Fintype State] : ℕ := 16 * (Fintype.card (Option State) + 4)

/-- The number of gates computing the features of a column. -/
def colWidth (k : ℕ) : ℕ := 16 * (1 + 4 * k)

/-- The number of columns: the work cells `-T, …, T`. -/
def numCols (T : ℕ) : ℕ := 2 * T + 1

/-- The start of the global gates within a block. -/
def globStart (k T : ℕ) : ℕ := numCols T * scanWidth k

/-- The start of the global features within a block. -/
def gfStart (k : ℕ) (State : Type) [Fintype State] (T : ℕ) : ℕ :=
  globStart k T + globWidth k State

/-- The start of the column features within a block. -/
def colStart (k : ℕ) (State : Type) [Fintype State] (T : ℕ) : ℕ :=
  gfStart k State T + gfWidth State

/-- The number of gates of a block. -/
def blockSize (k : ℕ) (State : Type) [Fintype State] (T : ℕ) : ℕ :=
  colStart k State T + numCols T * colWidth k

/-- The number of gates of the tableau: the two constants and `T + 1` blocks. -/
def numGates (k : ℕ) (State : Type) [Fintype State] (T : ℕ) : ℕ :=
  2 + (T + 1) * blockSize k State T

/-- The offset of a position in column `c` from the start of its block. -/
noncomputable def Loc.offset (T c : ℕ) : Loc k State → ℕ
  | .scan l => c * scanWidth k + l.idx
  | .glob l => globStart k T + l.idx
  | .gf f b j => gfStart k State T + gadgetIdx f.idx b j
  | .col f b j => colStart k State T + c * colWidth k + gadgetIdx f.idx b j

/-- **The wire of a position** `l` of block `t`, in column `c`: the inputs come first, then the
two constants, then the blocks. -/
noncomputable def wire (n T t : ℕ) (l : Loc k State) (c : ℕ) : ℕ :=
  n + 2 + t * blockSize k State T + l.offset T c

/-- Whether a guard holds in column `c`. -/
def Guard.test (n T c : ℕ) : Guard → Bool
  | .always => true
  | .pos => decide (1 ≤ c)
  | .ltLast => decide (c + 1 < numCols T)
  | .inRange => decide (1 ≤ c ∧ c ≤ n)
  | .outRange => !decide (1 ≤ c ∧ c ≤ n)
  | .isZero => decide (c = 0)
  | .isEnd => decide (c = n + 1)
  | .leEnd => decide (1 ≤ c ∧ c ≤ n + 1)

/-- The column selected relative to column `c`. -/
def ColSel.apply (T c : ℕ) : ColSel → ℕ
  | .same => c
  | .prev => c - 1
  | .next => c + 1
  | .last => 2 * T

/-- **The wire of a reference** from block `t` and column `c`. -/
noncomputable def Ref.resolve (n T t c : ℕ) : Ref k State → ℕ
  | .fls => n
  | .tru => n + 1
  | .inp => if 1 ≤ c ∧ c ≤ n then c - 1 else n
  | .node p l cs g => if g.test n T c then wire n T (if p then t - 1 else t) l (cs.apply T c) else n

/-- The arguments of a gate with operation `op`, from its two candidate wires. -/
def argsOf (op : Op) (a b : ℕ) : List ℕ :=
  match op with
  | .const _ => []
  | .not => [a]
  | .and => [a, b]
  | .or => [a, b]

/-! ### Decoding positions -/

/-- The cell symbol with a number. -/
def symOf (m : ℕ) : Option Bool := if m = 0 then none else if m = 1 then some false else some true

/-- The scanned quantity with a number. -/
def ScanQ.ofIdx (m : ℕ) : ScanQ k :=
  if m < 3 then .inRead (symOf m)
  else if h : (m - 3) / 3 < k then .read ⟨(m - 3) / 3, h⟩ (symOf ((m - 3) % 3)) else .inRead none

/-- The gate of the scan at a position within a column. -/
def ScanLoc.ofIdx (m : ℕ) : ScanLoc k :=
  if h : m < k then .nh ⟨m, h⟩
  else if m = k then .nx
  else if (m - (k + 1)) % 2 = 0 then .term (ScanQ.ofIdx ((m - (k + 1)) / 2))
  else .acc (ScanQ.ofIdx ((m - (k + 1)) / 2))

/-- The global gate at a position. -/
noncomputable def GlobLoc.ofIdx (m : ℕ) : GlobLoc k State :=
  if h : m < numSit k State * (k + 1) then
    .sit ⟨m / (k + 1), Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at h)⟩
      ⟨m % (k + 1), Nat.mod_lt _ (Nat.succ_pos k)⟩
  else if h' : (m - numSit k State * (k + 1)) / (numSit k State + 1) <
      Fintype.card (Attr k State) then
    .attr ((Fintype.equivFin (Attr k State)).symm
        ⟨(m - numSit k State * (k + 1)) / (numSit k State + 1), h'⟩)
      ⟨(m - numSit k State * (k + 1)) % (numSit k State + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  else .attr (.inMove 0) 0

/-- The global feature with a number. -/
noncomputable def GFeat.ofIdx (m : ℕ) : GFeat State :=
  if h : m < Fintype.card (Option State) then
    .state ((Fintype.equivFin (Option State)).symm ⟨m, h⟩)
  else .out (OutView.ofIndex (m - Fintype.card (Option State)))

/-- The column feature with a number. -/
def ColFeat.ofIdx (m : ℕ) : ColFeat k :=
  if m = 0 then .inPos
  else if h : m - 1 < k then .head ⟨m - 1, h⟩
  else if h' : (m - 1 - k) / 3 < k then .cell ⟨(m - 1 - k) / 3, h'⟩ (symOf ((m - 1 - k) % 3))
  else .inPos

/-- The kind of the gate at a position within the gates of a feature. -/
def gadgetB (m : ℕ) : Bool := decide (8 ≤ m % 16)

/-- The term of the gate at a position within the gates of a feature. -/
def gadgetJ (m : ℕ) : Fin 8 := ⟨m % 8, Nat.mod_lt _ (by norm_num)⟩

/-! ### Decoding inverts the layout -/

private theorem symOf_symIdx (s : Option Bool) : symOf (symIdx s) = s := by
  rcases s with _ | _ | _ <;> rfl

private theorem symIdx_lt (s : Option Bool) : symIdx s < 3 := by
  rcases s with _ | _ | _ <;> simp [symIdx]

/-- Decoding the index of a scanned quantity recovers the quantity. -/
theorem ScanQ.ofIdx_idx (q : ScanQ k) : ScanQ.ofIdx q.idx = q := by
  rcases q with s | ⟨i, s⟩
  · simp [ScanQ.idx, ScanQ.ofIdx, symIdx_lt, symOf_symIdx]
  · have hs := symIdx_lt s
    have h₁ : (3 + 3 * (i : ℕ) + symIdx s - 3) / 3 = i := by omega
    have h₂ : (3 + 3 * (i : ℕ) + symIdx s - 3) % 3 = symIdx s := by omega
    simp only [ScanQ.idx, ScanQ.ofIdx, show ¬3 + 3 * (i : ℕ) + symIdx s < 3 by omega,
      ↓reduceIte, h₁, i.isLt, ↓reduceDIte, h₂, symOf_symIdx]

/-- The index of a scanned quantity is strictly less than `3 + 3 * k`. -/
theorem ScanQ.idx_lt (q : ScanQ k) : q.idx < 3 + 3 * k := by
  rcases q with s | ⟨i, s⟩ <;> simp only [ScanQ.idx] <;> have := symIdx_lt s
  · omega
  · have := i.isLt; omega

/-- Decoding the index of a scan position recovers the position. -/
theorem ScanLoc.ofIdx_idx (l : ScanLoc k) : ScanLoc.ofIdx l.idx = l := by
  rcases l with i | _ | q | q
  · simp [ScanLoc.idx, ScanLoc.ofIdx]
  · simp [ScanLoc.idx, ScanLoc.ofIdx]
  · simp only [ScanLoc.idx, ScanLoc.ofIdx, show ¬k + 1 + 2 * q.idx < k by omega,
      show k + 1 + 2 * q.idx ≠ k by omega, ↓reduceDIte, ↓reduceIte,
      show (k + 1 + 2 * q.idx - (k + 1)) % 2 = 0 by omega,
      show (k + 1 + 2 * q.idx - (k + 1)) / 2 = q.idx by omega, ScanQ.ofIdx_idx]
  · simp only [ScanLoc.idx, ScanLoc.ofIdx, show ¬k + 2 + 2 * q.idx < k by omega,
      show k + 2 + 2 * q.idx ≠ k by omega, ↓reduceDIte, ↓reduceIte,
      show (k + 2 + 2 * q.idx - (k + 1)) % 2 = 1 by omega,
      show (k + 2 + 2 * q.idx - (k + 1)) / 2 = q.idx by omega, ScanQ.ofIdx_idx]
    rfl

/-- The index of a scan position is strictly less than `scanWidth k`. -/
theorem ScanLoc.idx_lt (l : ScanLoc k) : l.idx < scanWidth k := by
  rcases l with i | _ | q | q <;> simp only [ScanLoc.idx, scanWidth]
  · have := i.isLt; omega
  · omega
  · have := q.idx_lt; omega
  · have := q.idx_lt; omega

private theorem attrIdx_lt (v : Attr k State) : attrIdx v < Fintype.card (Attr k State) :=
  (Fintype.equivFin (Attr k State) v).isLt

/-- The index of a global gate position is strictly less than `globWidth k State`. -/
theorem GlobLoc.idx_lt (l : GlobLoc k State) : l.idx < globWidth k State := by
  rcases l with ⟨j, i⟩ | ⟨v, j⟩ <;> simp only [GlobLoc.idx, globWidth]
  · have := j.isLt
    have := i.isLt
    have : (j : ℕ) * (k + 1) + i < (j + 1) * (k + 1) := by rw [Nat.succ_mul]; omega
    have : ((j : ℕ) + 1) * (k + 1) ≤ numSit k State * (k + 1) := Nat.mul_le_mul_right _ ‹_›
    omega
  · have h₁ := j.isLt
    have h₂ := attrIdx_lt v
    have : attrIdx v * (numSit k State + 1) + j < (attrIdx v + 1) * (numSit k State + 1) := by
      rw [Nat.succ_mul]; omega
    have : (attrIdx v + 1) * (numSit k State + 1) ≤
        Fintype.card (Attr k State) * (numSit k State + 1) := Nat.mul_le_mul_right _ h₂
    omega

/-- Decoding the index of a global gate position recovers the position. -/
theorem GlobLoc.ofIdx_idx (l : GlobLoc k State) : GlobLoc.ofIdx l.idx = l := by
  rcases l with ⟨j, i⟩ | ⟨v, j⟩
  · have hlt : (j : ℕ) * (k + 1) + i < numSit k State * (k + 1) := by
      have := (GlobLoc.sit (State := State) j i).idx_lt
      have : (j : ℕ) * (k + 1) + i < (j + 1) * (k + 1) := by rw [Nat.succ_mul]; omega
      have : ((j : ℕ) + 1) * (k + 1) ≤ numSit k State * (k + 1) :=
        Nat.mul_le_mul_right _ j.isLt
      omega
    simp only [GlobLoc.idx, GlobLoc.ofIdx, hlt, ↓reduceDIte, GlobLoc.sit.injEq]
    constructor <;> ext
    · simp [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos k), Nat.div_eq_of_lt i.isLt]
    · simp [Nat.add_comm, Nat.mod_eq_of_lt i.isLt]
  · have hm : ¬ numSit k State * (k + 1) + attrIdx v * (numSit k State + 1) + j <
        numSit k State * (k + 1) := by omega
    have h₁ : (numSit k State * (k + 1) + attrIdx v * (numSit k State + 1) + j -
        numSit k State * (k + 1)) / (numSit k State + 1) = attrIdx v := by
      rw [show numSit k State * (k + 1) + attrIdx v * (numSit k State + 1) + j -
        numSit k State * (k + 1) = j + attrIdx v * (numSit k State + 1) by omega,
        Nat.add_mul_div_right _ _ (Nat.succ_pos _), Nat.div_eq_of_lt j.isLt, Nat.zero_add]
    have h₂ : (numSit k State * (k + 1) + attrIdx v * (numSit k State + 1) + j -
        numSit k State * (k + 1)) % (numSit k State + 1) = j := by
      rw [show numSit k State * (k + 1) + attrIdx v * (numSit k State + 1) + j -
        numSit k State * (k + 1) = j + attrIdx v * (numSit k State + 1) by omega,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
    simp only [GlobLoc.idx, GlobLoc.ofIdx, hm, ↓reduceDIte, h₁, attrIdx_lt v, h₂]
    congr
    exact (Fintype.equivFin (Attr k State)).symm_apply_apply v

/-- The index of a global feature is strictly less than `Fintype.card (Option State) + 4`. -/
theorem GFeat.idx_lt (f : GFeat State) : f.idx < Fintype.card (Option State) + 4 := by
  rcases f with q | o
  · have := (Fintype.equivFin (Option State) q).isLt
    simp only [GFeat.idx]
    omega
  · have := o.index_lt
    simp only [GFeat.idx]
    omega

/-- Decoding the index of a global feature recovers the feature. -/
theorem GFeat.ofIdx_idx (f : GFeat State) : GFeat.ofIdx f.idx = f := by
  rcases f with q | o
  · simp only [GFeat.idx, GFeat.ofIdx, Fin.is_lt, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply]
  · rw [GFeat.ofIdx]
    split_ifs with h
    · exact absurd h (by simp only [GFeat.idx]; omega)
    · simp [GFeat.idx]

/-- The index of a column feature is strictly less than `1 + 4 * k`. -/
theorem ColFeat.idx_lt (f : ColFeat k) : f.idx < 1 + 4 * k := by
  rcases f with _ | i | ⟨i, s⟩ <;> simp only [ColFeat.idx]
  · omega
  · have := i.isLt; omega
  · have := i.isLt; have := symIdx_lt s; omega

/-- Decoding the index of a column feature recovers the feature. -/
theorem ColFeat.ofIdx_idx (f : ColFeat k) : ColFeat.ofIdx f.idx = f := by
  rcases f with _ | i | ⟨i, s⟩
  · rfl
  · simp [ColFeat.idx, ColFeat.ofIdx]
  · have hs := symIdx_lt s
    have h₁ : (1 + k + 3 * (i : ℕ) + symIdx s - 1 - k) / 3 = i := by omega
    have h₂ : (1 + k + 3 * (i : ℕ) + symIdx s - 1 - k) % 3 = symIdx s := by omega
    simp only [ColFeat.idx, ColFeat.ofIdx, show 1 + k + 3 * (i : ℕ) + symIdx s ≠ 0 by omega,
      show ¬1 + k + 3 * (i : ℕ) + symIdx s - 1 < k by omega, ↓reduceIte, ↓reduceDIte, h₁,
      i.isLt, h₂, symOf_symIdx]

/-- The gadget index for feature `fi` is strictly less than `16 * (fi + 1)`. -/
theorem gadgetIdx_lt (fi : ℕ) (b : Bool) (j : Fin 8) :
    gadgetIdx fi b j < 16 * (fi + 1) := by
  have := j.isLt
  cases b <;>
    simp only [gadgetIdx, Bool.toNat_false, Bool.toNat_true, mul_zero, mul_one, add_zero,
      gt_iff_lt] <;> omega

/-- Dividing `gadgetIdx fi b j` by `16` recovers the feature index `fi`. -/
theorem gadgetIdx_div (fi : ℕ) (b : Bool) (j : Fin 8) : gadgetIdx fi b j / 16 = fi := by
  have := j.isLt
  cases b <;>
    simp only [gadgetIdx, Bool.toNat_false, Bool.toNat_true, mul_zero, mul_one, add_zero] <;> omega

/-- Decoding the gate kind from `gadgetIdx fi b j` recovers `b`. -/
theorem gadgetB_gadgetIdx (fi : ℕ) (b : Bool) (j : Fin 8) :
    gadgetB (gadgetIdx fi b j) = b := by
  have := j.isLt
  cases b <;>
    simp only [gadgetB, gadgetIdx, Bool.toNat_false, Bool.toNat_true, mul_zero, mul_one, add_zero,
      Nat.mul_add_mod_self_left, decide_eq_false_iff_not, decide_eq_true_eq, not_le, ge_iff_le,
      gt_iff_lt] <;> omega

/-- Decoding the term index from `gadgetIdx fi b j` recovers `j`. -/
theorem gadgetJ_gadgetIdx (fi : ℕ) (b : Bool) (j : Fin 8) :
    gadgetJ (gadgetIdx fi b j) = j := by
  have := j.isLt
  ext
  cases b <;>
    simp only [gadgetJ, gadgetIdx, Bool.toNat_false, Bool.toNat_true, mul_zero, mul_one,
      add_zero] <;> omega

/-! ### Block bounds and wire division -/

variable {T : ℕ}

/-- The column `c` is admissible for the position `l`: a column of the window for a gate of the
scan or a column feature, and `0` for a global gate. -/
def Loc.ColOK (T c : ℕ) : Loc k State → Prop
  | .scan _ => c < numCols T
  | .col _ _ _ => c < numCols T
  | .glob _ => c = 0
  | .gf _ _ _ => c = 0

private theorem mul_add_lt_mul {c w W i : ℕ} (hc : c < W) (hi : i < w) : c * w + i < W * w :=
  calc c * w + i < (c + 1) * w := by rw [Nat.succ_mul]; omega
    _ ≤ W * w := Nat.mul_le_mul_right _ hc

/-- Any scan gate offset in a valid column is strictly less than `globStart k T`. -/
theorem scan_offset_lt_globStart {c : ℕ} (hc : c < numCols T) (l : ScanLoc k) :
    c * scanWidth k + l.idx < globStart k T :=
  mul_add_lt_mul hc l.idx_lt

/-- Any global-feature gadget offset is strictly less than `colStart k State T`. -/
theorem gfStart_add_gadgetIdx_lt (f : GFeat State) (b : Bool) (j : Fin 8) :
    gfStart k State T + gadgetIdx f.idx b j < colStart k State T := by
  have h₁ := gadgetIdx_lt f.idx b j
  have h₂ := f.idx_lt
  simp only [colStart, gfWidth]
  omega

private theorem colStart_add_lt {c : ℕ} (hc : c < numCols T) (f : ColFeat k)
    (b : Bool) (j : Fin 8) :
    colStart k State T + c * colWidth k + gadgetIdx f.idx b j < blockSize k State T := by
  have h₁ := gadgetIdx_lt f.idx b j
  have h₂ := f.idx_lt
  have : gadgetIdx f.idx b j < colWidth k := by simp only [colWidth]; omega
  have := mul_add_lt_mul hc this
  simp only [blockSize]
  omega

/-- A position lies within its block. -/
theorem Loc.offset_lt {l : Loc k State} {c : ℕ} (hl : l.ColOK T c) :
    l.offset T c < blockSize k State T := by
  have hgs : globStart k T ≤ gfStart k State T := Nat.le_add_right _ _
  have hgc : gfStart k State T ≤ colStart k State T := Nat.le_add_right _ _
  have hcb : colStart k State T ≤ blockSize k State T := Nat.le_add_right _ _
  rcases l with l | l | ⟨f, b, j⟩ | ⟨f, b, j⟩ <;> simp only [Loc.offset] <;>
    simp only [Loc.ColOK] at hl
  · have := mul_add_lt_mul hl l.idx_lt
    simp only [globStart] at hgs
    omega
  · have := l.idx_lt
    simp only [gfStart] at hgc
    omega
  · have := gfStart_add_gadgetIdx_lt (k := k) (T := T) f b j
    omega
  · exact colStart_add_lt hl f b j

/-- Every position lies within its block, for a column of the window. -/
theorem Loc.offset_lt_of_lt {l : Loc k State} {c : ℕ} (hc : c < numCols T) :
    l.offset T c < blockSize k State T := by
  rcases l with l | l | ⟨f, b, j⟩ | ⟨f, b, j⟩
  · exact Loc.offset_lt (l := .scan l) hc
  · exact Loc.offset_lt (l := .glob l) (c := 0) rfl
  · exact Loc.offset_lt (l := .gf f b j) (c := 0) rfl
  · exact Loc.offset_lt (l := .col f b j) hc

/-- Any admissible column `c` for a position `l` satisfies `c < numCols T`. -/
theorem Loc.ColOK.lt {l : Loc k State} {c : ℕ} (hl : l.ColOK T c) : c < numCols T := by
  rcases l with l | l | ⟨f, b, j⟩ | ⟨f, b, j⟩ <;> simp only [Loc.ColOK] at hl <;>
    first | exact hl | (subst hl; simp [numCols])

/-- The scan region has positive width, including for a machine with no work tapes. -/
theorem scanWidth_pos : 0 < scanWidth k := by simp only [scanWidth]; omega

/-- Subtracting the input offset gives the index of a tableau gate. -/
theorem wire_sub (n T t : ℕ) (l : Loc k State) (c : ℕ) :
    wire n T t l c - n = 2 + t * blockSize k State T + l.offset T c := by
  simp only [wire]
  omega

/-- Dividing and reducing `wire n T t l c - n - 2` modulo `blockSize` recovers the block `t` and
intra-block offset `l.offset T c`. -/
theorem div_mod_wire {n T t : ℕ} {l : Loc k State} {c : ℕ} (hl : l.ColOK T c) :
    (wire n T t l c - n - 2) / blockSize k State T = t ∧
      (wire n T t l c - n - 2) % blockSize k State T = l.offset T c := by
  have h := Loc.offset_lt hl
  rw [wire_sub, show 2 + t * blockSize k State T + l.offset T c - 2 =
    l.offset T c + t * blockSize k State T by omega]
  exact ⟨by rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h, Nat.zero_add],
    by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]⟩

/-! ### Every gate sits at a position -/

private theorem symIdx_symOf {m : ℕ} (hm : m < 3) : symIdx (symOf m) = m := by
  rcases m with _ | _ | _ | m
  · rfl
  · rfl
  · rfl
  · omega

/-- Encoding `ScanQ.ofIdx m` for `m < 3 + 3 * k` recovers `m`. -/
theorem ScanQ.idx_ofIdx {m : ℕ} (hm : m < 3 + 3 * k) :
    (ScanQ.ofIdx m : ScanQ k).idx = m := by
  rw [ScanQ.ofIdx]
  split_ifs with h₁ h₂
  · exact symIdx_symOf h₁
  · simp only [ScanQ.idx]
    rw [symIdx_symOf (Nat.mod_lt _ (by norm_num))]
    omega
  · exact absurd (by omega) h₂

/-- Encoding `ScanLoc.ofIdx m` for `m < scanWidth k` recovers `m`. -/
theorem ScanLoc.idx_ofIdx {m : ℕ} (hm : m < scanWidth k) :
    (ScanLoc.ofIdx m : ScanLoc k).idx = m := by
  simp only [scanWidth] at hm
  rw [ScanLoc.ofIdx]
  split_ifs with h₁ h₂ h₃
  · rfl
  · simp only [ScanLoc.idx]; omega
  · simp only [ScanLoc.idx]
    rw [ScanQ.idx_ofIdx (by omega)]
    omega
  · simp only [ScanLoc.idx]
    rw [ScanQ.idx_ofIdx (by omega)]
    omega

/-- Encoding `GlobLoc.ofIdx m` for `m < globWidth k State` recovers `m`. -/
theorem GlobLoc.idx_ofIdx {m : ℕ} (hm : m < globWidth k State) :
    (GlobLoc.ofIdx m : GlobLoc k State).idx = m := by
  simp only [globWidth] at hm
  rw [GlobLoc.ofIdx]
  split_ifs with h₁ h₂
  · simp only [GlobLoc.idx]
    exact Nat.div_add_mod' m (k + 1)
  · simp only [GlobLoc.idx, attrIdx, Equiv.apply_symm_apply]
    have := Nat.div_add_mod' (m - numSit k State * (k + 1)) (numSit k State + 1)
    omega
  · have : m - numSit k State * (k + 1) <
        Fintype.card (Attr k State) * (numSit k State + 1) := by omega
    exact absurd ((Nat.div_lt_iff_lt_mul (by omega)).2 this) h₂

/-- Encoding `GFeat.ofIdx m` for `m < Fintype.card (Option State) + 4` recovers `m`. -/
theorem GFeat.idx_ofIdx {m : ℕ} (hm : m < Fintype.card (Option State) + 4) :
    (GFeat.ofIdx m : GFeat State).idx = m := by
  rw [GFeat.ofIdx]
  split_ifs with h
  · simp [GFeat.idx]
  · simp only [GFeat.idx]
    rw [OutView.index_ofIndex (by omega)]
    omega

/-- Encoding `ColFeat.ofIdx m` for `m < 1 + 4 * k` recovers `m`. -/
theorem ColFeat.idx_ofIdx {m : ℕ} (hm : m < 1 + 4 * k) :
    (ColFeat.ofIdx m : ColFeat k).idx = m := by
  rw [ColFeat.ofIdx]
  split_ifs with h₁ h₂ h₃
  · simp only [ColFeat.idx]; omega
  · simp only [ColFeat.idx]; omega
  · simp only [ColFeat.idx]
    rw [symIdx_symOf (Nat.mod_lt _ (by norm_num))]
    omega
  · exact absurd (by omega) h₃

private theorem gadgetIdx_decode (m : ℕ) : gadgetIdx (m / 16) (gadgetB m) (gadgetJ m) = m := by
  simp only [gadgetIdx, gadgetB, gadgetJ]
  by_cases h : 8 ≤ m % 16 <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false, mul_one, mul_zero,
    add_zero] <;> omega

/-- **Every gate after the constants sits at a position** of a block. -/
theorem exists_wire_eq {n T g : ℕ} (hg₂ : 2 ≤ g) (hg : g < numGates k State T) :
    ∃ t ≤ T, ∃ (l : Loc k State) (c : ℕ), l.ColOK T c ∧ wire n T t l c - n = g := by
  have hB : 0 < blockSize k State T := by
    have := Loc.offset_lt_of_lt (k := k) (State := State) (l := .scan .nx) (T := T) (c := 0)
      (by simp [numCols])
    omega
  have hdm := Nat.div_add_mod' (g - 2) (blockSize k State T)
  set t := (g - 2) / blockSize k State T
  set r := (g - 2) % blockSize k State T
  have hr : r < blockSize k State T := Nat.mod_lt _ hB
  have hgr : g = 2 + t * blockSize k State T + r := by omega
  have ht : t ≤ T := by
    have h₁ : g - 2 < (T + 1) * blockSize k State T := by
      simp only [numGates] at hg
      omega
    have : (g - 2) / blockSize k State T < T + 1 := (Nat.div_lt_iff_lt_mul hB).2 h₁
    omega
  refine ⟨t, ht, ?_⟩
  have hsw := scanWidth_pos (k := k)
  have hcw : 0 < colWidth k := by simp only [colWidth]; omega
  have hwire (l : Loc k State) (c : ℕ) (h : l.offset T c = r) : wire n T t l c - n = g := by
    rw [wire_sub, h, hgr]
  by_cases h₁ : r < globStart k T
  · refine ⟨.scan (ScanLoc.ofIdx (r % scanWidth k)), r / scanWidth k, ?_, hwire _ _ ?_⟩
    · simp only [Loc.ColOK, globStart] at h₁ ⊢
      rwa [Nat.div_lt_iff_lt_mul hsw]
    · simp only [Loc.offset]
      rw [ScanLoc.idx_ofIdx (Nat.mod_lt _ hsw), Nat.mul_comm]
      exact Nat.div_add_mod r _
  by_cases h₂ : r < gfStart k State T
  · refine ⟨.glob (GlobLoc.ofIdx (r - globStart k T)), 0, rfl, hwire _ _ ?_⟩
    simp only [Loc.offset]
    rw [GlobLoc.idx_ofIdx (by simp only [gfStart] at h₂; omega)]
    omega
  by_cases h₃ : r < colStart k State T
  · set m := r - gfStart k State T
    refine ⟨.gf (GFeat.ofIdx (m / 16)) (gadgetB m) (gadgetJ m), 0, rfl, hwire _ _ ?_⟩
    simp only [Loc.offset]
    rw [GFeat.idx_ofIdx (by simp only [colStart, gfWidth] at h₃; omega), gadgetIdx_decode]
    omega
  · set m := r - colStart k State T
    have hm : m < numCols T * colWidth k := by simp only [blockSize] at hr; omega
    refine ⟨.col (ColFeat.ofIdx (m % colWidth k / 16)) (gadgetB (m % colWidth k))
      (gadgetJ (m % colWidth k)), m / colWidth k, ?_, hwire _ _ ?_⟩
    · simp only [Loc.ColOK]
      rwa [Nat.div_lt_iff_lt_mul hcw]
    · simp only [Loc.offset]
      have hmod := Nat.mod_lt m hcw
      rw [ColFeat.idx_ofIdx (by simp only [colWidth] at hmod ⊢; omega), gadgetIdx_decode]
      have := Nat.div_add_mod' m (colWidth k)
      omega

end Cslib.Circuits.Boolean.Tableau
