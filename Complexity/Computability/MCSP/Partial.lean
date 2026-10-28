/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.BinaryCost
public import Complexity.Computability.MCSP.Basic
public import Complexity.Computability.MCSP.Succinct

/-!
# The Partial Minimum Circuit Size Problem (`MCSP*`)

The *Partial Minimum Circuit Size Problem* (`MCSP*` or `PartialMCSP`) asks, given the truth table
of a partial Boolean function $f^* : \{0, 1\}^n \to \{0, 1, *\}$ on `arity = n` inputs and a size
threshold `s`, whether there exists a total Boolean function $f : \{0, 1\}^n \to \{0, 1\}$ that
extends $f^*$ (agreeing with $f^*$ on every input where $f^*(x) \ne *$) and has a circuit of size
at most `s` [Ilango2020FOCS, Section II.B; ECCC TR20-183, Section 2.2; Hirahara2022, ECCC TR22-119,
Definition 8.4, p. 30].

In `PartialMCSP.Instance`, the truth table has $2^n$ entries in `Option Bool`, where `some b`
requires the circuit to output `b` and `none` represents the "don't care" symbol `*` (also written
`?` in [Hirahara2022, ECCC TR22-119, Definition 8.4]).

`Cslib.PartialMCSP` uses the standard De Morgan all-gates size measure `Circuit.size`
(`complexityOn interpretation x.definedInputs (single x.completion)`), matching `Cslib.MCSP` and
`Cslib.SuccinctMCSP`. We also define `Cslib.PartialMCSP.BinaryGate` using
the AND/OR-only gate count `c.program.cost binaryCost` from [Ilango2020FOCS, Section II.B and
Section III.B, p. 427; ECCC TR20-183, Section 2.2] (where NOT and constant gates are free), and
prove the threshold-$n-1$ bridge theorems relating the two measures using the binary-cost support
bounds in `Complexity.Computability.Circuit.Boolean.BinaryCost`:
* Every yes-instance of `PartialMCSP` is a yes-instance of `PartialMCSP.BinaryGate`
  (`PartialMCSP.mem_binaryGate_of_mem`).
* When all `n` input coordinates are essential for the partial function, no circuit with fewer than
  `n - 1` binary gates can agree with it (`PartialMCSP.not_mem_binaryGate_of_threshold_lt`), and at
  threshold `n - 1` any all-gates circuit agreeing with it must have size `n - 1`, binary cost
  `n - 1`, and consist solely of binary AND/OR gates
  (`PartialMCSP.isBinary_of_mem_of_threshold_le`).

String encodings of `PartialMCSP.Instance`, membership in `NP`, and the polynomial-time many-one
reduction from `MCSP` to `PartialMCSP` are in `Complexity.Computability.MCSP.PartialNP`.

## Main definitions

* `Cslib.PartialMCSP.Instance`: an instance of partial-function MCSP (`arity`, `table` of length
  $2^{\text{arity}}$ over `Option Bool`, and `threshold`).
* `Cslib.PartialMCSP.Instance.AgreesWith`: a total Boolean function extends the partial truth table.
* `Cslib.PartialMCSP`: yes-instances under the all-gates De Morgan circuit size measure.
* `Cslib.PartialMCSP.BinaryGate`: yes-instances under Ilango's AND/OR-only gate measure
  (`binaryCost`).
* `Cslib.PartialMCSP.Instance.ofTotal`, `Cslib.PartialMCSP.Instance.toSuccinct`,
  `Cslib.PartialMCSP.Instance.restrictTable`: embeddings into `PartialMCSP` from `MCSP`, from
  `PartialMCSP` into `SuccinctMCSP`, and by restricting a total truth table to a subset of inputs.

## Main results

* `Cslib.PartialMCSP.mem_iff_exists_circuit`, `Cslib.PartialMCSP.mem_iff_exists_total_extension`:
  characterizations of `PartialMCSP` via circuits and via total function extensions.
* `Cslib.PartialMCSP.mem_binaryGate_of_mem`,
  `Cslib.PartialMCSP.not_mem_binaryGate_of_threshold_lt`,
  `Cslib.PartialMCSP.isBinary_of_mem_of_threshold_le`,
  `Cslib.PartialMCSP.mem_iff_mem_binaryGate_of_all_isBinary`: bridge theorems between `PartialMCSP`
  and `PartialMCSP.BinaryGate`.
* `Cslib.PartialMCSP.ofTotal_mem_iff`, `Cslib.PartialMCSP.toSuccinct_mem_iff`,
  `Cslib.PartialMCSP.restrictTable_mem_iff`: exact compatibility with `MCSP` and `SuccinctMCSP`.

## References

* [R. Ilango, *Constant Depth Formula and Partial Function Versions of MCSP are
  Hard*][Ilango2020FOCS]
* [S. Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*][Hirahara2022]
-/

@[expose] public section

namespace Cslib

open Circuits Circuits.Boolean

namespace PartialMCSP

variable {n s t : ℕ}

/-- An instance of the Partial Minimum Circuit Size Problem (`MCSP*`): the truth table of a partial
Boolean function on `arity` inputs (`none` for `*` / don't-care, `some b` for a required output `b`)
and a circuit-size threshold [Ilango2020FOCS, Section II.B; ECCC TR20-183, Section 2.2;
Hirahara2022, ECCC TR22-119, Definition 8.4, p. 30]. -/
structure Instance where
  /-- The number of input variables of the partial Boolean function. -/
  arity : ℕ
  /-- The truth table of the partial Boolean function, indexed via `BitString.equivFin`. -/
  table : Fin (2 ^ arity) → Option Bool
  /-- The maximum number of gates allowed. -/
  threshold : ℕ

/-- The partial Boolean function represented by an instance. -/
def Instance.partialFunction (x : Instance) (y : BitString x.arity) : Option Bool :=
  x.table (BitString.equivFin x.arity y)

@[simp] theorem Instance.partialFunction_apply (x : Instance) (y : BitString x.arity) :
    x.partialFunction y = x.table (BitString.equivFin x.arity y) :=
  rfl

/-- The set of inputs on which the partial Boolean function is defined (not `*`). -/
def Instance.definedInputs (x : Instance) : Set (BitString x.arity) :=
  {y | (x.partialFunction y).isSome}

/-- The finite set of inputs on which the partial Boolean function is defined. -/
def Instance.definedFinset (x : Instance) : Finset (BitString x.arity) :=
  Finset.univ.filter fun y => (x.partialFunction y).isSome

@[simp] theorem Instance.coe_definedFinset (x : Instance) :
    (x.definedFinset : Set (BitString x.arity)) = x.definedInputs := by
  ext y
  simp only [Instance.definedFinset, Instance.definedInputs, Finset.mem_coe, Finset.mem_filter,
    Finset.mem_univ, true_and, Set.mem_ofPred_eq]

/-- The canonical total completion of `x.partialFunction` that maps undefined (`*`) entries to
`false`. On `x.definedInputs`, a circuit agrees with `x` if and only if it agrees with
`x.completion`. -/
def Instance.completion (x : Instance) (y : BitString x.arity) : Bool :=
  (x.partialFunction y).getD false

/-- A total Boolean function `f` agrees with (extends) the partial truth table of `x` when `f y = b`
for every input `y` where `x.partialFunction y = some b` [Ilango2020FOCS, Section II.B;
ECCC TR20-183, Section 2.2]. -/
def Instance.AgreesWith (x : Instance) (f : BooleanFunction x.arity) : Prop :=
  ∀ y b, x.partialFunction y = some b → f y = b

/-- Agreement stated directly in terms of the table indices `Fin (2 ^ x.arity)`. -/
theorem Instance.agreesWith_iff_table {x : Instance} {f : BooleanFunction x.arity} :
    x.AgreesWith f ↔
      ∀ i b, x.table i = some b → f ((BitString.equivFin x.arity).symm i) = b := by
  constructor
  · intro h i b hi
    exact h ((BitString.equivFin x.arity).symm i) b (by simp [Instance.partialFunction, hi])
  · intro h y b hy
    simpa using h (BitString.equivFin x.arity y) b hy

/-- A total function agrees with `x` iff it equals `x.completion` on `x.definedInputs`. -/
theorem Instance.agreesWith_iff_eqOn_completion {x : Instance} {f : BooleanFunction x.arity} :
    x.AgreesWith f ↔ Set.EqOn f x.completion x.definedInputs := by
  constructor
  · intro h y hy
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hy
    rw [Instance.completion, hb, Option.getD_some]
    exact h y b hb
  · intro h y b hb
    have hy : y ∈ x.definedInputs := by
      change (x.partialFunction y).isSome = true
      rw [hb]
      rfl
    have hcy := h hy
    rw [hcy, Instance.completion, hb, Option.getD_some]

/-- The canonical completion `x.completion` agrees with `x`. -/
theorem Instance.agreesWith_completion (x : Instance) : x.AgreesWith x.completion :=
  Instance.agreesWith_iff_eqOn_completion.mpr (Set.eqOn_refl _ _)

/-- A one-output circuit computes `single x.completion` on `x.definedInputs` if and only if its
output `0` agrees with `x`. -/
theorem Instance.computesOn_definedInputs_iff {x : Instance} {c : Circuit signature x.arity 1} :
    c.ComputesOn interpretation x.definedInputs (single x.completion) ↔
      x.AgreesWith fun y => c.eval interpretation y 0 := by
  rw [Circuit.computesOn_single_iff, Instance.agreesWith_iff_eqOn_completion]
  rfl

end PartialMCSP

open PartialMCSP

/-- **The Partial Minimum Circuit Size Problem (`MCSP*`)** [Ilango2020FOCS, Section II.B;
ECCC TR20-183, Section 2.2; Hirahara2022, ECCC TR22-119, Definition 8.4, p. 30]: the
partial-function instances that can be computed on their defined inputs by a De Morgan circuit with
at most `threshold` gates. -/
def PartialMCSP : Set PartialMCSP.Instance :=
  {x | complexityOn interpretation x.definedInputs (single x.completion) ≤ x.threshold}

namespace PartialMCSP

variable {n s t : ℕ}

/-- **The Partial Minimum Circuit Size Problem under the binary-gate cost measure**
[Ilango2020FOCS, Section II.B and Section III.B, p. 427; ECCC TR20-183, Section 2.2]: the
partial-function instances for which some De Morgan circuit using at most `threshold` binary
(AND/OR) gates agrees with the partial truth table. -/
def BinaryGate : Set Instance :=
  {x | ∃ c : Circuit signature x.arity 1,
    c.program.cost binaryCost ≤ x.threshold ∧
      x.AgreesWith fun y => c.eval interpretation y 0}

theorem mem_iff {x : Instance} :
    x ∈ PartialMCSP ↔
      complexityOn interpretation x.definedInputs (single x.completion) ≤ x.threshold :=
  Iff.rfl

/-- An instance is in `PartialMCSP` if and only if some De Morgan circuit of size at most
`x.threshold` agrees with `x.partialFunction` on all defined inputs. -/
theorem mem_iff_exists_circuit {x : Instance} :
    x ∈ PartialMCSP ↔ ∃ c : Circuit signature x.arity 1,
      c.size ≤ x.threshold ∧
        ∀ y b, x.partialFunction y = some b → c.eval interpretation y 0 = b := by
  rw [mem_iff, complexityOn_le_iff]
  exact exists_congr fun c => by
    rw [Instance.computesOn_definedInputs_iff, and_comm]
    rfl

/-- Circuit characterization of `PartialMCSP` indexed by `Fin (2 ^ x.arity)`. -/
theorem mem_iff_exists_circuit_table {x : Instance} :
    x ∈ PartialMCSP ↔ ∃ c : Circuit signature x.arity 1,
      c.size ≤ x.threshold ∧
        ∀ i b, x.table i = some b →
          c.eval interpretation ((BitString.equivFin x.arity).symm i) 0 = b := by
  rw [mem_iff_exists_circuit]
  exact exists_congr fun c => and_congr_right fun _ => Instance.agreesWith_iff_table

/-- **Total-extension characterization of `PartialMCSP`** [Ilango2020FOCS, Section II.B;
ECCC TR20-183, Section 2.2]: an instance is in `PartialMCSP` if and only if some total Boolean
function `f` agrees with `x` on all non-`*` entries and has circuit complexity at most
`x.threshold`. -/
theorem mem_iff_exists_total_extension {x : Instance} :
    x ∈ PartialMCSP ↔ ∃ f : BooleanFunction x.arity,
      x.AgreesWith f ∧ complexity interpretation (single f) ≤ x.threshold := by
  rw [mem_iff_exists_circuit]
  constructor
  · rintro ⟨c, hsize, hagree⟩
    refine ⟨fun y => c.eval interpretation y 0, hagree, ?_⟩
    exact complexity_le_iff.mpr ⟨c, Circuit.computes_single_iff.mpr fun _ => rfl, hsize⟩
  · rintro ⟨f, hagree, hcomp⟩
    obtain ⟨c, hc, hsize⟩ := complexity_le_iff.mp hcomp
    refine ⟨c, hsize, fun y b hy => ?_⟩
    rw [Circuit.computes_single_iff.mp hc y]
    exact hagree y b hy

/-- An instance is in `PartialMCSP` if and only if some function in
`computableFunctions x.arity x.threshold` agrees with `x`. -/
theorem mem_iff_exists_mem_computableFunctions {x : Instance} :
    x ∈ PartialMCSP ↔
      ∃ f ∈ computableFunctions x.arity x.threshold, x.AgreesWith f := by
  rw [mem_iff_exists_total_extension]
  exact exists_congr fun f => by
    rw [mem_computableFunctions_iff_complexity_le, and_comm]

/-- Raising the threshold preserves membership in `PartialMCSP`. -/
theorem mem_of_le {T : Fin (2 ^ n) → Option Bool} (h : ⟨n, T, s⟩ ∈ PartialMCSP) (hst : s ≤ t) :
    ⟨n, T, t⟩ ∈ PartialMCSP :=
  le_trans h hst

/-- Raising the threshold preserves membership in `PartialMCSP.BinaryGate`. -/
theorem mem_binaryGate_of_le {T : Fin (2 ^ n) → Option Bool}
    (h : ⟨n, T, s⟩ ∈ BinaryGate) (hst : s ≤ t) :
    ⟨n, T, t⟩ ∈ BinaryGate :=
  let ⟨c, hc, hagree⟩ := h
  ⟨c, hc.trans hst, hagree⟩

/-! ### Bridge between all-gates `PartialMCSP` and binary-gate `PartialMCSP.BinaryGate` -/

/-- Every yes-instance under the all-gates measure is a yes-instance under the binary-gate measure,
since `c.program.cost binaryCost ≤ c.size`. -/
theorem mem_binaryGate_of_mem {x : Instance} (h : x ∈ PartialMCSP) : x ∈ BinaryGate := by
  obtain ⟨c, hsize, hagree⟩ := mem_iff_exists_circuit.mp h
  exact ⟨c, (c.program.cost_binaryCost_le).trans hsize, hagree⟩

/-- Coordinate `i` is *essential* for the partial Boolean function of `x` when some pair of inputs
differing only at `i` are both defined in `x` and assigned opposite Boolean values. -/
def Instance.EssentialAt (x : Instance) (i : Fin x.arity) : Prop :=
  ∃ y₀ y₁ b₀ b₁, (∀ k, k ≠ i → y₀ k = y₁ k) ∧
    x.partialFunction y₀ = some b₀ ∧ x.partialFunction y₁ = some b₁ ∧ b₀ ≠ b₁

/-- If coordinate `i` is essential for `x`, then `i` is essential for every total Boolean function
that agrees with `x`. -/
theorem Instance.EssentialAt.essentialAt_of_agreesWith {x : Instance} {i : Fin x.arity}
    {f : BooleanFunction x.arity} (hi : x.EssentialAt i) (hf : x.AgreesWith f) :
    Circuits.EssentialAt f i := by
  obtain ⟨y₀, y₁, b₀, b₁, hdiff, hy₀, hy₁, hne⟩ := hi
  refine ⟨y₀, y₁, hdiff, ?_⟩
  rw [hf y₀ b₀ hy₀, hf y₁ b₁ hy₁]
  exact hne

/-- If coordinate `i` is essential for `x`, then `i` belongs to `c.inputSupport` for every circuit
`c` whose output agrees with `x`. -/
theorem Instance.EssentialAt.mem_inputSupport {x : Instance} {i : Fin x.arity}
    {c : Circuit signature x.arity 1} (hi : x.EssentialAt i)
    (hc : x.AgreesWith fun y => c.eval interpretation y 0) :
    i ∈ c.inputSupport := by
  have hess : Circuits.EssentialAt (c.eval interpretation) i := by
    obtain ⟨y₀, y₁, hdiff, hne⟩ := hi.essentialAt_of_agreesWith hc
    exact ⟨y₀, y₁, hdiff, fun h => hne (congrFun h 0)⟩
  exact hess.mem_support (c.dependsOn_eval interpretation)

/-- When all `x.arity` input coordinates are essential for `x`, every circuit agreeing with `x` has
full input support `c.inputSupport = Finset.univ`. -/
theorem Instance.inputSupport_eq_univ_of_forall_essentialAt {x : Instance}
    {c : Circuit signature x.arity 1} (hess : ∀ i : Fin x.arity, x.EssentialAt i)
    (hc : x.AgreesWith fun y => c.eval interpretation y 0) :
    c.inputSupport = Finset.univ :=
  Finset.eq_univ_iff_forall.mpr fun i => (hess i).mem_inputSupport hc

/-- When all `x.arity` input coordinates are essential for `x`, every circuit agreeing with `x`
uses at least `x.arity - 1` binary (AND/OR) gates (`x.arity ≤ 1 + c.program.cost binaryCost`). -/
theorem Instance.arity_le_one_add_cost_binaryCost {x : Instance}
    {c : Circuit signature x.arity 1} (hess : ∀ i : Fin x.arity, x.EssentialAt i)
    (hc : x.AgreesWith fun y => c.eval interpretation y 0) :
    x.arity ≤ 1 + c.program.cost binaryCost := by
  have hcard : c.inputSupport.card = x.arity := by
    rw [x.inputSupport_eq_univ_of_forall_essentialAt hess hc, Finset.card_univ, Fintype.card_fin]
  simpa [hcard] using c.card_inputSupport_le_cost_binaryCost

/-- When all `x.arity` coordinates are essential for `x` and `x.threshold + 1 < x.arity`
(i.e. `x.threshold < x.arity - 1`), `x` is a no-instance even under the binary-gate measure. -/
theorem not_mem_binaryGate_of_threshold_lt {x : Instance}
    (hess : ∀ i : Fin x.arity, x.EssentialAt i) (ht : x.threshold + 1 < x.arity) :
    x ∉ BinaryGate := by
  rintro ⟨c, hcost, hagree⟩
  have := x.arity_le_one_add_cost_binaryCost hess hagree
  omega

/-- When all `x.arity` coordinates are essential for `x` and `x.threshold + 1 < x.arity`, `x` is a
no-instance of `PartialMCSP`. -/
theorem not_mem_of_threshold_lt {x : Instance}
    (hess : ∀ i : Fin x.arity, x.EssentialAt i) (ht : x.threshold + 1 < x.arity) :
    x ∉ PartialMCSP :=
  fun h => not_mem_binaryGate_of_threshold_lt hess ht (mem_binaryGate_of_mem h)

/-- **Threshold-`n - 1` rigidity.** When all `x.arity` coordinates are
essential for `x` and `x.threshold + 1 ≤ x.arity`, any all-gates circuit `c` of size at most
`x.threshold` agreeing with `x` has `c.program.cost binaryCost = x.arity - 1`,
`c.size = x.arity - 1`, and consists exclusively of binary AND and OR gates (no NOT or constant
gates). -/
theorem isBinary_of_mem_of_threshold_le {x : Instance} {c : Circuit signature x.arity 1}
    (hess : ∀ i : Fin x.arity, x.EssentialAt i)
    (hc : x.AgreesWith fun y => c.eval interpretation y 0)
    (hsize : c.size ≤ x.threshold) (ht : x.threshold + 1 ≤ x.arity) :
    c.program.cost binaryCost = x.arity - 1 ∧ c.size = x.arity - 1 ∧
      ∀ k : Fin c.size, (c.program.lines k).op.IsBinary := by
  have hsupp : x.arity ≤ c.inputSupport.card := by
    rw [x.inputSupport_eq_univ_of_forall_essentialAt hess hc, Finset.card_univ, Fintype.card_fin]
  obtain ⟨hcost, hsz, hbin⟩ := c.cost_binaryCost_eq_size_of_size_le hsupp (by omega)
  exact ⟨hcost.trans hsz, hsz, hbin⟩

/-- Any circuit whose gates are all binary AND/OR gates has `c.size = c.program.cost binaryCost`,
so a binary-gate witness without NOT or constant gates is immediately an all-gates witness of the
same size. -/
theorem mem_of_exists_all_isBinary {x : Instance}
    (h : ∃ c : Circuit signature x.arity 1,
      (∀ k : Fin c.size, (c.program.lines k).op.IsBinary) ∧
      c.program.cost binaryCost ≤ x.threshold ∧
      x.AgreesWith fun y => c.eval interpretation y 0) :
    x ∈ PartialMCSP := by
  obtain ⟨c, hbin, hcost, hagree⟩ := h
  rw [mem_iff_exists_circuit]
  have hsz : c.program.cost binaryCost = c.size :=
    Program.cost_binaryCost_eq_iff_forall_isBinary.mpr hbin
  exact ⟨c, hsz ▸ hcost, hagree⟩

/-- When all `x.arity` coordinates are essential for `x`, `1 ≤ x.arity`, and
`x.threshold = x.arity - 1`, `x ∈ PartialMCSP` if and only if there is a circuit of size
`x.arity - 1` whose gates are all binary AND/OR gates that agrees with `x`. -/
theorem mem_iff_exists_all_isBinary_of_threshold_eq_arity_sub_one {x : Instance}
    (hess : ∀ i : Fin x.arity, x.EssentialAt i) (hpos : 1 ≤ x.arity)
    (ht : x.threshold = x.arity - 1) :
    x ∈ PartialMCSP ↔ ∃ c : Circuit signature x.arity 1,
      c.size = x.arity - 1 ∧
      (∀ k : Fin c.size, (c.program.lines k).op.IsBinary) ∧
      x.AgreesWith fun y => c.eval interpretation y 0 := by
  rw [mem_iff_exists_circuit]
  constructor
  · rintro ⟨c, hsize, hagree⟩
    obtain ⟨-, hsz, hbin⟩ := isBinary_of_mem_of_threshold_le hess hagree hsize (by omega)
    exact ⟨c, hsz, hbin, hagree⟩
  · rintro ⟨c, hsz, -, hagree⟩
    exact ⟨c, by omega, hagree⟩

/-- If every binary-gate circuit for `x` of cost at most `x.threshold` can be replaced by a
NOT-free, constant-free circuit of no greater binary cost (for example, in monotone reductions such
as [Ilango2020FOCS, Theorem I.3; ECCC TR20-183, Theorem 3] where yes-instances have read-once
monotone formulas of size `n - 1` and no-instances require at least `n` binary gates), then
`x ∈ PartialMCSP ↔ x ∈ BinaryGate`. -/
theorem mem_iff_mem_binaryGate_of_all_isBinary {x : Instance}
    (h : x ∈ BinaryGate → ∃ c : Circuit signature x.arity 1,
      (∀ k : Fin c.size, (c.program.lines k).op.IsBinary) ∧
      c.program.cost binaryCost ≤ x.threshold ∧
      x.AgreesWith fun y => c.eval interpretation y 0) :
    x ∈ PartialMCSP ↔ x ∈ BinaryGate :=
  ⟨mem_binaryGate_of_mem, fun hbg => mem_of_exists_all_isBinary (h hbg)⟩

/-! ### Embeddings from `MCSP` and into `SuccinctMCSP` -/

/-- View a total `MCSP.Instance` as a `PartialMCSP.Instance` with no `*` (`none`) entries. -/
def Instance.ofTotal (x : MCSP.Instance) : Instance where
  arity := x.arity
  table i := some (x.table i)
  threshold := x.threshold

@[simp] theorem Instance.partialFunction_ofTotal (x : MCSP.Instance) (y : BitString x.arity) :
    (Instance.ofTotal x).partialFunction y = some (x.function y) :=
  rfl

@[simp] theorem Instance.definedInputs_ofTotal (x : MCSP.Instance) :
    (Instance.ofTotal x).definedInputs = Set.univ := by
  ext y
  simp [Instance.definedInputs, Instance.ofTotal]

@[simp] theorem Instance.completion_ofTotal (x : MCSP.Instance) :
    (Instance.ofTotal x).completion = x.function :=
  rfl

/-- A total instance belongs to `PartialMCSP` if and only if it belongs to `MCSP`. -/
@[simp] theorem ofTotal_mem_iff (x : MCSP.Instance) :
    Instance.ofTotal x ∈ PartialMCSP ↔ x ∈ MCSP := by
  simp only [PartialMCSP, MCSP, Set.mem_ofPred_eq, Instance.definedInputs_ofTotal,
    Instance.completion_ofTotal]
  rfl

/-- View a `PartialMCSP.Instance` as a `SuccinctMCSP.Instance` whose samples are the defined entries
of its truth table. -/
def Instance.toSuccinct (x : Instance) : SuccinctMCSP.Instance :=
  SuccinctMCSP.Instance.ofFunction x.completion x.definedFinset x.threshold

/-- A partial truth table is in `PartialMCSP` if and only if its set of defined samples is in
`SuccinctMCSP`. -/
@[simp] theorem toSuccinct_mem_iff (x : Instance) :
    x.toSuccinct ∈ SuccinctMCSP ↔ x ∈ PartialMCSP := by
  rw [Instance.toSuccinct, SuccinctMCSP.ofFunction_mem_iff, Instance.coe_definedFinset, mem_iff]

/-- Restrict a total truth table `T : BitString (2 ^ n)` to a subset `S : Finset (BitString n)` of
defined inputs at threshold `s`, setting all entries outside `S` to `none` (`*`). -/
def Instance.restrictTable {n : ℕ} (T : BitString (2 ^ n)) (S : Finset (BitString n)) (s : ℕ) :
    Instance where
  arity := n
  table i := if (BitString.equivFin n).symm i ∈ S then some (T i) else none
  threshold := s

@[simp] theorem Instance.arity_restrictTable {n : ℕ} (T : BitString (2 ^ n))
    (S : Finset (BitString n)) (s : ℕ) :
    (Instance.restrictTable T S s).arity = n :=
  rfl

@[simp] theorem Instance.threshold_restrictTable {n : ℕ} (T : BitString (2 ^ n))
    (S : Finset (BitString n)) (s : ℕ) :
    (Instance.restrictTable T S s).threshold = s :=
  rfl

@[simp] theorem Instance.partialFunction_restrictTable {n : ℕ} (T : BitString (2 ^ n))
    (S : Finset (BitString n)) (s : ℕ) (y : BitString n) :
    (Instance.restrictTable T S s).partialFunction y =
      if y ∈ S then some (T (BitString.equivFin n y)) else none := by
  change (if (BitString.equivFin n).symm (BitString.equivFin n y) ∈ S then
    some (T (BitString.equivFin n y)) else none) = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem Instance.definedFinset_restrictTable {n : ℕ} (T : BitString (2 ^ n))
    (S : Finset (BitString n)) (s : ℕ) :
    (Instance.restrictTable T S s).definedFinset = S := by
  change Finset.univ.filter
    (fun z : BitString n => ((Instance.restrictTable T S s).partialFunction z).isSome) = S
  ext y
  simp

/-- Viewing `Instance.restrictTable T S s` as a `SuccinctMCSP.Instance` via `Instance.toSuccinct`
yields `SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s`. -/
@[simp] theorem Instance.toSuccinct_restrictTable {n : ℕ} (T : BitString (2 ^ n))
    (S : Finset (BitString n)) (s : ℕ) :
    (Instance.restrictTable T S s).toSuccinct =
      SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s := by
  unfold Instance.toSuccinct SuccinctMCSP.Instance.ofFunction
  simp only [Instance.arity_restrictTable, Instance.definedFinset_restrictTable,
    Instance.threshold_restrictTable]
  congr 1
  refine Finset.image_congr fun y hy => ?_
  have hyS : y ∈ S := Finset.mem_coe.mp hy
  simp [Instance.completion, hyS]

/-- The partial truth table `Instance.restrictTable T S s` is in `PartialMCSP` if and only if
`SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s` is in `SuccinctMCSP`. -/
@[simp] theorem restrictTable_mem_iff {n : ℕ} (T : BitString (2 ^ n))
    (S : Finset (BitString n)) (s : ℕ) :
    Instance.restrictTable T S s ∈ PartialMCSP ↔
      SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s ∈ SuccinctMCSP := by
  rw [← toSuccinct_mem_iff, Instance.toSuccinct_restrictTable]

end PartialMCSP

end Cslib
