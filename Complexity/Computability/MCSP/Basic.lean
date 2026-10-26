/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Complexity
public import Complexity.Computability.Circuit.Counting
public import Complexity.Computability.Complexity.Classes.Promise.Basic
public import Complexity.Computability.Languages.Slice
public import Complexity.Foundations.Data.BitString.Basic
public import Cslib.Computability.Circuit.Boolean.Complexity
public import Cslib.Computability.Circuit.Boolean.Counting
public import Mathlib.Computability.Language
public import Mathlib.Data.Set.Card

/-!
# The Minimum Circuit Size Problem

The *Minimum Circuit Size Problem* (MCSP) asks, given the truth table of a Boolean function `f`
on `n` inputs and a number `s`, whether `f` has a circuit with at most `s` gates
[KabanetsCai2000]. Its gap version `GapMCSP[s₁, s₂]` is the promise problem of telling, for each
`n`, the truth tables of functions with circuits of at most `s₁ n` gates from those of functions
that need more than `s₂ n` gates [OliveiraPichSanthanam2019, Definition 2.4].

The truth table of `f` lists its `2 ^ n` values in the order of `BitString.equivFin`. Circuits are
De Morgan circuits, and their size counts every AND, OR, NOT and constant gate, so the measure is
cslib's `complexity interpretation (single f)`; see `Cslib.Computability.Circuit.Boolean.Basic`.
Only the semantics of the problems is defined here. An encoding of the instances of MCSP as
strings, and the proof that MCSP is in `NP` for it, are in `Complexity.Computability.MCSP.NP`.

The yes-instances of MCSP on functions of `n` inputs at threshold `s` are the truth tables of
cslib's `computableFunctions n s`, so there are as many of them as such functions
(`MCSP.ncard_setOf_mem`).

## Main definitions

* `Cslib.MCSP.truthTable`: truth tables of Boolean functions.
* `Cslib.Circuits.Boolean.truthTableLanguage`: the truth tables of a property, as a language.
* `Cslib.MCSP.Instance`, `Cslib.MCSP`: the instances and the yes-instances of MCSP.
* `Cslib.GapMCSP`: `GapMCSP[s₁, s₂]` as a `PromiseProblem (List Bool)`, with sides
  `Cslib.GapMCSP.yesSet` and `Cslib.GapMCSP.noSet`.

## Main results

* `Cslib.Circuits.Boolean.ofFn_mem_truthTableLanguage`: membership of an `ofFn`-vector in
  `truthTableLanguage`.
* `Cslib.MCSP.mem_iff_exists_circuit`, `Cslib.MCSP.mem_iff_mem_computableFunctions`: the yes-
  instances of MCSP, as circuits and as computable functions.
* `Cslib.MCSP.ncard_setOf_mem`: the number of yes-instances of a given arity and threshold.
* `Cslib.GapMCSP.ofFn_mem_yesSet_iff_mem_MCSP`,
  `Cslib.GapMCSP.slice_yesSet_eq_true_iff`,
  `Cslib.GapMCSP.ofFn_mem_noSet_iff_notMem_MCSP`: characterization of truth tables of length `2^n`
  in the yes and no sets.
* `Cslib.GapMCSP.disjoint_yesSet_noSet`: the promise of `GapMCSP[s₁, s₂]` is consistent when
  `s₁ n ≤ s₂ n` for all `n`.

## References

* [V. Kabanets, J.-Y. Cai, *Circuit minimization problem*][KabanetsCai2000]
* [I. C. Oliveira, J. Pich, R. Santhanam, *Hardness magnification near state-of-the-art lower
  bounds*][OliveiraPichSanthanam2019]
-/

@[expose] public section

namespace Cslib

open Circuits Circuits.Boolean

namespace MCSP

variable {n : ℕ}

variable (n) in
/-- The truth table of a Boolean function on `n` inputs: its values on the `2 ^ n` inputs, in the
order of `BitString.equivFin`. -/
def truthTable : BooleanFunction n ≃ BitString (2 ^ n) where
  toFun f i := f ((BitString.equivFin n).symm i)
  invFun T x := T (BitString.equivFin n x)
  left_inv f := funext fun x => by simp
  right_inv T := funext fun i => by simp

@[simp] theorem truthTable_apply (f : BooleanFunction n) (i : Fin (2 ^ n)) :
    truthTable n f i = f ((BitString.equivFin n).symm i) :=
  rfl

@[simp] theorem truthTable_symm_apply (T : BitString (2 ^ n)) (x : BitString n) :
    (truthTable n).symm T x = T (BitString.equivFin n x) :=
  rfl

/-- An instance of the Minimum Circuit Size Problem: the truth table of a Boolean function on
`arity` inputs, and a size threshold. -/
structure Instance where
  /-- The number of inputs of the function. -/
  arity : ℕ
  /-- The truth table of the function. -/
  table : BitString (2 ^ arity)
  /-- The number of gates allowed. -/
  threshold : ℕ

/-- The Boolean function whose truth table an instance gives. -/
def Instance.function (x : Instance) : BooleanFunction x.arity :=
  (truthTable x.arity).symm x.table

end MCSP

open MCSP

/-- **The Minimum Circuit Size Problem** [KabanetsCai2000]: the instances whose function has a
De Morgan circuit with at most `threshold` gates. -/
def MCSP : Set MCSP.Instance :=
  {x | complexity interpretation (single x.function) ≤ x.threshold}

namespace MCSP

variable {n s t : ℕ}

theorem mem_iff {x : Instance} :
    x ∈ MCSP ↔ complexity interpretation (single x.function) ≤ x.threshold :=
  Iff.rfl

/-- The truth table of `f` with threshold `s` is a yes-instance exactly when `f` has complexity at
most `s`. -/
@[simp] theorem mk_truthTable_mem_iff {f : BooleanFunction n} :
    ⟨n, truthTable n f, s⟩ ∈ MCSP ↔ complexity interpretation (single f) ≤ s := by
  simp [mem_iff, Instance.function]

/-- The truth table of `f` with threshold `s` is a yes-instance exactly when `f` is computable
with at most `s` gates. -/
theorem mk_truthTable_mem_iff_mem {f : BooleanFunction n} :
    ⟨n, truthTable n f, s⟩ ∈ MCSP ↔ f ∈ computableFunctions n s := by
  rw [mk_truthTable_mem_iff, mem_computableFunctions_iff_complexity_le]

/-- An instance is a yes-instance exactly when some circuit with at most `threshold` gates
computes its function. -/
theorem mem_iff_exists_circuit {x : Instance} :
    x ∈ MCSP ↔ ∃ c : Circuit signature x.arity 1,
      c.Computes interpretation (single x.function) ∧ c.size ≤ x.threshold :=
  complexity_le_iff

/-- The yes-instances are the truth tables of the functions computable within the threshold. -/
theorem mem_iff_mem_computableFunctions {x : Instance} :
    x ∈ MCSP ↔ x.function ∈ computableFunctions x.arity x.threshold :=
  mem_computableFunctions_iff_complexity_le.symm

/-- Raising the threshold keeps a yes-instance a yes-instance. -/
theorem mem_of_le {T : BitString (2 ^ n)} (h : ⟨n, T, s⟩ ∈ MCSP) (hst : s ≤ t) :
    ⟨n, T, t⟩ ∈ MCSP :=
  le_trans h hst

/-- There are as many yes-instances of arity `n` and threshold `s` as functions on `n` inputs
computable with at most `s` gates. -/
theorem ncard_setOf_mem (n s : ℕ) :
    {T : BitString (2 ^ n) | ⟨n, T, s⟩ ∈ MCSP}.ncard = (computableFunctions n s).card := by
  have h : {T : BitString (2 ^ n) | ⟨n, T, s⟩ ∈ MCSP} =
      truthTable n '' (computableFunctions n s : Set (BooleanFunction n)) := by
    ext T
    obtain ⟨f, rfl⟩ := (truthTable n).surjective T
    simp only [Set.mem_ofPred_eq, mk_truthTable_mem_iff_mem, Set.mem_image, SetLike.mem_coe,
      EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
  rw [h, Set.ncard_image_of_injective _ (truthTable n).injective, Set.ncard_coe_finset]

end MCSP

namespace Circuits.Boolean

/-- The truth tables of a property, as a language [RazborovRudich1997]: a word of length `2 ^ n`
belongs to it when it is the truth table of a function in `C n`. Words whose length is not a power
of two do not belong to it. -/
def truthTableLanguage (C : ∀ n, Set (BooleanFunction n)) : Language Bool :=
  {w | ∃ n, ∃ h : w.length = 2 ^ n,
    (MCSP.truthTable n).symm (fun i => w[(i : ℕ)]'(i.isLt.trans_eq h.symm)) ∈ C n}

/-- A `2 ^ n`-bit string `T`, viewed as a list via `List.ofFn`, belongs to `truthTableLanguage C`
if and only if its corresponding Boolean function lies in `C n`. -/
theorem ofFn_mem_truthTableLanguage {C : ∀ n, Set (BooleanFunction n)} {n : ℕ}
    {T : BitString (2 ^ n)} :
    List.ofFn T ∈ truthTableLanguage C ↔ (MCSP.truthTable n).symm T ∈ C n := by
  constructor
  · rintro ⟨m, h, hm⟩
    obtain rfl : m = n :=
      Nat.pow_right_injective le_rfl (h.symm.trans (List.length_ofFn (f := T)))
    simpa only [List.getElem_ofFn] using hm
  · intro h
    exact ⟨n, List.length_ofFn, by simpa only [List.getElem_ofFn] using h⟩

end Circuits.Boolean

namespace GapMCSP

open MCSP Circuits.Boolean

variable {s₁ s₂ : ℕ → ℕ}

/-- The yes-instances of `GapMCSP[s₁, s₂]` across all lengths [OliveiraPichSanthanam2019,
Definition 2.4]: the truth tables of Boolean functions with circuit complexity at most
`s₁ n`. -/
def yesSet (s₁ : ℕ → ℕ) : Language Bool :=
  truthTableLanguage fun n => {f | complexity interpretation (single f) ≤ s₁ n}

/-- The no-instances of `GapMCSP[s₁, s₂]` across all lengths [OliveiraPichSanthanam2019,
Definition 2.4]: the truth tables of Boolean functions with circuit complexity greater than
`s₂ n`. -/
def noSet (s₂ : ℕ → ℕ) : Language Bool :=
  truthTableLanguage fun n => {f | s₂ n < complexity interpretation (single f)}

/-- A `2 ^ n`-bit string `T`, viewed as a list via `List.ofFn`, belongs to `yesSet s₁`
if and only if its circuit complexity is at most `s₁ n`. -/
@[simp] theorem ofFn_mem_yesSet_iff {n : ℕ} {T : BitString (2 ^ n)} :
    List.ofFn T ∈ yesSet s₁ ↔ complexity interpretation (single ((truthTable n).symm T)) ≤ s₁ n :=
  ofFn_mem_truthTableLanguage

/-- A `2 ^ n`-bit string `T`, viewed as a list via `List.ofFn`, belongs to `yesSet s₁`
if and only if `⟨n, T, s₁ n⟩ ∈ MCSP`. -/
theorem ofFn_mem_yesSet_iff_mem_MCSP {n : ℕ} {T : BitString (2 ^ n)} :
    List.ofFn T ∈ yesSet s₁ ↔ (⟨n, T, s₁ n⟩ : MCSP.Instance) ∈ MCSP :=
  ofFn_mem_yesSet_iff

/-- The `2 ^ n`-bit slice of `yesSet s₁` evaluates to `true` on `T` if and only if its circuit
complexity is at most `s₁ n`. -/
theorem slice_yesSet_eq_true_iff {n : ℕ} {T : BitString (2 ^ n)} :
    (yesSet s₁).slice (2 ^ n) T = true ↔
      complexity interpretation (single ((truthTable n).symm T)) ≤ s₁ n := by
  rw [Language.slice_eq_true_iff, ofFn_mem_yesSet_iff]

/-- A `2 ^ n`-bit string `T`, viewed as a list via `List.ofFn`, belongs to `noSet s₂`
if and only if its circuit complexity is strictly greater than `s₂ n`. -/
@[simp] theorem ofFn_mem_noSet_iff {n : ℕ} {T : BitString (2 ^ n)} :
    List.ofFn T ∈ noSet s₂ ↔ s₂ n < complexity interpretation (single ((truthTable n).symm T)) :=
  ofFn_mem_truthTableLanguage

/-- A `2 ^ n`-bit string `T`, viewed as a list via `List.ofFn`, belongs to `noSet s₂`
if and only if `⟨n, T, s₂ n⟩ ∉ MCSP`. -/
theorem ofFn_mem_noSet_iff_notMem_MCSP {n : ℕ} {T : BitString (2 ^ n)} :
    List.ofFn T ∈ noSet s₂ ↔ (⟨n, T, s₂ n⟩ : MCSP.Instance) ∉ MCSP := by
  rw [ofFn_mem_noSet_iff]
  exact not_le.symm

/-- When `s₁ n ≤ s₂ n` for all `n`, no truth table is both a yes-instance and a no-instance. -/
theorem disjoint_yesSet_noSet (h : ∀ n, s₁ n ≤ s₂ n) : Disjoint (yesSet s₁) (noSet s₂) := by
  refine Set.disjoint_left.mpr fun w hyes hno => ?_
  obtain ⟨n₁, hn₁, hf₁⟩ := hyes
  obtain ⟨n₂, hn₂, hf₂⟩ := hno
  obtain rfl : n₁ = n₂ :=
    Nat.pow_right_injective le_rfl (hn₁.symm.trans hn₂)
  have h_eq : (truthTable n₁).symm (fun i => w[(i : ℕ)]'(i.isLt.trans_eq hn₁.symm)) =
      (truthTable n₁).symm (fun i => w[(i : ℕ)]'(i.isLt.trans_eq hn₂.symm)) := rfl
  rw [h_eq] at hf₁
  exact (lt_irrefl _) ((hf₁.trans (h n₁)).trans_lt hf₂)

/-- Raising the yes-threshold adds yes-instances. -/
theorem yesSet_mono {s₁' : ℕ → ℕ} (h : ∀ n, s₁ n ≤ s₁' n) : yesSet s₁ ≤ yesSet s₁' :=
  fun _ ⟨n, hn, hf⟩ => ⟨n, hn, le_trans hf (h n)⟩

/-- Raising the no-threshold removes no-instances. -/
theorem noSet_anti {s₂' : ℕ → ℕ} (h : ∀ n, s₂ n ≤ s₂' n) : noSet s₂' ≤ noSet s₂ :=
  fun _ ⟨n, hn, hf⟩ => ⟨n, hn, lt_of_le_of_lt (h n) hf⟩

end GapMCSP

/-- **`GapMCSP[s₁, s₂]`** [OliveiraPichSanthanam2019, Definition 2.4]: the promise problem whose
yes-instances are truth tables of functions with circuits of at most `s₁ n` gates and whose
no-instances are truth tables of functions that need more than `s₂ n` gates, when `s₁ n ≤ s₂ n`
for all `n`. Following OPS19, the hypothesis `∀ n, s₁ n ≤ s₂ n` is bundled to guarantee
disjointness of the promise problem by construction. -/
def GapMCSP (s₁ s₂ : ℕ → ℕ) (h : ∀ n, s₁ n ≤ s₂ n) :
    Complexity.PromiseProblem (List Bool) where
  yes := GapMCSP.yesSet s₁
  no := GapMCSP.noSet s₂
  disjoint := GapMCSP.disjoint_yesSet_noSet h

namespace GapMCSP

variable {s₁ s₂ : ℕ → ℕ}
variable (h : ∀ n, s₁ n ≤ s₂ n)

@[simp] theorem yes_eq : (GapMCSP s₁ s₂ h).yes = yesSet s₁ := rfl

@[simp] theorem no_eq : (GapMCSP s₁ s₂ h).no = noSet s₂ := rfl

end GapMCSP

end Cslib
