/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.DataStructure.CellProbe.Randomized.StateTransition
import Complexity.Probability.PMF.Expect

/-!
# Oblivious-Sequence Cell-Probe Implementations and Zero-Error Yao Averaging

This file connects state-free oblivious-sequence specifications
(`Cslib.DataStructure.ObliviousSequenceSpec`) to randomized cell-probe schemes
(`Cslib.CellProbe.Randomized.Scheme`, [Miltersen1999]) and provides the `DataStructure`-level
averaging (coin-fixing) corollaries, the easy direction of Yao's principle [Yao1977], for
zero-error (Las Vegas) schemes against oblivious operation sequences:

1. **`ObliviousSequenceImpl`**: certifies that `P : Cslib.CellProbe.Randomized.Scheme S.Op S.Result
   cells w` satisfies `S.Contract ops ((P.runSeq ops).map Prod.fst)` and
   `P.expectedSeqProbes ops ≤ initPotential + (ops.map charge).sum` on every `S.ValidOpSeq ops`
   (covering both zero-error contracts via `D.toObliviousSequenceSpec s₀` and bounded-error Monte
   Carlo contracts via general `ObliviousSequenceSpec`), with cell padding `padCells` and contract
   weakening `weaken`.
2. **State-transition lift (`StateTransitionImpl.toObliviousSequenceImpl`)**: canonically embeds
   any `Randomized.StateTransitionImpl` (and any deterministic `CellProbe.StateTransitionImpl`)
   whose `charge` is bounded by `opCharge : D.Op → ℕ` into `ObliviousSequenceImpl`.
3. **Averaging (easy) direction of Yao's principle [Yao1977] for zero-error schemes on oblivious
   sequences**: wraps `Scheme.exists_det_indexedScheme_le_expectedSeqProbes` and
   `Scheme.exists_det_scheme_le_expectedSeqProbes` over `D.toObliviousSequenceSpec s₀` on
   deterministic specifications (`[D.HasStepFn f]`):
   * Parameterized over an explicit finite `opsAlphabet : Finset D.Op` and `horizon : ℕ`, with
     `correctSeqs` separated from `hardDist`, so infinite operation types such as
     `Dictionary.Op U` (carrying `v : ℕ`) work directly without `[Fintype D.Op]`; bounded-error
     Monte Carlo schemes and adaptive sequence adversaries are out of scope.
   * Fixing per-operation coins yields a step-indexed `Cslib.CellProbe.IndexedScheme` (the
     **time-aware relaxation** with a free step clock outside cell memory), so any deterministic
     cell-probe lower bound paired with `exists_det_indexedScheme_le_expectedSeqProbes` must hold
     against step-indexed `IndexedScheme`s.
   * In the **random initial memory / coin-free steps** specialization (`IsCoinFree`, where
     randomness lives only in `P.init` and operations observe it only by probing cells),
     `exists_det_scheme_le_expectedSeqProbes` produces a time-invariant `Cslib.CellProbe.Scheme`
     without `opsAlphabet` or `horizon`.

## Main definitions

* `Cslib.DataStructure.CellProbe.Randomized.ObliviousSequenceImpl`: certified randomized cell-probe
  implementation of `S : ObliviousSequenceSpec`.
* `Cslib.DataStructure.CellProbe.Randomized.ObliviousSequenceImpl.padCells`,
  `Cslib.DataStructure.CellProbe.Randomized.ObliviousSequenceImpl.weaken`: cell-space monotonicity
  and specification weakening on `ObliviousSequenceImpl`.
* `Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl.toObliviousSequenceImpl`,
  `Cslib.DataStructure.CellProbe.StateTransitionImpl.toObliviousSequenceImpl`: canonical embeddings
  into `ObliviousSequenceImpl` over `D.toObliviousSequenceSpec s₀`.

## Main results

* `Cslib.DataStructure.CellProbe.Randomized.exists_det_indexedScheme_le_expectedSeqProbes` and
`Cslib.DataStructure.CellProbe.Randomized.exists_det_indexedScheme_le_expectedSeqProbes_of_fintype`
  — averaging (easy) direction of Yao's principle [Yao1977] for zero-error schemes on
  `D.toObliviousSequenceSpec s₀`, producing a step-indexed `IndexedScheme` over an explicit finite
  `opsAlphabet` (or `[Fintype D.Op]`).
* `Cslib.DataStructure.CellProbe.Randomized.exists_det_scheme_le_expectedSeqProbes`: random initial
  memory / coin-free steps specialization producing a time-invariant `Cslib.CellProbe.Scheme`.
* Under `Cslib.DataStructure.CellProbe.Randomized`:
  `ObliviousSequenceImpl.exists_det_indexedScheme`,
  `ObliviousSequenceImpl.le_expected_charge_of_det_indexedScheme`,
  `StateTransitionImpl.exists_det_indexedScheme`,
  `StateTransitionImpl.exists_det_scheme`, and
  `StateTransitionImpl.le_expected_totalCost_of_det_indexedScheme` — end-to-end coin-fixing and
  lower-bound transfer corollaries for `ObliviousSequenceImpl` and `Randomized.StateTransitionImpl`
  (bounding the certified budget `initPotential + E[totalCost]`, not raw `E[P.expectedSeqProbes]`).

## References

* [A. C.-C. Yao, *Probabilistic Computations: Toward a Unified Measure of Complexity*][Yao1977]
* [P. B. Miltersen, *Cell Probe Complexity — a Survey*][Miltersen1999]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 17.3][CLRS2009]
-/

public section

namespace Cslib.DataStructure.CellProbe.Randomized

open Cslib.CellProbe Cslib.Probability
open scoped ENNReal

universe u v

/-! ### `ObliviousSequenceImpl`: randomized cell-probe implementation of `ObliviousSequenceSpec` -/

/-- Certified randomized cell-probe implementation of `S : ObliviousSequenceSpec` in `cells` cells
of `w`-bit words (`cells * w` bits total). -/
structure ObliviousSequenceImpl {cells w : ℕ}
    (S : ObliviousSequenceSpec.{u, 0})
    (P : Cslib.CellProbe.Randomized.Scheme S.Op S.Result cells w) where
  /-- Upper bound on initial potential (`0` when unamortized). -/
  initPotential : ℕ := 0
  /-- Per-operation expected probe charge. -/
  charge : S.Op → ℕ
  /-- Distributional transcript correctness across every admissible sequence `ops`. -/
  contract_runSeq : ∀ ⦃ops : List S.Op⦄, S.ValidOpSeq ops →
    S.Contract ops ((P.runSeq ops).map Prod.fst)
  /-- Expected total probe bound across every admissible sequence `ops`. -/
  expectedSeqProbes_le : ∀ ⦃ops : List S.Op⦄, S.ValidOpSeq ops →
    P.expectedSeqProbes ops ≤ (initPotential : ℝ≥0∞) + (((ops.map charge).sum : ℕ) : ℝ≥0∞)

namespace ObliviousSequenceImpl

variable {cells cells' w : ℕ} {S : ObliviousSequenceSpec.{u, 0}}
  {P : Cslib.CellProbe.Randomized.Scheme S.Op S.Result cells w}

/-- Lift an `ObliviousSequenceImpl` from `cells` cells to `cells'` cells (`cells ≤ cells'`) via
`Cslib.CellProbe.Randomized.Scheme.padCells`. -/
@[expose] def padCells (h : cells ≤ cells') (C : ObliviousSequenceImpl S P) :
    ObliviousSequenceImpl S (P.padCells h) where
  initPotential := C.initPotential
  charge := C.charge
  contract_runSeq {_} hv := by
    rw [Cslib.CellProbe.Randomized.Scheme.runSeq_padCells]
    exact C.contract_runSeq hv
  expectedSeqProbes_le {_} hv := by
    rw [Cslib.CellProbe.Randomized.Scheme.expectedSeqProbes_padCells]
    exact C.expectedSeqProbes_le hv

@[simp]
theorem padCells_initPotential (h : cells ≤ cells') (C : ObliviousSequenceImpl S P) :
    (C.padCells h).initPotential = C.initPotential :=
  rfl

@[simp]
theorem padCells_charge (h : cells ≤ cells') (C : ObliviousSequenceImpl S P) :
    (C.padCells h).charge = C.charge :=
  rfl

/-- Transport an `ObliviousSequenceImpl` along `ObliviousSequenceSpec.weaken`. -/
@[expose] def weaken (C : ObliviousSequenceImpl S P)
    {ValidOpSeq' : List S.Op → Prop}
    {Contract' : (ops : List S.Op) → PMF (List (Sigma S.Result)) → Prop}
    (hV : ∀ ops, ValidOpSeq' ops → S.ValidOpSeq ops)
    (hC : ∀ ops μ, S.ValidOpSeq ops → S.Contract ops μ → Contract' ops μ) :
    ObliviousSequenceImpl (S.weaken ValidOpSeq' Contract') P where
  initPotential := C.initPotential
  charge := C.charge
  contract_runSeq {_} hv := S.contract_weaken hV hC hv fun hvS => C.contract_runSeq hvS
  expectedSeqProbes_le {ops} hv := C.expectedSeqProbes_le (hV ops hv)

@[simp]
theorem weaken_initPotential (C : ObliviousSequenceImpl S P)
    {ValidOpSeq' : List S.Op → Prop}
    {Contract' : (ops : List S.Op) → PMF (List (Sigma S.Result)) → Prop}
    (hV : ∀ ops, ValidOpSeq' ops → S.ValidOpSeq ops)
    (hC : ∀ ops μ, S.ValidOpSeq ops → S.Contract ops μ → Contract' ops μ) :
    (C.weaken hV hC).initPotential = C.initPotential :=
  rfl

@[simp]
theorem weaken_charge (C : ObliviousSequenceImpl S P)
    {ValidOpSeq' : List S.Op → Prop}
    {Contract' : (ops : List S.Op) → PMF (List (Sigma S.Result)) → Prop}
    (hV : ∀ ops, ValidOpSeq' ops → S.ValidOpSeq ops)
    (hC : ∀ ops μ, S.ValidOpSeq ops → S.Contract ops μ → Contract' ops μ) :
    (C.weaken hV hC).charge = C.charge :=
  rfl

end ObliviousSequenceImpl

end Cslib.DataStructure.CellProbe.Randomized

/-! ### Canonical embeddings of `StateTransitionImpl` into `ObliviousSequenceImpl` -/

namespace Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl

open Cslib.CellProbe

universe u v

/-- Canonical embedding of any relational `Randomized.StateTransitionImpl` into
`ObliviousSequenceImpl` over `D.toObliviousSequenceSpec s₀`, given a state-independent operation
charge bound `opCharge : D.Op → ℕ` with `∀ s o, D.valid s o → C.charge s o ≤ opCharge o`. -/
@[expose] def toObliviousSequenceImpl {cells w : ℕ} {D : StateTransitionSpec.{u, v, 0}}
    {P : Cslib.CellProbe.Randomized.Scheme D.Op D.Result cells w} {s₀ : D.State}
    (C : StateTransitionImpl D P s₀)
    (opCharge : D.Op → ℕ := C.charge s₀)
    (hcharge : ∀ s o, D.valid s o → C.charge s o ≤ opCharge o := by
      intros; first | exact le_rfl | simp) :
    ObliviousSequenceImpl (D.toObliviousSequenceSpec s₀) P where
  initPotential := C.initPotential
  charge := opCharge
  contract_runSeq {_} hv := C.contract_runSeq hv
  expectedSeqProbes_le {_} hv := C.expectedSeqProbes_le_of_opCharge hcharge hv

@[simp]
theorem toObliviousSequenceImpl_initPotential {cells w : ℕ} {D : StateTransitionSpec.{u, v, 0}}
    {P : Cslib.CellProbe.Randomized.Scheme D.Op D.Result cells w} {s₀ : D.State}
    (C : StateTransitionImpl D P s₀) (opCharge) (hcharge) :
    (C.toObliviousSequenceImpl opCharge hcharge).initPotential = C.initPotential :=
  rfl

@[simp]
theorem toObliviousSequenceImpl_charge {cells w : ℕ} {D : StateTransitionSpec.{u, v, 0}}
    {P : Cslib.CellProbe.Randomized.Scheme D.Op D.Result cells w} {s₀ : D.State}
    (C : StateTransitionImpl D P s₀) (opCharge) (hcharge) :
    (C.toObliviousSequenceImpl opCharge hcharge).charge = opCharge :=
  rfl

end Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl

namespace Cslib.DataStructure.CellProbe.StateTransitionImpl

open Cslib.CellProbe Cslib.DataStructure.CellProbe.Randomized

universe u v

/-- Canonical embedding of any deterministic `CellProbe.StateTransitionImpl` into
`Randomized.ObliviousSequenceImpl` over `D.toObliviousSequenceSpec s₀`. -/
@[expose] noncomputable def toObliviousSequenceImpl {cells w : ℕ}
    {D : StateTransitionSpec.{u, v, 0}}
    {P : Scheme D.Op D.Result cells w} {s₀ : D.State}
    (C : StateTransitionImpl D P s₀)
    (opCharge : D.Op → ℕ := C.charge s₀)
    (hcharge : ∀ s o, D.valid s o → C.charge s o ≤ opCharge o := by
      intros; first | exact le_rfl | simp) :
    ObliviousSequenceImpl (D.toObliviousSequenceSpec s₀)
      (Cslib.CellProbe.Randomized.Scheme.ofDeterministic P) :=
  C.toRandomized.toObliviousSequenceImpl opCharge
    (by simpa only [toRandomized_charge] using hcharge)

@[simp]
theorem toObliviousSequenceImpl_initPotential {cells w : ℕ} {D : StateTransitionSpec.{u, v, 0}}
    {P : Scheme D.Op D.Result cells w} {s₀ : D.State}
    (C : StateTransitionImpl D P s₀) (opCharge) (hcharge) :
    (C.toObliviousSequenceImpl opCharge hcharge).initPotential = C.initPotential :=
  rfl

@[simp]
theorem toObliviousSequenceImpl_charge {cells w : ℕ} {D : StateTransitionSpec.{u, v, 0}}
    {P : Scheme D.Op D.Result cells w} {s₀ : D.State}
    (C : StateTransitionImpl D P s₀) (opCharge) (hcharge) :
    (C.toObliviousSequenceImpl opCharge hcharge).charge = opCharge :=
  rfl

end Cslib.DataStructure.CellProbe.StateTransitionImpl

/-! ### Averaging (easy) direction of Yao's principle [Yao1977] for zero-error schemes -/

namespace Cslib.DataStructure.CellProbe.Randomized

open Cslib.CellProbe Cslib.Probability
open scoped ENNReal

universe u v

/-- **Averaging (coin-fixing) argument, the easy direction of Yao's principle [Yao1977], for
zero-error schemes on oblivious sequences (`IndexedScheme` over explicit finite `opsAlphabet`):**
Suppose `D : StateTransitionSpec` is deterministic (`[D.HasStepFn f]`), `opsAlphabet : Finset D.Op`
is a finite set of admissible operations, `correctSeqs` is any set of admissible histories
(`D.ValidHistory s₀ ops`) of length `≤ horizon` over `opsAlphabet` on which `P` satisfies the
zero-error contract `(D.toObliviousSequenceSpec s₀).Contract ops ((P.runSeq ops).map Prod.fst)`
(bounded-error Monte Carlo schemes and adaptive sequence adversaries are out of scope), and
`hardDist : PMF (List D.Op)` is any sequence distribution supported on sequences of length
`≤ horizon` over `opsAlphabet`.

Then there exists a deterministic `D_det` in `(P.indexedSchemeLaw horizon opsAlphabet).support`
(the **time-aware relaxation** with a free step clock outside cell memory; deterministic lower
bounds paired with this theorem must hold against step-indexed `IndexedScheme`s) that returns the
canonical transcript `(D.run s₀ ops).2` on all `ops ∈ correctSeqs` and incurs expected probes over
`hardDist` at most that of `P`. -/
theorem exists_det_indexedScheme_le_expectedSeqProbes
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    [DecidableEq D.Op] [∀ o, Inhabited (D.Result o)]
    {cells w : ℕ} (s₀ : D.State)
    (P : Cslib.CellProbe.Randomized.Scheme D.Op D.Result cells w)
    (opsAlphabet : Finset D.Op) (horizon : ℕ)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs,
      D.ValidHistory s₀ ops ∧ ops.length ≤ horizon ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (hcorr : ∀ ops ∈ correctSeqs,
      (D.toObliviousSequenceSpec s₀).Contract ops ((P.runSeq ops).map Prod.fst))
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support,
      ops.length ≤ horizon ∧ ∀ o ∈ ops, o ∈ opsAlphabet) :
    ∃ D_det ∈ (P.indexedSchemeLaw horizon opsAlphabet).support,
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) ∧
      (∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) ≤
        ∑' ops, hardDist ops * P.expectedSeqProbes ops :=
  P.exists_det_indexedScheme_le_expectedSeqProbes opsAlphabet horizon correctSeqs
    (fun ops hops => (hcorrectSeqs ops hops).2)
    (fun ops tr => tr = (D.run s₀ ops).2)
    (fun ops hops =>
      (D.toObliviousSequenceSpec_contract_iff_of_hasStepFn s₀ (hcorrectSeqs ops hops).1 _).mp
        (hcorr ops hops))
    hardDist hhardDist

/-- `[Fintype D.Op]` convenience corollary of `exists_det_indexedScheme_le_expectedSeqProbes`,
instantiating `opsAlphabet := Finset.univ`. -/
theorem exists_det_indexedScheme_le_expectedSeqProbes_of_fintype
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    [Fintype D.Op] [DecidableEq D.Op] [∀ o, Inhabited (D.Result o)]
    {cells w : ℕ} (s₀ : D.State)
    (P : Cslib.CellProbe.Randomized.Scheme D.Op D.Result cells w)
    (horizon : ℕ)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs, D.ValidHistory s₀ ops ∧ ops.length ≤ horizon)
    (hcorr : ∀ ops ∈ correctSeqs,
      (D.toObliviousSequenceSpec s₀).Contract ops ((P.runSeq ops).map Prod.fst))
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support, ops.length ≤ horizon) :
    ∃ D_det ∈ (P.indexedSchemeLaw horizon Finset.univ).support,
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) ∧
      (∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) ≤
        ∑' ops, hardDist ops * P.expectedSeqProbes ops :=
  exists_det_indexedScheme_le_expectedSeqProbes s₀ P Finset.univ horizon correctSeqs
    (fun ops hops => ⟨(hcorrectSeqs ops hops).1, (hcorrectSeqs ops hops).2,
      fun _ _ => Finset.mem_univ _⟩)
    hcorr hardDist
    (fun ops hops => ⟨hhardDist ops hops, fun _ _ => Finset.mem_univ _⟩)

/-- **Random initial memory / coin-free steps averaging argument [Yao1977] (`CellProbe.Scheme`):**
when randomness lives only in initial memory `P.init` and per-operation trees draw no private coins
(`∀ o, (P.step o).IsCoinFree`, so operations observe `P.init` only by probing cells), zero-error
averaging over `D.toObliviousSequenceSpec s₀` produces a time-invariant deterministic
`D_det : Cslib.CellProbe.Scheme D.Op D.Result cells w` in `(P.schemeLaw hstep).support` without
requiring `[DecidableEq D.Op]`, `[∀ o, Inhabited (D.Result o)]`, `opsAlphabet`, or `horizon`. -/
theorem exists_det_scheme_le_expectedSeqProbes
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {cells w : ℕ} (s₀ : D.State)
    (P : Cslib.CellProbe.Randomized.Scheme D.Op D.Result cells w)
    (hstep : ∀ o, (P.step o).IsCoinFree)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs, D.ValidHistory s₀ ops)
    (hcorr : ∀ ops ∈ correctSeqs,
      (D.toObliviousSequenceSpec s₀).Contract ops ((P.runSeq ops).map Prod.fst))
    (hardDist : PMF (List D.Op)) :
    ∃ D_det ∈ (P.schemeLaw hstep).support,
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) ∧
      (∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) ≤
        ∑' ops, hardDist ops * P.expectedSeqProbes ops :=
  P.exists_det_scheme_le_expectedSeqProbes hstep correctSeqs
    (fun ops tr => tr = (D.run s₀ ops).2)
    (fun ops hops =>
      (D.toObliviousSequenceSpec_contract_iff_of_hasStepFn s₀ (hcorrectSeqs ops hops) _).mp
        (hcorr ops hops))
    hardDist

private theorem tsum_mul_le_init_add {Op : Type v} {Result : Op → Type} {cells w : ℕ}
    (P : Cslib.CellProbe.Randomized.Scheme Op Result cells w)
    (hardDist : PMF (List Op)) (initPotential : ℕ) (cost : List Op → ℝ≥0∞)
    (hcost : ∀ ops ∈ hardDist.support,
      P.expectedSeqProbes ops ≤ (initPotential : ℝ≥0∞) + cost ops) :
    (∑' ops, hardDist ops * P.expectedSeqProbes ops) ≤
      (initPotential : ℝ≥0∞) + ∑' ops, hardDist ops * cost ops := by
  calc
    (∑' ops, hardDist ops * P.expectedSeqProbes ops)
      ≤ ∑' ops, hardDist ops * ((initPotential : ℝ≥0∞) + cost ops) := by
          refine tsum_le_tsum fun ops => ?_
          by_cases hops : ops ∈ hardDist.support
          · exact mul_le_mul_right (hcost ops hops) _
          · rw [(PMF.apply_eq_zero_iff _ _).mpr hops, zero_mul, zero_mul]
    _ = (initPotential : ℝ≥0∞) + ∑' ops, hardDist ops * cost ops := by
          simp_rw [mul_add, tsum_add, ENNReal.tsum_mul_right, hardDist.tsum_coe, one_mul]

/-- Zero-error Yao averaging (easy direction [Yao1977]) packaged directly for an
`ObliviousSequenceImpl (D.toObliviousSequenceSpec s₀) P` on a deterministic specification
(`[D.HasStepFn f]`): produces a step-indexed `IndexedScheme` (in the time-aware relaxation with a
free step clock) correct on `correctSeqs` with expected probes bounded by `C`'s amortized budget. -/
theorem ObliviousSequenceImpl.exists_det_indexedScheme
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    [DecidableEq D.Op] [∀ o, Inhabited (D.Result o)]
    {cells w : ℕ} {s₀ : D.State}
    {P : Cslib.CellProbe.Randomized.Scheme D.Op D.Result cells w}
    (C : ObliviousSequenceImpl (D.toObliviousSequenceSpec s₀) P)
    (opsAlphabet : Finset D.Op) (horizon : ℕ)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs,
      D.ValidHistory s₀ ops ∧ ops.length ≤ horizon ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support,
      D.ValidHistory s₀ ops ∧ ops.length ≤ horizon ∧ ∀ o ∈ ops, o ∈ opsAlphabet) :
    ∃ D_det ∈ (P.indexedSchemeLaw horizon opsAlphabet).support,
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) ∧
      (∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) ≤
        (C.initPotential : ℝ≥0∞) +
          ∑' ops, hardDist ops * (((ops.map C.charge).sum : ℕ) : ℝ≥0∞) := by
  obtain ⟨D_det, hmem, hcorr, hle⟩ :=
    exists_det_indexedScheme_le_expectedSeqProbes s₀ P opsAlphabet horizon correctSeqs hcorrectSeqs
      (fun ops hops =>
        C.contract_runSeq ((D.validOpSeq_iff_validHistory s₀ ops).mpr (hcorrectSeqs ops hops).1))
      hardDist (fun ops hops => (hhardDist ops hops).2)
  refine ⟨D_det, hmem, hcorr, hle.trans (tsum_mul_le_init_add P hardDist C.initPotential _ ?_)⟩
  intro ops hops
  exact C.expectedSeqProbes_le ((D.validOpSeq_iff_validHistory s₀ ops).mpr (hhardDist ops hops).1)

/-- Lower-bound transfer for `ObliviousSequenceImpl (D.toObliviousSequenceSpec s₀) P`: any
distributional lower bound `L` proved against all deterministic step-indexed `IndexedScheme`s
correct on `correctSeqs` transfers directly to `C.initPotential + E_{hardDist}[sum charge]`. -/
theorem ObliviousSequenceImpl.le_expected_charge_of_det_indexedScheme
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {cells w : ℕ} {s₀ : D.State}
    {P : Cslib.CellProbe.Randomized.Scheme D.Op D.Result cells w}
    (C : ObliviousSequenceImpl (D.toObliviousSequenceSpec s₀) P)
    (opsAlphabet : Finset D.Op) (horizon : ℕ)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs,
      D.ValidHistory s₀ ops ∧ ops.length ≤ horizon ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support,
      D.ValidHistory s₀ ops ∧ ops.length ≤ horizon ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    {L : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme D.Op D.Result cells w,
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) →
      L ≤ ∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    L ≤ (C.initPotential : ℝ≥0∞) +
          ∑' ops, hardDist ops * (((ops.map C.charge).sum : ℕ) : ℝ≥0∞) := by
  classical
  have _ : ∀ o, Inhabited (D.Result o) := fun o => ⟨(f s₀ o).2⟩
  obtain ⟨D_det, _, hcorr, hle⟩ :=
    C.exists_det_indexedScheme opsAlphabet horizon correctSeqs hcorrectSeqs hardDist hhardDist
  exact (hlb D_det hcorr).trans hle

/-- Zero-error Yao averaging (easy direction [Yao1977]) packaged directly for a
`Randomized.StateTransitionImpl D P s₀` on a deterministic specification (`[D.HasStepFn f]`),
producing a step-indexed `IndexedScheme` (in the time-aware relaxation with a free step clock)
bounded by `C.initPotential + E_{hardDist}[D.totalCost C.charge s₀ ops]`. -/
theorem StateTransitionImpl.exists_det_indexedScheme
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    [DecidableEq D.Op] [∀ o, Inhabited (D.Result o)]
    {cells w : ℕ} {s₀ : D.State}
    {P : Cslib.CellProbe.Randomized.Scheme D.Op D.Result cells w}
    (C : StateTransitionImpl D P s₀)
    (opsAlphabet : Finset D.Op) (horizon : ℕ)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs,
      D.ValidHistory s₀ ops ∧ ops.length ≤ horizon ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support,
      D.ValidHistory s₀ ops ∧ ops.length ≤ horizon ∧ ∀ o ∈ ops, o ∈ opsAlphabet) :
    ∃ D_det ∈ (P.indexedSchemeLaw horizon opsAlphabet).support,
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) ∧
      (∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) ≤
        (C.initPotential : ℝ≥0∞) +
          ∑' ops, hardDist ops * (D.totalCost C.charge s₀ ops : ℝ≥0∞) := by
  obtain ⟨D_det, hmem, hcorr, hle⟩ :=
    exists_det_indexedScheme_le_expectedSeqProbes s₀ P opsAlphabet horizon correctSeqs hcorrectSeqs
      (fun ops hops => (C.seq_expected_amortized_ofFn ops (hcorrectSeqs ops hops).1).1)
      hardDist (fun ops hops => (hhardDist ops hops).2)
  refine ⟨D_det, hmem, hcorr, hle.trans (tsum_mul_le_init_add P hardDist C.initPotential _ ?_)⟩
  intro ops hops
  exact C.expectedSeqProbes_le_ofFn ops (hhardDist ops hops).1

/-- Random initial memory / coin-free steps averaging specialization [Yao1977] for
`Randomized.StateTransitionImpl D P s₀` (`[D.HasStepFn f]`), returning a time-invariant
`Cslib.CellProbe.Scheme` without `opsAlphabet` or `horizon`. -/
theorem StateTransitionImpl.exists_det_scheme
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {cells w : ℕ} {s₀ : D.State}
    {P : Cslib.CellProbe.Randomized.Scheme D.Op D.Result cells w}
    (C : StateTransitionImpl D P s₀)
    (hstep : ∀ o, (P.step o).IsCoinFree)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs, D.ValidHistory s₀ ops)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support, D.ValidHistory s₀ ops) :
    ∃ D_det ∈ (P.schemeLaw hstep).support,
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) ∧
      (∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) ≤
        (C.initPotential : ℝ≥0∞) +
          ∑' ops, hardDist ops * (D.totalCost C.charge s₀ ops : ℝ≥0∞) := by
  obtain ⟨D_det, hmem, hcorr, hle⟩ :=
    exists_det_scheme_le_expectedSeqProbes s₀ P hstep correctSeqs hcorrectSeqs
      (fun ops hops => (C.seq_expected_amortized_ofFn ops (hcorrectSeqs ops hops)).1)
      hardDist
  refine ⟨D_det, hmem, hcorr, hle.trans (tsum_mul_le_init_add P hardDist C.initPotential _ ?_)⟩
  intro ops hops
  exact C.expectedSeqProbes_le_ofFn ops (hhardDist ops hops)

/-- Lower-bound transfer for `Randomized.StateTransitionImpl D P s₀`: any distributional lower bound
`L` proved against all deterministic step-indexed `IndexedScheme`s correct on `correctSeqs`
transfers directly to `C.initPotential + E_{hardDist}[D.totalCost C.charge s₀ ops]`. -/
theorem StateTransitionImpl.le_expected_totalCost_of_det_indexedScheme
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {cells w : ℕ} {s₀ : D.State}
    {P : Cslib.CellProbe.Randomized.Scheme D.Op D.Result cells w}
    (C : StateTransitionImpl D P s₀)
    (opsAlphabet : Finset D.Op) (horizon : ℕ)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs,
      D.ValidHistory s₀ ops ∧ ops.length ≤ horizon ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support,
      D.ValidHistory s₀ ops ∧ ops.length ≤ horizon ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    {L : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme D.Op D.Result cells w,
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) →
      L ≤ ∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    L ≤ (C.initPotential : ℝ≥0∞) +
          ∑' ops, hardDist ops * (D.totalCost C.charge s₀ ops : ℝ≥0∞) := by
  classical
  have _ : ∀ o, Inhabited (D.Result o) := fun o => ⟨(f s₀ o).2⟩
  obtain ⟨D_det, _, hcorr, hle⟩ :=
    C.exists_det_indexedScheme opsAlphabet horizon correctSeqs hcorrectSeqs hardDist hhardDist
  exact (hlb D_det hcorr).trans hle

end Cslib.DataStructure.CellProbe.Randomized
