/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.CellProbe.OfWordRAM
public import CslibFrontier.DataStructure.CellProbe.Randomized.ObliviousSequence
public import CslibFrontier.DataStructure.WordRAM.Randomized.ObliviousSequence
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map

/-!
# Word-RAM-to-Cell-Probe Data-Structure Simulation Bridges and Lower-Bound Transfer

This file lifts the program-level Word-RAM-to-cell-probe simulators of
`CslibFrontier.Computability.CellProbe.OfWordRAM` ([Miltersen1999], §1.2) to the relational and
oblivious-sequence data-structure `Impl` hierarchies (`Cslib.DataStructure.WordRAM` →
`Cslib.DataStructure.CellProbe`, [CLRS2009], Section 17.3), and combines them with the zero-error
averaging direction of Yao's principle [Yao1977] to obtain unconditional contrapositive Word-RAM
instruction lower bounds from deterministic step-indexed cell-probe lower bounds.

Four simulation and transfer layers are provided, each in both **standard `w`-bit layout**
(`space + persistentRegCount P` cells of width `w`, additive overhead `2 * persistentRegCount P`,
which equals `0` extra cells and `0` extra probes when `∀ i, P.input i = true`) and **wide-cell
single-spill layout** (`space + 1` cells of width `wideSubroutineWidth P w`, additive overhead at
most `2` regardless of register count `r`):
1. **Deterministic `WordRAM.StateTransitionImpl` (`toCellProbe`, `toCellProbeWide`, `simInit`):**
   Uses `rep_supported` and `potential_supported` with `zeroOutside` so no extra read-footprint
   hypothesis is required on `WordRAM.StateTransitionImpl`; pre-operation initialization is packed
   into `Scheme.init` at `0` operation probes, and `simInit` additionally simulates `P.initFresh`
   from zeroed cell memory in at most `C.initTime + persistentRegCount P` probes.
2. **Flat `(p_init, p_op)` programs (`ExecFlatProgramOps`, `exists_cellProbe_of_flatPrograms`,
   `flat_wordRAM_lower_bound_of_det_cellProbe`):** Direct multi-operation Las Vegas bridge for flat
   `WordRAM.Program B r` pairs without wrapping `SubroutineCode`.
3. **Randomized Las Vegas `WordRAM.Randomized.StateTransitionImpl` (`exists_cellProbe_lasVegas`,
   `wordRAM_lower_bound_of_det_cellProbe_lower_bound`,
   `wordRAM_lower_bound_of_det_cellProbe_wide`):** Buffered finite-horizon truncation preserves
   **100% zero-error transcript correctness** on all admissible histories over `opsAlphabet` up to
   `M_corr` (without `[Fintype D.Op]`), and taking `η → 0` eliminates truncation slack completely
   from the contrapositive Word-RAM lower bound.
4. **Randomized `WordRAM.Randomized.ObliviousSequenceImpl` (`exists_cellProbe_of_execRand`,
   `exists_cellProbe_lasVegas`, `wordRAM_lower_bound_of_det_cellProbe_lower_bound`):** Exact
   zero-slack simulation for finite-tree `ExecRand` on arbitrary `ObliviousSequenceSpec`s (including
   Monte Carlo contracts) and buffered zero-error simulation + lower-bound transfer on
   `D.toObliviousSequenceSpec s₀`.

## Main definitions

* `Cslib.DataStructure.WordRAM.StateTransitionImpl.toCellProbe`,
  `Cslib.DataStructure.WordRAM.StateTransitionImpl.toCellProbeWide`,
  `Cslib.DataStructure.WordRAM.StateTransitionImpl.simInit`: deterministic `StateTransitionImpl`
  simulation bridges and fresh-initializer probe tree.
* `Cslib.DataStructure.CellProbe.prepareFlatRegs`,
  `Cslib.DataStructure.CellProbe.ExecFlatProgramOps`: flat `(p_init, p_op)` multi-operation Las
  Vegas execution contract.
* `Cslib.DataStructure.WordRAM.Randomized.ObliviousSequenceImpl.HasFiniteExecRand`: finite-tree
  `ExecRand` step witness for exact zero-slack oblivious-sequence simulation.

## Main results

* `Cslib.DataStructure.CellProbe.exists_cellProbe_of_flatPrograms`,
  `Cslib.DataStructure.CellProbe.exists_cellProbeWide_of_flatPrograms`,
  `Cslib.DataStructure.CellProbe.flat_wordRAM_lower_bound_of_det_cellProbe`,
  `Cslib.DataStructure.CellProbe.flat_wordRAM_lower_bound_of_det_cellProbe_wide`: flat-program
  simulation and contrapositive lower-bound transfer.
* `Cslib.DataStructure.WordRAM.Randomized.StateTransitionImpl.exists_cellProbe_lasVegas`,
  `Cslib.DataStructure.WordRAM.Randomized.StateTransitionImpl.exists_cellProbeWide_lasVegas`,
  `Cslib.DataStructure.CellProbe.wordRAM_lower_bound_of_det_cellProbe_lower_bound`,
  `Cslib.DataStructure.CellProbe.wordRAM_lower_bound_of_det_cellProbe_wide`: Las Vegas
  `StateTransitionImpl` simulation and `η`-free contrapositive Word-RAM lower-bound transfer over an
  explicit `opsAlphabet : Finset D.Op` (plus `_of_fintype` corollaries).
* `Cslib.DataStructure.WordRAM.Randomized.ObliviousSequenceImpl.exists_cellProbe_of_execRand`,
  `Cslib.DataStructure.WordRAM.Randomized.ObliviousSequenceImpl.exists_cellProbe_lasVegas`,
  `Cslib.DataStructure.CellProbe.oblivious_wordRAM_lower_bound_of_det_cellProbe`,
  `Cslib.DataStructure.CellProbe.oblivious_wordRAM_lower_bound_of_det_cellProbe_wide`:
  `ObliviousSequenceImpl` simulation and contrapositive lower-bound transfer.

## References

* [P. B. Miltersen, *Cell Probe Complexity — a Survey*, §1.2][Miltersen1999]
* [A. C.-C. Yao, *Probabilistic Computations: Toward a Unified Measure of Complexity*][Yao1977]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 17.3][CLRS2009]
-/

public section

open Cslib.WordRAM Cslib.CellProbe Cslib.Probability
open scoped ENNReal

namespace Cslib.DataStructure.CellProbe

/-! ### 0. Shared `ENNReal`, worst-case horizon, and initial-state helpers -/

/-- Eliminate arbitrary per-step truncation slack `η > 0` in `ℝ≥0∞`: if `LB ≤ R + η * M` holds for
every `0 < η`, then `LB ≤ R`. -/
theorem le_of_forall_pos_le_add_mul {LB R : ℝ≥0∞} {M : ℕ}
    (h : ∀ {η : ℝ≥0∞}, 0 < η → LB ≤ R + η * (M : ℝ≥0∞)) : LB ≤ R := by
  by_contra hnot
  have hlt : R < LB := lt_of_not_ge hnot
  have hR_ne_top : R ≠ ⊤ := ne_top_of_lt hlt
  by_cases hM : M = 0
  · subst hM
    have h1 := h zero_lt_one
    simp only [Nat.cast_zero, mul_zero, add_zero] at h1
    exact hnot h1
  · have hc_ne_zero : ((M : ℝ≥0∞)) ≠ 0 := Nat.cast_ne_zero.mpr hM
    have hc_ne_top : ((M : ℝ≥0∞)) ≠ ⊤ := ENNReal.natCast_ne_top M
    have hdiff_pos : 0 < LB - R := tsub_pos_of_lt hlt
    set δ : ℝ≥0∞ := min 1 ((LB - R) / 2)
    have hδ_pos : 0 < δ :=
      lt_min zero_lt_one (ENNReal.div_pos hdiff_pos.ne' (by norm_num))
    have hδ_ne_top : δ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _)
    have hRδ_lt : R + δ < LB := by
      by_cases hLB : LB = ⊤
      · rw [hLB]
        exact lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hR_ne_top, hδ_ne_top⟩)
      · have hdiff_ne_top : LB - R ≠ ⊤ := ne_top_of_le_ne_top hLB tsub_le_self
        have hδ_lt_diff : δ < LB - R :=
          (min_le_right _ _).trans_lt (ENNReal.half_lt_self hdiff_pos.ne' hdiff_ne_top)
        calc R + δ
          _ < R + (LB - R) := ENNReal.add_lt_add_left hR_ne_top hδ_lt_diff
          _ = LB := add_tsub_cancel_of_le hlt.le
    have hη_pos : 0 < δ / (M : ℝ≥0∞) := ENNReal.div_pos hδ_pos.ne' hc_ne_top
    have hle : LB ≤ R + δ := by
      refine (h hη_pos).trans (add_le_add le_rfl ?_)
      rw [mul_comm]
      exact ENNReal.mul_div_le
    exact lt_irrefl (R + δ) (hRδ_lt.trans_le hle)

/-- If every single-operation tree of `Q` has expected probes at most `W` on every memory, then
`Q.expectedProbesFrom m ops ≤ ops.length * W` on every memory `m`. -/
theorem expectedProbesFrom_le_mul {Op : Type*} {Result : Op → Type} {cells w : ℕ}
    (Q : Cslib.CellProbe.Randomized.Scheme Op Result cells w) (W : ℝ≥0∞)
    (hW : ∀ o m, (Q.step o).expectedProbes m ≤ W) :
    ∀ (ops : List Op) (m : Mem cells w),
      Q.expectedProbesFrom m ops ≤ (ops.length : ℝ≥0∞) * W
  | [], _ => by simp [Cslib.CellProbe.Randomized.Scheme.expectedProbesFrom]
  | o :: ops, m => by
    rw [Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl.expectedProbesFrom_cons]
    have htail :
        (∑' am : Result o × Mem cells w,
            (((Q.step o).run m).map Prod.fst) am * Q.expectedProbesFrom am.2 ops) ≤
          (ops.length : ℝ≥0∞) * W := by
      refine (tsum_le_tsum fun (am : Result o × Mem cells w) =>
        mul_le_mul' le_rfl (expectedProbesFrom_le_mul Q W hW ops am.2)).trans ?_
      rw [ENNReal.tsum_mul_right, (((Q.step o).run m).map Prod.fst).tsum_coe, one_mul]
    calc (Q.step o).expectedProbes m +
          ∑' am : Result o × Mem cells w,
            (((Q.step o).run m).map Prod.fst) am * Q.expectedProbesFrom am.2 ops
      _ ≤ W + (ops.length : ℝ≥0∞) * W := add_le_add (hW o m) htail
      _ = ((o :: ops).length : ℝ≥0∞) * W := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-- Construct a canonical zeroed-memory initial `Data r_ds` for a zero-parameter
`SubroutineCode B r_ds 0` from `Fits w base` alone. -/
def mkInitData0 {B : Basis} {r_ds : ℕ} (P : SubroutineCode B r_ds 0) (base : ℕ) : Data r_ds where
  regs i := if i = P.frontierReg then base else 0
  mem _ := 0

theorem mkInitData0_spec {B : Basis} {r_ds w base : ℕ} (P : SubroutineCode B r_ds 0)
    (params : Fin 0 → ℕ) (hfit_base : Fits w base) :
    (mkInitData0 P base).Bounded w ∧
      (mkInitData0 P base).regs P.frontierReg = base ∧
      (∀ j, (mkInitData0 P base).regs (P.initParams j) = params j) ∧
      ∀ a, (mkInitData0 P base).mem a = 0 := by
  refine ⟨⟨fun i => ?_, fun _ => fits_zero w⟩, by simp [mkInitData0], fun j => Fin.elim0 j,
    fun _ => rfl⟩
  dsimp only [mkInitData0]
  split_ifs
  · exact hfit_base
  · exact fits_zero w

end Cslib.DataStructure.CellProbe

/-! ### 1. Deterministic `WordRAM.StateTransitionImpl` → `CellProbe.StateTransitionImpl` -/

namespace Cslib.DataStructure.WordRAM.StateTransitionImpl

open Cslib.DataStructure.CellProbe

universe u v

variable {B : Basis} {r_ds k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init}
  {D : StateTransitionSpec.{u, v, 0}} [∀ o, Inhabited (D.Result o)]
  {params : Fin k_init → ℕ} {s₀ : D.State}

omit [∀ o, Inhabited (D.Result o)] in
private theorem initFresh_zeroMem (C : WordRAM.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j) :
    ∃ y₀, ExecWithin w P.initFresh { regs := d₀.regs, mem := fun _ => 0 } y₀ C.initTime ∧
      C.rep s₀ y₀ ∧ C.potential y₀ ≤ C.initPotential := by
  have hd₀' : ({ regs := d₀.regs, mem := fun _ => 0 } : Data r_ds).Bounded w :=
    ⟨hd₀.1, fun _ => fits_zero w⟩
  obtain ⟨y₀, he, _, hr₀, hpot₀, _⟩ :=
    C.initFresh_exec (x := { regs := d₀.regs, mem := fun _ => 0 }) hd₀' hfr hpar (fun _ _ => rfl)
  exact ⟨y₀, he, hr₀, hpot₀⟩

/-- Unified deterministic `WordRAM.StateTransitionImpl` → `CellProbe.StateTransitionImpl` simulation
over an arbitrary `RegLayout`: uses `rep_supported` and `potential_supported` with `zeroOutside` so
no extra read-footprint hypothesis is needed on `C`. -/
noncomputable def toCellProbeLayout (C : WordRAM.StateTransitionImpl P D w base params s₀)
    {regCells wCell : ℕ} (L : RegLayout r_ds P.input base C.space w regCells wCell)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j) :
    Σ P_cp : Scheme D.Op D.Result (C.space + regCells) wCell,
      { C_cp : Cslib.DataStructure.CellProbe.StateTransitionImpl D P_cp s₀ //
        C_cp.initPotential = C.initPotential ∧
          ∀ s o, C_cp.charge s o = C.charge s o + L.overhead } := by
  let hex₀ := C.initFresh_zeroMem hd₀ hfr hpar
  let y₀ := Classical.choose hex₀
  have hy₀_spec := Classical.choose_spec hex₀
  let P_cp : Scheme D.Op D.Result (C.space + regCells) wCell :=
    { init := L.pack y₀
      step := fun o =>
        simProgDetAuto L (P.code.program P.output) (C.encode o)
          (fun _ regs => C.decode o regs) default }
  refine ⟨P_cp, ⟨{
    rep := fun s m => L.ValidMem m ∧ C.rep s (L.unpack (fun _ => 0) m)
    potential := fun m => C.potential (L.unpack (fun _ => 0) m)
    initPotential := C.initPotential
    charge := fun s o => C.charge s o + L.overhead
    init_rep := ?_
    init_potential := ?_
    step_exec := ?_
  }, ⟨rfl, fun _ _ => rfl⟩⟩⟩
  · have hy₀_bdd : y₀.Bounded w := C.bounded hy₀_spec.2.1
    refine ⟨L.validMem_pack y₀, C.rep_supported (fun i hi => ?_) (fun a ha => ?_)
      (L.unpack_bounded (fun _ _ => fits_zero w) _) hy₀_spec.2.1⟩
    · have h := L.unpack_pack_regs (fun _ => 0) hy₀_bdd i
      simp only [hi, Bool.false_eq_true, ↓reduceIte] at h
      exact h
    · rw [L.unpack_pack_mem (fun _ => 0) hy₀_bdd a]
      exact zeroOutside_mem_of_mem_footprint y₀ ha
  · have hy₀_bdd : y₀.Bounded w := C.bounded hy₀_spec.2.1
    have hpot_eq : C.potential (L.unpack (fun _ => 0) (L.pack y₀)) = C.potential y₀ :=
      C.potential_supported
        (fun i hi => by
          have h := L.unpack_pack_regs (fun _ => 0) hy₀_bdd i
          simp only [hi, Bool.false_eq_true, ↓reduceIte] at h
          exact h)
        (fun a ha => by
          rw [L.unpack_pack_mem (fun _ => 0) hy₀_bdd a]
          exact zeroOutside_mem_of_mem_footprint y₀ ha)
        hy₀_spec.2.1
    exact hpot_eq.le.trans hy₀_spec.2.2
  · intro s m o ⟨hm_val, hr_can⟩ hv
    let x_op := L.unpack (C.encode o) m
    have harg_fit : ∀ i, P.input i = true → Fits w (C.encode o i) := C.arguments_fit o hv
    have hx_bdd : x_op.Bounded w := L.unpack_bounded harg_fit m
    have hpers_eq : ∀ i, P.input i = false → x_op.regs i = (L.unpack (fun _ => 0) m).regs i :=
      fun i hi => L.unpack_regs_pers (C.encode o) (fun _ => 0) m i hi
    have hmem_eq : ∀ a ∈ (Block.mk base C.space).footprint,
        x_op.mem a = (L.unpack (fun _ => 0) m).mem a :=
      fun a _ => (L.unpack_mem (C.encode o) m a).trans (L.unpack_mem (fun _ => 0) m a).symm
    have hr_op : C.rep s x_op := C.rep_supported hpers_eq hmem_eq hx_bdd hr_can
    have hpot_op : C.potential x_op = C.potential (L.unpack (fun _ => 0) m) :=
      C.potential_supported hpers_eq hmem_eq hr_can
    have hregs_prep :
        x_op.regs = fun i =>
          if P.input i then C.encode o i else (L.unpack (fun _ => 0) m).regs i := by
      funext i
      by_cases hi : P.input i = true
      · simp only [hi, ↓reduceIte]
        exact L.unpack_regs_input (C.encode o) m i hi
      · have hif : P.input i = false := Bool.eq_false_iff.mpr hi
        simp only [hif, Bool.false_eq_true, ↓reduceIte]
        exact hpers_eq i hif
    have harg_match : C.argMatch o x_op.regs := by
      rw [hregs_prep]
      exact C.encode_matches o (L.unpack (fun _ => 0) m).regs
    obtain ⟨y, s', a, n, he, hdstep, hdec, hr_y, _, hamort⟩ := C.step_exec o hr_op hv harg_match
    have hruns : Runs w (P.code.program P.output) ⟨0, x_op⟩ ⟨0 + P.code.size, y⟩ n :=
      he.runs (pc := 0) (p := P.code.program P.output) (Program.Contains.self _).append_left
    have hhalt : step w (P.code.program P.output) ⟨0 + P.code.size, y⟩ = .halt (y.regs P.output) :=
      step_halt (by simp [Code.program])
    obtain ⟨hrun_sim, hpr_sim⟩ :=
      simProgDetAuto_spec L (P.code.program P.output) (C.encode o)
        (fun _ regs => C.decode o regs) (default : D.Result o) hm_val harg_fit hruns hhalt
    change (P_cp.step o).run m = _ at hrun_sim
    change (P_cp.step o).probes m ≤ _ at hpr_sim
    rw [hdec, Option.getD_some] at hrun_sim
    have hy_bdd : y.Bounded w := C.bounded hr_y
    have hr_pack : C.rep s' (L.unpack (fun _ => 0) (L.pack y)) :=
      C.rep_supported
        (fun i hi => by
          have h := L.unpack_pack_regs (fun _ => 0) hy_bdd i
          simp only [hi, Bool.false_eq_true, ↓reduceIte] at h
          exact h)
        (fun addr ha => by
          rw [L.unpack_pack_mem (fun _ => 0) hy_bdd addr]
          exact zeroOutside_mem_of_mem_footprint y ha)
        (L.unpack_bounded (fun _ _ => fits_zero w) _) hr_y
    have hpot_pack : C.potential (L.unpack (fun _ => 0) (L.pack y)) = C.potential y :=
      C.potential_supported
        (fun i hi => by
          have h := L.unpack_pack_regs (fun _ => 0) hy_bdd i
          simp only [hi, Bool.false_eq_true, ↓reduceIte] at h
          exact h)
        (fun addr ha => by
          rw [L.unpack_pack_mem (fun _ => 0) hy_bdd addr]
          exact zeroOutside_mem_of_mem_footprint y ha)
        hr_y
    refine ⟨s', ?_, ?_, ?_⟩
    · rw [hrun_sim]
      exact hdstep
    · rw [hrun_sim]
      exact ⟨L.validMem_pack y, hr_pack⟩
    · rw [hrun_sim]
      dsimp only
      rw [hpot_pack, ← hpot_op]
      omega

/-- **Bridge 1 (Deterministic `WordRAM.StateTransitionImpl.toCellProbe`):**
Any deterministic `WordRAM.StateTransitionImpl` using `C.space` words and `persistentRegCount P`
persistent registers induces a deterministic `CellProbe.StateTransitionImpl` on
`C.space + persistentRegCount P` cells of width `w` with `initPotential = C.initPotential` and
per-operation probe charge `C.charge s o + 2 * persistentRegCount P` (`0` extra cells and `0` extra
probes when `∀ i, P.input i = true`). -/
noncomputable def toCellProbe (C : WordRAM.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j) :
    Σ P_cp : Scheme D.Op D.Result (C.space + persistentRegCount P) w,
      { C_cp : Cslib.DataStructure.CellProbe.StateTransitionImpl D P_cp s₀ //
        C_cp.initPotential = C.initPotential ∧
          ∀ s o, C_cp.charge s o = C.charge s o + 2 * persistentRegCount P } := by
  let S := C.toCellProbeLayout (standardLayout P.input base C.space w) hd₀ hfr hpar
  refine ⟨S.1, ⟨S.2.1, S.2.2.1, fun s o => (S.2.2.2 s o).trans ?_⟩⟩
  rw [standardLayout_overhead, persistentRegCount_eq_persCount]

/-- Fresh-initializer cell-probe tree for `(C.toCellProbe hd₀ hfr hpar).1`: starting from zeroed
cell memory `fun _ => 0`, simulates `P.initFresh` in at most `C.initTime + persistentRegCount P`
cell probes and leaves `(C.toCellProbe hd₀ hfr hpar).1.init` in memory. -/
noncomputable def simInit (C : WordRAM.StateTransitionImpl P D w base params s₀)
    (d₀ : Data r_ds) : ProbeTree (C.space + persistentRegCount P) w PUnit :=
  simProgInitDet (standardLayout P.input base C.space w)
    (P.initFresh.program P.output) d₀.regs (C.initTime + 1)

theorem simInit_spec (C : WordRAM.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j) :
    (C.simInit d₀).run (fun _ => 0) = (PUnit.unit, (C.toCellProbe hd₀ hfr hpar).1.init) ∧
      (C.simInit d₀).probes (fun _ => 0) ≤ C.initTime + persistentRegCount P := by
  let hex₀ := C.initFresh_zeroMem hd₀ hfr hpar
  let y₀ := Classical.choose hex₀
  have hspec₀ := Classical.choose_spec hex₀
  obtain ⟨n, hn_le, he⟩ := hspec₀.1
  have hruns :
      Runs w (P.initFresh.program P.output) ⟨0, { regs := d₀.regs, mem := fun _ => 0 }⟩
        ⟨0 + P.initFresh.size, y₀⟩ n :=
    he.runs (pc := 0) (p := P.initFresh.program P.output) (Program.Contains.self _).append_left
  have hhalt :
      step w (P.initFresh.program P.output) ⟨0 + P.initFresh.size, y₀⟩ =
        .halt (y₀.regs P.output) :=
    step_halt (by simp [Code.program])
  obtain ⟨hrun, hpr⟩ :=
    simProgInitDet_spec (standardLayout P.input base C.space w)
      (P.initFresh.program P.output) d₀.regs
      (standardLayout_validMem P.input base C.space w _) hd₀.1 hruns hhalt
      (Nat.succ_le_succ hn_le)
  refine ⟨hrun, hpr.trans ?_⟩
  rw [standardLayout_spillProbes, ← persistentRegCount_eq_persCount]
  exact Nat.add_le_add_right hn_le _

/-- **Wide-Cell Deterministic Bridge (`WordRAM.StateTransitionImpl.toCellProbeWide`):**
Packs all `persistentRegCount P` persistent registers into `1` wide cell of width
`wideSubroutineWidth P w := max (persistentRegCount P) 1 * w` over `C.space + 1` cells, paying at
most `2` additive probes per operation (`0` when `persistentRegCount P = 0`) regardless of `r_ds`.
-/
noncomputable def toCellProbeWide (C : WordRAM.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j) :
    Σ P_cp : Scheme D.Op D.Result (C.space + 1) (wideSubroutineWidth P w),
      { C_cp : Cslib.DataStructure.CellProbe.StateTransitionImpl D P_cp s₀ //
        C_cp.initPotential = C.initPotential ∧
          ∀ s o, C_cp.charge s o =
            C.charge s o + if persistentRegCount P = 0 then 0 else 2 } := by
  let S := C.toCellProbeLayout (wideLayout P.input base C.space w) hd₀ hfr hpar
  refine ⟨S.1, ⟨S.2.1, S.2.2.1, fun s o => (S.2.2.2 s o).trans ?_⟩⟩
  rw [wideLayout_overhead, persistentRegCount_eq_persCount]

end Cslib.DataStructure.WordRAM.StateTransitionImpl

/-! ### 2. Flat `(p_init, p_op)` Las Vegas simulation and contrapositive lower-bound transfer -/

namespace Cslib.DataStructure.CellProbe

universe u v z

/-- Load operation arguments `encode o` into input registers (`input i = true`), preserving
persistent registers (`input i = false`) and all of `x.mem`. -/
@[expose] def prepareFlatRegs {Op : Type*} {r : ℕ} (input : Fin r → Bool)
    (encode : Op → Fin r → ℕ) (o : Op) (x : Data r) : Data r where
  regs i := if input i then encode o i else x.regs i
  mem := x.mem

theorem unpack_pack_eq_prepareFlatRegs {Op : Type*} {r S regCells w wCell base : ℕ}
    {input : Fin r → Bool} (L : RegLayout r input base S w regCells wCell)
    (encode : Op → Fin r → ℕ) (o : Op) {x : Data r}
    (hx_bdd : x.Bounded w)
    (hx_out : ∀ a ∉ (Block.mk base S).footprint, x.mem a = 0) :
    L.unpack (encode o) (L.pack x) = prepareFlatRegs input encode o x := by
  ext i
  · exact L.unpack_pack_regs (encode o) hx_bdd i
  · rw [L.unpack_pack_mem (encode o) hx_bdd i]
    dsimp only [prepareFlatRegs, zeroOutside]
    split_ifs with ha
    · rfl
    · symm
      refine hx_out i fun hmem => ha ?_
      rw [Block.mem_footprint] at hmem
      exact hmem

/-- Multi-operation distributional execution of a flat `WordRAM.Program B r` over a deterministic
state-transition specification `D : StateTransitionSpec` (`[D.HasStepFn f]`). -/
inductive ExecFlatProgramOps {B : Basis} {r : ℕ}
    (D : StateTransitionSpec.{u, v, 0})
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (Latent : Type z) (w base space : ℕ)
    (p_op : Program B r) (input : Fin r → Bool)
    (encode : D.Op → Fin r → ℕ)
    (decode : (o : D.Op) → ℕ → (Fin r → ℕ) → Option (D.Result o)) :
    D.State → List D.Op → PMF (Latent × Data r) → PMF (Latent × Data r) → ℝ≥0∞ → Prop where
  | nil (s : D.State) (ν : PMF (Latent × Data r)) :
      ExecFlatProgramOps D Latent w base space p_op input encode decode s [] ν ν 0
  | cons {s : D.State} {o : D.Op} {ops : List D.Op}
      {ν ν_final : PMF (Latent × Data r)}
      {μ_step : Latent × Data r → PMF (Latent × ℕ × Data r)}
      {T_step : Latent × Data r → ℝ≥0∞} {T_rest : ℝ≥0∞} :
      (∀ p ∈ ν.support,
        (∀ i, input i = true → Fits w (encode o i)) ∧
        ExecProgramDist w p_op (prepareFlatRegs input encode o p.2)
          ((μ_step p).map Prod.snd) (T_step p + 1) ∧
        ∀ q ∈ (μ_step p).support,
          q.2.2.Bounded w ∧
          decode o q.2.1 q.2.2.regs = some (D.stepFn s o).2 ∧
          Modifies (Block.mk base space).footprint p.2.mem q.2.2.mem) →
      ExecFlatProgramOps D Latent w base space p_op input encode decode (D.stepFn s o).1 ops
        (ν.bind fun p => (μ_step p).map fun q => (q.1, q.2.2)) ν_final T_rest →
      ExecFlatProgramOps D Latent w base space p_op input encode decode s (o :: ops) ν ν_final
        ((∑' p, ν p * T_step p) + T_rest)

private theorem simFlatOps_induction {B : Basis} {r regCells wCell w base space : ℕ}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    [∀ o, Inhabited (D.Result o)]
    {Latent : Type z} {p_op : Program B r} {input : Fin r → Bool}
    {encode : D.Op → Fin r → ℕ}
    {decode : (o : D.Op) → ℕ → (Fin r → ℕ) → Option (D.Result o)}
    (L : RegLayout r input base space w regCells wCell)
    (initMem : PMF (Mem (space + regCells) wCell))
    (opsAlphabet : Finset D.Op) (M_corr : ℕ) (K : ℕ) (η : ℝ≥0∞)
    (hK_tail : ∀ o ∈ opsAlphabet, ∀ m : Mem (space + regCells) wCell,
      (∃ μ_p : PMF (ℕ × Data r), ∃ T_p : ℝ≥0∞, T_p ≠ ⊤ ∧
        ExecProgramDist w p_op (L.unpack (encode o) m) μ_p (T_p + 1)) →
      (evalRand w p_op K ⟨0, L.unpack (encode o) m⟩).toOuterMeasure (RandCfg.runningSet r) *
        ((((2 * space + regCells) + M_corr * (2 * space + regCells + L.overhead) : ℕ) : ℝ≥0∞) +
          (M_corr : ℝ≥0∞) * (K : ℝ≥0∞)) ≤ η)
    {s : D.State} {ops : List D.Op} {ν ν_final : PMF (Latent × Data r)} {T_ops : ℝ≥0∞}
    (hex : ExecFlatProgramOps D Latent w base space p_op input encode decode s ops ν ν_final T_ops)
    (hlen : ops.length ≤ M_corr)
    (halph : ∀ o ∈ ops, o ∈ opsAlphabet)
    (hT_fin : T_ops ≠ ⊤)
    (hsupp : ∀ p ∈ ν.support,
      p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0) :
    let P_cp : Cslib.CellProbe.Randomized.Scheme D.Op D.Result (space + regCells) wCell :=
      { init := initMem
        step := fun o =>
          simProgRand (w := w) L p_op (encode o) (decode o) default K }
    (∀ p ∈ ν.support, ∀ tm ∈ ((P_cp.runFrom (L.pack p.2) ops).map Prod.fst).support,
      tm.1 = (D.run s ops).2) ∧
    (∑' p, ν p * P_cp.expectedProbesFrom (L.pack p.2) ops) ≤
      T_ops + ((L.overhead : ℝ≥0∞) + η) * (ops.length : ℝ≥0∞) := by
  intro P_cp
  set W_step : ℝ≥0∞ := ((K + 2 * space + regCells + L.overhead : ℕ) : ℝ≥0∞)
  have hW_step : ∀ o m, (P_cp.step o).expectedProbes m ≤ W_step := fun o m =>
    simProgRand_expectedProbes_le_worstCase L p_op (encode o) (decode o) default K m
  induction hex with
  | nil s ν =>
    refine ⟨fun p _ tm htm => ?_, ?_⟩
    · simp only [Cslib.CellProbe.Randomized.Scheme.runFrom, PMF.pure_map, PMF.support_pure,
        Set.mem_singleton_iff] at htm
      rw [htm, StateTransitionSpec.run_nil]
    · simp [Cslib.CellProbe.Randomized.Scheme.expectedProbesFrom]
  | @cons s o ops_rem ν ν_final μ_step T_step T_rest hstep _ ih =>
    have ho_alph : o ∈ opsAlphabet := halph o List.mem_cons_self
    have halph_rem : ∀ o' ∈ ops_rem, o' ∈ opsAlphabet :=
      fun o' ho' => halph o' (List.mem_cons_of_mem o ho')
    have hlen_rem : ops_rem.length ≤ M_corr := Nat.le_of_succ_le hlen
    have hsum_fin : (∑' p, ν p * T_step p) ≠ ⊤ :=
      ne_top_of_le_ne_top hT_fin le_self_add
    have hT_rest_fin : T_rest ≠ ⊤ :=
      ne_top_of_le_ne_top hT_fin le_add_self
    have hsupp₁ :
        ∀ p₁ ∈ (ν.bind fun p => (μ_step p).map fun q => (q.1, q.2.2)).support,
          p₁.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p₁.2.mem a = 0 := by
      intro p₁ hp₁
      rw [PMF.mem_support_bind_iff] at hp₁
      obtain ⟨p, hp, hq_map⟩ := hp₁
      rw [PMF.mem_support_map_iff] at hq_map
      obtain ⟨q, hq, rfl⟩ := hq_map
      obtain ⟨hq_bdd, _, hmod⟩ := (hstep p hp).2.2 q hq
      exact ⟨hq_bdd, fun a ha => (hmod a ha).trans ((hsupp p hp).2 a ha)⟩
    obtain ⟨hcorr_rem, hexp_rem⟩ := ih hlen_rem halph_rem hT_rest_fin hsupp₁
    refine ⟨?_, ?_⟩
    · intro p hp tm htm
      rw [Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl.runFrom_cons_fst,
        PMF.mem_support_bind_iff] at htm
      obtain ⟨z₁, hz₁, htm_rem⟩ := htm
      rw [PMF.mem_support_map_iff] at hz₁
      obtain ⟨z_full, hz_full, rfl⟩ := hz₁
      rw [PMF.mem_support_map_iff] at htm_rem
      obtain ⟨tm_rem, htm_rem_mem, rfl⟩ := htm_rem
      obtain ⟨hp_bdd, hp_out⟩ := hsupp p hp
      obtain ⟨harg, hpdist, hq_all⟩ := hstep p hp
      have hunp : L.unpack (encode o) (L.pack p.2) = prepareFlatRegs input encode o p.2 :=
        unpack_pack_eq_prepareFlatRegs L encode o hp_bdd hp_out
      rw [← hunp] at hpdist
      obtain ⟨hsup_sim, _, _⟩ :=
        simProgRand_lasVegas_spec L p_op (encode o) (decode o) (default : D.Result o) K
          (L.validMem_pack p.2) harg hpdist
      obtain ⟨vy, hvy, hz₁_eq⟩ := hsup_sim z_full hz_full
      rw [PMF.mem_support_map_iff] at hvy
      obtain ⟨q, hq, rfl⟩ := hvy
      obtain ⟨_, hdec_q, _⟩ := hq_all q hq
      have hz₁_ans : z_full.1.1 = (D.stepFn s o).2 := by
        have h1 := congrArg Prod.fst hz₁_eq
        simpa [hdec_q] using h1
      have hz₁_mem : z_full.1.2 = L.pack q.2.2 := congrArg Prod.snd hz₁_eq
      rw [hz₁_mem] at htm_rem_mem
      have hp₁_mem :
          (q.1, q.2.2) ∈ (ν.bind fun p' => (μ_step p').map fun q' => (q'.1, q'.2.2)).support := by
        rw [PMF.mem_support_bind_iff]
        exact ⟨p, hp, (PMF.mem_support_map_iff _ _ _).mpr ⟨q, hq, rfl⟩⟩
      have htr_rem := hcorr_rem (q.1, q.2.2) hp₁_mem tm_rem htm_rem_mem
      simp only [StateTransitionSpec.run_cons, hz₁_ans, htr_rem]
    · set B_rem : ℝ≥0∞ := (M_corr : ℝ≥0∞) * W_step
      have hB_rem_eq :
          ((2 * space + regCells : ℕ) : ℝ≥0∞) + B_rem =
            (((2 * space + regCells) + M_corr * (2 * space + regCells + L.overhead) : ℕ) : ℝ≥0∞) +
              (M_corr : ℝ≥0∞) * (K : ℝ≥0∞) := by
        dsimp only [B_rem, W_step]
        push_cast
        ring
      have hpt : ∀ p,
          ν p * P_cp.expectedProbesFrom (L.pack p.2) (o :: ops_rem) ≤
            ν p * T_step p +
              ν p * ((L.overhead : ℝ≥0∞) + η) +
              ν p * (∑' q, μ_step p q * P_cp.expectedProbesFrom (L.pack q.2.2) ops_rem) := by
        intro p
        by_cases hp : p ∈ ν.support
        · obtain ⟨hp_bdd, hp_out⟩ := hsupp p hp
          obtain ⟨harg, hpdist, _⟩ := hstep p hp
          have hTp_fin : T_step p ≠ ⊤ := by
            intro htop
            have hle_sum : ν p * T_step p ≤ ∑' p', ν p' * T_step p' := by
              have hiSup : (∑' p', ν p' * T_step p') =
                  ⨆ s : Finset (Latent × Data r), ∑ p' ∈ s, ν p' * T_step p' :=
                tsum_eq_iSup_sum
              rw [hiSup]
              simpa using le_iSup
                (fun s : Finset (Latent × Data r) => ∑ p' ∈ s, ν p' * T_step p') {p}
            have hνp_ne : ν p ≠ 0 := (PMF.mem_support_iff _ _).mp hp
            rw [htop, ENNReal.mul_top hνp_ne, top_le_iff] at hle_sum
            exact hsum_fin hle_sum
          have hunp : L.unpack (encode o) (L.pack p.2) = prepareFlatRegs input encode o p.2 :=
            unpack_pack_eq_prepareFlatRegs L encode o hp_bdd hp_out
          rw [← hunp] at hpdist
          obtain ⟨_, hexp_sim, hcoupl⟩ :=
            simProgRand_lasVegas_spec L p_op (encode o) (decode o) (default : D.Result o) K
              (L.validMem_pack p.2) harg hpdist
          have hcont_le :
              (∑ t ∈ Finset.range K,
                  (evalRand w p_op t ⟨0, L.unpack (encode o) (L.pack p.2)⟩).toOuterMeasure
                    {cfg | isContinuingCfg p_op cfg = true}) ≤ T_step p :=
            continuing_sum_le_of_almostSurelyHalts hpdist.almostSurelyHalts hpdist.1 K
          have hg_bound : ∀ om ∈ (((P_cp.step o).run (L.pack p.2)).map Prod.fst).support,
              P_cp.expectedProbesFrom om.2 ops_rem ≤ B_rem := by
            intro om _
            exact (expectedProbesFrom_le_mul P_cp W_step hW_step ops_rem om.2).trans
              (mul_le_mul' (Nat.cast_le.mpr hlen_rem) le_rfl)
          have hcoupl_rem := hcoupl (fun om => P_cp.expectedProbesFrom om.2 ops_rem) B_rem hg_bound
          rw [Probability.PMF.tsum_map_mul (μ_step p) Prod.snd] at hcoupl_rem
          dsimp only at hcoupl_rem
          have hcons_eq :
              P_cp.expectedProbesFrom (L.pack p.2) (o :: ops_rem) =
                (P_cp.step o).expectedProbes (L.pack p.2) +
                  ∑' om, (((P_cp.step o).run (L.pack p.2)).map Prod.fst) om *
                    P_cp.expectedProbesFrom om.2 ops_rem :=
            Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl.expectedProbesFrom_cons
              P_cp (L.pack p.2) o ops_rem
          have htail_le :
              (evalRand w p_op K ⟨0, L.unpack (encode o) (L.pack p.2)⟩).toOuterMeasure
                  (RandCfg.runningSet r) *
                (((2 * space + regCells : ℕ) : ℝ≥0∞) + B_rem) ≤ η := by
            rw [hB_rem_eq]
            exact hK_tail o ho_alph (L.pack p.2)
              ⟨(μ_step p).map Prod.snd, T_step p, hTp_fin, hpdist⟩
          have htot_p :
              P_cp.expectedProbesFrom (L.pack p.2) (o :: ops_rem) ≤
                T_step p + ((L.overhead : ℝ≥0∞) + η) +
                  ∑' q, μ_step p q * P_cp.expectedProbesFrom (L.pack q.2.2) ops_rem := by
            rw [hcons_eq]
            set p_run := (evalRand w p_op K ⟨0, L.unpack (encode o) (L.pack p.2)⟩).toOuterMeasure
              (RandCfg.runningSet r)
            calc (P_cp.step o).expectedProbes (L.pack p.2) +
                  ∑' om, (((P_cp.step o).run (L.pack p.2)).map Prod.fst) om *
                    P_cp.expectedProbesFrom om.2 ops_rem
              _ ≤ (T_step p + (L.overhead : ℝ≥0∞) +
                    p_run * ((2 * space + regCells : ℕ) : ℝ≥0∞)) +
                  ((∑' q, μ_step p q * P_cp.expectedProbesFrom (L.pack q.2.2) ops_rem) +
                    p_run * B_rem) :=
                  add_le_add (hexp_sim.trans (add_le_add (add_le_add hcont_le le_rfl) le_rfl))
                    hcoupl_rem
              _ = T_step p + (L.overhead : ℝ≥0∞) +
                    (∑' q, μ_step p q * P_cp.expectedProbesFrom (L.pack q.2.2) ops_rem) +
                    p_run * (((2 * space + regCells : ℕ) : ℝ≥0∞) + B_rem) := by ring
              _ ≤ T_step p + (L.overhead : ℝ≥0∞) +
                    (∑' q, μ_step p q * P_cp.expectedProbesFrom (L.pack q.2.2) ops_rem) + η :=
                  add_le_add le_rfl htail_le
              _ = T_step p + ((L.overhead : ℝ≥0∞) + η) +
                    ∑' q, μ_step p q * P_cp.expectedProbesFrom (L.pack q.2.2) ops_rem := by ac_rfl
          simpa only [mul_add, add_assoc] using mul_le_mul' le_rfl htot_p
        · rw [(PMF.apply_eq_zero_iff _ _).mpr hp]
          simp
      have hbind_eq :
          (∑' p, ν p * ∑' q, μ_step p q * P_cp.expectedProbesFrom (L.pack q.2.2) ops_rem) =
            ∑' p₁, (ν.bind fun p => (μ_step p).map fun q => (q.1, q.2.2)) p₁ *
              P_cp.expectedProbesFrom (L.pack p₁.2) ops_rem := by
        rw [Probability.PMF.tsum_bind_mul]
        refine tsum_congr fun p => congrArg (ν p * ·) ?_
        exact (Probability.PMF.tsum_map_mul (μ_step p) (fun q => (q.1, q.2.2))
          (fun p₁ => P_cp.expectedProbesFrom (L.pack p₁.2) ops_rem)).symm
      refine (tsum_le_tsum hpt).trans ?_
      rw [tsum_add, tsum_add, ENNReal.tsum_mul_right, ν.tsum_coe, one_mul, hbind_eq]
      calc (∑' p, ν p * T_step p) + ((L.overhead : ℝ≥0∞) + η) +
            ∑' p₁, (ν.bind fun p => (μ_step p).map fun q => (q.1, q.2.2)) p₁ *
              P_cp.expectedProbesFrom (L.pack p₁.2) ops_rem
        _ ≤ (∑' p, ν p * T_step p) + ((L.overhead : ℝ≥0∞) + η) +
              (T_rest + ((L.overhead : ℝ≥0∞) + η) * (ops_rem.length : ℝ≥0∞)) :=
            add_le_add le_rfl hexp_rem
        _ = ((∑' p, ν p * T_step p) + T_rest) +
              ((L.overhead : ℝ≥0∞) + η) * ((o :: ops_rem).length : ℝ≥0∞) := by
            simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
            ring

/-- Uniform layout-parametric cell-probe simulation of a flat `(ν₀, p_op)` Las Vegas Word-RAM
program pair: constructs a single `P_cp` **outside** `∀ ops` that is 100% zero-error on all
histories over `opsAlphabet` of length `≤ M_corr` admitting a finite-time `ExecFlatProgramOps`
derivation, with `P_cp.expectedSeqProbes ops ≤ T_ops + (L.overhead + η) * ops.length`. -/
theorem exists_cellProbeLayout_of_flatPrograms {B : Basis} {r regCells wCell w base space : ℕ}
    {input : Fin r → Bool}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    [∀ o, Inhabited (D.Result o)]
    {Latent : Type z} (s₀ : D.State)
    (L : RegLayout r input base space w regCells wCell)
    (p_op : Program B r) (encode : D.Op → Fin r → ℕ)
    (decode : (o : D.Op) → ℕ → (Fin r → ℕ) → Option (D.Result o))
    (ν₀ : PMF (Latent × Data r))
    (hsupp₀ : ∀ p ∈ ν₀.support,
      p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ P_cp : Cslib.CellProbe.Randomized.Scheme D.Op D.Result (space + regCells) wCell,
      ∀ (ops : List D.Op) {ν_final : PMF (Latent × Data r)} {T_ops : ℝ≥0∞},
        D.ValidHistory s₀ ops →
        ops.length ≤ M_corr →
        (∀ o ∈ ops, o ∈ opsAlphabet) →
        T_ops ≠ ⊤ →
        ExecFlatProgramOps D Latent w base space p_op input encode decode s₀ ops ν₀ ν_final T_ops →
        (D.toObliviousSequenceSpec s₀).Contract ops ((P_cp.runSeq ops).map Prod.fst) ∧
          P_cp.expectedSeqProbes ops ≤
            T_ops + ((L.overhead : ℝ≥0∞) + η) * (ops.length : ℝ≥0∞) := by
  let Good : D.Op → Mem (space + regCells) wCell → Prop := fun o m =>
    ∃ μ_p : PMF (ℕ × Data r), ∃ T_p : ℝ≥0∞, T_p ≠ ⊤ ∧
      ExecProgramDist w p_op (L.unpack (encode o) m) μ_p (T_p + 1)
  have hGood_fin : ∀ o ∈ opsAlphabet, ∀ m, Good o m →
      expectedTime w p_op ⟨0, L.unpack (encode o) m⟩ ≠ ⊤ := by
    rintro o _ m ⟨μ_p, T_p, hTp_fin, hpdist⟩
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hTp_fin, ENNReal.one_ne_top⟩) hpdist.1
  obtain ⟨K, _, hK_tail⟩ := exists_uniform_cutoff L opsAlphabet Good (fun _ => p_op) encode
    hGood_fin ((2 * space + regCells) + M_corr * (2 * space + regCells + L.overhead)) M_corr hη
  let P_cp : Cslib.CellProbe.Randomized.Scheme D.Op D.Result (space + regCells) wCell :=
    { init := ν₀.map fun p => L.pack p.2
      step := fun o => simProgRand (w := w) L p_op (encode o) (decode o) default K }
  refine ⟨P_cp, fun ops {ν_final T_ops} hv hlen halph hT_fin hex => ?_⟩
  obtain ⟨hcorr, hexp⟩ :=
    simFlatOps_induction L (ν₀.map fun p => L.pack p.2) opsAlphabet M_corr K η hK_tail hex
      hlen halph hT_fin hsupp₀
  refine ⟨?_, ?_⟩
  · rw [D.toObliviousSequenceSpec_contract_iff_of_hasStepFn s₀ hv]
    intro out hout
    rw [Cslib.CellProbe.Randomized.Scheme.runSeq, PMF.map_bind, PMF.mem_support_bind_iff] at hout
    obtain ⟨m₀, hm₀, hout_from⟩ := hout
    rw [PMF.mem_support_map_iff] at hm₀
    obtain ⟨p, hp, rfl⟩ := hm₀
    rw [PMF.map_comp, PMF.mem_support_map_iff] at hout_from
    obtain ⟨z_fin, htm, hout_eq⟩ := hout_from
    rcases z_fin with ⟨⟨tr, m_fin⟩, pr⟩
    dsimp only [Function.comp_apply] at hout_eq
    subst hout_eq
    exact hcorr p hp (tr, m_fin) ((PMF.mem_support_map_iff _ _ _).mpr ⟨((tr, m_fin), pr), htm, rfl⟩)
  · rw [Cslib.CellProbe.Randomized.Scheme.expectedSeqProbes_eq_init_tsum]
    dsimp only [P_cp]
    rw [Probability.PMF.tsum_map_mul]
    exact hexp

/-- Standard `w`-bit cell-probe simulation of a flat `(ν₀, p_op)` Las Vegas Word-RAM program pair
over `space + persCount input` cells (`0` extra cells and `0` overhead when `∀ i, input i = true`).
-/
theorem exists_cellProbe_of_flatPrograms {B : Basis} {r w base space : ℕ} {input : Fin r → Bool}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    [∀ o, Inhabited (D.Result o)]
    {Latent : Type z} (s₀ : D.State)
    (p_op : Program B r) (encode : D.Op → Fin r → ℕ)
    (decode : (o : D.Op) → ℕ → (Fin r → ℕ) → Option (D.Result o))
    (ν₀ : PMF (Latent × Data r))
    (hsupp₀ : ∀ p ∈ ν₀.support,
      p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ P_cp : Cslib.CellProbe.Randomized.Scheme D.Op D.Result (space + persCount input) w,
      ∀ (ops : List D.Op) {ν_final : PMF (Latent × Data r)} {T_ops : ℝ≥0∞},
        D.ValidHistory s₀ ops →
        ops.length ≤ M_corr →
        (∀ o ∈ ops, o ∈ opsAlphabet) →
        T_ops ≠ ⊤ →
        ExecFlatProgramOps D Latent w base space p_op input encode decode s₀ ops ν₀ ν_final T_ops →
        (D.toObliviousSequenceSpec s₀).Contract ops ((P_cp.runSeq ops).map Prod.fst) ∧
          P_cp.expectedSeqProbes ops ≤
            T_ops + (((2 * persCount input : ℕ) : ℝ≥0∞) + η) * (ops.length : ℝ≥0∞) := by
  obtain ⟨P_cp, hP⟩ := exists_cellProbeLayout_of_flatPrograms s₀
    (standardLayout input base space w) p_op encode decode ν₀ hsupp₀ opsAlphabet M_corr hη
  refine ⟨P_cp, fun ops {ν_final T_ops} hv hlen halph hT hex => ?_⟩
  obtain ⟨hc, he⟩ := hP ops hv hlen halph hT hex
  rw [standardLayout_overhead] at he
  exact ⟨hc, he⟩

/-- Wide-cell (`space + 1` cells of width `wideWidth input w`) simulation of a flat `(ν₀, p_op)`
Las Vegas Word-RAM program pair (`≤ 2` additive probes per operation regardless of `r`). -/
theorem exists_cellProbeWide_of_flatPrograms {B : Basis} {r w base space : ℕ}
    {input : Fin r → Bool}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    [∀ o, Inhabited (D.Result o)]
    {Latent : Type z} (s₀ : D.State)
    (p_op : Program B r) (encode : D.Op → Fin r → ℕ)
    (decode : (o : D.Op) → ℕ → (Fin r → ℕ) → Option (D.Result o))
    (ν₀ : PMF (Latent × Data r))
    (hsupp₀ : ∀ p ∈ ν₀.support,
      p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ P_cp :
        Cslib.CellProbe.Randomized.Scheme D.Op D.Result (space + 1) (wideWidth input w),
      ∀ (ops : List D.Op) {ν_final : PMF (Latent × Data r)} {T_ops : ℝ≥0∞},
        D.ValidHistory s₀ ops →
        ops.length ≤ M_corr →
        (∀ o ∈ ops, o ∈ opsAlphabet) →
        T_ops ≠ ⊤ →
        ExecFlatProgramOps D Latent w base space p_op input encode decode s₀ ops ν₀ ν_final T_ops →
        (D.toObliviousSequenceSpec s₀).Contract ops ((P_cp.runSeq ops).map Prod.fst) ∧
          P_cp.expectedSeqProbes ops ≤
            T_ops + (((if persCount input = 0 then 0 else 2 : ℕ) : ℝ≥0∞) + η) *
              (ops.length : ℝ≥0∞) := by
  obtain ⟨P_cp, hP⟩ := exists_cellProbeLayout_of_flatPrograms s₀
    (wideLayout input base space w) p_op encode decode ν₀ hsupp₀ opsAlphabet M_corr hη
  refine ⟨P_cp, fun ops {ν_final T_ops} hv hlen halph hT hex => ?_⟩
  obtain ⟨hc, he⟩ := hP ops hv hlen halph hT hex
  rw [wideLayout_overhead] at he
  exact ⟨hc, he⟩

private theorem flat_lower_bound_layout {B : Basis} {r regCells wCell w base space S_max : ℕ}
    {input : Fin r → Bool}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {Latent : Type z} (s₀ : D.State)
    (L : RegLayout r input base space w regCells wCell)
    (hspace : space + regCells ≤ S_max)
    (p_op : Program B r) (encode : D.Op → Fin r → ℕ)
    (decode : (o : D.Op) → ℕ → (Fin r → ℕ) → Option (D.Result o))
    (ν₀ : PMF (Latent × Data r))
    (hsupp₀ : ∀ p ∈ ν₀.support,
      p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (hex_corr : ∀ ops ∈ correctSeqs, ∃ ν_final T_ops, T_ops ≠ ⊤ ∧
      ExecFlatProgramOps D Latent w base space p_op input encode decode s₀ ops ν₀ ν_final T_ops)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (timeBound : List D.Op → ℝ≥0∞)
    (hex_hard : ∀ ops ∈ hardDist.support, ∃ ν_final T_ops,
      T_ops ≤ timeBound ops ∧ T_ops ≠ ⊤ ∧
      ExecFlatProgramOps D Latent w base space p_op input encode decode s₀ ops ν₀ ν_final T_ops)
    {LB : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme D.Op D.Result S_max wCell,
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) →
      LB ≤ ∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    LB ≤ ∑' ops, hardDist ops *
      (timeBound ops + (L.overhead : ℝ≥0∞) * (ops.length : ℝ≥0∞)) := by
  classical
  have _ : ∀ o, Inhabited (D.Result o) := fun o => ⟨(f s₀ o).2⟩
  refine le_of_forall_pos_le_add_mul (M := M_corr) fun {η} hη => ?_
  obtain ⟨P_raw, hP_raw⟩ :=
    exists_cellProbeLayout_of_flatPrograms s₀ L p_op encode decode ν₀ hsupp₀ opsAlphabet M_corr hη
  let P_pad := P_raw.padCells hspace
  have hcorr_pad : ∀ ops ∈ correctSeqs,
      (D.toObliviousSequenceSpec s₀).Contract ops ((P_pad.runSeq ops).map Prod.fst) := by
    intro ops hops
    obtain ⟨hv, hlen, halph⟩ := hcorrectSeqs ops hops
    obtain ⟨ν_final, T_ops, hT_fin, hex⟩ := hex_corr ops hops
    rw [Cslib.CellProbe.Randomized.Scheme.runSeq_padCells]
    exact (hP_raw ops hv hlen halph hT_fin hex).1
  obtain ⟨D_det, _, hD_corr, hD_probes⟩ :=
    Cslib.DataStructure.CellProbe.Randomized.exists_det_indexedScheme_le_expectedSeqProbes
      s₀ P_pad opsAlphabet M_corr correctSeqs hcorrectSeqs hcorr_pad hardDist
      (fun ops hops => (hhardDist ops hops).2)
  refine (hlb D_det hD_corr).trans (hD_probes.trans ?_)
  have hpt : ∀ ops,
      hardDist ops * P_pad.expectedSeqProbes ops ≤
        hardDist ops * (timeBound ops + (L.overhead : ℝ≥0∞) * (ops.length : ℝ≥0∞)) +
          hardDist ops * (η * (M_corr : ℝ≥0∞)) := by
    intro ops
    by_cases hops : ops ∈ hardDist.support
    · obtain ⟨hv, hlen, halph⟩ := hhardDist ops hops
      obtain ⟨ν_final, T_ops, hT_le, hT_fin, hex⟩ := hex_hard ops hops
      rw [Cslib.CellProbe.Randomized.Scheme.expectedSeqProbes_padCells]
      have hexp := (hP_raw ops hv hlen halph hT_fin hex).2
      have h1 :
          P_raw.expectedSeqProbes ops ≤
            (timeBound ops + (L.overhead : ℝ≥0∞) * (ops.length : ℝ≥0∞)) +
              η * (M_corr : ℝ≥0∞) := by
        calc P_raw.expectedSeqProbes ops
          _ ≤ T_ops + ((L.overhead : ℝ≥0∞) + η) * (ops.length : ℝ≥0∞) := hexp
          _ = (T_ops + (L.overhead : ℝ≥0∞) * (ops.length : ℝ≥0∞)) +
                η * (ops.length : ℝ≥0∞) := by ring
          _ ≤ (timeBound ops + (L.overhead : ℝ≥0∞) * (ops.length : ℝ≥0∞)) +
                η * (M_corr : ℝ≥0∞) :=
              add_le_add (add_le_add hT_le le_rfl)
                (mul_le_mul' le_rfl (Nat.cast_le.mpr hlen))
      simpa only [mul_add] using mul_le_mul' le_rfl h1
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hops]
      simp
  refine (tsum_le_tsum hpt).trans ?_
  rw [tsum_add, ENNReal.tsum_mul_right, hardDist.tsum_coe, one_mul]

/-- **Contrapositive Word-RAM lower-bound transfer for flat `(ν₀, p_op)` programs** (standard
`w`-bit cell layout over `S_max ≥ space + persCount input` cells, `0` `η`-loss, no
`[Fintype D.Op]`). -/
theorem flat_wordRAM_lower_bound_of_det_cellProbe {B : Basis} {r w base space S_max : ℕ}
    {input : Fin r → Bool}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {Latent : Type z} (s₀ : D.State)
    (hspace : space + persCount input ≤ S_max)
    (p_op : Program B r) (encode : D.Op → Fin r → ℕ)
    (decode : (o : D.Op) → ℕ → (Fin r → ℕ) → Option (D.Result o))
    (ν₀ : PMF (Latent × Data r))
    (hsupp₀ : ∀ p ∈ ν₀.support,
      p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (hex_corr : ∀ ops ∈ correctSeqs, ∃ ν_final T_ops, T_ops ≠ ⊤ ∧
      ExecFlatProgramOps D Latent w base space p_op input encode decode s₀ ops ν₀ ν_final T_ops)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (timeBound : List D.Op → ℝ≥0∞)
    (hex_hard : ∀ ops ∈ hardDist.support, ∃ ν_final T_ops,
      T_ops ≤ timeBound ops ∧ T_ops ≠ ⊤ ∧
      ExecFlatProgramOps D Latent w base space p_op input encode decode s₀ ops ν₀ ν_final T_ops)
    {LB : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme D.Op D.Result S_max w,
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) →
      LB ≤ ∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    LB ≤ ∑' ops, hardDist ops *
      (timeBound ops + ((2 * persCount input : ℕ) : ℝ≥0∞) * (ops.length : ℝ≥0∞)) := by
  simpa only [standardLayout_overhead] using
    flat_lower_bound_layout s₀ (standardLayout input base space w) hspace p_op encode decode ν₀
      hsupp₀ opsAlphabet M_corr correctSeqs hcorrectSeqs hex_corr hardDist hhardDist timeBound
      hex_hard hlb

/-- **Wide-cell contrapositive Word-RAM lower-bound transfer for flat `(ν₀, p_op)` programs**
(`S_max ≥ space + 1` cells of width `wideWidth input w`, `≤ 2` additive probes per operation
regardless of `r`, `0` `η`-loss, no `[Fintype D.Op]`). -/
theorem flat_wordRAM_lower_bound_of_det_cellProbe_wide {B : Basis} {r w base space S_max : ℕ}
    {input : Fin r → Bool}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {Latent : Type z} (s₀ : D.State)
    (hspace : space + 1 ≤ S_max)
    (p_op : Program B r) (encode : D.Op → Fin r → ℕ)
    (decode : (o : D.Op) → ℕ → (Fin r → ℕ) → Option (D.Result o))
    (ν₀ : PMF (Latent × Data r))
    (hsupp₀ : ∀ p ∈ ν₀.support,
      p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (hex_corr : ∀ ops ∈ correctSeqs, ∃ ν_final T_ops, T_ops ≠ ⊤ ∧
      ExecFlatProgramOps D Latent w base space p_op input encode decode s₀ ops ν₀ ν_final T_ops)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (timeBound : List D.Op → ℝ≥0∞)
    (hex_hard : ∀ ops ∈ hardDist.support, ∃ ν_final T_ops,
      T_ops ≤ timeBound ops ∧ T_ops ≠ ⊤ ∧
      ExecFlatProgramOps D Latent w base space p_op input encode decode s₀ ops ν₀ ν_final T_ops)
    {LB : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme D.Op D.Result S_max (wideWidth input w),
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) →
      LB ≤ ∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    LB ≤ ∑' ops, hardDist ops *
      (timeBound ops +
        ((if persCount input = 0 then 0 else 2 : ℕ) : ℝ≥0∞) * (ops.length : ℝ≥0∞)) := by
  simpa only [wideLayout_overhead] using
    flat_lower_bound_layout s₀ (wideLayout input base space w) hspace p_op encode decode ν₀
      hsupp₀ opsAlphabet M_corr correctSeqs hcorrectSeqs hex_corr hardDist hhardDist timeBound
      hex_hard hlb

end Cslib.DataStructure.CellProbe

/-! ### 3. `WordRAM.Randomized.StateTransitionImpl` Las Vegas simulation and lower-bound transfer -/

namespace Cslib.DataStructure.WordRAM.Randomized.StateTransitionImpl

open Cslib.DataStructure.CellProbe

universe u v

variable {B : Basis} {r_ds k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init}
  {D : StateTransitionSpec.{u, v, 0}}
  {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
  {params : Fin k_init → ℕ} {s₀ : D.State}

/-- Compile a structured `ExecStepsOfFn` derivation on `C` to `ExecFlatProgramOps` on
`P.code.program P.output`. -/
theorem ExecStepsOfFn.toExecFlatProgramOps
    (C : WordRAM.Randomized.StateTransitionImpl P D w base params s₀)
    {s : D.State} {ops : List D.Op} {ν ν_final : PMF (C.Seed × Data r_ds)} {T_ops : ℝ≥0∞}
    (hex : C.ExecStepsOfFn s ops ν ν_final T_ops)
    (hv : D.ValidHistory s ops) :
    ExecFlatProgramOps D C.Seed w base C.space (P.code.program P.output) P.input C.encode
      (fun o _ regs => C.decode o regs) s ops ν ν_final T_ops := by
  induction hex with
  | nil s ν => exact .nil s ν
  | @cons s o ops_rem ν ν_final μ_step T_step T_rest hstep _ ih =>
    obtain ⟨hvo, hv_rem⟩ := hv
    let μ_flat : C.Seed × Data r_ds → PMF (C.Seed × ℕ × Data r_ds) :=
      fun p => (μ_step p).map fun q => (q.1, q.2.regs P.output, q.2)
    have hbind_eq :
        (ν.bind fun p => (μ_flat p).map fun q => (q.1, q.2.2)) = ν.bind μ_step := by
      refine congrArg (ν.bind ·) (funext fun p => ?_)
      dsimp only [μ_flat]
      rw [PMF.map_comp]
      exact PMF.map_id (μ_step p)
    refine .cons (μ_step := μ_flat) (T_step := T_step) (fun p hp => ?_) (hbind_eq.symm ▸ ih hv_rem)
    obtain ⟨hcdist, hq_all⟩ := hstep p hp
    have hprep_eq : C.toDynamicProgram.prepare o p.2 = prepareFlatRegs P.input C.encode o p.2 :=
      rfl
    have hpdist := execProgramDist_of_execCodeDist (hprep_eq ▸ hcdist) P.output
    have hmap_snd :
        ((μ_step p).map Prod.snd).map (fun y => (y.regs P.output, y)) =
          (μ_flat p).map Prod.snd := by
      dsimp only [μ_flat]
      rw [PMF.map_comp, PMF.map_comp]
      rfl
    rw [hmap_snd] at hpdist
    refine ⟨C.arguments_fit o hvo, hpdist, fun q hq => ?_⟩
    rw [PMF.mem_support_map_iff] at hq
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    obtain ⟨hdec, hrep, hmod⟩ := hq_all q₀ hq₀
    exact ⟨C.bounded hrep, hdec, hmod⟩

private theorem exists_init_and_flat_steps
    (C : WordRAM.Randomized.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j) :
    ∃ ν₀ : PMF (C.Seed × Data r_ds),
      (∀ p ∈ ν₀.support,
        p.2.Bounded w ∧ ∀ a ∉ (Block.mk base C.space).footprint, p.2.mem a = 0) ∧
      ∀ ops : List D.Op, D.ValidHistory s₀ ops →
        ∃ ν_final T_ops,
          T_ops ≤ (C.initPotential : ℝ≥0∞) + (D.totalCost C.charge s₀ ops : ℝ≥0∞) ∧
          T_ops ≠ ⊤ ∧
          ExecFlatProgramOps D C.Seed w base C.space (P.code.program P.output) P.input C.encode
            (fun o _ regs => C.decode o regs) s₀ ops ν₀ ν_final T_ops := by
  let d₀' : Data r_ds := { regs := d₀.regs, mem := fun _ => 0 }
  have hd₀' : d₀'.Bounded w := ⟨hd₀.1, fun _ => fits_zero w⟩
  obtain ⟨ν₀, _, hseed₀, hsupp₀⟩ := C.initFresh_exec hd₀' hfr hpar (fun _ _ => rfl)
  refine ⟨ν₀, fun p hp => ?_, fun ops hv => ?_⟩
  · obtain ⟨_, hrep, _, hmod⟩ := hsupp₀ p hp
    exact ⟨C.bounded hrep, fun a ha => hmod a ha⟩
  · have hrep₀ : ∀ p ∈ ν₀.support, C.rep p.1 s₀ p.2 := fun p hp => (hsupp₀ p hp).2.1
    obtain ⟨ν_final, T_ops, hex, _, _, hamort⟩ :=
      C.steps_expected_amortized_ofFn ops ν₀ hv hseed₀ hrep₀
    have hpot₀ : (∑' p, ν₀ p * (C.potential p.1 p.2 : ℝ≥0∞)) ≤ (C.initPotential : ℝ≥0∞) := by
      refine (tsum_le_tsum (g := fun p => ν₀ p * (C.initPotential : ℝ≥0∞)) fun p => ?_).trans ?_
      · by_cases hp : p ∈ ν₀.support
        · exact mul_le_mul' le_rfl (Nat.cast_le.mpr (hsupp₀ p hp).2.2.1)
        · rw [(PMF.apply_eq_zero_iff _ _).mpr hp, zero_mul]
          exact zero_le
      · rw [ENNReal.tsum_mul_right, ν₀.tsum_coe, one_mul]
    have hT_le : T_ops ≤ (C.initPotential : ℝ≥0∞) + (D.totalCost C.charge s₀ ops : ℝ≥0∞) := by
      calc T_ops
        _ ≤ T_ops + ∑' q, ν_final q * (C.potential q.1 q.2 : ℝ≥0∞) := le_self_add
        _ ≤ (D.totalCost C.charge s₀ ops : ℝ≥0∞) + ∑' p, ν₀ p * (C.potential p.1 p.2 : ℝ≥0∞) :=
            hamort
        _ ≤ (D.totalCost C.charge s₀ ops : ℝ≥0∞) + (C.initPotential : ℝ≥0∞) :=
            add_le_add le_rfl hpot₀
        _ = (C.initPotential : ℝ≥0∞) + (D.totalCost C.charge s₀ ops : ℝ≥0∞) := add_comm _ _
    have hT_fin : T_ops ≠ ⊤ :=
      ne_top_of_le_ne_top
        (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, ENNReal.natCast_ne_top _⟩) hT_le
    exact ⟨ν_final, T_ops, hT_le, hT_fin, hex.toExecFlatProgramOps C hv⟩

/-- **Bridge 3 (Las Vegas `WordRAM.Randomized.StateTransitionImpl` → `CellProbe.Randomized.Scheme`,
standard `w`-bit layout):**
Uniformly over all admissible histories over `opsAlphabet` of length `≤ M_corr` (without
`[Fintype D.Op]`), buffered finite-horizon simulation produces a single `P_cp` on
`C.space + persistentRegCount P` cells of width `w` preserving **100% zero-error transcript
correctness** with expected probes at most
`C.initPotential + D.totalCost C.charge s₀ ops + (2 * persistentRegCount P + η) * ops.length`. -/
theorem exists_cellProbe_lasVegas [∀ o, Inhabited (D.Result o)]
    (C : WordRAM.Randomized.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ P_cp :
        Cslib.CellProbe.Randomized.Scheme D.Op D.Result (C.space + persistentRegCount P) w,
      ∀ ops : List D.Op,
        D.ValidHistory s₀ ops →
        ops.length ≤ M_corr →
        (∀ o ∈ ops, o ∈ opsAlphabet) →
        (D.toObliviousSequenceSpec s₀).Contract ops ((P_cp.runSeq ops).map Prod.fst) ∧
          P_cp.expectedSeqProbes ops ≤
            (C.initPotential : ℝ≥0∞) + (D.totalCost C.charge s₀ ops : ℝ≥0∞) +
              (((2 * persistentRegCount P : ℕ) : ℝ≥0∞) + η) * (ops.length : ℝ≥0∞) := by
  obtain ⟨ν₀, hsupp₀, hsteps⟩ := C.exists_init_and_flat_steps hd₀ hfr hpar
  obtain ⟨P_cp, hP⟩ :=
    exists_cellProbe_of_flatPrograms (input := P.input) s₀ (P.code.program P.output) C.encode
      (fun o _ regs => C.decode o regs) ν₀ hsupp₀ opsAlphabet M_corr hη
  refine ⟨P_cp, fun ops hv hlen halph => ?_⟩
  obtain ⟨ν_final, T_ops, hT_le, hT_fin, hex⟩ := hsteps ops hv
  obtain ⟨hc, he⟩ := hP ops hv hlen halph hT_fin hex
  refine ⟨hc, he.trans ?_⟩
  rw [persistentRegCount_eq_persCount]
  exact add_le_add hT_le le_rfl

/-- **Wide-Cell Las Vegas Bridge (`exists_cellProbeWide_lasVegas`):**
Packs all persistent registers into `1` cell of width `wideSubroutineWidth P w` over `C.space + 1`
cells, incurring at most `2 + η` additive probes per operation regardless of `r_ds`. -/
theorem exists_cellProbeWide_lasVegas [∀ o, Inhabited (D.Result o)]
    (C : WordRAM.Randomized.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ P_cp :
        Cslib.CellProbe.Randomized.Scheme D.Op D.Result (C.space + 1) (wideSubroutineWidth P w),
      ∀ ops : List D.Op,
        D.ValidHistory s₀ ops →
        ops.length ≤ M_corr →
        (∀ o ∈ ops, o ∈ opsAlphabet) →
        (D.toObliviousSequenceSpec s₀).Contract ops ((P_cp.runSeq ops).map Prod.fst) ∧
          P_cp.expectedSeqProbes ops ≤
            (C.initPotential : ℝ≥0∞) + (D.totalCost C.charge s₀ ops : ℝ≥0∞) +
              (((if persistentRegCount P = 0 then 0 else 2 : ℕ) : ℝ≥0∞) + η) *
                (ops.length : ℝ≥0∞) := by
  obtain ⟨ν₀, hsupp₀, hsteps⟩ := C.exists_init_and_flat_steps hd₀ hfr hpar
  obtain ⟨P_cp, hP⟩ :=
    exists_cellProbeWide_of_flatPrograms (input := P.input) s₀ (P.code.program P.output) C.encode
      (fun o _ regs => C.decode o regs) ν₀ hsupp₀ opsAlphabet M_corr hη
  refine ⟨P_cp, fun ops hv hlen halph => ?_⟩
  obtain ⟨ν_final, T_ops, hT_le, hT_fin, hex⟩ := hsteps ops hv
  obtain ⟨hc, he⟩ := hP ops hv hlen halph hT_fin hex
  refine ⟨hc, he.trans ?_⟩
  rw [persistentRegCount_eq_persCount]
  exact add_le_add hT_le le_rfl

end Cslib.DataStructure.WordRAM.Randomized.StateTransitionImpl

namespace Cslib.DataStructure.CellProbe

universe u v

/-- **Contrapositive Deterministic-Cell-Probe-to-Word-RAM Lower-Bound Transfer
(`wordRAM_lower_bound_of_det_cellProbe_lower_bound`, standard `w`-bit layout):**
Any distributional probe lower bound `LB` proved against deterministic step-indexed
`IndexedScheme D.Op D.Result S_max w`s that are zero-error on `correctSeqs` (histories of length
`≤ M_corr` over `opsAlphabet`, without `[Fintype D.Op]`) transfers unconditionally to the certified
budget of every zero-error `WordRAM.Randomized.StateTransitionImpl` with
`C.space + persistentRegCount P ≤ S_max`, with **zero** `η` truncation loss (`0` extra cells and
`0` extra probes per operation when `∀ i, P.input i = true`). -/
theorem wordRAM_lower_bound_of_det_cellProbe_lower_bound
    {B : Basis} {r_ds k_init w base S_max : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {params : Fin k_init → ℕ} {s₀ : D.State}
    (C : WordRAM.Randomized.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (hspace : C.space + persistentRegCount P ≤ S_max)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    {LB : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme D.Op D.Result S_max w,
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) →
      LB ≤ ∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    LB ≤ (C.initPotential : ℝ≥0∞) +
      ∑' ops, hardDist ops *
        ((D.totalCost C.charge s₀ ops : ℝ≥0∞) +
          ((2 * persistentRegCount P : ℕ) : ℝ≥0∞) * (ops.length : ℝ≥0∞)) := by
  obtain ⟨ν₀, hsupp₀, hsteps⟩ := C.exists_init_and_flat_steps hd₀ hfr hpar
  have hraw :=
    flat_wordRAM_lower_bound_of_det_cellProbe (input := P.input) s₀ hspace
      (P.code.program P.output) C.encode (fun o _ regs => C.decode o regs) ν₀ hsupp₀
      opsAlphabet M_corr correctSeqs hcorrectSeqs
      (fun ops hops => by
        obtain ⟨ν_f, T_ops, _, hT_fin, hex⟩ := hsteps ops (hcorrectSeqs ops hops).1
        exact ⟨ν_f, T_ops, hT_fin, hex⟩)
      hardDist hhardDist
      (fun ops => (C.initPotential : ℝ≥0∞) + (D.totalCost C.charge s₀ ops : ℝ≥0∞))
      (fun ops hops => hsteps ops (hhardDist ops hops).1)
      hlb
  refine hraw.trans ?_
  have hrw : ∀ ops,
      hardDist ops *
          (((C.initPotential : ℝ≥0∞) + (D.totalCost C.charge s₀ ops : ℝ≥0∞)) +
            ((2 * persCount P.input : ℕ) : ℝ≥0∞) * (ops.length : ℝ≥0∞)) =
        hardDist ops * (C.initPotential : ℝ≥0∞) +
          hardDist ops *
            ((D.totalCost C.charge s₀ ops : ℝ≥0∞) +
              ((2 * persistentRegCount P : ℕ) : ℝ≥0∞) * (ops.length : ℝ≥0∞)) := by
    intro ops
    rw [persistentRegCount_eq_persCount, add_assoc, mul_add]
  simp_rw [hrw]
  rw [tsum_add, ENNReal.tsum_mul_right, hardDist.tsum_coe, one_mul]

set_option linter.unusedFintypeInType false in
/-- `[Fintype D.Op]` convenience specialization of
`wordRAM_lower_bound_of_det_cellProbe_lower_bound`, instantiating `opsAlphabet := Finset.univ`. -/
theorem wordRAM_lower_bound_of_det_cellProbe_of_fintype
    {B : Basis} {r_ds k_init w base S_max : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {D : StateTransitionSpec.{u, v, 0}} [Fintype D.Op]
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {params : Fin k_init → ℕ} {s₀ : D.State}
    (C : WordRAM.Randomized.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (hspace : C.space + persistentRegCount P ≤ S_max)
    (M_corr : ℕ) (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs, D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support, D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr)
    {LB : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme D.Op D.Result S_max w,
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) →
      LB ≤ ∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    LB ≤ (C.initPotential : ℝ≥0∞) +
      ∑' ops, hardDist ops *
        ((D.totalCost C.charge s₀ ops : ℝ≥0∞) +
          ((2 * persistentRegCount P : ℕ) : ℝ≥0∞) * (ops.length : ℝ≥0∞)) :=
  wordRAM_lower_bound_of_det_cellProbe_lower_bound C hd₀ hfr hpar hspace Finset.univ M_corr
    correctSeqs
    (fun ops hops => ⟨(hcorrectSeqs ops hops).1, (hcorrectSeqs ops hops).2,
      fun _ _ => Finset.mem_univ _⟩)
    hardDist
    (fun ops hops => ⟨(hhardDist ops hops).1, (hhardDist ops hops).2,
      fun _ _ => Finset.mem_univ _⟩)
    hlb

/-- **Wide-Cell Contrapositive Word-RAM Lower-Bound Transfer
(`wordRAM_lower_bound_of_det_cellProbe_wide`):**
Transfers any deterministic step-indexed cell-probe lower bound at cell width
`wideSubroutineWidth P w := max (persistentRegCount P) 1 * w` and space `S_max ≥ C.space + 1` to
arbitrary `r_ds`-register `WordRAM.Randomized.StateTransitionImpl`s with **at most `2` additive
probes per operation** (`0` when `persistentRegCount P = 0`) and **zero** `η` truncation loss! -/
theorem wordRAM_lower_bound_of_det_cellProbe_wide
    {B : Basis} {r_ds k_init w base S_max : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {params : Fin k_init → ℕ} {s₀ : D.State}
    (C : WordRAM.Randomized.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (hspace : C.space + 1 ≤ S_max)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    {LB : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme D.Op D.Result S_max (wideSubroutineWidth P w),
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) →
      LB ≤ ∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    LB ≤ (C.initPotential : ℝ≥0∞) +
      ∑' ops, hardDist ops *
        ((D.totalCost C.charge s₀ ops : ℝ≥0∞) + (2 : ℝ≥0∞) * (ops.length : ℝ≥0∞)) := by
  obtain ⟨ν₀, hsupp₀, hsteps⟩ := C.exists_init_and_flat_steps hd₀ hfr hpar
  have hraw :=
    flat_wordRAM_lower_bound_of_det_cellProbe_wide (input := P.input) s₀ hspace
      (P.code.program P.output) C.encode (fun o _ regs => C.decode o regs) ν₀ hsupp₀
      opsAlphabet M_corr correctSeqs hcorrectSeqs
      (fun ops hops => by
        obtain ⟨ν_f, T_ops, _, hT_fin, hex⟩ := hsteps ops (hcorrectSeqs ops hops).1
        exact ⟨ν_f, T_ops, hT_fin, hex⟩)
      hardDist hhardDist
      (fun ops => (C.initPotential : ℝ≥0∞) + (D.totalCost C.charge s₀ ops : ℝ≥0∞))
      (fun ops hops => hsteps ops (hhardDist ops hops).1)
      hlb
  refine hraw.trans ?_
  have hov_le : ((if persCount P.input = 0 then 0 else 2 : ℕ) : ℝ≥0∞) ≤ 2 := by
    split_ifs <;> norm_num
  have hpt : ∀ ops,
      hardDist ops *
          (((C.initPotential : ℝ≥0∞) + (D.totalCost C.charge s₀ ops : ℝ≥0∞)) +
            ((if persCount P.input = 0 then 0 else 2 : ℕ) : ℝ≥0∞) * (ops.length : ℝ≥0∞)) ≤
        hardDist ops * (C.initPotential : ℝ≥0∞) +
          hardDist ops *
            ((D.totalCost C.charge s₀ ops : ℝ≥0∞) + (2 : ℝ≥0∞) * (ops.length : ℝ≥0∞)) := by
    intro ops
    rw [add_assoc, mul_add]
    exact add_le_add le_rfl
      (mul_le_mul' le_rfl (add_le_add le_rfl (mul_le_mul' hov_le le_rfl)))
  refine (tsum_le_tsum hpt).trans ?_
  rw [tsum_add, ENNReal.tsum_mul_right, hardDist.tsum_coe, one_mul]

set_option linter.unusedFintypeInType false in
/-- `[Fintype D.Op]` convenience specialization of `wordRAM_lower_bound_of_det_cellProbe_wide`. -/
theorem wordRAM_lower_bound_of_det_cellProbe_wide_of_fintype
    {B : Basis} {r_ds k_init w base S_max : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {D : StateTransitionSpec.{u, v, 0}} [Fintype D.Op]
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {params : Fin k_init → ℕ} {s₀ : D.State}
    (C : WordRAM.Randomized.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (hspace : C.space + 1 ≤ S_max)
    (M_corr : ℕ) (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs, D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support, D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr)
    {LB : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme D.Op D.Result S_max (wideSubroutineWidth P w),
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) →
      LB ≤ ∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    LB ≤ (C.initPotential : ℝ≥0∞) +
      ∑' ops, hardDist ops *
        ((D.totalCost C.charge s₀ ops : ℝ≥0∞) + (2 : ℝ≥0∞) * (ops.length : ℝ≥0∞)) :=
  wordRAM_lower_bound_of_det_cellProbe_wide C hd₀ hfr hpar hspace Finset.univ M_corr correctSeqs
    (fun ops hops => ⟨(hcorrectSeqs ops hops).1, (hcorrectSeqs ops hops).2,
      fun _ _ => Finset.mem_univ _⟩)
    hardDist
    (fun ops hops => ⟨(hhardDist ops hops).1, (hhardDist ops hops).2,
      fun _ _ => Finset.mem_univ _⟩)
    hlb

end Cslib.DataStructure.CellProbe

/-! ### 4. `WordRAM.Randomized.ObliviousSequenceImpl` simulation and lower-bound transfer -/

namespace Cslib.DataStructure.WordRAM.Randomized

open Cslib.DataStructure.CellProbe

universe u z

/-- Finite-tree `ExecRand` step witness for an `ObliviousSequenceImpl`: strengthens `ExecSteps` by
witnessing a finite `ProbComp (Data r_ds × ℕ)` computation `mc t` (`ExecRand`) on each step rather
than an unbounded `ExecCodeDist` loop, enabling exact zero-slack `RandProbeTree` simulation on
arbitrary (including Monte Carlo) `ObliviousSequenceSpec`s. -/
inductive ExecStepsRand {B : Basis} {r_ds k_init : ℕ}
    (P : SubroutineCode B r_ds k_init)
    (S : DataStructure.ObliviousSequenceSpec.{u, 0})
    (Latent : Type z) (w base space : ℕ)
    (encode : S.Op → Fin r_ds → ℕ)
    (decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)) :
    List S.Op → PMF (SeqOutcome Latent S.Result r_ds) →
      PMF (SeqOutcome Latent S.Result r_ds) → ℝ≥0∞ → Prop where
  | nil (ν : PMF (SeqOutcome Latent S.Result r_ds)) :
      ExecStepsRand P S Latent w base space encode decode [] ν ν 0
  | cons {o : S.Op} {ops : List S.Op}
      {ν ν_final : PMF (SeqOutcome Latent S.Result r_ds)}
      {mc : SeqOutcome Latent S.Result r_ds → ProbComp (Data r_ds × ℕ)}
      {μ_step : SeqOutcome Latent S.Result r_ds → PMF (StepOutcome Latent (S.Result o) r_ds)}
      {T_rest : ℝ≥0∞} :
      (∀ t ∈ ν.support,
        t.data.Bounded w ∧
        (∀ i, P.input i = true → Fits w (encode o i)) ∧
        ExecRand w P.code ((P.toDynamicProgram encode decode).prepare o t.data) (mc t) ∧
        (mc t).eval.map Prod.fst = (μ_step t).map StepOutcome.data ∧
        ∀ q ∈ (μ_step t).support,
          q.data.Bounded w ∧
          decode o q.data.regs = some q.result ∧
          Modifies (Block.mk base space).footprint t.data.mem q.data.mem) →
      ExecStepsRand P S Latent w base space encode decode ops
        (ν.bind fun t => (μ_step t).map (t.appendStep o)) ν_final T_rest →
      ExecStepsRand P S Latent w base space encode decode (o :: ops) ν ν_final
        ((∑' t, ν t * ProbComp.expect (mc t) (fun z => (z.2 : ℝ≥0∞))) + T_rest)

/-- Predicate asserting that every admissible sequence on `C : ObliviousSequenceImpl` executes via
finite `ExecRand` computation trees (`ExecStepsRand`). -/
def ObliviousSequenceImpl.HasFiniteExecRand {B : Basis} {r_ds k_init w base : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {S : DataStructure.ObliviousSequenceSpec.{u, 0}}
    {params : Fin k_init → ℕ}
    (C : ObliviousSequenceImpl.{u, 0, z} P S w base params) : Prop :=
  ∀ (ops : List S.Op) (ν₀ : PMF (LatentState C.Latent r_ds)),
    S.ValidOpSeq ops → C.initInv ν₀ →
    ∃ (ν_final : PMF (SeqOutcome C.Latent S.Result r_ds)) (T_ops : ℝ≥0∞),
      ExecStepsRand P S C.Latent w base C.space C.encode C.decode ops
        (ν₀.map SeqOutcome.ofLatentState) ν_final T_ops ∧
      S.Contract ops (ν_final.map SeqOutcome.transcript) ∧
      T_ops ≤ (C.initPotential : ℝ≥0∞) + ((ops.map C.charge).sum : ℝ≥0∞)

private theorem simExecStepsRand_induction {B : Basis} {r_ds k_init regCells wCell w base space : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {S : DataStructure.ObliviousSequenceSpec.{u, 0}} [∀ o, Inhabited (S.Result o)]
    {Latent : Type z}
    {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    (L : RegLayout r_ds P.input base space w regCells wCell)
    (initMem : PMF (Mem (space + regCells) wCell))
    {ops : List S.Op} {ν ν_final : PMF (SeqOutcome Latent S.Result r_ds)} {T_ops : ℝ≥0∞}
    (hex : ExecStepsRand P S Latent w base space encode decode ops ν ν_final T_ops)
    (hsupp : ∀ t ∈ ν.support,
      t.data.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, t.data.mem a = 0) :
    let P_cp : Cslib.CellProbe.Randomized.Scheme S.Op S.Result (space + regCells) wCell :=
      { init := initMem
        step := fun o =>
          simProgRand (w := w) L (P.code.program P.output) (encode o)
            (fun _ regs => decode o regs) default (autoRandFuel L P.code (encode o)) }
    (ν.bind fun t =>
        ((P_cp.runFrom (L.pack t.data) ops).map Prod.fst).map (fun tm => t.transcript ++ tm.1)) =
      ν_final.map SeqOutcome.transcript ∧
    (∑' t, ν t * P_cp.expectedProbesFrom (L.pack t.data) ops) ≤
      T_ops + (L.overhead : ℝ≥0∞) * (ops.length : ℝ≥0∞) := by
  intro P_cp
  induction hex with
  | nil ν =>
    refine ⟨?_, by simp [Cslib.CellProbe.Randomized.Scheme.expectedProbesFrom]⟩
    simp only [Cslib.CellProbe.Randomized.Scheme.runFrom, PMF.pure_map, List.append_nil]
    ext tr
    simp [PMF.bind_apply, PMF.map_apply]
  | @cons o ops_rem ν ν_final mc μ_step T_rest hstep _ ih =>
    have hsupp₁ :
        ∀ t₁ ∈ (ν.bind fun t => (μ_step t).map (t.appendStep o)).support,
          t₁.data.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, t₁.data.mem a = 0 := by
      intro t₁ ht₁
      rw [PMF.mem_support_bind_iff] at ht₁
      obtain ⟨t, ht, hq_map⟩ := ht₁
      rw [PMF.mem_support_map_iff] at hq_map
      obtain ⟨q, hq, rfl⟩ := hq_map
      obtain ⟨hq_bdd, _, hmod⟩ := (hstep t ht).2.2.2.2 q hq
      exact ⟨hq_bdd, fun a ha => (hmod a ha).trans ((hsupp t ht).2 a ha)⟩
    obtain ⟨hlaw_rem, hexp_rem⟩ := ih hsupp₁
    have hstep_law : ∀ t ∈ ν.support,
        ((P_cp.step o).run (L.pack t.data)).map Prod.fst =
          (μ_step t).map (fun q => (q.result, L.pack q.data)) ∧
        (P_cp.step o).expectedProbes (L.pack t.data) ≤
          ProbComp.expect (mc t) (fun z => (z.2 : ℝ≥0∞)) + (L.overhead : ℝ≥0∞) := by
      intro t ht
      obtain ⟨ht_bdd, ht_out⟩ := hsupp t ht
      obtain ⟨_, harg, hexec_t, hmc_eq, hq_all⟩ := hstep t ht
      have hunp : L.unpack (encode o) (L.pack t.data) =
          (P.toDynamicProgram encode decode).prepare o t.data :=
        unpack_pack_eq_prepareFlatRegs L encode o ht_bdd ht_out
      rw [← hunp] at hexec_t
      obtain ⟨hlaw_sim, hexp_sim⟩ :=
        simExecRandLayout L P.code P.output (encode o) (decode o) (default : S.Result o)
          (L.validMem_pack t.data) harg hexec_t
      refine ⟨?_, hexp_sim⟩
      have hpush :
          (mc t).eval.map (fun z => ((decode o z.1.regs).getD default, L.pack z.1)) =
            ((mc t).eval.map Prod.fst).map
              (fun y => ((decode o y.regs).getD default, L.pack y)) := by
        rw [PMF.map_comp]
        rfl
      rw [hlaw_sim, hpush, hmc_eq, PMF.map_comp]
      ext am
      simp only [PMF.map_apply]
      dsimp only [Function.comp_apply]
      refine tsum_congr fun q => ?_
      by_cases hq : q ∈ (μ_step t).support
      · have hdec_eq : (decode o q.data.regs).getD default = q.result := by
          simp [(hq_all q hq).2.1]
        by_cases ham : am = (q.result, L.pack q.data)
        · have ham' : am = ((decode o q.data.regs).getD default, L.pack q.data) := by
            rwa [hdec_eq]
          rw [ite_eq_left ham', ite_eq_left ham]
        · have ham' : am ≠ ((decode o q.data.regs).getD default, L.pack q.data) := by
            rwa [hdec_eq]
          rw [ite_eq_right ham', ite_eq_right ham]
      · have hq0 : μ_step t q = 0 := (PMF.apply_eq_zero_iff _ _).mpr hq
        simp [hq0]
    refine ⟨?_, ?_⟩
    · rw [← hlaw_rem, PMF.bind_bind]
      ext tr_out
      simp only [PMF.bind_apply]
      refine tsum_congr fun t => ?_
      by_cases ht : t ∈ ν.support
      · refine congrArg (ν t * ·) ?_
        have h1 :
            (((P_cp.runFrom (L.pack t.data) (o :: ops_rem)).map Prod.fst).map
                (fun tm => t.transcript ++ tm.1)) =
              (((P_cp.step o).run (L.pack t.data)).map Prod.fst).bind fun am =>
                ((P_cp.runFrom am.2 ops_rem).map Prod.fst).map
                  (fun tm_r => t.transcript ++ (⟨o, am.1⟩ :: tm_r.1)) := by
          rw [Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl.runFrom_cons_fst,
            PMF.map_bind]
          refine congrArg ((((P_cp.step o).run (L.pack t.data)).map Prod.fst).bind ·)
            (funext fun ⟨a, m'⟩ => ?_)
          rw [PMF.map_comp]
          rfl
        rw [h1, (hstep_law t ht).1, PMF.bind_map, PMF.bind_apply,
          Probability.PMF.tsum_map_mul (μ_step t) (t.appendStep o)]
        refine tsum_congr fun q => congrArg (μ_step t q * ·) ?_
        dsimp only [Function.comp_def, SeqOutcome.appendStep]
        refine congrArg (fun f =>
            (PMF.map f ((P_cp.runFrom (L.pack q.data) ops_rem).map Prod.fst)) tr_out)
          (funext fun tm_r => ?_)
        simp [List.append_assoc]
      · rw [(PMF.apply_eq_zero_iff _ _).mpr ht, zero_mul, zero_mul]
    · have hpt : ∀ t,
          ν t * P_cp.expectedProbesFrom (L.pack t.data) (o :: ops_rem) ≤
            ν t * ProbComp.expect (mc t) (fun z => (z.2 : ℝ≥0∞)) +
              ν t * (L.overhead : ℝ≥0∞) +
              ν t * (∑' q, μ_step t q * P_cp.expectedProbesFrom (L.pack q.data) ops_rem) := by
        intro t
        by_cases ht : t ∈ ν.support
        · obtain ⟨hlaw_t, hexp_t⟩ := hstep_law t ht
          have hcons :
              P_cp.expectedProbesFrom (L.pack t.data) (o :: ops_rem) =
                (P_cp.step o).expectedProbes (L.pack t.data) +
                  ∑' q, μ_step t q * P_cp.expectedProbesFrom (L.pack q.data) ops_rem := by
            have hc1 :=
              Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl.expectedProbesFrom_cons
                P_cp (L.pack t.data) o ops_rem
            rw [hc1, hlaw_t, Probability.PMF.tsum_map_mul]
          have hle_t :
              P_cp.expectedProbesFrom (L.pack t.data) (o :: ops_rem) ≤
                ProbComp.expect (mc t) (fun z => (z.2 : ℝ≥0∞)) + (L.overhead : ℝ≥0∞) +
                  ∑' q, μ_step t q * P_cp.expectedProbesFrom (L.pack q.data) ops_rem := by
            rw [hcons]
            exact add_le_add hexp_t le_rfl
          simpa only [mul_add, add_assoc] using mul_le_mul' le_rfl hle_t
        · rw [(PMF.apply_eq_zero_iff _ _).mpr ht]
          simp
      have hbind_eq :
          (∑' t, ν t * ∑' q, μ_step t q * P_cp.expectedProbesFrom (L.pack q.data) ops_rem) =
            ∑' t₁, (ν.bind fun t => (μ_step t).map (t.appendStep o)) t₁ *
              P_cp.expectedProbesFrom (L.pack t₁.data) ops_rem := by
        rw [Probability.PMF.tsum_bind_mul]
        refine tsum_congr fun t => congrArg (ν t * ·) ?_
        exact (Probability.PMF.tsum_map_mul (μ_step t) (t.appendStep o)
          (fun t₁ => P_cp.expectedProbesFrom (L.pack t₁.data) ops_rem)).symm
      refine (tsum_le_tsum hpt).trans ?_
      rw [tsum_add, tsum_add, ENNReal.tsum_mul_right, ν.tsum_coe, one_mul, hbind_eq]
      calc (∑' t, ν t * ProbComp.expect (mc t) (fun z => (z.2 : ℝ≥0∞))) + (L.overhead : ℝ≥0∞) +
            ∑' t₁, (ν.bind fun t => (μ_step t).map (t.appendStep o)) t₁ *
              P_cp.expectedProbesFrom (L.pack t₁.data) ops_rem
        _ ≤ (∑' t, ν t * ProbComp.expect (mc t) (fun z => (z.2 : ℝ≥0∞))) + (L.overhead : ℝ≥0∞) +
              (T_rest + (L.overhead : ℝ≥0∞) * (ops_rem.length : ℝ≥0∞)) :=
            add_le_add le_rfl hexp_rem
        _ = ((∑' t, ν t * ProbComp.expect (mc t) (fun z => (z.2 : ℝ≥0∞))) + T_rest) +
              (L.overhead : ℝ≥0∞) * ((o :: ops_rem).length : ℝ≥0∞) := by
            simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
            ring

/-- **Bridge 2 (`ObliviousSequenceImpl.exists_cellProbe_of_execRand`, exact finite-tree
simulation):**
When `C : ObliviousSequenceImpl` satisfies `C.HasFiniteExecRand`, `C` induces a
`CellProbe.Randomized.ObliviousSequenceImpl` on `C.space + persistentRegCount P` cells of width `w`
reproducing the **exact** transcript distribution (`S.Contract ops` holds on arbitrary — including
Monte Carlo — `ObliviousSequenceSpec`s with `0` error distortion and `0` `η`-loss) and per-operation
probe charge `C.charge o + 2 * persistentRegCount P`. -/
theorem ObliviousSequenceImpl.exists_cellProbe_of_execRand
    {B : Basis} {r_ds k_init w base : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {S : DataStructure.ObliviousSequenceSpec.{u, 0}} [∀ o, Inhabited (S.Result o)]
    {params : Fin k_init → ℕ}
    (C : ObliviousSequenceImpl.{u, 0, z} P S w base params)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (hfin : C.HasFiniteExecRand) :
    ∃ P_cp :
        Cslib.CellProbe.Randomized.Scheme S.Op S.Result (C.space + persistentRegCount P) w,
      ∃ C_cp : Cslib.DataStructure.CellProbe.Randomized.ObliviousSequenceImpl S P_cp,
        C_cp.initPotential = C.initPotential ∧
        (∀ o, C_cp.charge o = C.charge o + 2 * persistentRegCount P) := by
  rw [persistentRegCount_eq_persCount]
  let L := standardLayout P.input base C.space w
  let d₀' : Data r_ds := { regs := d₀.regs, mem := fun _ => 0 }
  have hd₀' : d₀'.Bounded w := ⟨hd₀.1, fun _ => fits_zero w⟩
  obtain ⟨ν₀, _, hinv₀, hsupp₀⟩ := C.initFresh_exec hd₀' hfr hpar (fun _ _ => rfl)
  set ν₀_seq := ν₀.map (SeqOutcome.ofLatentState (Result := S.Result))
  have hsupp_seq : ∀ t ∈ ν₀_seq.support,
      t.data.Bounded w ∧ ∀ a ∉ (Block.mk base C.space).footprint, t.data.mem a = 0 := by
    intro t ht
    rw [PMF.mem_support_map_iff] at ht
    obtain ⟨z₀, hz₀, rfl⟩ := ht
    obtain ⟨hbdd, _, hmod⟩ := hsupp₀ z₀ hz₀
    exact ⟨hbdd, fun a ha => hmod a ha⟩
  let P_cp : Cslib.CellProbe.Randomized.Scheme S.Op S.Result (C.space + persCount P.input) w :=
    { init := ν₀_seq.map fun t => L.pack t.data
      step := fun o =>
        simProgRand (w := w) L (P.code.program P.output) (C.encode o)
          (fun _ regs => C.decode o regs) default (autoRandFuel L P.code (C.encode o)) }
  refine ⟨P_cp, ⟨{
    initPotential := C.initPotential
    charge := fun o => C.charge o + 2 * persCount P.input
    contract_runSeq := ?_
    expectedSeqProbes_le := ?_
  }, rfl, fun _ => rfl⟩⟩
  · intro ops hv
    obtain ⟨ν_final, T_ops, hex, hcontract, _⟩ := hfin ops ν₀ hv hinv₀
    change ExecStepsRand P S C.Latent w base C.space C.encode C.decode ops ν₀_seq ν_final T_ops
      at hex
    obtain ⟨hlaw, _⟩ :=
      simExecStepsRand_induction L (ν₀_seq.map fun t => L.pack t.data) hex hsupp_seq
    have hrun_eq : (P_cp.runSeq ops).map Prod.fst = ν_final.map SeqOutcome.transcript := by
      rw [← hlaw, Cslib.CellProbe.Randomized.Scheme.runSeq]
      dsimp only [P_cp]
      rw [PMF.map_bind, PMF.bind_map]
      ext out_tr
      simp only [PMF.bind_apply, Function.comp_apply]
      refine tsum_congr fun t => ?_
      by_cases ht : t ∈ ν₀_seq.support
      · have hnil : t.transcript = [] := by
          dsimp only [ν₀_seq] at ht
          rw [PMF.mem_support_map_iff] at ht
          obtain ⟨_, _, rfl⟩ := ht
          rfl
        rw [hnil]
        simp only [PMF.map_comp]
        refine congrArg (_ * ·)
          (congrArg (fun f => (PMF.map f _) out_tr)
            (funext fun ⟨⟨_, _⟩, _⟩ => rfl))
      · rw [(PMF.apply_eq_zero_iff _ _).mpr ht, zero_mul, zero_mul]
    exact hrun_eq ▸ hcontract
  · intro ops hv
    obtain ⟨ν_final, T_ops, hex, _, hcost⟩ := hfin ops ν₀ hv hinv₀
    change ExecStepsRand P S C.Latent w base C.space C.encode C.decode ops ν₀_seq ν_final T_ops
      at hex
    obtain ⟨_, hexp⟩ :=
      simExecStepsRand_induction L (ν₀_seq.map fun t => L.pack t.data) hex hsupp_seq
    rw [Cslib.CellProbe.Randomized.Scheme.expectedSeqProbes_eq_init_tsum]
    dsimp only [P_cp]
    rw [Probability.PMF.tsum_map_mul]
    refine hexp.trans ?_
    have hsum_eq : ∀ l : List S.Op,
        ((l.map fun o => C.charge o + 2 * persCount P.input).sum : ℕ) =
          (l.map C.charge).sum + 2 * persCount P.input * l.length := by
      intro l
      induction l with
      | nil => simp
      | cons o os ih =>
        rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, List.length_cons, ih]
        ring
    rw [hsum_eq ops, Nat.cast_add, Nat.cast_mul]
    calc T_ops + (L.overhead : ℝ≥0∞) * (ops.length : ℝ≥0∞)
      _ ≤ ((C.initPotential : ℝ≥0∞) + ((ops.map C.charge).sum : ℝ≥0∞)) +
            ((2 * persCount P.input : ℕ) : ℝ≥0∞) * (ops.length : ℝ≥0∞) := by
          rw [standardLayout_overhead]
          exact add_le_add hcost le_rfl
      _ = (C.initPotential : ℝ≥0∞) +
            (((ops.map C.charge).sum : ℝ≥0∞) +
              ((2 * persCount P.input : ℕ) : ℝ≥0∞) * (ops.length : ℝ≥0∞)) := by ac_rfl

private theorem simExecStepsLasVegas_induction
    {B : Basis} {r_ds k_init regCells wCell w base space : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {S : DataStructure.ObliviousSequenceSpec.{u, 0}} [∀ o, Inhabited (S.Result o)]
    {Latent : Type z}
    {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    (L : RegLayout r_ds P.input base space w regCells wCell)
    (initMem : PMF (Mem (space + regCells) wCell))
    (opsAlphabet : Finset S.Op) (M_corr K : ℕ) (η : ℝ≥0∞)
    (hK_tail : ∀ o ∈ opsAlphabet, ∀ m : Mem (space + regCells) wCell,
      (∃ μ_p : PMF (ℕ × Data r_ds), ∃ T_p : ℝ≥0∞, T_p ≠ ⊤ ∧
        ExecProgramDist w (P.code.program P.output) (L.unpack (encode o) m) μ_p (T_p + 1)) →
      (evalRand w (P.code.program P.output) K ⟨0, L.unpack (encode o) m⟩).toOuterMeasure
          (RandCfg.runningSet r_ds) *
        ((((2 * space + regCells) + M_corr * (2 * space + regCells + L.overhead) : ℕ) : ℝ≥0∞) +
          (M_corr : ℝ≥0∞) * (K : ℝ≥0∞)) ≤ η)
    {ops : List S.Op} {ν ν_final : PMF (SeqOutcome Latent S.Result r_ds)} {T_ops : ℝ≥0∞}
    (hex : ExecSteps P S Latent w base space encode decode ops ν ν_final T_ops)
    (hlen : ops.length ≤ M_corr)
    (halph : ∀ o ∈ ops, o ∈ opsAlphabet)
    (hT_fin : T_ops ≠ ⊤)
    (hsupp : ∀ t ∈ ν.support,
      t.data.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, t.data.mem a = 0) :
    let P_cp : Cslib.CellProbe.Randomized.Scheme S.Op S.Result (space + regCells) wCell :=
      { init := initMem
        step := fun o =>
          simProgRand (w := w) L (P.code.program P.output) (encode o)
            (fun _ regs => decode o regs) default K }
    (∀ t ∈ ν.support, ∀ tm ∈ ((P_cp.runFrom (L.pack t.data) ops).map Prod.fst).support,
      t.transcript ++ tm.1 ∈ (ν_final.map SeqOutcome.transcript).support) ∧
    (∑' t, ν t * P_cp.expectedProbesFrom (L.pack t.data) ops) ≤
      T_ops + ((L.overhead : ℝ≥0∞) + η) * (ops.length : ℝ≥0∞) := by
  intro P_cp
  set p_op := P.code.program P.output
  set W_step : ℝ≥0∞ := ((K + 2 * space + regCells + L.overhead : ℕ) : ℝ≥0∞)
  have hW_step : ∀ o m, (P_cp.step o).expectedProbes m ≤ W_step := fun o m =>
    simProgRand_expectedProbes_le_worstCase L p_op (encode o) (fun _ regs => decode o regs)
      default K m
  induction hex with
  | nil ν =>
    refine ⟨fun t ht tm htm => ?_, by simp [Cslib.CellProbe.Randomized.Scheme.expectedProbesFrom]⟩
    simp only [Cslib.CellProbe.Randomized.Scheme.runFrom, PMF.pure_map, PMF.support_pure,
      Set.mem_singleton_iff] at htm
    rw [htm, List.append_nil]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨t, ht, rfl⟩
  | @cons o ops_rem ν ν_final μ_step T_step T_rest hstep _ ih =>
    have ho_alph : o ∈ opsAlphabet := halph o List.mem_cons_self
    have halph_rem : ∀ o' ∈ ops_rem, o' ∈ opsAlphabet :=
      fun o' ho' => halph o' (List.mem_cons_of_mem o ho')
    have hlen_rem : ops_rem.length ≤ M_corr := Nat.le_of_succ_le hlen
    have hsum_fin : (∑' t, ν t * T_step t) ≠ ⊤ := ne_top_of_le_ne_top hT_fin le_self_add
    have hT_rest_fin : T_rest ≠ ⊤ := ne_top_of_le_ne_top hT_fin le_add_self
    have hsupp₁ :
        ∀ t₁ ∈ (ν.bind fun t => (μ_step t).map (t.appendStep o)).support,
          t₁.data.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, t₁.data.mem a = 0 := by
      intro t₁ ht₁
      rw [PMF.mem_support_bind_iff] at ht₁
      obtain ⟨t, ht, hq_map⟩ := ht₁
      rw [PMF.mem_support_map_iff] at hq_map
      obtain ⟨q, hq, rfl⟩ := hq_map
      obtain ⟨hq_bdd, _, hmod⟩ := (hstep t ht).2.2.2.2 q hq
      exact ⟨hq_bdd, fun a ha => (hmod a ha).trans ((hsupp t ht).2 a ha)⟩
    obtain ⟨hcorr_rem, hexp_rem⟩ := ih hlen_rem halph_rem hT_rest_fin hsupp₁
    refine ⟨?_, ?_⟩
    · intro t ht tm htm
      rw [Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl.runFrom_cons_fst,
        PMF.mem_support_bind_iff] at htm
      obtain ⟨z₁, hz₁, htm_rem⟩ := htm
      rw [PMF.mem_support_map_iff] at hz₁
      obtain ⟨z_full, hz_full, rfl⟩ := hz₁
      rw [PMF.mem_support_map_iff] at htm_rem
      obtain ⟨tm_rem, htm_rem_mem, rfl⟩ := htm_rem
      obtain ⟨ht_bdd, ht_out⟩ := hsupp t ht
      obtain ⟨_, harg, _, hcdist, hq_all⟩ := hstep t ht
      have hunp : L.unpack (encode o) (L.pack t.data) =
          (P.toDynamicProgram encode decode).prepare o t.data :=
        unpack_pack_eq_prepareFlatRegs L encode o ht_bdd ht_out
      rw [← hunp] at hcdist
      have hpdist := execProgramDist_of_execCodeDist hcdist P.output
      obtain ⟨hsup_sim, _, _⟩ :=
        simProgRand_lasVegas_spec L p_op (encode o) (fun _ regs => decode o regs)
          (default : S.Result o) K (L.validMem_pack t.data) harg hpdist
      obtain ⟨vy, hvy, hz₁_eq⟩ := hsup_sim z_full hz_full
      rw [PMF.mem_support_map_iff] at hvy
      obtain ⟨y, hy_mem, rfl⟩ := hvy
      rw [PMF.mem_support_map_iff] at hy_mem
      obtain ⟨q, hq, rfl⟩ := hy_mem
      obtain ⟨_, hdec_q, _⟩ := hq_all q hq
      have hz₁_ans : z_full.1.1 = q.result := by
        have h1 := congrArg Prod.fst hz₁_eq
        simpa [hdec_q] using h1
      have hz₁_mem : z_full.1.2 = L.pack q.data := congrArg Prod.snd hz₁_eq
      rw [hz₁_mem] at htm_rem_mem
      have ht₁_mem : t.appendStep o q ∈
          (ν.bind fun t' => (μ_step t').map (t'.appendStep o)).support := by
        rw [PMF.mem_support_bind_iff]
        exact ⟨t, ht, (PMF.mem_support_map_iff _ _ _).mpr ⟨q, hq, rfl⟩⟩
      have hmem_fin := hcorr_rem (t.appendStep o q) ht₁_mem tm_rem htm_rem_mem
      simpa only [SeqOutcome.appendStep, List.append_assoc, List.singleton_append, hz₁_ans]
        using hmem_fin
    · set B_rem : ℝ≥0∞ := (M_corr : ℝ≥0∞) * W_step
      have hB_rem_eq :
          ((2 * space + regCells : ℕ) : ℝ≥0∞) + B_rem =
            (((2 * space + regCells) + M_corr * (2 * space + regCells + L.overhead) : ℕ) : ℝ≥0∞) +
              (M_corr : ℝ≥0∞) * (K : ℝ≥0∞) := by
        dsimp only [B_rem, W_step]
        push_cast
        ring
      have hpt : ∀ t,
          ν t * P_cp.expectedProbesFrom (L.pack t.data) (o :: ops_rem) ≤
            ν t * T_step t +
              ν t * ((L.overhead : ℝ≥0∞) + η) +
              ν t * (∑' q, μ_step t q * P_cp.expectedProbesFrom (L.pack q.data) ops_rem) := by
        intro t
        by_cases ht : t ∈ ν.support
        · obtain ⟨ht_bdd, ht_out⟩ := hsupp t ht
          obtain ⟨_, harg, _, hcdist, _⟩ := hstep t ht
          have hTt_fin : T_step t ≠ ⊤ := by
            intro htop
            have hle_sum : ν t * T_step t ≤ ∑' t', ν t' * T_step t' := by
              rw [tsum_eq_iSup_sum]
              simpa using le_iSup
                (fun s : Finset (SeqOutcome Latent S.Result r_ds) => ∑ t' ∈ s, ν t' * T_step t')
                {t}
            have hνt_ne : ν t ≠ 0 := (PMF.mem_support_iff _ _).mp ht
            rw [htop, ENNReal.mul_top hνt_ne, top_le_iff] at hle_sum
            exact hsum_fin hle_sum
          have hunp : L.unpack (encode o) (L.pack t.data) =
              (P.toDynamicProgram encode decode).prepare o t.data :=
            unpack_pack_eq_prepareFlatRegs L encode o ht_bdd ht_out
          rw [← hunp] at hcdist
          have hpdist := execProgramDist_of_execCodeDist hcdist P.output
          obtain ⟨_, hexp_sim, hcoupl⟩ :=
            simProgRand_lasVegas_spec L p_op (encode o) (fun _ regs => decode o regs)
              (default : S.Result o) K (L.validMem_pack t.data) harg hpdist
          have hcont_le :
              (∑ k ∈ Finset.range K,
                  (evalRand w p_op k ⟨0, L.unpack (encode o) (L.pack t.data)⟩).toOuterMeasure
                    {cfg | isContinuingCfg p_op cfg = true}) ≤ T_step t :=
            continuing_sum_le_of_almostSurelyHalts hpdist.almostSurelyHalts hpdist.1 K
          have hg_bound : ∀ om ∈ (((P_cp.step o).run (L.pack t.data)).map Prod.fst).support,
              P_cp.expectedProbesFrom om.2 ops_rem ≤ B_rem := fun om _ =>
            (expectedProbesFrom_le_mul P_cp W_step hW_step ops_rem om.2).trans
              (mul_le_mul' (Nat.cast_le.mpr hlen_rem) le_rfl)
          have hcoupl_rem := hcoupl (fun om => P_cp.expectedProbesFrom om.2 ops_rem) B_rem hg_bound
          rw [Probability.PMF.tsum_map_mul ((μ_step t).map StepOutcome.data),
            Probability.PMF.tsum_map_mul (μ_step t) StepOutcome.data] at hcoupl_rem
          dsimp only at hcoupl_rem
          have hcons_eq :
              P_cp.expectedProbesFrom (L.pack t.data) (o :: ops_rem) =
                (P_cp.step o).expectedProbes (L.pack t.data) +
                  ∑' om, (((P_cp.step o).run (L.pack t.data)).map Prod.fst) om *
                    P_cp.expectedProbesFrom om.2 ops_rem :=
            Cslib.DataStructure.CellProbe.Randomized.StateTransitionImpl.expectedProbesFrom_cons
              P_cp (L.pack t.data) o ops_rem
          have htail_le :
              (evalRand w p_op K ⟨0, L.unpack (encode o) (L.pack t.data)⟩).toOuterMeasure
                  (RandCfg.runningSet r_ds) *
                (((2 * space + regCells : ℕ) : ℝ≥0∞) + B_rem) ≤ η := by
            rw [hB_rem_eq]
            exact hK_tail o ho_alph (L.pack t.data) ⟨_, T_step t, hTt_fin, hpdist⟩
          have htot_t :
              P_cp.expectedProbesFrom (L.pack t.data) (o :: ops_rem) ≤
                T_step t + ((L.overhead : ℝ≥0∞) + η) +
                  ∑' q, μ_step t q * P_cp.expectedProbesFrom (L.pack q.data) ops_rem := by
            rw [hcons_eq]
            set p_run :=
              (evalRand w p_op K ⟨0, L.unpack (encode o) (L.pack t.data)⟩).toOuterMeasure
                (RandCfg.runningSet r_ds)
            calc (P_cp.step o).expectedProbes (L.pack t.data) +
                  ∑' om, (((P_cp.step o).run (L.pack t.data)).map Prod.fst) om *
                    P_cp.expectedProbesFrom om.2 ops_rem
              _ ≤ (T_step t + (L.overhead : ℝ≥0∞) +
                    p_run * ((2 * space + regCells : ℕ) : ℝ≥0∞)) +
                  ((∑' q, μ_step t q * P_cp.expectedProbesFrom (L.pack q.data) ops_rem) +
                    p_run * B_rem) :=
                  add_le_add (hexp_sim.trans (add_le_add (add_le_add hcont_le le_rfl) le_rfl))
                    hcoupl_rem
              _ = T_step t + (L.overhead : ℝ≥0∞) +
                    (∑' q, μ_step t q * P_cp.expectedProbesFrom (L.pack q.data) ops_rem) +
                    p_run * (((2 * space + regCells : ℕ) : ℝ≥0∞) + B_rem) := by ring
              _ ≤ T_step t + (L.overhead : ℝ≥0∞) +
                    (∑' q, μ_step t q * P_cp.expectedProbesFrom (L.pack q.data) ops_rem) + η :=
                  add_le_add le_rfl htail_le
              _ = T_step t + ((L.overhead : ℝ≥0∞) + η) +
                    ∑' q, μ_step t q * P_cp.expectedProbesFrom (L.pack q.data) ops_rem := by ac_rfl
          simpa only [mul_add, add_assoc] using mul_le_mul' le_rfl htot_t
        · rw [(PMF.apply_eq_zero_iff _ _).mpr ht]
          simp
      have hbind_eq :
          (∑' t, ν t * ∑' q, μ_step t q * P_cp.expectedProbesFrom (L.pack q.data) ops_rem) =
            ∑' t₁, (ν.bind fun t => (μ_step t).map (t.appendStep o)) t₁ *
              P_cp.expectedProbesFrom (L.pack t₁.data) ops_rem := by
        rw [Probability.PMF.tsum_bind_mul]
        refine tsum_congr fun t => congrArg (ν t * ·) ?_
        exact (Probability.PMF.tsum_map_mul (μ_step t) (t.appendStep o)
          (fun t₁ => P_cp.expectedProbesFrom (L.pack t₁.data) ops_rem)).symm
      refine (tsum_le_tsum hpt).trans ?_
      rw [tsum_add, tsum_add, ENNReal.tsum_mul_right, ν.tsum_coe, one_mul, hbind_eq]
      calc (∑' t, ν t * T_step t) + ((L.overhead : ℝ≥0∞) + η) +
            ∑' t₁, (ν.bind fun t => (μ_step t).map (t.appendStep o)) t₁ *
              P_cp.expectedProbesFrom (L.pack t₁.data) ops_rem
        _ ≤ (∑' t, ν t * T_step t) + ((L.overhead : ℝ≥0∞) + η) +
              (T_rest + ((L.overhead : ℝ≥0∞) + η) * (ops_rem.length : ℝ≥0∞)) :=
            add_le_add le_rfl hexp_rem
        _ = ((∑' t, ν t * T_step t) + T_rest) +
              ((L.overhead : ℝ≥0∞) + η) * ((o :: ops_rem).length : ℝ≥0∞) := by
            simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
            ring

end Cslib.DataStructure.WordRAM.Randomized

namespace Cslib.DataStructure.WordRAM.Randomized.ObliviousSequenceImpl

open Cslib.DataStructure.CellProbe

universe u v z

/-- Layout-parametric buffered Las Vegas simulation of any `ObliviousSequenceImpl` over
`D.toObliviousSequenceSpec s₀` (even for nondeterministic relational `D`, without `[D.HasStepFn f]`
or `[Fintype D.Op]`). -/
theorem exists_cellProbeLayout_lasVegas
    {B : Basis} {r_ds k_init regCells wCell w base : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {D : StateTransitionSpec.{u, v, 0}} [∀ o, Inhabited (D.Result o)]
    {params : Fin k_init → ℕ} {s₀ : D.State}
    (C : ObliviousSequenceImpl.{v, 0, z} P (D.toObliviousSequenceSpec s₀) w base params)
    (L : RegLayout r_ds P.input base C.space w regCells wCell)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ P_cp : Cslib.CellProbe.Randomized.Scheme D.Op D.Result (C.space + regCells) wCell,
      ∀ ops : List D.Op,
        D.ValidOpSeq s₀ ops →
        ops.length ≤ M_corr →
        (∀ o ∈ ops, o ∈ opsAlphabet) →
        (D.toObliviousSequenceSpec s₀).Contract ops ((P_cp.runSeq ops).map Prod.fst) ∧
          P_cp.expectedSeqProbes ops ≤
            (C.initPotential : ℝ≥0∞) + ((ops.map C.charge).sum : ℝ≥0∞) +
              ((L.overhead : ℝ≥0∞) + η) * (ops.length : ℝ≥0∞) := by
  let d₀' : Data r_ds := { regs := d₀.regs, mem := fun _ => 0 }
  have hd₀' : d₀'.Bounded w := ⟨hd₀.1, fun _ => fits_zero w⟩
  obtain ⟨ν₀, _, hinv₀, hsupp₀⟩ := C.initFresh_exec hd₀' hfr hpar (fun _ _ => rfl)
  let ν₀_seq := ν₀.map (SeqOutcome.ofLatentState (Result := D.Result))
  have hsupp_seq : ∀ t ∈ ν₀_seq.support,
      t.data.Bounded w ∧ ∀ a ∉ (Block.mk base C.space).footprint, t.data.mem a = 0 := by
    intro t ht
    rw [PMF.mem_support_map_iff] at ht
    obtain ⟨z₀, hz₀, rfl⟩ := ht
    obtain ⟨hbdd, _, hmod⟩ := hsupp₀ z₀ hz₀
    exact ⟨hbdd, fun a ha => hmod a ha⟩
  set p_op := P.code.program P.output
  let Good : D.Op → Mem (C.space + regCells) wCell → Prop := fun o m =>
    ∃ μ_p : PMF (ℕ × Data r_ds), ∃ T_p : ℝ≥0∞, T_p ≠ ⊤ ∧
      ExecProgramDist w p_op (L.unpack (C.encode o) m) μ_p (T_p + 1)
  have hGood_fin : ∀ o ∈ opsAlphabet, ∀ m, Good o m →
      expectedTime w p_op ⟨0, L.unpack (C.encode o) m⟩ ≠ ⊤ := by
    rintro o _ m ⟨μ_p, T_p, hTp_fin, hpdist⟩
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hTp_fin, ENNReal.one_ne_top⟩) hpdist.1
  obtain ⟨K, _, hK_tail⟩ := exists_uniform_cutoff L opsAlphabet Good (fun _ => p_op) C.encode
    hGood_fin ((2 * C.space + regCells) + M_corr * (2 * C.space + regCells + L.overhead)) M_corr hη
  let P_cp : Cslib.CellProbe.Randomized.Scheme D.Op D.Result (C.space + regCells) wCell :=
    { init := ν₀_seq.map fun t => L.pack t.data
      step := fun o =>
        simProgRand (w := w) L p_op (C.encode o) (fun _ regs => C.decode o regs) default K }
  refine ⟨P_cp, fun ops hv hlen halph => ?_⟩
  obtain ⟨ν_final, T_ops, hex, hcontract, hcost⟩ := C.steps_exec ops ν₀ hv hinv₀
  have hT_fin : T_ops ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, ENNReal.natCast_ne_top _⟩) hcost
  obtain ⟨hcorr, hexp⟩ :=
    simExecStepsLasVegas_induction L (ν₀_seq.map fun t => L.pack t.data) opsAlphabet M_corr K η
      hK_tail hex hlen halph hT_fin hsupp_seq
  refine ⟨?_, ?_⟩
  · intro out hout
    rw [Cslib.CellProbe.Randomized.Scheme.runSeq, PMF.map_bind, PMF.mem_support_bind_iff] at hout
    obtain ⟨m₀, hm₀, hout_from⟩ := hout
    rw [PMF.mem_support_map_iff] at hm₀
    obtain ⟨t, ht, rfl⟩ := hm₀
    rw [PMF.map_comp, PMF.mem_support_map_iff] at hout_from
    obtain ⟨z_fin, htm, hout_eq⟩ := hout_from
    rcases z_fin with ⟨⟨tr, m_fin⟩, pr⟩
    dsimp only [Function.comp_apply] at hout_eq
    subst hout_eq
    have hnil : t.transcript = [] := by
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨_, _, rfl⟩ := ht
      rfl
    have hmem_ideal :=
      hcorr t ht (tr, m_fin) ((PMF.mem_support_map_iff _ _ _).mpr ⟨((tr, m_fin), pr), htm, rfl⟩)
    rw [hnil, List.nil_append] at hmem_ideal
    exact hcontract tr hmem_ideal
  · rw [Cslib.CellProbe.Randomized.Scheme.expectedSeqProbes_eq_init_tsum]
    dsimp only [P_cp]
    rw [Probability.PMF.tsum_map_mul]
    exact hexp.trans (add_le_add hcost le_rfl)

/-- Standard `w`-bit Las Vegas simulation of any zero-error `ObliviousSequenceImpl` over
`D.toObliviousSequenceSpec s₀`. -/
theorem exists_cellProbe_lasVegas
    {B : Basis} {r_ds k_init w base : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {D : StateTransitionSpec.{u, v, 0}} [∀ o, Inhabited (D.Result o)]
    {params : Fin k_init → ℕ} {s₀ : D.State}
    (C : ObliviousSequenceImpl.{v, 0, z} P (D.toObliviousSequenceSpec s₀) w base params)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ P_cp :
        Cslib.CellProbe.Randomized.Scheme D.Op D.Result (C.space + persistentRegCount P) w,
      ∀ ops : List D.Op,
        D.ValidOpSeq s₀ ops →
        ops.length ≤ M_corr →
        (∀ o ∈ ops, o ∈ opsAlphabet) →
        (D.toObliviousSequenceSpec s₀).Contract ops ((P_cp.runSeq ops).map Prod.fst) ∧
          P_cp.expectedSeqProbes ops ≤
            (C.initPotential : ℝ≥0∞) + ((ops.map C.charge).sum : ℝ≥0∞) +
              (((2 * persistentRegCount P : ℕ) : ℝ≥0∞) + η) * (ops.length : ℝ≥0∞) := by
  obtain ⟨P_cp, hP⟩ := C.exists_cellProbeLayout_lasVegas (standardLayout P.input base C.space w)
    hd₀ hfr hpar opsAlphabet M_corr hη
  refine ⟨P_cp, fun ops hv hlen halph => ?_⟩
  obtain ⟨hc, he⟩ := hP ops hv hlen halph
  refine ⟨hc, he.trans ?_⟩
  rw [standardLayout_overhead, ← persistentRegCount_eq_persCount]

end Cslib.DataStructure.WordRAM.Randomized.ObliviousSequenceImpl

namespace Cslib.DataStructure.CellProbe

universe u v z

private theorem oblivious_lower_bound_layout
    {B : Basis} {r_ds k_init regCells wCell w base S_max : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {params : Fin k_init → ℕ} {s₀ : D.State}
    (C : WordRAM.Randomized.ObliviousSequenceImpl.{v, 0, z}
      P (D.toObliviousSequenceSpec s₀) w base params)
    (L : RegLayout r_ds P.input base C.space w regCells wCell)
    (hspace : C.space + regCells ≤ S_max)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    {LB : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme D.Op D.Result S_max wCell,
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) →
      LB ≤ ∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    LB ≤ (C.initPotential : ℝ≥0∞) +
      ∑' ops, hardDist ops *
        (((ops.map C.charge).sum : ℝ≥0∞) + (L.overhead : ℝ≥0∞) * (ops.length : ℝ≥0∞)) := by
  classical
  have _ : ∀ o, Inhabited (D.Result o) := fun o => ⟨(f s₀ o).2⟩
  refine le_of_forall_pos_le_add_mul (M := M_corr) fun {η} hη => ?_
  obtain ⟨P_raw, hP_raw⟩ :=
    C.exists_cellProbeLayout_lasVegas L hd₀ hfr hpar opsAlphabet M_corr hη
  let P_pad := P_raw.padCells hspace
  have hcorr_pad : ∀ ops ∈ correctSeqs,
      (D.toObliviousSequenceSpec s₀).Contract ops ((P_pad.runSeq ops).map Prod.fst) := by
    intro ops hops
    obtain ⟨hv, hlen, halph⟩ := hcorrectSeqs ops hops
    rw [Cslib.CellProbe.Randomized.Scheme.runSeq_padCells]
    exact (hP_raw ops ((D.validOpSeq_iff_validHistory s₀ ops).mpr hv) hlen halph).1
  obtain ⟨D_det, _, hD_corr, hD_probes⟩ :=
    Cslib.DataStructure.CellProbe.Randomized.exists_det_indexedScheme_le_expectedSeqProbes
      s₀ P_pad opsAlphabet M_corr correctSeqs hcorrectSeqs hcorr_pad hardDist
      (fun ops hops => (hhardDist ops hops).2)
  refine (hlb D_det hD_corr).trans (hD_probes.trans ?_)
  have hpt : ∀ ops,
      hardDist ops * P_pad.expectedSeqProbes ops ≤
        hardDist ops * (C.initPotential : ℝ≥0∞) +
          hardDist ops *
            (((ops.map C.charge).sum : ℝ≥0∞) + (L.overhead : ℝ≥0∞) * (ops.length : ℝ≥0∞)) +
          hardDist ops * (η * (M_corr : ℝ≥0∞)) := by
    intro ops
    by_cases hops : ops ∈ hardDist.support
    · obtain ⟨hv, hlen, halph⟩ := hhardDist ops hops
      rw [Cslib.CellProbe.Randomized.Scheme.expectedSeqProbes_padCells]
      have hexp := (hP_raw ops ((D.validOpSeq_iff_validHistory s₀ ops).mpr hv) hlen halph).2
      have h1 :
          P_raw.expectedSeqProbes ops ≤
            (C.initPotential : ℝ≥0∞) +
              (((ops.map C.charge).sum : ℝ≥0∞) + (L.overhead : ℝ≥0∞) * (ops.length : ℝ≥0∞)) +
              η * (M_corr : ℝ≥0∞) := by
        calc P_raw.expectedSeqProbes ops
          _ ≤ (C.initPotential : ℝ≥0∞) + ((ops.map C.charge).sum : ℝ≥0∞) +
                ((L.overhead : ℝ≥0∞) + η) * (ops.length : ℝ≥0∞) := hexp
          _ = (C.initPotential : ℝ≥0∞) +
                (((ops.map C.charge).sum : ℝ≥0∞) + (L.overhead : ℝ≥0∞) * (ops.length : ℝ≥0∞)) +
                η * (ops.length : ℝ≥0∞) := by ring
          _ ≤ (C.initPotential : ℝ≥0∞) +
                (((ops.map C.charge).sum : ℝ≥0∞) + (L.overhead : ℝ≥0∞) * (ops.length : ℝ≥0∞)) +
                η * (M_corr : ℝ≥0∞) :=
              add_le_add le_rfl (mul_le_mul' le_rfl (Nat.cast_le.mpr hlen))
      simpa only [mul_add, add_assoc] using mul_le_mul' le_rfl h1
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hops]
      simp
  refine (tsum_le_tsum hpt).trans ?_
  rw [tsum_add, tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, hardDist.tsum_coe,
    one_mul, one_mul, add_assoc]

/-- **Contrapositive Word-RAM lower-bound transfer for zero-error `ObliviousSequenceImpl`s**
(standard `w`-bit layout, `0` `η`-loss, no `[Fintype D.Op]`). -/
theorem oblivious_wordRAM_lower_bound_of_det_cellProbe
    {B : Basis} {r_ds k_init w base S_max : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {params : Fin k_init → ℕ} {s₀ : D.State}
    (C : WordRAM.Randomized.ObliviousSequenceImpl.{v, 0, z}
      P (D.toObliviousSequenceSpec s₀) w base params)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (hspace : C.space + persistentRegCount P ≤ S_max)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    {LB : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme D.Op D.Result S_max w,
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) →
      LB ≤ ∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    LB ≤ (C.initPotential : ℝ≥0∞) +
      ∑' ops, hardDist ops *
        (((ops.map C.charge).sum : ℝ≥0∞) +
          ((2 * persistentRegCount P : ℕ) : ℝ≥0∞) * (ops.length : ℝ≥0∞)) := by
  simpa only [standardLayout_overhead, ← persistentRegCount_eq_persCount] using
    oblivious_lower_bound_layout C (standardLayout P.input base C.space w) hspace hd₀ hfr hpar
      opsAlphabet M_corr correctSeqs hcorrectSeqs hardDist hhardDist hlb

/-- **Wide-cell contrapositive Word-RAM lower-bound transfer for zero-error
`ObliviousSequenceImpl`s** (`S_max ≥ C.space + 1` cells of width `wideSubroutineWidth P w`,
`≤ 2` additive probes per operation regardless of `r_ds`, `0` `η`-loss, no `[Fintype D.Op]`). -/
theorem oblivious_wordRAM_lower_bound_of_det_cellProbe_wide
    {B : Basis} {r_ds k_init w base S_max : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {params : Fin k_init → ℕ} {s₀ : D.State}
    (C : WordRAM.Randomized.ObliviousSequenceImpl.{v, 0, z}
      P (D.toObliviousSequenceSpec s₀) w base params)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (hspace : C.space + 1 ≤ S_max)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    {LB : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme D.Op D.Result S_max (wideSubroutineWidth P w),
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) →
      LB ≤ ∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    LB ≤ (C.initPotential : ℝ≥0∞) +
      ∑' ops, hardDist ops *
        (((ops.map C.charge).sum : ℝ≥0∞) + (2 : ℝ≥0∞) * (ops.length : ℝ≥0∞)) := by
  have hraw :=
    oblivious_lower_bound_layout C (wideLayout P.input base C.space w) hspace hd₀ hfr hpar
      opsAlphabet M_corr correctSeqs hcorrectSeqs hardDist hhardDist hlb
  refine hraw.trans (add_le_add le_rfl (tsum_le_tsum fun ops => mul_le_mul' le_rfl ?_))
  refine add_le_add le_rfl (mul_le_mul' ?_ le_rfl)
  rw [wideLayout_overhead]
  split_ifs <;> norm_num

end Cslib.DataStructure.CellProbe
