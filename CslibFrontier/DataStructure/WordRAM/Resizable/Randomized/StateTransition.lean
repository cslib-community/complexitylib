/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.WordRAM.Resizable.StateTransition
import CslibFrontier.Foundations.Analysis.ENNRealTsum
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.SupportTsum

/-!
# Randomized Resizable Word RAM State-Transition Implementations

Reusable randomized subroutine implementation certificates (`Randomized.StateTransitionImpl`) over
the word-granular **Resizable Word RAM** (`Cslib.WordRAM.Resizable.ExecRCodeDist` and
`ExecRProgramDist`), accompanying the word-granular resizable memory models of
[LiLiangYuZhou2023Succincter], Section 2.1, and [KuszmaulLiangZhou2026], Section 5.1, and adapting
the bit-granular virtual-memory variant of [LiLiangYuZhou2024], Section 3.2, at word granularity.
Expected potential-amortized step charges ([CLRS2009], Chapter 17) compose across sequences by
linearity of expectation ([MitzenmacherUpfal2017], Section 2.1). A certificate couples
`[base, x.frontier)` execution with `Seed : Type`, state-indexed `seedLaw : D.State → PMF Seed` up
to `seedSlack : ℝ≥0∞`, resting bound `spaceBound`, and peak bound `peakSpaceBound`; sequence
theorems require `Fits w (base + peakSpaceBound s_t o_t)` only along reachable states of `ops` and
compile to `ExecRProgramDist` (rejecting 1-instruction `[.halt out]` stubs).

## Main definitions

* `Randomized.CoupledRState`, `Randomized.StateTransitionImpl`,
  `Randomized.StateTransitionImpl.ofFn`: coupled state bundle, randomized Resizable Word RAM
  certificate, and `abbrev` constructor for `[D.HasStepFn stepFn]`.
* `Resizable.StateTransitionImpl.toRandomized`: canonical embedding of deterministic certificates.
* `Randomized.StateTransitionImpl.ExecSteps`, `Randomized.StateTransitionImpl.ExecStepsOfFn`,
  `Randomized.StateTransitionImpl.ExecProgramSteps`,
  `Randomized.StateTransitionImpl.ExecProgramStepsOfFn`: structured and flat-program execution
  relations.

## Main results

* `Randomized.StateTransitionImpl.mapSimulates`, `Randomized.StateTransitionImpl.toStandard`:
  basis transport from `Basis.exact` to `Basis.standard`.
* `Randomized.StateTransitionImpl.steps_expected_amortized`,
  `Randomized.StateTransitionImpl.seq_expected_amortized`,
  `Randomized.StateTransitionImpl.steps_expected_amortized_ofFn`,
  `Randomized.StateTransitionImpl.seq_expected_amortized_ofFn`:
  trajectory-relative expected-amortized sequence bounds preserving caller memory `[0, base)`.
* `Randomized.StateTransitionImpl.ExecSteps.toExecRProgramDist`,
  `Randomized.StateTransitionImpl.ExecStepsOfFn.toExecRProgramDist`,
  `Randomized.StateTransitionImpl.seq_toExecRProgramDist`,
  `Randomized.StateTransitionImpl.seq_toExecRProgramDist_ofFn`:
  compilation to flat `ExecRProgramDist` across multi-operation sequences.
* `Randomized.StateTransitionImpl.not_execProgramSteps_halt`,
  `Randomized.StateTransitionImpl.not_execProgramStepsOfFn_halt`:
  `.halt`-rejection soundness checks on compiled flat `RProgram` sequences.

## References

* [CLRS2009] Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein,
  *Introduction to Algorithms*, 3rd ed., MIT Press, 2009, Chapter 17.
* [MitzenmacherUpfal2017] Michael Mitzenmacher and Eli Upfal, *Probability and Computing*, 2nd ed.,
  Cambridge University Press, 2017, Section 2.1.
* [LiLiangYuZhou2023Succincter] Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic
  "Succincter"*, FOCS 2023, pp. 1715–1733 (`arXiv:2309.12950v1`, Section 2.1, PDF pp. 6–7 /
  printed pp. 5–6).
* [LiLiangYuZhou2024] Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic Dictionary
  with Subconstant Wasted Bits per Key*, SODA 2024 (`arXiv:2310.20536v1`, Section 3.2, PDF pp. 9–10
  / printed pp. 8–9).
* [KuszmaulLiangZhou2026] William Kuszmaul, Jingxun Liang, and Renfei Zhou, *Succinct Dynamic
  Rank/Select: Bypassing the Tree-Structure Bottleneck*, SODA 2026 (`arXiv:2510.19175v1`,
  Section 5.1, PDF pp. 16–20 / printed pp. 15–19).
-/

public section

open scoped ENNReal

namespace Cslib.DataStructure.WordRAM.Resizable.Randomized

open Cslib.WordRAM Cslib.WordRAM.Resizable Cslib.DataStructure
open Cslib.DataStructure.WordRAM.Resizable

universe u v z

/-- Coupled latent seed, abstract specification state, and concrete Resizable Word RAM state
`RData r`. -/
structure CoupledRState (Seed : Type) (State : Type u) (r : ℕ) : Type u where
  /-- Latent random seed. -/
  seed : Seed
  /-- Abstract specification state. -/
  state : State
  /-- Concrete Resizable Word RAM register, memory, and frontier state. -/
  data : RData r

/-- Reusable randomized Resizable Word RAM implementation certificate with state-dependent resting
footprint `[base, base + spaceBound s)` and intermediate execution peak bound
`[base, base + peakSpaceBound s o)`. -/
structure StateTransitionImpl {B : Basis} {r_ds k_init : ℕ}
    (P : SubroutineCode B r_ds k_init) (D : StateTransitionSpec.{u, v, z})
    (w base : ℕ) (params : Fin k_init → ℕ) (s₀ : D.State) : Type (max u v z 1) where
  /-- Latent random seed type (such as hash-function keys or random coins). -/
  Seed : Type
  /-- Reference distribution on `Seed` indexed by abstract state. -/
  seedLaw : D.State → PMF Seed
  /-- Pointwise multiplicative slack (`(ν.map seed) θ ≤ seedSlack * seedLaw s θ`). -/
  seedSlack : ℝ≥0∞ := 1
  seedSlack_ne_top : seedSlack ≠ ⊤ := by simp
  /-- Resting post-operation word-footprint upper bound `x.frontier ≤ base + spaceBound s`. -/
  spaceBound : D.State → ℕ
  /-- Peak intermediate word-footprint upper bound `y.frontier ≤ base + peakSpaceBound s o`. -/
  peakSpaceBound : D.State → D.Op → ℕ
  /-- Expected instruction bound for `P.initCode`. -/
  initTime : ℝ≥0∞
  /-- Upper bound on initial concrete potential (`0` when unamortized). -/
  initPotential : ℕ := 0
  /-- Amortized instruction charge per operation. -/
  charge : D.State → D.Op → ℕ
  /-- Representation invariant coupling latent seed, abstract state, and concrete `RData r_ds`. -/
  rep : Seed → D.State → RData r_ds → Prop
  /-- Concrete nonnegative potential function (`0` when worst-case expected). -/
  potential : Seed → RData r_ds → ℕ := fun _ _ => 0
  /-- Standalone register encoding for argument delivery. -/
  encode : D.Op → Fin r_ds → ℕ
  /-- Register-agreement predicate checked at subroutine entry. -/
  argMatch : D.Op → (Fin r_ds → ℕ) → Prop
  /-- Output decoder reading typed operation results from final registers. -/
  decode : (o : D.Op) → (Fin r_ds → ℕ) → Option (D.Result o)
  bounded : ∀ {θ s x}, rep θ s x → x.Bounded w
  frontier_le : ∀ {θ s x}, rep θ s x →
    base ≤ x.frontier ∧ x.frontier ≤ base + spaceBound s ∧ x.regs P.baseReg = base
  /-- `rep` depends only on persistent registers, `x.frontier`, and active `[base, x.frontier)`. -/
  rep_supported : ∀ {θ s x x'},
    (∀ i, P.input i = false → x'.regs i = x.regs i) → x'.frontier = x.frontier →
    (∀ a, base ≤ a → a < x.frontier → x'.mem a = x.mem a) →
    x'.Bounded w → rep θ s x → rep θ s x'
  potential_supported : ∀ {θ s x x'},
    (∀ i, P.input i = false → x'.regs i = x.regs i) → x'.frontier = x.frontier →
    (∀ a, base ≤ a → a < x.frontier → x'.mem a = x.mem a) →
    rep θ s x → potential θ x' = potential θ x
  arguments_fit : ∀ {s} (o), D.valid s o → ∀ i, P.input i = true → Fits w (encode o i)
  encode_matches : ∀ (o : D.Op) (regs : Fin r_ds → ℕ),
    argMatch o (fun i => if P.input i then encode o i else regs i)
  init_exec : ∀ {x₀ : RData r_ds},
    x₀.Bounded w → x₀.frontier = base → (∀ j, x₀.regs (P.initParams j) = params j) →
    Fits w (base + spaceBound s₀) →
    ∃ ν₀ : PMF (Seed × RData r_ds),
      ExecRCodeDist w P.initCode x₀ (ν₀.map Prod.snd) initTime (base + spaceBound s₀) ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ seedSlack * seedLaw s₀ θ) ∧
      ∀ p ∈ ν₀.support, rep p.1 s₀ p.2 ∧ potential p.1 p.2 ≤ initPotential ∧
        (∀ addr < base, p.2.mem addr = x₀.mem addr)
  /-- Optional single-state concentration flag (`True` for `ofFn` functional specs). -/
  singleState : Prop := False
  step_exec : ∀ (o : D.Op) (ν : PMF (CoupledRState Seed D.State r_ds)),
    (singleState → ∃ s, ∀ t ∈ ν.support, t.state = s) →
    (∀ s, (∀ t ∈ ν.support, t.state = s) →
      ∀ θ, (ν.map CoupledRState.seed) θ ≤ seedSlack * seedLaw s θ) →
    (∀ t ∈ ν.support,
      D.valid t.state o ∧ rep t.seed t.state t.data ∧ argMatch o t.data.regs ∧
      Fits w (base + peakSpaceBound t.state o)) →
    ∃ (μ_step : CoupledRState Seed D.State r_ds → PMF (CoupledRState Seed D.State r_ds))
      (T_step : CoupledRState Seed D.State r_ds → ℝ≥0∞),
      (∀ t ∈ ν.support,
        ExecRCodeDist w P.code t.data ((μ_step t).map CoupledRState.data) (T_step t)
          (base + peakSpaceBound t.state o) ∧
        ∀ q ∈ (μ_step t).support, ∃ a : D.Result o,
          D.step t.state o q.state a ∧ decode o q.data.regs = some a ∧
          rep q.seed q.state q.data ∧ (∀ addr < base, q.data.mem addr = t.data.mem addr)) ∧
      (∀ s', (∀ q ∈ (ν.bind μ_step).support, q.state = s') →
        ∀ θ', ((ν.bind μ_step).map CoupledRState.seed) θ' ≤ seedSlack * seedLaw s' θ') ∧
      (singleState → ∃ s', ∀ q ∈ (ν.bind μ_step).support, q.state = s') ∧
      (∑' t, ν t * (T_step t + ∑' q, μ_step t q * (potential q.seed q.data : ℝ≥0∞))) ≤
        ∑' t, ν t * ((charge t.state o : ℝ≥0∞) + (potential t.seed t.data : ℝ≥0∞))

end Cslib.DataStructure.WordRAM.Resizable.Randomized

/-! ## Deterministic-to-randomized embedding (`toRandomized`) -/

namespace Cslib.DataStructure.WordRAM.Resizable.StateTransitionImpl

open Cslib.WordRAM Cslib.WordRAM.Resizable
open Cslib.DataStructure.WordRAM.Resizable.Randomized (CoupledRState)

universe u v z

variable {B : Basis} {r_ds k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init} {D : StateTransitionSpec.{u, v, z}}
  {params : Fin k_init → ℕ} {s₀ : D.State}

private structure DetStepChoice (C : StateTransitionImpl P D w base params s₀)
    (s : D.State) (x : RData r_ds) (o : D.Op) where
  y : RData r_ds
  s' : D.State
  a : D.Result o
  n : ℕ
  exec : RDemonicExec w (base + C.peakSpaceBound s o) P.code x n (· = y)
  step : D.step s o s' a
  decode_eq : C.decode o y.regs = some a
  rep_post : C.rep s' y
  caller_mem : ∀ addr < base, y.mem addr = x.mem addr
  amort : n + C.potential y ≤ C.charge s o + C.potential x

private noncomputable def chooseDetStep (C : StateTransitionImpl P D w base params s₀)
    {s : D.State} {x : RData r_ds} (o : D.Op)
    (hrep : C.rep s x) (hv : D.valid s o) (harg : C.argMatch o x.regs)
    (hfit : Fits w (base + C.peakSpaceBound s o)) : DetStepChoice C s x o :=
  Classical.choice <|
    let ⟨y, s', a, n, hexec, hstep, hdec, hrep', hcaller, hamort⟩ := C.step_exec o hrep hv harg hfit
    ⟨⟨y, s', a, n, hexec, hstep, hdec, hrep', hcaller, hamort⟩⟩

/-- Canonical embedding of any deterministic `Resizable.StateTransitionImpl` certificate into
`Resizable.Randomized.StateTransitionImpl` (`Seed := Unit`, `seedLaw := fun _ => PMF.pure ()`,
`seedSlack := 1`). -/
@[expose] noncomputable def toRandomized (C : StateTransitionImpl P D w base params s₀) :
    Randomized.StateTransitionImpl P D w base params s₀ where
  Seed := Unit; seedLaw _ := PMF.pure (); seedSlack := 1
  spaceBound := C.spaceBound; peakSpaceBound := C.peakSpaceBound
  initTime := C.initTime; initPotential := C.initPotential; charge := C.charge
  rep _ s x := C.rep s x; potential _ x := C.potential x
  encode := C.encode; argMatch := C.argMatch; decode := C.decode
  bounded := C.bounded; frontier_le := C.frontier_le
  rep_supported := C.rep_supported; potential_supported := C.potential_supported
  arguments_fit := C.arguments_fit; encode_matches := C.encode_matches
  init_exec hx₀ hfr hpar hfit := by
    obtain ⟨y, he, hrep, hpot, hcaller⟩ := C.init_exec hx₀ hfr hpar hfit
    refine ⟨PMF.pure ((), y), by simpa using ExecRCodeDist.of_demonicExec he,
      fun θ => by cases θ; simp, fun p hp => ?_⟩
    have hp_eq : p = ((), y) := by simpa using hp
    subst hp_eq; exact ⟨hrep, hpot, hcaller⟩
  step_exec o ν _ _ hsupp := by
    classical
    let hasInv (t : CoupledRState Unit D.State r_ds) : Prop :=
      D.valid t.state o ∧ C.rep t.state t.data ∧ C.argMatch o t.data.regs ∧
      Fits w (base + C.peakSpaceBound t.state o)
    let pick (t : CoupledRState Unit D.State r_ds) (ht : hasInv t) :=
      let ⟨hv, hrep, harg, hfit⟩ := ht; chooseDetStep C o hrep hv harg hfit
    let nextData (t : CoupledRState Unit D.State r_ds) : RData r_ds :=
      if ht : hasInv t then (pick t ht).y else t.data
    let nextState (t : CoupledRState Unit D.State r_ds) : D.State :=
      if ht : hasInv t then (pick t ht).s' else t.state
    let nextSteps (t : CoupledRState Unit D.State r_ds) : ℕ :=
      if ht : hasInv t then (pick t ht).n else 0
    let μ_step (t : CoupledRState Unit D.State r_ds) : PMF (CoupledRState Unit D.State r_ds) :=
      PMF.pure ⟨(), nextState t, nextData t⟩
    let T_step (t : CoupledRState Unit D.State r_ds) : ℝ≥0∞ := (nextSteps t : ℝ≥0∞)
    refine ⟨μ_step, T_step, ?_, ?_, nofun, ?_⟩
    · intro t ht_mem
      have ht : hasInv t := hsupp t ht_mem
      refine ⟨by simpa [μ_step, T_step, nextData, nextSteps, ht] using
          ExecRCodeDist.of_demonicExec (pick t ht).exec, fun q hq => ?_⟩
      have hq_eq : q = ⟨(), nextState t, nextData t⟩ := by simpa [μ_step] using hq
      subst hq_eq; simp only [nextData, nextState, ht, ↓reduceDIte]
      exact ⟨(pick t ht).a, (pick t ht).step, (pick t ht).decode_eq,
        (pick t ht).rep_post, (pick t ht).caller_mem⟩
    · intro _ _ θ'; cases θ'
      have hconst : ((ν.bind μ_step).map CoupledRState.seed) () = 1 := by
        rw [PMF.map_bind]; simp [μ_step]
      simp [hconst]
    · refine tsum_le_tsum fun t => ?_
      by_cases ht_mem : t ∈ ν.support
      · refine mul_le_mul_right ?_ _
        have ht : hasInv t := hsupp t ht_mem
        rw [tsum_eq_single ⟨(), nextState t, nextData t⟩
          (fun q hq => by simp [μ_step, PMF.pure_apply, hq])]
        simp only [μ_step, T_step, PMF.pure_apply_self, one_mul, nextData, nextSteps, ht,
          ↓reduceDIte]
        exact_mod_cast (pick t ht).amort
      · rw [(PMF.apply_eq_zero_iff _ _).mpr ht_mem, zero_mul, zero_mul]

@[simp] theorem toRandomized_spaceBound (C : StateTransitionImpl P D w base params s₀) :
    C.toRandomized.spaceBound = C.spaceBound := rfl
@[simp] theorem toRandomized_peakSpaceBound (C : StateTransitionImpl P D w base params s₀) :
    C.toRandomized.peakSpaceBound = C.peakSpaceBound := rfl
@[simp] theorem toRandomized_charge (C : StateTransitionImpl P D w base params s₀) :
    C.toRandomized.charge = C.charge := rfl
@[simp] theorem toRandomized_initPotential (C : StateTransitionImpl P D w base params s₀) :
    C.toRandomized.initPotential = C.initPotential := rfl

end Cslib.DataStructure.WordRAM.Resizable.StateTransitionImpl

/-! ## `ofFn`, basis transport, and caller framing on `Randomized.StateTransitionImpl` -/

namespace Cslib.DataStructure.WordRAM.Resizable.Randomized.StateTransitionImpl

open Cslib.WordRAM Cslib.WordRAM.Resizable Cslib.DataStructure
open Cslib.DataStructure.WordRAM.Resizable

universe u v z

variable {B B' : Basis} {r_ds k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init} {D : StateTransitionSpec.{u, v, z}}
  {params : Fin k_init → ℕ} {s₀ : D.State}

/-- Construct a `Randomized.StateTransitionImpl` for a functional specification
(`[D.HasStepFn stepFn]`). Defined as `abbrev` (`singleState := True`) so `D.Result` reduces
transparently without unfolding `StateTransitionSpec.ofFn`. -/
noncomputable abbrev ofFn {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    [D.HasStepFn stepFn]
    (Seed : Type) (seedLaw : D.State → PMF Seed) (seedSlack : ℝ≥0∞ := 1)
    (seedSlack_ne_top : seedSlack ≠ ⊤ := by simp)
    (spaceBound : D.State → ℕ) (peakSpaceBound : D.State → D.Op → ℕ)
    (initTime : ℝ≥0∞) (initPotential : ℕ := 0) (charge : D.State → D.Op → ℕ)
    (rep : Seed → D.State → RData r_ds → Prop)
    (potential : Seed → RData r_ds → ℕ := fun _ _ => 0)
    (encode : D.Op → Fin r_ds → ℕ) (argMatch : D.Op → (Fin r_ds → ℕ) → Prop)
    (decode : (o : D.Op) → (Fin r_ds → ℕ) → Option (D.Result o))
    (bounded : ∀ {θ s x}, rep θ s x → x.Bounded w)
    (frontier_le : ∀ {θ s x}, rep θ s x →
      base ≤ x.frontier ∧ x.frontier ≤ base + spaceBound s ∧ x.regs P.baseReg = base)
    (rep_supported : ∀ {θ s x x'},
      (∀ i, P.input i = false → x'.regs i = x.regs i) → x'.frontier = x.frontier →
      (∀ a, base ≤ a → a < x.frontier → x'.mem a = x.mem a) →
      x'.Bounded w → rep θ s x → rep θ s x')
    (potential_supported : ∀ {θ s x x'},
      (∀ i, P.input i = false → x'.regs i = x.regs i) → x'.frontier = x.frontier →
      (∀ a, base ≤ a → a < x.frontier → x'.mem a = x.mem a) →
      rep θ s x → potential θ x' = potential θ x)
    (arguments_fit : ∀ {s} (o), D.valid s o → ∀ i, P.input i = true → Fits w (encode o i))
    (encode_matches : ∀ (o : D.Op) (regs : Fin r_ds → ℕ),
      argMatch o (fun i => if P.input i then encode o i else regs i))
    (init_exec : ∀ {x₀ : RData r_ds},
      x₀.Bounded w → x₀.frontier = base → (∀ j, x₀.regs (P.initParams j) = params j) →
      Fits w (base + spaceBound s₀) →
      ∃ ν₀ : PMF (Seed × RData r_ds),
        ExecRCodeDist w P.initCode x₀ (ν₀.map Prod.snd) initTime (base + spaceBound s₀) ∧
        (∀ θ, (ν₀.map Prod.fst) θ ≤ seedSlack * seedLaw s₀ θ) ∧
        ∀ p ∈ ν₀.support, rep p.1 s₀ p.2 ∧ potential p.1 p.2 ≤ initPotential ∧
          (∀ addr < base, p.2.mem addr = x₀.mem addr))
    (step_exec : ∀ {s : D.State} (o : D.Op) (ν : PMF (Seed × RData r_ds)),
      D.valid s o → Fits w (base + peakSpaceBound s o) →
      (∀ θ, (ν.map Prod.fst) θ ≤ seedSlack * seedLaw s θ) →
      (∀ p ∈ ν.support, rep p.1 s p.2 ∧ argMatch o p.2.regs) →
      ∃ (μ_step : Seed × RData r_ds → PMF (Seed × RData r_ds))
        (T_step : Seed × RData r_ds → ℝ≥0∞),
        (∀ p ∈ ν.support,
          ExecRCodeDist w P.code p.2 ((μ_step p).map Prod.snd) (T_step p)
            (base + peakSpaceBound s o) ∧
          ∀ q ∈ (μ_step p).support,
            decode o q.2.regs = some (D.stepFn s o).2 ∧
            rep q.1 (D.stepFn s o).1 q.2 ∧ (∀ addr < base, q.2.mem addr = p.2.mem addr)) ∧
        (∀ θ', ((ν.bind μ_step).map Prod.fst) θ' ≤ seedSlack * seedLaw (D.stepFn s o).1 θ') ∧
        (∑' p, ν p * (T_step p + ∑' q, μ_step p q * (potential q.1 q.2 : ℝ≥0∞))) ≤
          (charge s o : ℝ≥0∞) + ∑' p, ν p * (potential p.1 p.2 : ℝ≥0∞)) :
    StateTransitionImpl P D w base params s₀ where
  Seed := Seed; seedLaw := seedLaw; seedSlack := seedSlack; seedSlack_ne_top := seedSlack_ne_top
  spaceBound := spaceBound; peakSpaceBound := peakSpaceBound
  initTime := initTime; initPotential := initPotential; charge := charge
  rep := rep; potential := potential
  encode := encode; argMatch := argMatch; decode := decode
  bounded := bounded; frontier_le := frontier_le
  rep_supported := rep_supported; potential_supported := potential_supported
  arguments_fit := arguments_fit; encode_matches := encode_matches
  init_exec := init_exec; singleState := True
  step_exec o ν hsingle hseed hsupp := by
    obtain ⟨s, hs⟩ := hsingle trivial
    obtain ⟨t₀, ht₀⟩ := ν.support_nonempty
    have hv : D.valid s o := hs t₀ ht₀ ▸ (hsupp t₀ ht₀).1
    have hfit : Fits w (base + peakSpaceBound s o) := hs t₀ ht₀ ▸ (hsupp t₀ ht₀).2.2.2
    let proj : CoupledRState Seed D.State r_ds → Seed × RData r_ds := fun t => (t.seed, t.data)
    let ν_det : PMF (Seed × RData r_ds) := ν.map proj
    have hseed_det : ∀ θ, (ν_det.map Prod.fst) θ ≤ seedSlack * seedLaw s θ := fun θ => by
      rw [PMF.map_comp]; exact hseed s hs θ
    have hsupp_det : ∀ p ∈ ν_det.support, rep p.1 s p.2 ∧ argMatch o p.2.regs := by
      intro p hp; rw [PMF.mem_support_map_iff] at hp; obtain ⟨t, ht, rfl⟩ := hp
      obtain ⟨_, hrep, harg, _⟩ := hsupp t ht; exact ⟨hs t ht ▸ hrep, harg⟩
    obtain ⟨μ_det, T_det, hstep_det, hseed_det', hamort_det⟩ :=
      step_exec o ν_det hv hfit hseed_det hsupp_det
    let μ_step : CoupledRState Seed D.State r_ds → PMF (CoupledRState Seed D.State r_ds) :=
      fun t => (μ_det (proj t)).map fun q => ⟨q.1, (D.stepFn s o).1, q.2⟩
    let T_step : CoupledRState Seed D.State r_ds → ℝ≥0∞ := fun t => T_det (proj t)
    have hstate_post : ∀ q' ∈ (ν.bind μ_step).support, q'.state = (D.stepFn s o).1 := by
      intro q' hq'; rw [PMF.mem_support_bind_iff] at hq'; obtain ⟨_, _, hq_map⟩ := hq'
      rw [PMF.mem_support_map_iff] at hq_map; obtain ⟨_, _, rfl⟩ := hq_map; rfl
    refine ⟨μ_step, T_step, ?_, ?_, fun _ => ⟨(D.stepFn s o).1, hstate_post⟩, ?_⟩
    · intro t ht
      obtain ⟨he_det, hq_det⟩ :=
        hstep_det (proj t) ((PMF.mem_support_map_iff _ _ _).mpr ⟨t, ht, rfl⟩)
      refine ⟨?_, fun q' hq' => ?_⟩
      · rw [hs t ht]; refine he_det.congr_dist ?_ le_rfl
        dsimp only [μ_step]; rw [PMF.map_comp]; rfl
      · dsimp only [μ_step] at hq'; rw [PMF.mem_support_map_iff] at hq'; obtain ⟨q, hq, rfl⟩ := hq'
        obtain ⟨hdec, hrep, hcaller⟩ := hq_det q hq
        exact ⟨(D.stepFn s o).2, hs t ht ▸ D.step_stepFn s o, hdec, hrep, hcaller⟩
    · intro s' hs' θ'
      obtain ⟨q₀, hq₀⟩ := (ν.bind μ_step).support_nonempty
      have hs'_eq : s' = (D.stepFn s o).1 := (hs' q₀ hq₀).symm.trans (hstate_post q₀ hq₀)
      subst hs'_eq
      have hmap_eq : (ν.bind μ_step).map CoupledRState.seed = (ν_det.bind μ_det).map Prod.fst := by
        dsimp only [ν_det, μ_step]; rw [PMF.map_bind, PMF.bind_map, PMF.map_bind]
        refine congrArg (ν.bind ·) (funext fun t => by rw [PMF.map_comp]; rfl)
      rw [hmap_eq]; exact hseed_det' θ'
    · have lhs_eq :
          (∑' t, ν t * (T_step t + ∑' q', μ_step t q' * (potential q'.seed q'.data : ℝ≥0∞))) =
            ∑' p, ν_det p * (T_det p + ∑' q, μ_det p q * (potential q.1 q.2 : ℝ≥0∞)) := by
        rw [Cslib.Probability.PMF.tsum_map_mul]
        refine tsum_congr fun t => congrArg (ν t * ·) (congrArg (T_det (proj t) + ·) ?_)
        exact Cslib.Probability.PMF.tsum_map_mul (μ_det (proj t)) _ _
      have rhs_eq :
          (∑' t, ν t * ((charge t.state o : ℝ≥0∞) + (potential t.seed t.data : ℝ≥0∞))) =
            (charge s o : ℝ≥0∞) + ∑' p, ν_det p * (potential p.1 p.2 : ℝ≥0∞) := by
        calc
          (∑' t, ν t * ((charge t.state o : ℝ≥0∞) + (potential t.seed t.data : ℝ≥0∞)))
            = ∑' t, ν t * ((charge s o : ℝ≥0∞) + (potential t.seed t.data : ℝ≥0∞)) :=
                Cslib.Probability.PMF.tsum_mul_congr_support ν fun t ht => by rw [hs t ht]
          _ = (charge s o : ℝ≥0∞) + ∑' t, ν t * (potential t.seed t.data : ℝ≥0∞) := by
                simp_rw [mul_add, tsum_add, ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]
          _ = (charge s o : ℝ≥0∞) + ∑' p, ν_det p * (potential p.1 p.2 : ℝ≥0∞) := by
                rw [Cslib.Probability.PMF.tsum_map_mul]
      rw [lhs_eq, rhs_eq]; exact hamort_det

/-- Lift a `Randomized.StateTransitionImpl` certificate along any defined-evaluation basis
simulation `φ : B.Simulates B'`. -/
@[expose] def mapSimulates (φ : B.Simulates B')
    (C : StateTransitionImpl P D w base params s₀) :
    StateTransitionImpl (P.mapSimulates φ) D w base params s₀ where
  Seed := C.Seed; seedLaw := C.seedLaw; seedSlack := C.seedSlack
  seedSlack_ne_top := C.seedSlack_ne_top
  spaceBound := C.spaceBound; peakSpaceBound := C.peakSpaceBound
  initTime := C.initTime; initPotential := C.initPotential; charge := C.charge
  rep := C.rep; potential := C.potential
  encode := C.encode; argMatch := C.argMatch; decode := C.decode
  bounded := C.bounded; frontier_le := C.frontier_le
  rep_supported := C.rep_supported; potential_supported := C.potential_supported
  arguments_fit := C.arguments_fit; encode_matches := C.encode_matches
  init_exec hx₀ hfr hpar hfit := by
    obtain ⟨ν₀, he, hseed, hsupp⟩ := C.init_exec hx₀ hfr hpar hfit
    exact ⟨ν₀, he.mapSimulates φ, hseed, hsupp⟩
  singleState := C.singleState
  step_exec o ν hsingle hseed hsupp := by
    obtain ⟨μ_step, T_step, hstep, hseed', hsingle', hamort⟩ :=
      C.step_exec o ν hsingle hseed hsupp
    refine ⟨μ_step, T_step, fun t ht => ?_, hseed', hsingle', hamort⟩
    obtain ⟨he, hq⟩ := hstep t ht
    exact ⟨he.mapSimulates φ, hq⟩

/-- Lift an exact-basis `Randomized.StateTransitionImpl` certificate to `Basis.standard`. -/
abbrev toStandard {P : SubroutineCode .exact r_ds k_init}
    (C : StateTransitionImpl P D w base params s₀) :
    StateTransitionImpl P.toStandard D w base params s₀ :=
  C.mapSimulates .exactStandard

/-- Prepare registers for operation `o` on `x`. -/
@[expose] def prepare (C : StateTransitionImpl P D w base params s₀) (o : D.Op) (x : RData r_ds) :
    RData r_ds :=
  P.prepare C.encode o x

theorem prepare_bounded (C : StateTransitionImpl P D w base params s₀)
    {s : D.State} {o : D.Op} {x : RData r_ds} (hx : x.Bounded w) (hv : D.valid s o) :
    (C.prepare o x).Bounded w :=
  P.prepare_bounded hx (C.arguments_fit o hv)

theorem prepare_rep (C : StateTransitionImpl P D w base params s₀)
    {θ : C.Seed} {s : D.State} {o : D.Op} {x : RData r_ds}
    (hr : C.rep θ s x) (hv : D.valid s o) : C.rep θ s (C.prepare o x) :=
  C.rep_supported (fun _ hi => P.prepare_regs_of_not_input hi o x) rfl (fun _ _ _ => rfl)
    (C.prepare_bounded (C.bounded hr) hv) hr

theorem prepare_potential (C : StateTransitionImpl P D w base params s₀)
    {θ : C.Seed} {s : D.State} {o : D.Op} {x : RData r_ds} (hr : C.rep θ s x) :
    C.potential θ (C.prepare o x) = C.potential θ x :=
  C.potential_supported (fun _ hi => P.prepare_regs_of_not_input hi o x) rfl (fun _ _ _ => rfl) hr

theorem prepare_argMatch (C : StateTransitionImpl P D w base params s₀)
    (o : D.Op) (x : RData r_ds) : C.argMatch o (C.prepare o x).regs := C.encode_matches o x.regs

/-- Caller-frame preservation on `rep` and `potential`. -/
theorem frame_caller (C : StateTransitionImpl P D w base params s₀)
    {θ : C.Seed} {s : D.State} {x x' : RData r_ds}
    (hregs : ∀ i, P.input i = false → x'.regs i = x.regs i) (hfr : x'.frontier = x.frontier)
    (hmem : ∀ a, base ≤ a → a < x.frontier → x'.mem a = x.mem a)
    (hb : x'.Bounded w) (hr : C.rep θ s x) :
    C.rep θ s x' ∧ C.potential θ x' = C.potential θ x :=
  ⟨C.rep_supported hregs hfr hmem hb hr, C.potential_supported hregs hfr hmem hr⟩

/-! ## Trajectory-relative expected-amortized sequence theorems -/

/-- Structured multi-operation distributional execution `C.ExecSteps` over `ExecRCodeDist`. -/
inductive ExecSteps (C : StateTransitionImpl P D w base params s₀) :
    List D.Op → PMF (CoupledRState C.Seed D.State r_ds) →
      PMF (CoupledRState C.Seed D.State r_ds) → ℝ≥0∞ → ℝ≥0∞ → Prop where
  | nil (ν : PMF (CoupledRState C.Seed D.State r_ds)) : C.ExecSteps [] ν ν 0 0
  | cons {o : D.Op} {ops : List D.Op} {ν ν_final : PMF (CoupledRState C.Seed D.State r_ds)}
      {μ_step : CoupledRState C.Seed D.State r_ds → PMF (CoupledRState C.Seed D.State r_ds)}
      {T_step : CoupledRState C.Seed D.State r_ds → ℝ≥0∞} {T_rest C_rest : ℝ≥0∞} :
      (∀ t ∈ ν.support,
        ExecRCodeDist w P.code (C.prepare o t.data)
          ((μ_step t).map CoupledRState.data) (T_step t) (base + C.peakSpaceBound t.state o) ∧
        ∀ q ∈ (μ_step t).support, ∃ a : D.Result o,
          D.step t.state o q.state a ∧ C.decode o q.data.regs = some a ∧
          C.rep q.seed q.state q.data ∧ (∀ addr < base, q.data.mem addr = t.data.mem addr)) →
      C.ExecSteps ops (ν.bind μ_step) ν_final T_rest C_rest →
      C.ExecSteps (o :: ops) ν ν_final ((∑' t, ν t * T_step t) + T_rest)
        ((∑' t, ν t * (C.charge t.state o : ℝ≥0∞)) + C_rest)

/-- `ExecSteps` preserves caller memory `[0, base)` across all support states. -/
theorem ExecSteps.caller_mem {C : StateTransitionImpl P D w base params s₀}
    {ops : List D.Op} {ν ν_final : PMF (CoupledRState C.Seed D.State r_ds)} {T_ops C_ops : ℝ≥0∞}
    (h : C.ExecSteps ops ν ν_final T_ops C_ops) {mem₀ : ℕ → ℕ}
    (h₀ : ∀ t ∈ ν.support, ∀ addr < base, t.data.mem addr = mem₀ addr) :
    ∀ q ∈ ν_final.support, ∀ addr < base, q.data.mem addr = mem₀ addr := by
  induction h with
  | nil _ => exact h₀
  | cons hstep _ ih =>
    refine ih fun q hq addr hlt => ?_
    rw [PMF.mem_support_bind_iff] at hq; obtain ⟨t, ht, hq_t⟩ := hq
    exact (((hstep t ht).2 q hq_t).choose_spec.2.2.2 addr hlt).trans (h₀ t ht addr hlt)

/-- **Trajectory-relative multi-operation expected-amortized telescope
(`steps_expected_amortized`).**
Requires `PeakFitsOpSeq w base C.peakSpaceBound t.state ops` **only** along states reached by `ops`
from `ν.support`. -/
theorem steps_expected_amortized (C : StateTransitionImpl P D w base params s₀)
    (ops : List D.Op) (ν : PMF (CoupledRState C.Seed D.State r_ds))
    (hv : ∀ t ∈ ν.support, D.ValidOpSeq t.state ops)
    (hfit : ∀ t ∈ ν.support, PeakFitsOpSeq w base C.peakSpaceBound t.state ops)
    (hseed : ∀ s, (∀ t ∈ ν.support, t.state = s) →
      ∀ θ, (ν.map CoupledRState.seed) θ ≤ C.seedSlack * C.seedLaw s θ)
    (hrep : ∀ t ∈ ν.support, C.rep t.seed t.state t.data)
    (hsingle : C.singleState → ∃ s, ∀ t ∈ ν.support, t.state = s := by intro h; cases h) :
    ∃ (ν_final : PMF (CoupledRState C.Seed D.State r_ds)) (T_ops C_ops : ℝ≥0∞),
      C.ExecSteps ops ν ν_final T_ops C_ops ∧
      (∀ s_fin, (∀ q ∈ ν_final.support, q.state = s_fin) →
        ∀ θ, (ν_final.map CoupledRState.seed) θ ≤ C.seedSlack * C.seedLaw s_fin θ) ∧
      (∀ q ∈ ν_final.support, C.rep q.seed q.state q.data) ∧
      T_ops + (∑' q, ν_final q * (C.potential q.seed q.data : ℝ≥0∞)) ≤
        C_ops + ∑' t, ν t * (C.potential t.seed t.data : ℝ≥0∞) := by
  induction ops generalizing ν with
  | nil => exact ⟨ν, 0, 0, .nil ν, hseed, hrep, by simp⟩
  | cons o os ih =>
    let prepMap : CoupledRState C.Seed D.State r_ds → CoupledRState C.Seed D.State r_ds :=
      fun t => ⟨t.seed, t.state, C.prepare o t.data⟩
    let ν_prep := ν.map prepMap
    have hsingle_prep : C.singleState → ∃ s, ∀ t' ∈ ν_prep.support, t'.state = s := fun hd => by
      obtain ⟨s, hs⟩ := hsingle hd
      refine ⟨s, fun t' ht' => ?_⟩
      rw [PMF.mem_support_map_iff] at ht'; obtain ⟨t, ht, rfl⟩ := ht'; exact hs t ht
    have hseed_prep : ∀ s, (∀ t' ∈ ν_prep.support, t'.state = s) →
        ∀ θ, (ν_prep.map CoupledRState.seed) θ ≤ C.seedSlack * C.seedLaw s θ := fun s hs θ => by
      rw [PMF.map_comp]
      exact hseed s (fun t ht => hs (prepMap t) ((PMF.mem_support_map_iff _ _ _).mpr ⟨t, ht, rfl⟩))
        θ
    have hsupp_prep : ∀ t' ∈ ν_prep.support,
        D.valid t'.state o ∧ C.rep t'.seed t'.state t'.data ∧ C.argMatch o t'.data.regs ∧
        Fits w (base + C.peakSpaceBound t'.state o) := by
      intro t' ht'; rw [PMF.mem_support_map_iff] at ht'; obtain ⟨t, ht, rfl⟩ := ht'
      exact ⟨(hv t ht).1, C.prepare_rep (hrep t ht) (hv t ht).1, C.prepare_argMatch o t.data,
        (hfit t ht).1⟩
    have hpot_prep :
        (∑' t', ν_prep t' *
            ((C.charge t'.state o : ℝ≥0∞) + (C.potential t'.seed t'.data : ℝ≥0∞))) =
          ∑' t, ν t * ((C.charge t.state o : ℝ≥0∞) + (C.potential t.seed t.data : ℝ≥0∞)) := by
      rw [Cslib.Probability.PMF.tsum_map_mul]
      exact Cslib.Probability.PMF.tsum_mul_congr_support ν fun t ht => by
        dsimp only [prepMap]; rw [C.prepare_potential (hrep t ht)]
    obtain ⟨μ_step, T_step, hstep, hseed₁, hsingle₁, hamort₁⟩ :=
      C.step_exec o ν_prep hsingle_prep hseed_prep hsupp_prep
    let μ_op (t : CoupledRState C.Seed D.State r_ds) := μ_step (prepMap t)
    let T_op (t : CoupledRState C.Seed D.State r_ds) := T_step (prepMap t)
    let ν₁ := ν.bind μ_op
    have hν₁_eq : ν₁ = ν_prep.bind μ_step := by simp [ν₁, ν_prep, μ_op, PMF.bind_map]; rfl
    have hv₁ : ∀ q ∈ ν₁.support, D.ValidOpSeq q.state os := by
      intro q hq; rw [PMF.mem_support_bind_iff] at hq; obtain ⟨t, ht, hq_op⟩ := hq
      obtain ⟨a, hstep_a, _, _, _⟩ :=
        (hstep (prepMap t) ((PMF.mem_support_map_iff _ _ _).mpr ⟨t, ht, rfl⟩)).2 q hq_op
      exact (hv t ht).2 q.state a hstep_a
    have hfit₁ : ∀ q ∈ ν₁.support, PeakFitsOpSeq w base C.peakSpaceBound q.state os := by
      intro q hq; rw [PMF.mem_support_bind_iff] at hq; obtain ⟨t, ht, hq_op⟩ := hq
      obtain ⟨a, hstep_a, _, _, _⟩ :=
        (hstep (prepMap t) ((PMF.mem_support_map_iff _ _ _).mpr ⟨t, ht, rfl⟩)).2 q hq_op
      exact (hfit t ht).2 q.state a hstep_a
    have hrep₁ : ∀ q ∈ ν₁.support, C.rep q.seed q.state q.data := by
      intro q hq; rw [hν₁_eq, PMF.mem_support_bind_iff] at hq; obtain ⟨t', ht', hq_s⟩ := hq
      obtain ⟨_, _, _, hr_q, _⟩ := (hstep t' ht').2 q hq_s; exact hr_q
    obtain ⟨ν_final, T_rest, C_rest, hex_rest, hseed_final, hrep_final, hamort_rest⟩ :=
      ih ν₁ hv₁ hfit₁ (hν₁_eq ▸ hseed₁) hrep₁ (hν₁_eq ▸ hsingle₁)
    let T₁ : ℝ≥0∞ := ∑' t, ν t * T_op t
    let C₁ : ℝ≥0∞ := ∑' t, ν t * (C.charge t.state o : ℝ≥0∞)
    have hT₁_eq : T₁ = ∑' t', ν_prep t' * T_step t' :=
      (Cslib.Probability.PMF.tsum_map_mul ν prepMap T_step).symm
    have hex_cons : C.ExecSteps (o :: os) ν ν_final (T₁ + T_rest) (C₁ + C_rest) :=
      .cons (μ_step := μ_op) (T_step := T_op)
        (fun t ht => hstep (prepMap t) ((PMF.mem_support_map_iff _ _ _).mpr ⟨t, ht, rfl⟩))
        hex_rest
    have hstep_split :
        T₁ + (∑' q, ν₁ q * (C.potential q.seed q.data : ℝ≥0∞)) =
          ∑' t', ν_prep t' *
            (T_step t' + ∑' q, μ_step t' q * (C.potential q.seed q.data : ℝ≥0∞)) := by
      rw [hT₁_eq, hν₁_eq]
      simp only [Cslib.Probability.PMF.tsum_bind_mul, ← tsum_add, mul_add]
    have hcharge_split :
        (∑' t, ν t * ((C.charge t.state o : ℝ≥0∞) + (C.potential t.seed t.data : ℝ≥0∞))) =
          C₁ + ∑' t, ν t * (C.potential t.seed t.data : ℝ≥0∞) := by
      simp_rw [mul_add, tsum_add]; rfl
    refine ⟨ν_final, T₁ + T_rest, C₁ + C_rest, hex_cons, hseed_final, hrep_final, ?_⟩
    calc
      (T₁ + T_rest) + ∑' q, ν_final q * (C.potential q.seed q.data : ℝ≥0∞)
        = T₁ + (T_rest + ∑' q, ν_final q * (C.potential q.seed q.data : ℝ≥0∞)) := by ac_rfl
      _ ≤ T₁ + (C_rest + ∑' q, ν₁ q * (C.potential q.seed q.data : ℝ≥0∞)) :=
          add_le_add le_rfl hamort_rest
      _ = C_rest + (T₁ + ∑' q, ν₁ q * (C.potential q.seed q.data : ℝ≥0∞)) := by ac_rfl
      _ ≤ C_rest + (C₁ + ∑' t, ν t * (C.potential t.seed t.data : ℝ≥0∞)) := by
          rw [hstep_split, ← hcharge_split, ← hpot_prep]
          exact add_le_add le_rfl hamort₁
      _ = (C₁ + C_rest) + ∑' t, ν t * (C.potential t.seed t.data : ℝ≥0∞) := by ac_rfl

/-- **End-to-end expected-amortized sequence theorem (`seq_expected_amortized`).** -/
theorem seq_expected_amortized (C : StateTransitionImpl P D w base params s₀)
    {x₀ : RData r_ds} (ops : List D.Op) (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hpar : ∀ j, x₀.regs (P.initParams j) = params j) (hfit₀ : Fits w (base + C.spaceBound s₀))
    (hv : D.ValidOpSeq s₀ ops) (hfit_ops : PeakFitsOpSeq w base C.peakSpaceBound s₀ ops) :
    ∃ (ν₀ : PMF (C.Seed × RData r_ds))
      (ν_final : PMF (CoupledRState C.Seed D.State r_ds)) (T_ops C_ops : ℝ≥0∞),
      ExecRCodeDist w P.initCode x₀ (ν₀.map Prod.snd) C.initTime (base + C.spaceBound s₀) ∧
      (∀ p ∈ ν₀.support, C.rep p.1 s₀ p.2 ∧ ∀ addr < base, p.2.mem addr = x₀.mem addr) ∧
      C.ExecSteps ops (ν₀.map fun p => ⟨p.1, s₀, p.2⟩) ν_final T_ops C_ops ∧
      (∀ s_fin, (∀ q ∈ ν_final.support, q.state = s_fin) →
        ∀ θ, (ν_final.map CoupledRState.seed) θ ≤ C.seedSlack * C.seedLaw s_fin θ) ∧
      (∀ q ∈ ν_final.support,
        C.rep q.seed q.state q.data ∧ ∀ addr < base, q.data.mem addr = x₀.mem addr) ∧
      C.initTime + T_ops + (∑' q, ν_final q * (C.potential q.seed q.data : ℝ≥0∞)) ≤
        C.initTime + (C.initPotential : ℝ≥0∞) + C_ops := by
  obtain ⟨ν₀, he_init, hseed₀, hsupp₀⟩ := C.init_exec hx₀ hfr₀ hpar hfit₀
  let ν₀_rel : PMF (CoupledRState C.Seed D.State r_ds) := ν₀.map fun p => ⟨p.1, s₀, p.2⟩
  have hs₀_rel : ∀ t ∈ ν₀_rel.support, t.state = s₀ := by
    intro t ht; rw [PMF.mem_support_map_iff] at ht; obtain ⟨_, _, rfl⟩ := ht; rfl
  have hv₀ : ∀ t ∈ ν₀_rel.support, D.ValidOpSeq t.state ops :=
    fun t ht => by rw [hs₀_rel t ht]; exact hv
  have hfit₀_rel : ∀ t ∈ ν₀_rel.support, PeakFitsOpSeq w base C.peakSpaceBound t.state ops :=
    fun t ht => by rw [hs₀_rel t ht]; exact hfit_ops
  have hseed₀_rel : ∀ s, (∀ t ∈ ν₀_rel.support, t.state = s) →
      ∀ θ, (ν₀_rel.map CoupledRState.seed) θ ≤ C.seedSlack * C.seedLaw s θ := fun s hs θ => by
    obtain ⟨t₀, ht₀⟩ := ν₀_rel.support_nonempty
    have hs_eq : s = s₀ := (hs t₀ ht₀).symm.trans (hs₀_rel t₀ ht₀)
    subst hs_eq; rw [PMF.map_comp]; exact hseed₀ θ
  have hrep₀ : ∀ t ∈ ν₀_rel.support, C.rep t.seed t.state t.data := by
    intro t ht; rw [PMF.mem_support_map_iff] at ht; obtain ⟨p, hp, rfl⟩ := ht; exact (hsupp₀ p hp).1
  obtain ⟨ν_final, T_ops, C_ops, hex_steps, hseed_final, hrep_final, hamort⟩ :=
    C.steps_expected_amortized ops ν₀_rel hv₀ hfit₀_rel hseed₀_rel hrep₀ (fun _ => ⟨s₀, hs₀_rel⟩)
  have hcaller_final := hex_steps.caller_mem (mem₀ := x₀.mem) fun t ht => by
    rw [PMF.mem_support_map_iff] at ht; obtain ⟨p, hp, rfl⟩ := ht; exact (hsupp₀ p hp).2.2
  have hpot₀ : (∑' t, ν₀_rel t * (C.potential t.seed t.data : ℝ≥0∞)) ≤ (C.initPotential : ℝ≥0∞) :=
    by
      rw [Cslib.Probability.PMF.tsum_map_mul]
      exact Cslib.Probability.PMF.tsum_mul_le_of_support ν₀ fun p hp =>
        Nat.cast_le.mpr (hsupp₀ p hp).2.1
  refine ⟨ν₀, ν_final, T_ops, C_ops, he_init, fun p hp => ⟨(hsupp₀ p hp).1, (hsupp₀ p hp).2.2⟩,
    hex_steps, hseed_final, fun q hq => ⟨hrep_final q hq, hcaller_final q hq⟩, ?_⟩
  rw [add_assoc, add_assoc, add_comm (C.initPotential : ℝ≥0∞)]
  exact add_le_add le_rfl (hamort.trans (add_le_add le_rfl hpot₀))

/-! ## Functional-specification sequence theorems (`ExecStepsOfFn`, `*_ofFn`) -/

/-- Structured multi-operation distributional execution relation for functional specifications
(`[D.HasStepFn stepFn]`). -/
inductive ExecStepsOfFn (C : StateTransitionImpl P D w base params s₀)
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn] :
    D.State → List D.Op → PMF (C.Seed × RData r_ds) → PMF (C.Seed × RData r_ds) → ℝ≥0∞ → Prop where
  | nil (s : D.State) (ν : PMF (C.Seed × RData r_ds)) :
      C.ExecStepsOfFn s [] ν ν 0
  | cons {s : D.State} {o : D.Op} {ops : List D.Op}
      {ν ν_final : PMF (C.Seed × RData r_ds)}
      {μ_step : C.Seed × RData r_ds → PMF (C.Seed × RData r_ds)}
      {T_step : C.Seed × RData r_ds → ℝ≥0∞} {T_rest : ℝ≥0∞} :
      (∀ p ∈ ν.support,
        ExecRCodeDist w P.code (C.prepare o p.2)
          ((μ_step p).map Prod.snd) (T_step p) (base + C.peakSpaceBound s o) ∧
        ∀ q ∈ (μ_step p).support,
          C.decode o q.2.regs = some (D.stepFn s o).2 ∧
          C.rep q.1 (D.stepFn s o).1 q.2 ∧
          (∀ addr < base, q.2.mem addr = p.2.mem addr)) →
      C.ExecStepsOfFn (D.stepFn s o).1 ops (ν.bind μ_step) ν_final T_rest →
      C.ExecStepsOfFn s (o :: ops) ν ν_final ((∑' p, ν p * T_step p) + T_rest)

/-- Project a relational `ExecSteps` derivation onto `ExecStepsOfFn` when `ν_rel` is concentrated
on a single abstract state `s` (`[D.HasStepFn stepFn]`). -/
theorem ExecSteps.toOfFn {C : StateTransitionImpl P D w base params s₀}
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
    {s : D.State} {ops : List D.Op}
    {ν_rel ν_final : PMF (CoupledRState C.Seed D.State r_ds)} {T_ops C_ops : ℝ≥0∞}
    (hex : C.ExecSteps ops ν_rel ν_final T_ops C_ops) (hs : ∀ t ∈ ν_rel.support, t.state = s) :
    C.ExecStepsOfFn s ops (ν_rel.map fun t => (t.seed, t.data))
      (ν_final.map fun t => (t.seed, t.data)) T_ops ∧
    C_ops = (D.totalCost C.charge s ops : ℝ≥0∞) ∧
    (∀ q ∈ ν_final.support, q.state = (D.run s ops).1) := by
  induction hex generalizing s with
  | nil ν_rel => exact ⟨.nil s _, by simp, hs⟩
  | @cons o ops ν_rel ν_final μ_step T_step T_rest C_rest hstep _ ih =>
    let proj : CoupledRState C.Seed D.State r_ds → C.Seed × RData r_ds := fun t => (t.seed, t.data)
    let lift : C.Seed × RData r_ds → CoupledRState C.Seed D.State r_ds := fun p => ⟨p.1, s, p.2⟩
    have hlift_proj : ∀ t ∈ ν_rel.support, lift (proj t) = t := by
      intro ⟨θ, s_t, x⟩ ht; have heq := hs ⟨θ, s_t, x⟩ ht; subst heq; rfl
    have hs₁ : ∀ q ∈ (ν_rel.bind μ_step).support, q.state = (D.stepFn s o).1 := by
      intro q hq; rw [PMF.mem_support_bind_iff] at hq; obtain ⟨t, ht, hq_s⟩ := hq
      obtain ⟨a, hstep_a, _, _, _⟩ := (hstep t ht).2 q hq_s; rw [hs t ht] at hstep_a
      exact congrArg Prod.fst ((D.step_iff_stepFn s o q.state a).mp hstep_a)
    obtain ⟨hex_rest_det, hC_rest, hs_final⟩ := ih hs₁
    let μ_det : C.Seed × RData r_ds → PMF (C.Seed × RData r_ds) :=
      fun p => (μ_step (lift p)).map proj
    let T_det : C.Seed × RData r_ds → ℝ≥0∞ := fun p => T_step (lift p)
    have hbind_eq : (ν_rel.map proj).bind μ_det = (ν_rel.bind μ_step).map proj := by
      rw [PMF.bind_map, PMF.map_bind]; ext q
      simp only [PMF.bind_apply, Function.comp_apply, μ_det]
      exact Cslib.Probability.PMF.tsum_mul_congr_support ν_rel fun t ht => by rw [hlift_proj t ht]
    have hT_eq : (∑' p, (ν_rel.map proj) p * T_det p) = ∑' t, ν_rel t * T_step t := by
      rw [Cslib.Probability.PMF.tsum_map_mul]
      exact Cslib.Probability.PMF.tsum_mul_congr_support ν_rel fun t ht => by
        dsimp only [T_det]; rw [hlift_proj t ht]
    have hC_eq : (∑' t, ν_rel t * (C.charge t.state o : ℝ≥0∞)) = (C.charge s o : ℝ≥0∞) :=
      (Cslib.Probability.PMF.tsum_mul_congr_support ν_rel fun t ht => by rw [hs t ht]).trans
        (by rw [ENNReal.tsum_mul_right, ν_rel.tsum_coe, one_mul])
    refine ⟨?_, ?_, fun q hq => by simp only [StateTransitionSpec.run_cons]; exact hs_final q hq⟩
    · rw [← hT_eq]
      refine .cons (μ_step := μ_det) (T_step := T_det) ?_ (hbind_eq ▸ hex_rest_det)
      intro p hp; rw [PMF.mem_support_map_iff] at hp; obtain ⟨t, ht, rfl⟩ := hp
      obtain ⟨he_rel, hq_rel⟩ := hstep (lift (proj t)) ((hlift_proj t ht).symm ▸ ht)
      refine ⟨he_rel.congr_dist (by dsimp only [μ_det]; rw [PMF.map_comp]; rfl) le_rfl, ?_⟩
      intro q hq; dsimp only [μ_det] at hq; rw [PMF.mem_support_map_iff] at hq
      obtain ⟨q_rel, hq_mem, rfl⟩ := hq
      obtain ⟨a, hstep_a, hdec, hrep', hcaller⟩ := hq_rel q_rel hq_mem
      have hpair := (D.step_iff_stepFn s o q_rel.state a).mp hstep_a
      exact ⟨congrArg Prod.snd hpair ▸ hdec, congrArg Prod.fst hpair ▸ hrep', hcaller⟩
    · simp only [hC_eq, hC_rest, StateTransitionSpec.totalCost_cons, Nat.cast_add]

/-- **Trajectory-relative expected-amortized telescope for functional specifications
(`steps_expected_amortized_ofFn`).** -/
theorem steps_expected_amortized_ofFn (C : StateTransitionImpl P D w base params s₀)
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
    {s : D.State} (ops : List D.Op) (ν : PMF (C.Seed × RData r_ds))
    (hv : D.ValidHistory s ops) (hfit : PeakFitsHistory w base C.peakSpaceBound s ops)
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw s θ)
    (hrep : ∀ p ∈ ν.support, C.rep p.1 s p.2) :
    ∃ (ν_final : PMF (C.Seed × RData r_ds)) (T_ops : ℝ≥0∞),
      C.ExecStepsOfFn s ops ν ν_final T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw (D.run s ops).1 θ) ∧
      (∀ p ∈ ν_final.support, C.rep p.1 (D.run s ops).1 p.2) ∧
      T_ops + (∑' q, ν_final q * (C.potential q.1 q.2 : ℝ≥0∞)) ≤
        (D.totalCost C.charge s ops : ℝ≥0∞) + ∑' p, ν p * (C.potential p.1 p.2 : ℝ≥0∞) := by
  let lift : C.Seed × RData r_ds → CoupledRState C.Seed D.State r_ds := fun p => ⟨p.1, s, p.2⟩
  let proj : CoupledRState C.Seed D.State r_ds → C.Seed × RData r_ds := fun t => (t.seed, t.data)
  let ν_rel := ν.map lift
  have hs₀ : ∀ t ∈ ν_rel.support, t.state = s := by
    intro t ht; rw [PMF.mem_support_map_iff] at ht; obtain ⟨_, _, rfl⟩ := ht; rfl
  have hv_rel : ∀ t ∈ ν_rel.support, D.ValidOpSeq t.state ops :=
    fun t ht => by rw [hs₀ t ht]; exact (D.validOpSeq_iff_validHistory s ops).mpr hv
  have hfit_rel : ∀ t ∈ ν_rel.support, PeakFitsOpSeq w base C.peakSpaceBound t.state ops :=
    fun t ht => by
      rw [hs₀ t ht]
      exact (peakFitsOpSeq_iff_peakFitsHistory w base C.peakSpaceBound s ops).mpr hfit
  have hseed_rel : ∀ s', (∀ t ∈ ν_rel.support, t.state = s') →
      ∀ θ, (ν_rel.map CoupledRState.seed) θ ≤ C.seedSlack * C.seedLaw s' θ := by
    intro s' hs' θ
    obtain ⟨t₀, ht₀⟩ := ν_rel.support_nonempty
    have hs'_eq : s' = s := (hs' t₀ ht₀).symm.trans (hs₀ t₀ ht₀)
    subst hs'_eq; rw [PMF.map_comp]; exact hseed θ
  have hrep_rel : ∀ t ∈ ν_rel.support, C.rep t.seed t.state t.data := by
    intro t ht; rw [PMF.mem_support_map_iff] at ht; obtain ⟨p, hp, rfl⟩ := ht; exact hrep p hp
  obtain ⟨ν_final_rel, T_ops, C_ops, hex_rel, hseed_final, hrep_final, hamort⟩ :=
    C.steps_expected_amortized ops ν_rel hv_rel hfit_rel hseed_rel hrep_rel (fun _ => ⟨s, hs₀⟩)
  obtain ⟨hex_det, rfl, hs_final⟩ := hex_rel.toOfFn hs₀
  have hproj_lift : ν_rel.map proj = ν := by
    dsimp only [ν_rel]; rw [PMF.map_comp]; exact PMF.map_id ν
  refine ⟨ν_final_rel.map proj, T_ops, hproj_lift ▸ hex_det,
    fun θ => by rw [PMF.map_comp]; exact hseed_final (D.run s ops).1 hs_final θ,
    fun p hp => by
      rw [PMF.mem_support_map_iff] at hp; obtain ⟨q, hq, rfl⟩ := hp
      exact hs_final q hq ▸ hrep_final q hq, ?_⟩
  rw [Cslib.Probability.PMF.tsum_map_mul]
  have hpot_init :=
    Cslib.Probability.PMF.tsum_map_mul ν lift fun t => (C.potential t.seed t.data : ℝ≥0∞)
  rw [← hpot_init]; exact hamort

/-- `ExecStepsOfFn` preserves caller memory `[0, base)` across all support states. -/
theorem ExecStepsOfFn.caller_mem {C : StateTransitionImpl P D w base params s₀}
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
    {s : D.State} {ops : List D.Op} {ν ν_final : PMF (C.Seed × RData r_ds)} {T_ops : ℝ≥0∞}
    (h : C.ExecStepsOfFn s ops ν ν_final T_ops) {mem₀ : ℕ → ℕ}
    (h₀ : ∀ p ∈ ν.support, ∀ addr < base, p.2.mem addr = mem₀ addr) :
    ∀ q ∈ ν_final.support, ∀ addr < base, q.2.mem addr = mem₀ addr := by
  induction h with
  | nil _ _ => exact h₀
  | cons hstep _ ih =>
    refine ih fun q hq addr hlt => ?_
    rw [PMF.mem_support_bind_iff] at hq; obtain ⟨p, hp, hq_p⟩ := hq
    exact ((hstep p hp).2 q hq_p).2.2 addr hlt |>.trans (h₀ p hp addr hlt)

/-- **End-to-end expected-amortized sequence theorem for functional specifications
(`seq_expected_amortized_ofFn`).** -/
theorem seq_expected_amortized_ofFn (C : StateTransitionImpl P D w base params s₀)
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
    {x₀ : RData r_ds} (ops : List D.Op)
    (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hpar : ∀ j, x₀.regs (P.initParams j) = params j)
    (hfit₀ : Fits w (base + C.spaceBound s₀))
    (hv : D.ValidHistory s₀ ops) (hfit_ops : PeakFitsHistory w base C.peakSpaceBound s₀ ops) :
    ∃ (ν₀ ν_final : PMF (C.Seed × RData r_ds)) (T_ops : ℝ≥0∞),
      ExecRCodeDist w P.initCode x₀ (ν₀.map Prod.snd) C.initTime (base + C.spaceBound s₀) ∧
      (∀ p ∈ ν₀.support, C.rep p.1 s₀ p.2 ∧ ∀ addr < base, p.2.mem addr = x₀.mem addr) ∧
      C.ExecStepsOfFn s₀ ops ν₀ ν_final T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw (D.run s₀ ops).1 θ) ∧
      (∀ p ∈ ν_final.support,
        C.rep p.1 (D.run s₀ ops).1 p.2 ∧ ∀ addr < base, p.2.mem addr = x₀.mem addr) ∧
      C.initTime + T_ops + (∑' q, ν_final q * (C.potential q.1 q.2 : ℝ≥0∞)) ≤
        C.initTime + (C.initPotential : ℝ≥0∞) + (D.totalCost C.charge s₀ ops : ℝ≥0∞) := by
  obtain ⟨ν₀, he_init, hseed₀, hsupp₀⟩ := C.init_exec hx₀ hfr₀ hpar hfit₀
  obtain ⟨ν_final, T_ops, hex, hseed_final, hrep_final, hamort⟩ :=
    C.steps_expected_amortized_ofFn ops ν₀ hv hfit_ops hseed₀ fun p hp => (hsupp₀ p hp).1
  have hcaller_final := hex.caller_mem (mem₀ := x₀.mem) fun p hp => (hsupp₀ p hp).2.2
  have hpot₀ : (∑' p, ν₀ p * (C.potential p.1 p.2 : ℝ≥0∞)) ≤ (C.initPotential : ℝ≥0∞) :=
    Cslib.Probability.PMF.tsum_mul_le_of_support ν₀ fun p hp => Nat.cast_le.mpr (hsupp₀ p hp).2.1
  refine ⟨ν₀, ν_final, T_ops, he_init, fun p hp => ⟨(hsupp₀ p hp).1, (hsupp₀ p hp).2.2⟩,
    hex, hseed_final, fun q hq => ⟨hrep_final q hq, hcaller_final q hq⟩, ?_⟩
  rw [add_assoc, add_assoc, add_comm (C.initPotential : ℝ≥0∞)]
  exact add_le_add le_rfl (hamort.trans (add_le_add le_rfl hpot₀))

/-! ## Compilation to flat `ExecRProgramDist` and `.halt` rejection -/

/-- Relational multi-operation flat-`RProgram` execution relation over `ExecRProgramDist`. -/
inductive ExecProgramSteps (C : StateTransitionImpl P D w base params s₀)
    (p_op : RProgram B r_ds) (out : Fin r_ds) :
    List D.Op → PMF (CoupledRState C.Seed D.State r_ds) →
      PMF (CoupledRState C.Seed D.State r_ds) → ℝ≥0∞ → ℝ≥0∞ → Prop where
  | nil (ν : PMF (CoupledRState C.Seed D.State r_ds)) :
      C.ExecProgramSteps p_op out [] ν ν 0 0
  | cons {o : D.Op} {ops : List D.Op}
      {ν ν_final : PMF (CoupledRState C.Seed D.State r_ds)}
      {μ_step : CoupledRState C.Seed D.State r_ds → PMF (CoupledRState C.Seed D.State r_ds)}
      {T_step : CoupledRState C.Seed D.State r_ds → ℝ≥0∞} {T_rest C_rest : ℝ≥0∞} :
      (∀ t ∈ ν.support,
        ExecRProgramDist w p_op out (C.prepare o t.data)
          ((μ_step t).map CoupledRState.data) (T_step t) (base + C.peakSpaceBound t.state o) ∧
        ∀ q ∈ (μ_step t).support,
          ∃ a : D.Result o,
            D.step t.state o q.state a ∧
            C.decode o q.data.regs = some a ∧
            C.rep q.seed q.state q.data ∧
            (∀ addr < base, q.data.mem addr = t.data.mem addr)) →
      C.ExecProgramSteps p_op out ops (ν.bind μ_step) ν_final T_rest C_rest →
      C.ExecProgramSteps p_op out (o :: ops) ν ν_final
        ((∑' t, ν t * T_step t) + T_rest)
        ((∑' t, ν t * (C.charge t.state o : ℝ≥0∞)) + C_rest)

/-- Functional multi-operation flat-`RProgram` execution relation over `ExecRProgramDist`. -/
inductive ExecProgramStepsOfFn (C : StateTransitionImpl P D w base params s₀)
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
    (p_op : RProgram B r_ds) (out : Fin r_ds) :
    D.State → List D.Op → PMF (C.Seed × RData r_ds) → PMF (C.Seed × RData r_ds) → ℝ≥0∞ → Prop where
  | nil (s : D.State) (ν : PMF (C.Seed × RData r_ds)) :
      C.ExecProgramStepsOfFn p_op out s [] ν ν 0
  | cons {s : D.State} {o : D.Op} {ops : List D.Op}
      {ν ν_final : PMF (C.Seed × RData r_ds)}
      {μ_step : C.Seed × RData r_ds → PMF (C.Seed × RData r_ds)}
      {T_step : C.Seed × RData r_ds → ℝ≥0∞} {T_rest : ℝ≥0∞} :
      (∀ p ∈ ν.support,
        ExecRProgramDist w p_op out (C.prepare o p.2)
          ((μ_step p).map Prod.snd) (T_step p) (base + C.peakSpaceBound s o) ∧
        ∀ q ∈ (μ_step p).support,
          C.decode o q.2.regs = some (D.stepFn s o).2 ∧
          C.rep q.1 (D.stepFn s o).1 q.2 ∧
          (∀ addr < base, q.2.mem addr = p.2.mem addr)) →
      C.ExecProgramStepsOfFn p_op out (D.stepFn s o).1 ops (ν.bind μ_step) ν_final T_rest →
      C.ExecProgramStepsOfFn p_op out s (o :: ops) ν ν_final ((∑' p, ν p * T_step p) + T_rest)

/-- Expected per-step `+ 1` `halt` charge accumulated over `o :: ops`. -/
theorem tsum_add_one_add_length_cons {α : Type*} {β : Type*}
    (ν : PMF α) (T_step : α → ℝ≥0∞) (T_rest : ℝ≥0∞) (o : β) (ops : List β) :
    (∑' a, ν a * (T_step a + 1)) + (T_rest + (ops.length : ℝ≥0∞)) =
      ((∑' a, ν a * T_step a) + T_rest) + ((o :: ops).length : ℝ≥0∞) := by
  simp_rw [mul_add, tsum_add, mul_one, ν.tsum_coe, List.length_cons, Nat.cast_add, Nat.cast_one]
  ac_rfl

/-- Compile a structured `C.ExecSteps` derivation to `C.ExecProgramSteps (P.opProg out) out`,
charging `+ 1` instruction per operation for the trailing `halt out`. -/
theorem ExecSteps.toExecRProgramDist {C : StateTransitionImpl P D w base params s₀}
    (out : Fin r_ds) {ops : List D.Op}
    {ν ν_final : PMF (CoupledRState C.Seed D.State r_ds)} {T_ops C_ops : ℝ≥0∞}
    (h : C.ExecSteps ops ν ν_final T_ops C_ops) :
    C.ExecProgramSteps (P.opProg out) out ops ν ν_final (T_ops + (ops.length : ℝ≥0∞)) C_ops := by
  induction h with
  | nil ν => simpa using ExecProgramSteps.nil ν
  | @cons o ops ν ν_final μ_step T_step T_rest C_rest hstep _ ih =>
    rw [← tsum_add_one_add_length_cons ν T_step T_rest o ops]
    refine .cons (μ_step := μ_step) (T_step := fun t => T_step t + 1) (fun t ht => ?_) ih
    obtain ⟨he, hq⟩ := hstep t ht
    exact ⟨he.toExecRProgramDist out, hq⟩

/-- Compile a structured `C.ExecStepsOfFn` derivation to
`C.ExecProgramStepsOfFn (P.opProg out) out`. -/
theorem ExecStepsOfFn.toExecRProgramDist {C : StateTransitionImpl P D w base params s₀}
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
    (out : Fin r_ds) {s : D.State} {ops : List D.Op}
    {ν ν_final : PMF (C.Seed × RData r_ds)} {T_ops : ℝ≥0∞}
    (h : C.ExecStepsOfFn s ops ν ν_final T_ops) :
    C.ExecProgramStepsOfFn (P.opProg out) out s ops ν ν_final (T_ops + (ops.length : ℝ≥0∞)) := by
  induction h with
  | nil s ν => simpa using ExecProgramStepsOfFn.nil s ν
  | @cons s o ops ν ν_final μ_step T_step T_rest hstep _ ih =>
    rw [← tsum_add_one_add_length_cons ν T_step T_rest o ops]
    refine .cons (μ_step := μ_step) (T_step := fun p => T_step p + 1) (fun p hp => ?_) ih
    obtain ⟨he, hq⟩ := hstep p hp
    exact ⟨he.toExecRProgramDist out, hq⟩

private theorem add_halt_amort_le {a b c d e L : ℝ≥0∞} (h : a + b + c ≤ a + d + e) :
    (a + 1) + (b + L) + c ≤ (a + 1) + d + e + L :=
  calc (a + 1) + (b + L) + c = (a + b + c) + 1 + L := by ac_rfl
    _ ≤ (a + d + e) + 1 + L := add_le_add (add_le_add h le_rfl) le_rfl
    _ = (a + 1) + d + e + L := by ac_rfl

/-- **End-to-end flat-`RProgram` expected-amortized theorem (`seq_toExecRProgramDist`).** -/
theorem seq_toExecRProgramDist (C : StateTransitionImpl P D w base params s₀)
    (out : Fin r_ds) {x₀ : RData r_ds} (ops : List D.Op)
    (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hpar : ∀ j, x₀.regs (P.initParams j) = params j) (hfit₀ : Fits w (base + C.spaceBound s₀))
    (hv : D.ValidOpSeq s₀ ops) (hfit_ops : PeakFitsOpSeq w base C.peakSpaceBound s₀ ops) :
    ∃ (ν₀ : PMF (C.Seed × RData r_ds))
      (ν_final : PMF (CoupledRState C.Seed D.State r_ds)) (T_prog C_ops : ℝ≥0∞),
      ExecRProgramDist w (P.initProg out) out x₀ (ν₀.map Prod.snd) (C.initTime + 1)
        (base + C.spaceBound s₀) ∧
      (∀ p ∈ ν₀.support, C.rep p.1 s₀ p.2 ∧ ∀ addr < base, p.2.mem addr = x₀.mem addr) ∧
      C.ExecProgramSteps (P.opProg out) out ops (ν₀.map fun p => ⟨p.1, s₀, p.2⟩)
        ν_final T_prog C_ops ∧
      (∀ q ∈ ν_final.support,
        C.rep q.seed q.state q.data ∧ ∀ addr < base, q.data.mem addr = x₀.mem addr) ∧
      (C.initTime + 1) + T_prog + (∑' q, ν_final q * (C.potential q.seed q.data : ℝ≥0∞)) ≤
        (C.initTime + 1) + (C.initPotential : ℝ≥0∞) + C_ops + (ops.length : ℝ≥0∞) := by
  obtain ⟨ν₀, ν_final, T_ops, C_ops, he_init, hinit_supp, hex, _, hfin_supp, hamort⟩ :=
    C.seq_expected_amortized ops hx₀ hfr₀ hpar hfit₀ hv hfit_ops
  exact ⟨ν₀, ν_final, T_ops + (ops.length : ℝ≥0∞), C_ops, he_init.toExecRProgramDist out,
    hinit_supp, hex.toExecRProgramDist out, hfin_supp, add_halt_amort_le hamort⟩

/-- **End-to-end flat-`RProgram` expected-amortized theorem for functional specifications
(`seq_toExecRProgramDist_ofFn`).** -/
theorem seq_toExecRProgramDist_ofFn (C : StateTransitionImpl P D w base params s₀)
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
    (out : Fin r_ds) {x₀ : RData r_ds} (ops : List D.Op)
    (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hpar : ∀ j, x₀.regs (P.initParams j) = params j) (hfit₀ : Fits w (base + C.spaceBound s₀))
    (hv : D.ValidHistory s₀ ops) (hfit_ops : PeakFitsHistory w base C.peakSpaceBound s₀ ops) :
    ∃ (ν₀ ν_final : PMF (C.Seed × RData r_ds)) (T_prog : ℝ≥0∞),
      ExecRProgramDist w (P.initProg out) out x₀ (ν₀.map Prod.snd) (C.initTime + 1)
        (base + C.spaceBound s₀) ∧
      (∀ p ∈ ν₀.support, C.rep p.1 s₀ p.2 ∧ ∀ addr < base, p.2.mem addr = x₀.mem addr) ∧
      C.ExecProgramStepsOfFn (P.opProg out) out s₀ ops ν₀ ν_final T_prog ∧
      (∀ p ∈ ν_final.support,
        C.rep p.1 (D.run s₀ ops).1 p.2 ∧ ∀ addr < base, p.2.mem addr = x₀.mem addr) ∧
      (C.initTime + 1) + T_prog + (∑' q, ν_final q * (C.potential q.1 q.2 : ℝ≥0∞)) ≤
        (C.initTime + 1) + (C.initPotential : ℝ≥0∞) +
          (D.totalCost C.charge s₀ ops : ℝ≥0∞) + (ops.length : ℝ≥0∞) := by
  obtain ⟨ν₀, ν_final, T_ops, he_init, hinit_supp, hex, _, hfin_supp, hamort⟩ :=
    C.seq_expected_amortized_ofFn ops hx₀ hfr₀ hpar hfit₀ hv hfit_ops
  exact ⟨ν₀, ν_final, T_ops + (ops.length : ℝ≥0∞), he_init.toExecRProgramDist out,
    hinit_supp, hex.toExecRProgramDist out, hfin_supp, add_halt_amort_le hamort⟩

/-- **`.halt`-rejection soundness check (`not_execProgramSteps_halt`):** `[.halt out]` cannot
satisfy `C.ExecProgramSteps [.halt out] out` on `(o :: ops)` whenever some `t ∈ ν.support` has no
valid post-outcome `(θ', s', a)` represented by `C.prepare o t.data`. -/
theorem not_execProgramSteps_halt (C : StateTransitionImpl P D w base params s₀)
    (out : Fin r_ds) {o : D.Op} {ops : List D.Op}
    {ν ν_final : PMF (CoupledRState C.Seed D.State r_ds)} {T_prog C_ops : ℝ≥0∞}
    {t : CoupledRState C.Seed D.State r_ds} (ht : t ∈ ν.support)
    (hbad : ∀ θ' s' a, D.step t.state o s' a →
      ¬(C.decode o (C.prepare o t.data).regs = some a ∧ C.rep θ' s' (C.prepare o t.data))) :
    ¬C.ExecProgramSteps [.halt out] out (o :: ops) ν ν_final T_prog C_ops := by
  intro h; cases h with
  | @cons _ _ _ _ μ_step _ _ _ hstep _ =>
    obtain ⟨hprog, hq_all⟩ := hstep t ht
    obtain ⟨q, hq⟩ := (μ_step t).support_nonempty
    obtain ⟨a, hstep_a, hdec, hrep, _⟩ := hq_all q hq
    by_cases hqd : q.data = C.prepare o t.data
    · rw [hqd] at hdec hrep; exact hbad q.seed q.state a hstep_a ⟨hdec, hrep⟩
    · exact not_execRProgramDist_halt ((PMF.mem_support_map_iff _ _ _).mpr ⟨q, hq, rfl⟩) hqd hprog

/-- **`.halt`-rejection soundness check (`not_execProgramStepsOfFn_halt`)** for `HasStepFn`. -/
theorem not_execProgramStepsOfFn_halt (C : StateTransitionImpl P D w base params s₀)
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
    (out : Fin r_ds) {s : D.State} {o : D.Op} {ops : List D.Op}
    {ν ν_final : PMF (C.Seed × RData r_ds)} {T_prog : ℝ≥0∞}
    {p : C.Seed × RData r_ds} (hp : p ∈ ν.support)
    (hbad : ∀ θ',
      ¬(C.decode o (C.prepare o p.2).regs = some (D.stepFn s o).2 ∧
        C.rep θ' (D.stepFn s o).1 (C.prepare o p.2))) :
    ¬C.ExecProgramStepsOfFn [.halt out] out s (o :: ops) ν ν_final T_prog := by
  intro h; cases h with
  | @cons _ _ _ _ _ μ_step _ _ hstep _ =>
    obtain ⟨hprog, hq_all⟩ := hstep p hp
    obtain ⟨q, hq⟩ := (μ_step p).support_nonempty
    obtain ⟨hdec, hrep, _⟩ := hq_all q hq
    by_cases hqd : q.2 = C.prepare o p.2
    · rw [hqd] at hdec hrep; exact hbad q.1 ⟨hdec, hrep⟩
    · exact not_execRProgramDist_halt ((PMF.mem_support_map_iff _ _ _).mpr ⟨q, hq, rfl⟩) hqd hprog

end Cslib.DataStructure.WordRAM.Resizable.Randomized.StateTransitionImpl
