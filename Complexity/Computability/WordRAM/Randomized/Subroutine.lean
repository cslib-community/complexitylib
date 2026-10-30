/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Subroutine
public import Complexity.Computability.WordRAM.Randomized.Expected
import Complexity.Probability.PMF.Expect

/-!
# Composable Randomized Word-RAM Data-Structure Subroutines

This file extends the deterministic `Cslib.WordRAM.SubroutineDS` interface to **randomized data
structures and Las Vegas subroutines** on the Word-RAM — covering both structures initialized from a
random seed (such as universal hash tables, 2-choice hash tables, and cuckoo hash tables) and
structures whose operations make random choices via `Instr.rand` (such as treaps, skip lists,
reservoir samplers, or randomized rehashing); see [MitzenmacherUpfal2017], Sections 2.1, 2.3, and
2.4.

## Core design

A `Cslib.WordRAM.Randomized.SubroutineDS P D w base params s₀` couples machine execution with a
latent seed type `Seed : Type` and reference distribution `seedLaw : PMF Seed` up to a bounded
density factor `seedSlack : ℝ≥0∞`:

1. **Seed-coupled representation (`rep θ s x`) and potential (`potential θ x`):**
   - Data structures without a persistent random seed set `Seed := Unit`, `seedLaw := PMF.pure ()`,
     and `seedSlack := 1` (in particular, `Cslib.WordRAM.SubroutineDS.toRandomized` embeds every
     deterministic `Cslib.WordRAM.SubroutineDS` directly).
   - Hash tables that resample their hash family on rare table-full events maintain a joint
     distribution `ν : PMF (Seed × Data r_ds)` whose marginal on `Seed` satisfies
     `(ν.map Prod.fst) θ ≤ seedSlack * seedLaw θ`.

2. **Distributional execution (`ExecCodeDist`):**
   - `setup_exec` and `step_exec` use `ExecCodeDist` from
     `Complexity.Computability.WordRAM.Randomized.Expected`, which supports both bounded
     randomized code (`ExecRand`) and unbounded almost-surely terminating Las Vegas `while` loops
     (`ExecCodeDist.loop_geometric`).

3. **Addition-only `ℝ≥0∞` amortized-in-expectation bound:**
   - Every admissible operation `o : D.Op` from abstract state `s : D.State` and coupled state
     distribution `ν : PMF (Seed × Data r_ds)` produces a transition kernel
     `μ_step : Seed × Data r_ds → PMF (Seed × Data r_ds)` and expected step count
     `T_step : Seed × Data r_ds → ℝ≥0∞` satisfying (for `Φ(p) := potential p.1 p.2`)
     `∑' p, ν p * (T_step p + ∑' q, μ_step p q * Φ(q)) ≤ charge s o + ∑' p, ν p * Φ(p)`.
   - Across any admissible finite operation sequence `ops : List D.Op`, `seq_expected_amortized`
     telescopes these one-step bounds without `ℝ≥0∞` subtraction:
     total expected step cost is at most `initTime + initPotential + D.totalCost charge s₀ ops`.

The sequence theorems charge initialization and subroutine bodies for a fixed operation list.
`prepare` delivers each operation's arguments by a semantic register replacement; its encoding
and delivery, caller dispatch and a whole-client driver are not charged. Callers requiring native
argument preparation can use `call_rename`, whose `B_prep` explicitly charges the preparation
code. Compiling a standalone body adds the final halt separately via `ExecCodeDist.program_halts`.

## Main definitions

* `Cslib.WordRAM.Randomized.SubroutineDS`: reusable randomized Word-RAM subroutine certificate for
  a deterministic specification `D : Stateful.Spec`.
* `Cslib.WordRAM.Randomized.SubroutineDS.ExecSteps`: multi-operation distributional execution trace
  threading coupled state distributions and expected step costs across `ops : List D.Op`.
* `Cslib.WordRAM.SubroutineDS.toRandomized`: canonical embedding of any deterministic
  `Cslib.WordRAM.SubroutineDS` into `Cslib.WordRAM.Randomized.SubroutineDS`.
* `Cslib.WordRAM.Randomized.SubroutineDS.mapSimulates`, `toStandard`: basis transport from
  `Basis.exact` to `Basis.standard`.

## Main results

* `Cslib.WordRAM.Randomized.SubroutineDS.initFresh_exec`, `initFresh_rename`: expected-time
  initialization on fresh zeroed memory.
* `Cslib.WordRAM.SubroutineCode.zeroFillCode_exec`,
  `Cslib.WordRAM.Randomized.SubroutineDS.initClear_exec`, `initClear_rename`:
  expected-time initialization on arbitrary dirty memory.
* `Cslib.WordRAM.Randomized.SubroutineDS.code_rename`, `call_rename`: inline subroutine invocation
  on caller state space `Data r_caller` via register injection `f : Fin r_ds → Fin r_caller`.
* `Cslib.WordRAM.Randomized.SubroutineDS.frame_caller`, `frame_caller_dist`: preservation of `rep`,
  `potential`, and the coupled `(Seed × Data r_caller)` distribution across arbitrary deterministic
  or randomized caller steps that do not modify persistent DS registers (`P.input i = false`) or
  `[base, base + space)`.
* `Cslib.WordRAM.Randomized.SubroutineDS.steps_expected_amortized`, `seq_expected_amortized`:
  telescope theorems bounding initialization and expected body time across any admissible operation
  sequence `ops : List D.Op`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 17][CLRS2009]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing: Randomization and Probabilistic
  Techniques in Algorithms and Data Analysis*][MitzenmacherUpfal2017], Sections 2.1, 2.3, and 2.4.
-/

@[expose] public section

namespace Cslib.WordRAM.Randomized

open Cslib.WordRAM
open scoped ENNReal

universe u v z

/-- Unified standalone and inline subroutine specification/resource certificate for a randomized
Word-RAM data structure `P` realizing `D` at word width `w`, base address `base`, runtime
parameters `params`, and initial abstract state `s₀`. -/
structure SubroutineDS {B : Basis} {r_ds k_init : ℕ}
    (P : SubroutineCode B r_ds k_init) (D : Stateful.Spec.{u, v, z})
    (w base : ℕ) (params : Fin k_init → ℕ) (s₀ : D.State) : Type (max u v z 1) where
  /-- Latent random seed type (use `Unit` when no persistent seed is needed). -/
  Seed : Type
  /-- Reference distribution over latent seeds. -/
  seedLaw : PMF Seed
  /-- Marginal density slack factor (`1` when the seed distribution is exact). -/
  seedSlack : ℝ≥0∞ := 1
  /-- The marginal density slack factor is finite. -/
  seedSlack_ne_top : seedSlack ≠ ⊤ := by simp
  /-- Contiguous memory footprint length `[base, base + space)`. -/
  space : ℕ
  /-- Worst-case instruction bound for `P.allocSpan`. -/
  spanTime : ℕ
  /-- Expected instruction bound for `P.initSetup`. -/
  setupTime : ℝ≥0∞
  /-- Upper bound on initial concrete potential after initialization. -/
  initPotential : ℕ
  /-- Amortized instruction charge per operation. -/
  charge : D.State → D.Op → ℕ
  /-- Seed-indexed representation invariant linking `Seed`, `D.State`, and `Data r_ds`. -/
  rep : Seed → D.State → Data r_ds → Prop
  /-- Seed-indexed nonnegative integer potential. -/
  potential : Seed → Data r_ds → ℕ
  /-- Standalone register encoding for argument delivery. -/
  encode : D.Op → Fin r_ds → ℕ
  /-- Partial argument-matching predicate for inline callers (refined by `encode`). -/
  argMatch : D.Op → (Fin r_ds → ℕ) → Prop
  /-- Output decoder reading typed operation observations from final registers. -/
  decode : (o : D.Op) → (Fin r_ds → ℕ) → Option (D.Result o)
  /-- Represented configurations are word-bounded. -/
  bounded : ∀ {θ s x}, rep θ s x → x.Bounded w
  /-- For a fixed seed `θ`, concrete machine data determines at most one abstract state. -/
  rep_unique : ∀ {θ s₁ s₂ x}, rep θ s₁ x → rep θ s₂ x → s₁ = s₂
  /-- Standalone encoded arguments fit in `w`-bit words on admissible calls. -/
  arguments_fit : ∀ {s} (o), D.valid s o → ∀ i, P.input i = true → Fits w (encode o i)
  /-- Full standalone argument delivery satisfies `argMatch`. -/
  encode_matches : ∀ (o : D.Op) (regs : Fin r_ds → ℕ),
    argMatch o (fun i => if P.input i then encode o i else regs i)
  /-- `rep` depends only on persistent registers (`P.input i = false`) and `[base, base + space)`.
  -/
  rep_supported : ∀ {θ s x x'},
    (∀ i, P.input i = false → x'.regs i = x.regs i) →
    (∀ a ∈ (Block.mk base space).footprint, x'.mem a = x.mem a) →
    x'.Bounded w → rep θ s x → rep θ s x'
  /-- `potential` depends only on persistent registers and `[base, base + space)` under `rep`. -/
  potential_supported : ∀ {θ s x x'},
    (∀ i, P.input i = false → x'.regs i = x.regs i) →
    (∀ a ∈ (Block.mk base space).footprint, x'.mem a = x.mem a) →
    rep θ s x → potential θ x' = potential θ x
  /-- Distinctness of registers used by `zeroFillCode` relative to `baseReg` and `frontierReg`. -/
  clear_nodup : [P.curReg, P.zeroReg, P.oneReg, P.baseReg, P.frontierReg].Nodup
  /-- Initialization parameter registers are not overwritten by `zeroFillCode`. -/
  params_not_clear : ∀ j, P.initParams j ∉ [P.curReg, P.zeroReg, P.oneReg]
  /-- `P.incCur` increments `P.curReg` by `1` when `P.oneReg = 1` and the sum fits in `w` bits. -/
  incCur_eval : ∀ {x : Data r_ds}, x.regs P.oneReg = 1 → Fits w (x.regs P.curReg + 1) →
    P.incCur.eval w x = some (x.set P.curReg (x.regs P.curReg + 1))
  /-- Execution of `P.allocSpan`: records `baseReg = base` and advances `frontierReg`. -/
  span_exec : ∀ {x : Data r_ds},
    x.Bounded w → x.regs P.frontierReg = base → (∀ j, x.regs (P.initParams j) = params j) →
    ∃ x₁, ExecWithin w P.allocSpan x x₁ spanTime ∧ x₁.mem = x.mem ∧
      x₁.regs P.baseReg = base ∧ x₁.regs P.frontierReg = base + space ∧
      (∀ j, x₁.regs (P.initParams j) = params j)
  /-- Execution of `P.initSetup` once `[base, base + space)` holds zeros, producing a coupled
  distribution `ν₀ : PMF (Seed × Data r_ds)` whose seed marginal is bounded by
  `seedSlack * seedLaw`. -/
  setup_exec : ∀ {x₁ : Data r_ds},
    x₁.Bounded w → x₁.regs P.baseReg = base → x₁.regs P.frontierReg = base + space →
    (∀ j, x₁.regs (P.initParams j) = params j) →
    (∀ a ∈ (Block.mk base space).footprint, x₁.mem a = 0) →
    ∃ ν₀ : PMF (Seed × Data r_ds),
      ExecCodeDist w P.initSetup x₁ (ν₀.map Prod.snd) setupTime ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ seedSlack * seedLaw θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs P.frontierReg = base + space ∧
        rep p.1 s₀ p.2 ∧
        potential p.1 p.2 ≤ initPotential ∧
        Modifies (Block.mk base space).footprint x₁.mem p.2.mem
  /-- Coupled one-step execution of `P.code` for any admissible operation `o` from abstract state
  `s` and coupled state distribution `ν : PMF (Seed × Data r_ds)` with seed marginal bounded by
  `seedSlack * seedLaw`: produces a transition kernel `μ_step` and expected step count `T_step`
  preserving the seed-marginal bound, realizing `D.step s o`, modifying only `[base, base + space)`,
  and satisfying the addition-only `ℝ≥0∞` amortized-in-expectation inequality. -/
  step_exec : ∀ {s : D.State} (o : D.Op) (ν : PMF (Seed × Data r_ds)),
    D.valid s o →
    (∀ θ, (ν.map Prod.fst) θ ≤ seedSlack * seedLaw θ) →
    (∀ p ∈ ν.support, rep p.1 s p.2 ∧ argMatch o p.2.regs) →
    ∃ (μ_step : Seed × Data r_ds → PMF (Seed × Data r_ds))
      (T_step : Seed × Data r_ds → ℝ≥0∞),
      (∀ p ∈ ν.support,
        ExecCodeDist w P.code p.2 ((μ_step p).map Prod.snd) (T_step p) ∧
        ∀ q ∈ (μ_step p).support,
          decode o q.2.regs = some (D.step s o).2 ∧
          rep q.1 (D.step s o).1 q.2 ∧
          Modifies (Block.mk base space).footprint p.2.mem q.2.mem) ∧
      (∀ θ', ((ν.bind μ_step).map Prod.fst) θ' ≤ seedSlack * seedLaw θ') ∧
      (∑' p, ν p * (T_step p + ∑' q, μ_step p q * (potential q.1 q.2 : ℝ≥0∞))) ≤
        (charge s o : ℝ≥0∞) + ∑' p, ν p * (potential p.1 p.2 : ℝ≥0∞)

end Cslib.WordRAM.Randomized

namespace Cslib.WordRAM.SubroutineDS

open scoped ENNReal

universe u v z

variable {B : Basis} {r_ds k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init} {D : Stateful.Spec.{u, v, z}}
  {params : Fin k_init → ℕ} {s₀ : D.State}

/-- Canonical embedding of any deterministic `Cslib.WordRAM.SubroutineDS` certificate into
`Cslib.WordRAM.Randomized.SubroutineDS` (`Seed := Unit`, `seedLaw := PMF.pure ()`,
`seedSlack := 1`). -/
noncomputable def toRandomized (C : SubroutineDS P D w base params s₀) :
    Randomized.SubroutineDS P D w base params s₀ where
  Seed := Unit
  seedLaw := PMF.pure ()
  seedSlack := 1
  space := C.space
  spanTime := C.spanTime
  setupTime := C.setupTime
  initPotential := C.initPotential
  charge := C.charge
  rep _ s x := C.rep s x
  potential _ x := C.potential x
  encode := C.encode
  argMatch := C.argMatch
  decode := C.decode
  bounded := C.bounded
  rep_unique := C.rep_unique
  arguments_fit := C.arguments_fit
  encode_matches := C.encode_matches
  rep_supported := C.rep_supported
  potential_supported := C.potential_supported
  clear_nodup := C.clear_nodup
  params_not_clear := C.params_not_clear
  incCur_eval := C.incCur_eval
  span_exec := C.span_exec
  setup_exec hx₁ hb hfr hpar hz := by
    obtain ⟨y, he, hfr', hrep, hpot, hmod⟩ := C.setup_exec hx₁ hb hfr hpar hz
    refine ⟨PMF.pure ((), y), ?_, ?_, ?_⟩
    · simpa using ExecCodeDist.of_execWithin he
    · intro θ
      cases θ
      simp
    · intro p hp
      rw [PMF.support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hfr', hrep, hpot, hmod⟩
  step_exec {s} o ν hv _ hsupp := by
    classical
    let y : Unit × Data r_ds → Data r_ds := fun p =>
      if hp : C.rep s p.2 ∧ C.argMatch o p.2.regs then
        Classical.choose (C.step_exec o hp.1 hv hp.2)
      else p.2
    let n : Unit × Data r_ds → ℕ := fun p =>
      if hp : C.rep s p.2 ∧ C.argMatch o p.2.regs then
        Classical.choose (Classical.choose_spec (C.step_exec o hp.1 hv hp.2))
      else 0
    refine ⟨fun p => PMF.pure ((), y p), fun p => (n p : ℝ≥0∞), ?_, ?_, ?_⟩
    · intro p hp_mem
      have hp : C.rep s p.2 ∧ C.argMatch o p.2.regs := hsupp p hp_mem
      have hspec := Classical.choose_spec (Classical.choose_spec (C.step_exec o hp.1 hv hp.2))
      rcases hspec with ⟨he, hdec, hrep', hmod, _⟩
      have hy_eq : y p = Classical.choose (C.step_exec o hp.1 hv hp.2) := by simp [y, hp]
      have hn_eq : n p =
          Classical.choose (Classical.choose_spec (C.step_exec o hp.1 hv hp.2)) := by simp [n, hp]
      refine ⟨?_, ?_⟩
      · simpa [hy_eq, hn_eq] using ExecCodeDist.of_exec he
      · intro q hq
        rw [PMF.support_pure, Set.mem_singleton_iff] at hq
        subst hq
        simpa only [hy_eq] using ⟨hdec, hrep', hmod⟩
    · intro θ'
      cases θ'
      have hconst : ((ν.bind fun p => PMF.pure ((), y p)).map Prod.fst) () = 1 := by
        rw [PMF.map_bind]
        simp
      simp [hconst]
    · calc
        (∑' p, ν p * ((n p : ℝ≥0∞) + ∑' q, PMF.pure ((), y p) q * (C.potential q.2 : ℝ≥0∞)))
          ≤ ∑' p, ν p * ((C.charge s o : ℝ≥0∞) + (C.potential p.2 : ℝ≥0∞)) := by
            refine tsum_le_tsum fun p => ?_
            by_cases hp_mem : p ∈ ν.support
            · refine mul_le_mul_right ?_ _
              have hp : C.rep s p.2 ∧ C.argMatch o p.2.regs := hsupp p hp_mem
              have hspec :=
                Classical.choose_spec (Classical.choose_spec (C.step_exec o hp.1 hv hp.2))
              rcases hspec with ⟨_, _, _, _, hpot⟩
              have hy_eq : y p = Classical.choose (C.step_exec o hp.1 hv hp.2) := by simp [y, hp]
              have hn_eq : n p =
                  Classical.choose (Classical.choose_spec (C.step_exec o hp.1 hv hp.2)) := by
                simp [n, hp]
              rw [tsum_eq_single ((), y p) (fun q hq => by simp [PMF.pure_apply, hq])]
              simp only [PMF.pure_apply_self, one_mul, hy_eq, hn_eq]
              exact_mod_cast hpot
            · rw [(PMF.apply_eq_zero_iff _ _).mpr hp_mem, zero_mul, zero_mul]
        _ = (C.charge s o : ℝ≥0∞) + ∑' p, ν p * (C.potential p.2 : ℝ≥0∞) := by
            simp_rw [mul_add, tsum_add, ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]

end Cslib.WordRAM.SubroutineDS

namespace Cslib.WordRAM.Randomized.SubroutineDS

open Cslib.WordRAM
open scoped ENNReal

universe u v z

variable {B B' : Basis} {r_ds r_caller k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init} {D : Stateful.Spec.{u, v, z}}
  {params : Fin k_init → ℕ} {s₀ : D.State}

/-- Total expected instruction bound for `P.initFresh`. -/
def initTime (C : SubroutineDS P D w base params s₀) : ℝ≥0∞ :=
  (C.spanTime : ℝ≥0∞) + C.setupTime

/-! ### Projection 1: Basis lifting (`mapSimulates`, `toStandard`) -/

/-- Lift a randomized `SubroutineDS` certificate along any defined-evaluation basis simulation. -/
def mapSimulates (φ : B.Simulates B') (C : SubroutineDS P D w base params s₀) :
    SubroutineDS (P.mapSimulates φ) D w base params s₀ where
  Seed := C.Seed
  seedLaw := C.seedLaw
  seedSlack := C.seedSlack
  seedSlack_ne_top := C.seedSlack_ne_top
  space := C.space
  spanTime := C.spanTime
  setupTime := C.setupTime
  initPotential := C.initPotential
  charge := C.charge
  rep := C.rep
  potential := C.potential
  encode := C.encode
  argMatch := C.argMatch
  decode := C.decode
  bounded := C.bounded
  rep_unique := C.rep_unique
  arguments_fit := C.arguments_fit
  encode_matches := C.encode_matches
  rep_supported := C.rep_supported
  potential_supported := C.potential_supported
  clear_nodup := C.clear_nodup
  params_not_clear := C.params_not_clear
  incCur_eval h1 hfit := Op.eval_mapSimulates_of_some φ (C.incCur_eval h1 hfit)
  span_exec hx hf hp :=
    let ⟨x₁, he, hm, hb, hfr, hpar⟩ := C.span_exec hx hf hp
    ⟨x₁, he.mapSimulates φ, hm, hb, hfr, hpar⟩
  setup_exec hx₁ hb hfr hpar hz :=
    let ⟨ν₀, he, hseed, hsupp⟩ := C.setup_exec hx₁ hb hfr hpar hz
    ⟨ν₀, he.mapSimulates φ, hseed, hsupp⟩
  step_exec o ν hv hseed hsupp :=
    let ⟨μ_step, T_step, hstep, hseed', hamort⟩ := C.step_exec o ν hv hseed hsupp
    ⟨μ_step, T_step,
      fun p hp => ⟨(hstep p hp).1.mapSimulates φ, (hstep p hp).2⟩,
      hseed', hamort⟩

/-- Lift an exact-basis randomized `SubroutineDS` certificate to `Basis.standard`. -/
abbrev toStandard {P : SubroutineCode .exact r_ds k_init}
    (C : SubroutineDS P D w base params s₀) :
    SubroutineDS P.toStandard D w base params s₀ :=
  C.mapSimulates .exactStandard

/-! ### Projection 2: Fresh initialization and register relocation (`initFresh_exec`,
`initFresh_rename`) -/

/-- Execute `P.initFresh` on zeroed `[base, base + C.space)` in `C.initTime` expected
instructions. -/
theorem initFresh_exec (C : SubroutineDS P D w base params s₀) {x : Data r_ds}
    (hx : x.Bounded w) (hfr : x.regs P.frontierReg = base)
    (hpar : ∀ j, x.regs (P.initParams j) = params j)
    (hz : ∀ a ∈ (Block.mk base C.space).footprint, x.mem a = 0) :
    ∃ ν₀ : PMF (C.Seed × Data r_ds),
      ExecCodeDist w P.initFresh x (ν₀.map Prod.snd) C.initTime ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs P.frontierReg = base + C.space ∧
        C.rep p.1 s₀ p.2 ∧
        C.potential p.1 p.2 ≤ C.initPotential ∧
        Modifies (Block.mk base C.space).footprint x.mem p.2.mem := by
  obtain ⟨x₁, he₁, hm₁, hb₁, hfr₁, hpar₁⟩ := C.span_exec hx hfr hpar
  have hx₁ : x₁.Bounded w := he₁.bounded hx
  have hz₁ : ∀ a ∈ (Block.mk base C.space).footprint, x₁.mem a = 0 := by
    intro a ha
    rw [hm₁]
    exact hz a ha
  obtain ⟨ν₀, he₂, hseed, hsupp⟩ := C.setup_exec hx₁ hb₁ hfr₁ hpar₁ hz₁
  rw [hm₁] at hsupp
  exact ⟨ν₀, (ExecCodeDist.of_execWithin he₁).seq_pure he₂, hseed, hsupp⟩

private theorem init_rename_of_exec (C : SubroutineDS P D w base params s₀)
    {c : Code B r_ds} {T : ℝ≥0∞} {f : Fin r_ds → Fin r_caller} (hf : f.Injective)
    {x : Data r_caller}
    (hex : ∃ ν₀ : PMF (C.Seed × Data r_ds),
      ExecCodeDist w c (x.comap f) (ν₀.map Prod.snd) T ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs P.frontierReg = base + C.space ∧
        C.rep p.1 s₀ p.2 ∧
        C.potential p.1 p.2 ≤ C.initPotential ∧
        Modifies (Block.mk base C.space).footprint (x.comap f).mem p.2.mem) :
    ∃ ν₀ : PMF (C.Seed × Data r_caller),
      ExecCodeDist w (c.rename f) x (ν₀.map Prod.snd) T ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs (f P.frontierReg) = base + C.space ∧
        C.rep p.1 s₀ (p.2.comap f) ∧
        C.potential p.1 (p.2.comap f) ≤ C.initPotential ∧
        Modifies (Block.mk base C.space).footprint x.mem p.2.mem ∧
        (∀ j ∉ Set.range f, p.2.regs j = x.regs j) := by
  obtain ⟨ν₀, he, hseed, hsupp⟩ := hex
  refine ⟨ν₀.map fun p => (p.1, p.2.extend f x), ?_, ?_, ?_⟩
  · have he' := he.rename hf
    refine he'.congr_dist ?_ le_rfl
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  · intro θ
    rw [PMF.map_comp]
    exact hseed θ
  · intro q hq
    rw [PMF.mem_support_map_iff] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    obtain ⟨hfr', hrep, hpot, hmod⟩ := hsupp p hp
    refine ⟨?_, ?_, ?_, hmod, fun j hj => Data.extend_regs_of_notMem p.2 x hj⟩
    · change ((p.2.extend f x).comap f).regs P.frontierReg = base + C.space
      rw [Data.comap_extend hf]
      exact hfr'
    · rw [Data.comap_extend hf]
      exact hrep
    · rw [Data.comap_extend hf]
      exact hpot

/-- Relocated fresh initialization along any injective register embedding `f`. -/
theorem initFresh_rename (C : SubroutineDS P D w base params s₀)
    {f : Fin r_ds → Fin r_caller} (hf : f.Injective) {x : Data r_caller}
    (hx : (x.comap f).Bounded w) (hfr : x.regs (f P.frontierReg) = base)
    (hpar : ∀ j, x.regs (f (P.initParams j)) = params j)
    (hz : ∀ a ∈ (Block.mk base C.space).footprint, x.mem a = 0) :
    ∃ ν₀ : PMF (C.Seed × Data r_caller),
      ExecCodeDist w (P.initFresh.rename f) x (ν₀.map Prod.snd) C.initTime ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs (f P.frontierReg) = base + C.space ∧
        C.rep p.1 s₀ (p.2.comap f) ∧
        C.potential p.1 (p.2.comap f) ≤ C.initPotential ∧
        Modifies (Block.mk base C.space).footprint x.mem p.2.mem ∧
        (∀ j ∉ Set.range f, p.2.regs j = x.regs j) :=
  C.init_rename_of_exec hf (C.initFresh_exec hx hfr hpar hz)

/-! ### Projection 3: Generic `O(space)` dirty-memory initialization (`zeroFillCode_exec`,
`initClear_exec`, `initClear_rename`) -/

/-- Execute `P.initClear` on **arbitrary dirty memory** in
`C.initTime + (4 * C.space + 6 : ℕ)` expected instructions. -/
theorem initClear_exec (C : SubroutineDS P D w base params s₀) {x : Data r_ds}
    (hx : x.Bounded w) (hfr : x.regs P.frontierReg = base)
    (hpar : ∀ j, x.regs (P.initParams j) = params j) :
    ∃ ν₀ : PMF (C.Seed × Data r_ds),
      ExecCodeDist w P.initClear x (ν₀.map Prod.snd)
        (C.initTime + (4 * C.space + 6 : ℕ)) ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs P.frontierReg = base + C.space ∧
        C.rep p.1 s₀ p.2 ∧
        C.potential p.1 p.2 ≤ C.initPotential ∧
        Modifies (Block.mk base C.space).footprint x.mem p.2.mem := by
  obtain ⟨x₁, he₁, hm₁, hb₁, hfr₁, hpar₁⟩ := C.span_exec hx hfr hpar
  obtain ⟨x₂, he₂, hx₂, hb₂, hfr₂, hpar₂, hz₂, hmod₂⟩ :=
    P.zeroFillCode_exec C.clear_nodup C.params_not_clear C.incCur_eval
      (he₁.bounded hx) hb₁ hfr₁ hpar₁
  obtain ⟨ν₀, he₃, hseed, hsupp⟩ := C.setup_exec hx₂ hb₂ hfr₂ hpar₂ hz₂
  rw [hm₁] at hmod₂
  have he_clear : ExecCodeDist w P.initClear x (ν₀.map Prod.snd)
      ((C.spanTime : ℝ≥0∞) + ((4 * C.space + 6 : ℕ) + C.setupTime)) :=
    (ExecCodeDist.of_execWithin he₁).seq_pure ((ExecCodeDist.of_execWithin he₂).seq_pure he₃)
  refine ⟨ν₀, he_clear.mono ?_, hseed, fun p hp => ?_⟩
  · unfold initTime
    exact le_of_eq (by ac_rfl)
  · obtain ⟨hfr₃, hrep, hpot, hmod₃⟩ := hsupp p hp
    have hmod : Modifies (Block.mk base C.space).footprint x.mem p.2.mem := by
      simpa only [Finset.union_idempotent] using hmod₂.trans hmod₃
    exact ⟨hfr₃, hrep, hpot, hmod⟩

/-- Relocated `O(space)` dirty-memory initialization along any injective register embedding `f`. -/
theorem initClear_rename (C : SubroutineDS P D w base params s₀)
    {f : Fin r_ds → Fin r_caller} (hf : f.Injective) {x : Data r_caller}
    (hx : (x.comap f).Bounded w) (hfr : x.regs (f P.frontierReg) = base)
    (hpar : ∀ j, x.regs (f (P.initParams j)) = params j) :
    ∃ ν₀ : PMF (C.Seed × Data r_caller),
      ExecCodeDist w (P.initClear.rename f) x (ν₀.map Prod.snd)
        (C.initTime + (4 * C.space + 6 : ℕ)) ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs (f P.frontierReg) = base + C.space ∧
        C.rep p.1 s₀ (p.2.comap f) ∧
        C.potential p.1 (p.2.comap f) ≤ C.initPotential ∧
        Modifies (Block.mk base C.space).footprint x.mem p.2.mem ∧
        (∀ j ∉ Set.range f, p.2.regs j = x.regs j) :=
  C.init_rename_of_exec hf (C.initClear_exec hx hfr hpar)

/-! ### Projection 4: Caller-to-DS bidirectional framing (`frame_caller`, `frame_caller_dist`) -/

/-- Any caller state transition that preserves `(x'.comap f).Bounded w`, leaves persistent DS
registers (`P.input i = false`) unchanged, and writes only to a set `F` disjoint from
`[base, base + C.space)` preserves both `C.rep θ s (x'.comap f)` and
`C.potential θ (x'.comap f)`. -/
theorem frame_caller (C : SubroutineDS P D w base params s₀)
    {f : Fin r_ds → Fin r_caller} {θ : C.Seed} {s : D.State} {x x' : Data r_caller}
    {F : Finset ℕ}
    (hr : C.rep θ s (x.comap f))
    (hb' : (x'.comap f).Bounded w)
    (hreg : ∀ i, P.input i = false → x'.regs (f i) = x.regs (f i))
    (hdisj : Disjoint (Block.mk base C.space).footprint F)
    (hmem : Modifies F x.mem x'.mem) :
    C.rep θ s (x'.comap f) ∧ C.potential θ (x'.comap f) = C.potential θ (x.comap f) := by
  have hag : ∀ a ∈ (Block.mk base C.space).footprint, x'.mem a = x.mem a := fun a ha =>
    hmem a (fun hf => Finset.disjoint_left.mp hdisj ha hf)
  exact ⟨C.rep_supported (x := x.comap f) (x' := x'.comap f) hreg hag hb' hr,
    C.potential_supported (x := x.comap f) (x' := x'.comap f) hreg hag hr⟩

/-- Coupled caller distribution after a caller transition kernel `μ_caller` that does not resample
the DS seed `θ`. -/
noncomputable def frameDist (C : SubroutineDS P D w base params s₀)
    (ν : PMF (C.Seed × Data r_caller))
    (μ_caller : C.Seed × Data r_caller → PMF (Data r_caller)) :
    PMF (C.Seed × Data r_caller) :=
  ν.bind fun p => (μ_caller p).map fun x' => (p.1, x')

@[simp]
theorem frameDist_map_fst (C : SubroutineDS P D w base params s₀)
    (ν : PMF (C.Seed × Data r_caller))
    (μ_caller : C.Seed × Data r_caller → PMF (Data r_caller)) :
    (C.frameDist ν μ_caller).map Prod.fst = ν.map Prod.fst := by
  unfold frameDist
  rw [PMF.map_bind, PMF.map]
  refine congrArg (ν.bind ·) (funext fun p => ?_)
  ext θ
  rw [PMF.map_comp]
  simp

/-- Distributional caller framing: any deterministic or randomized caller transition kernel
`μ_caller` (including caller steps that execute `Instr.rand`) that preserves
`(x'.comap f).Bounded w`, leaves persistent DS registers (`P.input i = false`) unchanged, and
writes only to a set `F` disjoint from `[base, base + C.space)` preserves the coupled seed
marginal bound, `C.rep`, and expected potential under `C.frameDist ν μ_caller`. -/
theorem frame_caller_dist (C : SubroutineDS P D w base params s₀)
    {f : Fin r_ds → Fin r_caller} {s : D.State}
    {ν : PMF (C.Seed × Data r_caller)}
    {μ_caller : C.Seed × Data r_caller → PMF (Data r_caller)}
    {F : Finset ℕ}
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ)
    (hrep : ∀ p ∈ ν.support, C.rep p.1 s (p.2.comap f))
    (hdisj : Disjoint (Block.mk base C.space).footprint F)
    (hframe : ∀ p ∈ ν.support, ∀ x' ∈ (μ_caller p).support,
      (x'.comap f).Bounded w ∧
      (∀ i, P.input i = false → x'.regs (f i) = p.2.regs (f i)) ∧
      Modifies F p.2.mem x'.mem) :
    (∀ θ, ((C.frameDist ν μ_caller).map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ) ∧
    (∀ q ∈ (C.frameDist ν μ_caller).support, C.rep q.1 s (q.2.comap f)) ∧
    (∑' q, C.frameDist ν μ_caller q * (C.potential q.1 (q.2.comap f) : ℝ≥0∞)) =
      ∑' p, ν p * (C.potential p.1 (p.2.comap f) : ℝ≥0∞) := by
  refine ⟨fun θ => by rw [C.frameDist_map_fst]; exact hseed θ, ?_, ?_⟩
  · intro q hq
    rw [frameDist, PMF.mem_support_bind_iff] at hq
    obtain ⟨p, hp, hq_map⟩ := hq
    rw [PMF.mem_support_map_iff] at hq_map
    obtain ⟨x', hx', rfl⟩ := hq_map
    obtain ⟨hb', hreg, hmem⟩ := hframe p hp x' hx'
    exact (C.frame_caller (hrep p hp) hb' hreg hdisj hmem).1
  · rw [frameDist, Cslib.Probability.PMF.tsum_bind_mul]
    refine tsum_congr fun p => ?_
    by_cases hp : p ∈ ν.support
    · rw [Cslib.Probability.PMF.tsum_map_mul]
      have hpot_eq : (∑' x', μ_caller p x' * (C.potential p.1 (x'.comap f) : ℝ≥0∞)) =
          ∑' x', μ_caller p x' * (C.potential p.1 (p.2.comap f) : ℝ≥0∞) := by
        refine tsum_congr fun x' => ?_
        by_cases hx' : x' ∈ (μ_caller p).support
        · obtain ⟨hb', hreg, hmem⟩ := hframe p hp x' hx'
          rw [(C.frame_caller (hrep p hp) hb' hreg hdisj hmem).2]
        · rw [(PMF.apply_eq_zero_iff _ _).mpr hx', zero_mul, zero_mul]
      rw [hpot_eq, ENNReal.tsum_mul_right, (μ_caller p).tsum_coe, one_mul]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hp, zero_mul, zero_mul]

/-! ### Projection 5: Relocated inline subroutine calls (`code_rename`, `call_rename`) -/

/-- Execute `P.code.rename f` inline when arguments already match `(p.2.comap f).regs` on the
support of a coupled caller distribution `ν : PMF (C.Seed × Data r_caller)`. -/
theorem code_rename (C : SubroutineDS P D w base params s₀)
    {f : Fin r_ds → Fin r_caller} (hf : f.Injective)
    {s : D.State} (o : D.Op) (ν : PMF (C.Seed × Data r_caller))
    (hv : D.valid s o)
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ)
    (hsupp : ∀ p ∈ ν.support, C.rep p.1 s (p.2.comap f) ∧ C.argMatch o (p.2.comap f).regs) :
    ∃ (μ_caller : C.Seed × Data r_caller → PMF (C.Seed × Data r_caller))
      (T_caller : C.Seed × Data r_caller → ℝ≥0∞),
      (∀ p ∈ ν.support,
        ExecCodeDist w (P.code.rename f) p.2 ((μ_caller p).map Prod.snd) (T_caller p) ∧
        ∀ q ∈ (μ_caller p).support,
          C.decode o (q.2.comap f).regs = some (D.step s o).2 ∧
          C.rep q.1 (D.step s o).1 (q.2.comap f) ∧
          Modifies (Block.mk base C.space).footprint p.2.mem q.2.mem ∧
          (∀ j ∉ Set.range f, q.2.regs j = p.2.regs j)) ∧
      (∀ θ', ((ν.bind μ_caller).map Prod.fst) θ' ≤ C.seedSlack * C.seedLaw θ') ∧
      (∑' p, ν p * (T_caller p + ∑' q, μ_caller p q * (C.potential q.1 (q.2.comap f) : ℝ≥0∞))) ≤
        (C.charge s o : ℝ≥0∞) + ∑' p, ν p * (C.potential p.1 (p.2.comap f) : ℝ≥0∞) := by
  let proj : C.Seed × Data r_caller → C.Seed × Data r_ds := fun p => (p.1, p.2.comap f)
  let ν_ds : PMF (C.Seed × Data r_ds) := ν.map proj
  have hseed_ds : ∀ θ, (ν_ds.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ := by
    intro θ
    rw [PMF.map_comp]
    exact hseed θ
  have hsupp_ds : ∀ p_ds ∈ ν_ds.support, C.rep p_ds.1 s p_ds.2 ∧ C.argMatch o p_ds.2.regs := by
    intro p_ds hp_ds
    rw [PMF.mem_support_map_iff] at hp_ds
    obtain ⟨p, hp, rfl⟩ := hp_ds
    exact hsupp p hp
  obtain ⟨μ_ds, T_ds, hstep_ds, hseed_ds', hamort_ds⟩ :=
    C.step_exec o ν_ds hv hseed_ds hsupp_ds
  let μ_caller : C.Seed × Data r_caller → PMF (C.Seed × Data r_caller) :=
    fun p => (μ_ds (proj p)).map fun q => (q.1, q.2.extend f p.2)
  let T_caller : C.Seed × Data r_caller → ℝ≥0∞ := fun p => T_ds (proj p)
  refine ⟨μ_caller, T_caller, ?_, ?_, ?_⟩
  · intro p hp
    have hp_ds : proj p ∈ ν_ds.support := (PMF.mem_support_map_iff _ _ _).mpr ⟨p, hp, rfl⟩
    obtain ⟨he_ds, hq_ds⟩ := hstep_ds (proj p) hp_ds
    refine ⟨?_, ?_⟩
    · have he_ren := he_ds.rename hf (x := p.2)
      refine he_ren.congr_dist ?_ le_rfl
      rw [PMF.map_comp, PMF.map_comp]
      rfl
    · intro q hq
      rw [PMF.mem_support_map_iff] at hq
      obtain ⟨q_ds, hq_mem, rfl⟩ := hq
      obtain ⟨hdec, hrep', hmod⟩ := hq_ds q_ds hq_mem
      refine ⟨?_, ?_, hmod, fun j hj => Data.extend_regs_of_notMem q_ds.2 p.2 hj⟩
      · rw [Data.comap_extend hf]
        exact hdec
      · rw [Data.comap_extend hf]
        exact hrep'
  · intro θ'
    have hmap_eq : (ν.bind μ_caller).map Prod.fst = (ν_ds.bind μ_ds).map Prod.fst := by
      rw [PMF.map_bind, PMF.map_bind, PMF.bind_map]
      refine congrArg (ν.bind ·) (funext fun p => ?_)
      rw [PMF.map_comp]
      rfl
    rw [hmap_eq]
    exact hseed_ds' θ'
  · have hPot_inner : ∀ p : C.Seed × Data r_caller,
        (∑' q, μ_caller p q * (C.potential q.1 (q.2.comap f) : ℝ≥0∞)) =
          ∑' q_ds, μ_ds (proj p) q_ds * (C.potential q_ds.1 q_ds.2 : ℝ≥0∞) := by
      intro p
      rw [Cslib.Probability.PMF.tsum_map_mul]
      refine tsum_congr fun q_ds => ?_
      rw [Data.comap_extend hf]
    simp_rw [hPot_inner]
    have hLHS :
        (∑' p, ν p * (T_caller p +
            ∑' q_ds, μ_ds (proj p) q_ds * (C.potential q_ds.1 q_ds.2 : ℝ≥0∞))) =
          ∑' p_ds, ν_ds p_ds * (T_ds p_ds +
            ∑' q_ds, μ_ds p_ds q_ds * (C.potential q_ds.1 q_ds.2 : ℝ≥0∞)) :=
      (Cslib.Probability.PMF.tsum_map_mul ν proj fun p_ds =>
        T_ds p_ds + ∑' q_ds, μ_ds p_ds q_ds * (C.potential q_ds.1 q_ds.2 : ℝ≥0∞)).symm
    have hRHS :
        (∑' p, ν p * (C.potential p.1 (p.2.comap f) : ℝ≥0∞)) =
          ∑' p_ds, ν_ds p_ds * (C.potential p_ds.1 p_ds.2 : ℝ≥0∞) :=
      (Cslib.Probability.PMF.tsum_map_mul ν proj
        fun p_ds => (C.potential p_ds.1 p_ds.2 : ℝ≥0∞)).symm
    rw [hLHS, hRHS]
    exact hamort_ds

/-- Execute `.seq prep (P.code.rename f)` inline after a (deterministic or randomized) caller
argument-preparation block `prep` that preserves persistent DS registers and memory in
`[base, base + C.space)`. -/
theorem call_rename (C : SubroutineDS P D w base params s₀)
    {f : Fin r_ds → Fin r_caller} (hf : f.Injective)
    {s : D.State} {prep : Code B r_caller} {B_prep : ℝ≥0∞}
    (o : D.Op) (ν : PMF (C.Seed × Data r_caller))
    {μ_prep : C.Seed × Data r_caller → PMF (Data r_caller)}
    {T_prep : C.Seed × Data r_caller → ℝ≥0∞}
    (hv : D.valid s o)
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ)
    (hrep : ∀ p ∈ ν.support, C.rep p.1 s (p.2.comap f))
    (hprep : ∀ p ∈ ν.support,
      ExecCodeDist w prep p.2 (μ_prep p) (T_prep p) ∧
      T_prep p ≤ B_prep ∧
      ∀ x' ∈ (μ_prep p).support,
        (x'.comap f).Bounded w ∧
        (∀ i, P.input i = false → x'.regs (f i) = p.2.regs (f i)) ∧
        (∀ a ∈ (Block.mk base C.space).footprint, x'.mem a = p.2.mem a) ∧
        C.argMatch o (x'.comap f).regs) :
    ∃ (μ_call : C.Seed × Data r_caller → PMF (C.Seed × Data r_caller))
      (T_call : C.Seed × Data r_caller → ℝ≥0∞),
      (∀ p ∈ ν.support,
        ExecCodeDist w (.seq prep (P.code.rename f)) p.2 ((μ_call p).map Prod.snd) (T_call p) ∧
        ∀ q ∈ (μ_call p).support,
          C.decode o (q.2.comap f).regs = some (D.step s o).2 ∧
          C.rep q.1 (D.step s o).1 (q.2.comap f) ∧
          ∃ x' ∈ (μ_prep p).support,
            Modifies (Block.mk base C.space).footprint x'.mem q.2.mem ∧
            ∀ j ∉ Set.range f, q.2.regs j = x'.regs j) ∧
      (∀ θ', ((ν.bind μ_call).map Prod.fst) θ' ≤ C.seedSlack * C.seedLaw θ') ∧
      (∑' p, ν p * (T_call p + ∑' q, μ_call p q * (C.potential q.1 (q.2.comap f) : ℝ≥0∞))) ≤
        B_prep + (C.charge s o : ℝ≥0∞) + ∑' p, ν p * (C.potential p.1 (p.2.comap f) : ℝ≥0∞) := by
  let ν_prep := C.frameDist ν μ_prep
  have hseed_prep : ∀ θ, (ν_prep.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ := by
    intro θ
    rw [C.frameDist_map_fst]
    exact hseed θ
  have hsupp_prep : ∀ p' ∈ ν_prep.support,
      C.rep p'.1 s (p'.2.comap f) ∧ C.argMatch o (p'.2.comap f).regs := by
    intro p' hp'
    simp only [ν_prep, frameDist, PMF.mem_support_bind_iff] at hp'
    obtain ⟨p, hp, hp_map⟩ := hp'
    rw [PMF.mem_support_map_iff] at hp_map
    obtain ⟨x', hx', rfl⟩ := hp_map
    obtain ⟨_, _, hfr_x'⟩ := hprep p hp
    obtain ⟨hb', hreg, hmem, harg⟩ := hfr_x' x' hx'
    exact ⟨C.rep_supported (x := p.2.comap f) (x' := x'.comap f) hreg hmem hb' (hrep p hp), harg⟩
  obtain ⟨μ_code, T_code, hcode, hseed_code, hamort_code⟩ :=
    C.code_rename hf o ν_prep hv hseed_prep hsupp_prep
  let μ_call : C.Seed × Data r_caller → PMF (C.Seed × Data r_caller) :=
    fun p => (μ_prep p).bind fun x' => μ_code (p.1, x')
  let T_call : C.Seed × Data r_caller → ℝ≥0∞ :=
    fun p => T_prep p + ∑' x', μ_prep p x' * T_code (p.1, x')
  refine ⟨μ_call, T_call, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨he_prep, _, hfr_x'⟩ := hprep p hp
    have he_seq := he_prep.seq
      (μ₂ := fun x' => (μ_code (p.1, x')).map Prod.snd)
      (T₂ := fun x' => T_code (p.1, x'))
      fun x' hx' => by
        have hp' : (p.1, x') ∈ ν_prep.support := by
          simp only [ν_prep, frameDist, PMF.mem_support_bind_iff]
          exact ⟨p, hp, (PMF.mem_support_map_iff _ _ _).mpr ⟨x', hx', rfl⟩⟩
        exact (hcode (p.1, x') hp').1
    refine ⟨he_seq.congr_dist ?_ le_rfl, ?_⟩
    · simp only [μ_call, PMF.map_bind]
    · intro q hq
      rw [PMF.mem_support_bind_iff] at hq
      obtain ⟨x', hx', hq_code⟩ := hq
      have hp' : (p.1, x') ∈ ν_prep.support := by
        simp only [ν_prep, frameDist, PMF.mem_support_bind_iff]
        exact ⟨p, hp, (PMF.mem_support_map_iff _ _ _).mpr ⟨x', hx', rfl⟩⟩
      obtain ⟨hdec, hrep', hmod, hregs⟩ := (hcode (p.1, x') hp').2 q hq_code
      exact ⟨hdec, hrep', x', hx', hmod, hregs⟩
  · intro θ'
    have hbind_eq : ν.bind μ_call = ν_prep.bind μ_code := by
      simp only [ν_prep, frameDist, μ_call, PMF.bind_bind, PMF.bind_map]
      rfl
    rw [hbind_eq]
    exact hseed_code θ'
  · have hpot_prep :
        (∑' p', ν_prep p' * (C.potential p'.1 (p'.2.comap f) : ℝ≥0∞)) =
          ∑' p, ν p * (C.potential p.1 (p.2.comap f) : ℝ≥0∞) := by
      simp only [ν_prep, frameDist, Cslib.Probability.PMF.tsum_bind_mul]
      refine tsum_congr fun p => ?_
      by_cases hp : p ∈ ν.support
      · rw [Cslib.Probability.PMF.tsum_map_mul]
        have hpot_eq : (∑' x', μ_prep p x' * (C.potential p.1 (x'.comap f) : ℝ≥0∞)) =
            ∑' x', μ_prep p x' * (C.potential p.1 (p.2.comap f) : ℝ≥0∞) := by
          refine tsum_congr fun x' => ?_
          by_cases hx' : x' ∈ (μ_prep p).support
          · obtain ⟨_, _, hfr_x'⟩ := hprep p hp
            obtain ⟨_, hreg, hmem, _⟩ := hfr_x' x' hx'
            rw [C.potential_supported (x := p.2.comap f) (x' := x'.comap f) hreg hmem (hrep p hp)]
          · rw [(PMF.apply_eq_zero_iff _ _).mpr hx', zero_mul, zero_mul]
        rw [hpot_eq, ENNReal.tsum_mul_right, (μ_prep p).tsum_coe, one_mul]
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hp, zero_mul, zero_mul]
    have hdecomp :
        (∑' p, ν p * (T_call p + ∑' q, μ_call p q * (C.potential q.1 (q.2.comap f) : ℝ≥0∞))) =
          (∑' p, ν p * T_prep p) +
            ∑' p', ν_prep p' *
              (T_code p' + ∑' q, μ_code p' q * (C.potential q.1 (q.2.comap f) : ℝ≥0∞)) := by
      have hinner : ∀ p : C.Seed × Data r_caller,
          T_call p + (∑' q, μ_call p q * (C.potential q.1 (q.2.comap f) : ℝ≥0∞)) =
            T_prep p + ∑' x', μ_prep p x' *
              (T_code (p.1, x') +
                ∑' q, μ_code (p.1, x') q * (C.potential q.1 (q.2.comap f) : ℝ≥0∞)) := by
        intro p
        simp only [T_call, μ_call, Cslib.Probability.PMF.tsum_bind_mul, add_assoc]
        congr 1
        rw [← tsum_add]
        simp_rw [mul_add]
      have hmul : ∀ p : C.Seed × Data r_caller,
          ν p * (T_call p + ∑' q, μ_call p q * (C.potential q.1 (q.2.comap f) : ℝ≥0∞)) =
            ν p * T_prep p + ν p * ∑' x', μ_prep p x' *
              (T_code (p.1, x') +
                ∑' q, μ_code (p.1, x') q * (C.potential q.1 (q.2.comap f) : ℝ≥0∞)) := by
        intro p
        rw [hinner p, mul_add]
      simp_rw [hmul]
      rw [tsum_add]
      congr 1
      symm
      dsimp only [ν_prep, frameDist]
      rw [Cslib.Probability.PMF.tsum_bind_mul]
      refine tsum_congr fun p => ?_
      rw [Cslib.Probability.PMF.tsum_map_mul]
    have hprep_le : (∑' p, ν p * T_prep p) ≤ B_prep := by
      calc
        (∑' p, ν p * T_prep p)
          ≤ ∑' p, ν p * B_prep := by
            refine tsum_le_tsum fun p => ?_
            by_cases hp : p ∈ ν.support
            · exact mul_le_mul_right (hprep p hp).2.1 _
            · rw [(PMF.apply_eq_zero_iff _ _).mpr hp, zero_mul, zero_mul]
        _ = B_prep := by rw [ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]
    rw [hdecomp]
    calc
      (∑' p, ν p * T_prep p) +
          ∑' p', ν_prep p' *
            (T_code p' + ∑' q, μ_code p' q * (C.potential q.1 (q.2.comap f) : ℝ≥0∞))
        ≤ B_prep + ((C.charge s o : ℝ≥0∞) +
            ∑' p', ν_prep p' * (C.potential p'.1 (p'.2.comap f) : ℝ≥0∞)) :=
          add_le_add hprep_le hamort_code
      _ = B_prep + (C.charge s o : ℝ≥0∞) +
            ∑' p, ν p * (C.potential p.1 (p.2.comap f) : ℝ≥0∞) := by
          rw [hpot_prep, add_assoc]

/-! ### Projection 6: End-to-end expected-amortized sequence telescope (`steps_expected_amortized`,
`seq_expected_amortized`) -/

/-- Reuse the signature-level program and argument-delivery API with the actual instruction basis.
This projection carries code and the calling convention, without a deterministic certificate. -/
def toDynamicProgram (C : SubroutineDS P D w base params s₀) : DynamicProgram D r_ds B :=
  P.toDynamicProgram C.encode C.decode

theorem prepare_rep (C : SubroutineDS P D w base params s₀)
    {θ : C.Seed} {s : D.State} {o : D.Op} {x : Data r_ds}
    (hr : C.rep θ s x) (hv : D.valid s o) :
    C.rep θ s (C.toDynamicProgram.prepare o x) :=
  C.rep_supported
    (fun _ hi => C.toDynamicProgram.prepare_regs_of_not_input hi o x)
    (fun _ _ => rfl)
    (C.toDynamicProgram.prepare_bounded (C.bounded hr) (C.arguments_fit _ hv))
    hr

theorem prepare_potential (C : SubroutineDS P D w base params s₀)
    {θ : C.Seed} {s : D.State} {o : D.Op} {x : Data r_ds}
    (hr : C.rep θ s x) :
    C.potential θ (C.toDynamicProgram.prepare o x) = C.potential θ x :=
  C.potential_supported
    (fun _ hi => C.toDynamicProgram.prepare_regs_of_not_input hi o x)
    (fun _ _ => rfl)
    hr

theorem prepare_argMatch (C : SubroutineDS P D w base params s₀) (o : D.Op) (x : Data r_ds) :
    C.argMatch o (C.toDynamicProgram.prepare o x).regs :=
  C.encode_matches o x.regs

/-- Inductive multi-operation distributional execution relation for a randomized subroutine `C`.
`C.ExecSteps s ops ν ν_final T_ops` witnesses that starting from abstract state `s` and coupled
state distribution `ν : PMF (C.Seed × Data r_ds)`, executing each operation `o` in `ops` by
delivering arguments via `C.toDynamicProgram.prepare o` and running `P.code` under `ExecCodeDist`
produces the
final coupled distribution `ν_final`, decodes the exact abstract return value `(D.step s o).2` at
every step, modifies memory only within `[base, base + C.space)`, and incurs total expected
operation body cost `T_ops`. Argument delivery is an external register replacement and
contributes no native instructions to this relation. -/
inductive ExecSteps (C : SubroutineDS P D w base params s₀) :
    D.State → List D.Op → PMF (C.Seed × Data r_ds) → PMF (C.Seed × Data r_ds) → ℝ≥0∞ → Prop where
  | nil (s : D.State) (ν : PMF (C.Seed × Data r_ds)) :
      C.ExecSteps s [] ν ν 0
  | cons {s : D.State} {o : D.Op} {ops : List D.Op}
      {ν ν_final : PMF (C.Seed × Data r_ds)}
      {μ_step : C.Seed × Data r_ds → PMF (C.Seed × Data r_ds)}
      {T_step : C.Seed × Data r_ds → ℝ≥0∞} {T_rest : ℝ≥0∞} :
      (∀ p ∈ ν.support,
        ExecCodeDist w P.code (C.toDynamicProgram.prepare o p.2)
          ((μ_step p).map Prod.snd) (T_step p) ∧
        ∀ q ∈ (μ_step p).support,
          C.decode o q.2.regs = some (D.step s o).2 ∧
          C.rep q.1 (D.step s o).1 q.2 ∧
          Modifies (Block.mk base C.space).footprint p.2.mem q.2.mem) →
      C.ExecSteps (D.step s o).1 ops (ν.bind μ_step) ν_final T_rest →
      C.ExecSteps s (o :: ops) ν ν_final ((∑' p, ν p * T_step p) + T_rest)

/-- **Multi-operation expected-amortized telescope (`steps_expected_amortized`).**
From any abstract state `s : D.State` and coupled state distribution `ν : PMF (C.Seed × Data r_ds)`
satisfying the seed-marginal bound and `C.rep p.1 s p.2` on `ν.support`, executing any admissible
operation sequence `ops : List D.Op` (`D.ValidHistory s ops`) produces a final coupled distribution
`ν_final` and total expected operation step count `T_ops : ℝ≥0∞` witnessing
`C.ExecSteps s ops ν ν_final T_ops` and satisfying the addition-only `ℝ≥0∞` telescope inequality
(with `Φ(p) := C.potential p.1 p.2`)
`T_ops + ∑' q, ν_final q * Φ(q) ≤ D.totalCost C.charge s ops + ∑' p, ν p * Φ(p)`. -/
theorem steps_expected_amortized (C : SubroutineDS P D w base params s₀)
    {s : D.State} (ops : List D.Op) (ν : PMF (C.Seed × Data r_ds))
    (hv : D.ValidHistory s ops)
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ)
    (hrep : ∀ p ∈ ν.support, C.rep p.1 s p.2) :
    ∃ (ν_final : PMF (C.Seed × Data r_ds)) (T_ops : ℝ≥0∞),
      C.ExecSteps s ops ν ν_final T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ) ∧
      (∀ p ∈ ν_final.support, C.rep p.1 (D.run s ops).1 p.2) ∧
      T_ops + (∑' q, ν_final q * (C.potential q.1 q.2 : ℝ≥0∞)) ≤
        (D.totalCost C.charge s ops : ℝ≥0∞) + ∑' p, ν p * (C.potential p.1 p.2 : ℝ≥0∞) := by
  induction ops generalizing s ν with
  | nil =>
    exact ⟨ν, 0, ExecSteps.nil s ν, hseed, hrep, by simp⟩
  | cons o os ih =>
    obtain ⟨hvo, hvos⟩ := hv
    let ν_prep : PMF (C.Seed × Data r_ds) := ν.map fun p => (p.1, C.toDynamicProgram.prepare o p.2)
    have hseed_prep : ∀ θ, (ν_prep.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ := by
      intro θ
      rw [PMF.map_comp]
      exact hseed θ
    have hsupp_prep : ∀ p' ∈ ν_prep.support, C.rep p'.1 s p'.2 ∧ C.argMatch o p'.2.regs := by
      intro p' hp'
      rw [PMF.mem_support_map_iff] at hp'
      obtain ⟨p, hp, rfl⟩ := hp'
      exact ⟨C.prepare_rep (hrep p hp) hvo, C.prepare_argMatch o p.2⟩
    have hpot_prep :
        (∑' p', ν_prep p' * (C.potential p'.1 p'.2 : ℝ≥0∞)) =
          ∑' p, ν p * (C.potential p.1 p.2 : ℝ≥0∞) := by
      rw [Cslib.Probability.PMF.tsum_map_mul]
      refine tsum_congr fun p => ?_
      by_cases hp : p ∈ ν.support
      · rw [C.prepare_potential (hrep p hp)]
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hp, zero_mul, zero_mul]
    obtain ⟨μ_step, T_step, hstep, hseed₁, hamort₁⟩ :=
      C.step_exec o ν_prep hvo hseed_prep hsupp_prep
    let μ_op : C.Seed × Data r_ds → PMF (C.Seed × Data r_ds) :=
      fun p => μ_step (p.1, C.toDynamicProgram.prepare o p.2)
    let T_op : C.Seed × Data r_ds → ℝ≥0∞ :=
      fun p => T_step (p.1, C.toDynamicProgram.prepare o p.2)
    let ν₁ := ν.bind μ_op
    have hν₁_eq : ν₁ = ν_prep.bind μ_step := by
      simp only [ν₁, ν_prep, μ_op, PMF.bind_map]
      rfl
    have hseed₁' : ∀ θ, (ν₁.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ := by
      rw [hν₁_eq]
      exact hseed₁
    have hrep₁ : ∀ q ∈ ν₁.support, C.rep q.1 (D.step s o).1 q.2 := by
      intro q hq
      rw [hν₁_eq, PMF.mem_support_bind_iff] at hq
      obtain ⟨p', hp', hq_step⟩ := hq
      exact ((hstep p' hp').2 q hq_step).2.1
    obtain ⟨ν_final, T_rest, hex_rest, hseed_final, hrep_final, hamort_rest⟩ :=
      ih ν₁ hvos hseed₁' hrep₁
    let T₁ : ℝ≥0∞ := ∑' p, ν p * T_op p
    have hT₁_eq : T₁ = ∑' p', ν_prep p' * T_step p' := by
      symm
      exact Cslib.Probability.PMF.tsum_map_mul ν
        (fun p => (p.1, C.toDynamicProgram.prepare o p.2)) T_step
    have hex_cons : C.ExecSteps s (o :: os) ν ν_final (T₁ + T_rest) := by
      refine ExecSteps.cons (μ_step := μ_op) (T_step := T_op) (fun p hp => ?_) hex_rest
      have hp' : (p.1, C.toDynamicProgram.prepare o p.2) ∈ ν_prep.support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨p, hp, rfl⟩
      exact hstep (p.1, C.toDynamicProgram.prepare o p.2) hp'
    have hstep_split :
        T₁ + (∑' q, ν₁ q * (C.potential q.1 q.2 : ℝ≥0∞)) =
          ∑' p', ν_prep p' * (T_step p' + ∑' q, μ_step p' q * (C.potential q.1 q.2 : ℝ≥0∞)) := by
      rw [hT₁_eq, hν₁_eq]
      simp only [Cslib.Probability.PMF.tsum_bind_mul, ← tsum_add, mul_add]
    refine ⟨ν_final, T₁ + T_rest, hex_cons, hseed_final, hrep_final, ?_⟩
    calc
      (T₁ + T_rest) + ∑' q, ν_final q * (C.potential q.1 q.2 : ℝ≥0∞)
        = T₁ + (T_rest + ∑' q, ν_final q * (C.potential q.1 q.2 : ℝ≥0∞)) := by ac_rfl
      _ ≤ T₁ + ((D.totalCost C.charge (D.step s o).1 os : ℝ≥0∞) +
            ∑' q, ν₁ q * (C.potential q.1 q.2 : ℝ≥0∞)) :=
          add_le_add le_rfl hamort_rest
      _ = (D.totalCost C.charge (D.step s o).1 os : ℝ≥0∞) +
            (T₁ + ∑' q, ν₁ q * (C.potential q.1 q.2 : ℝ≥0∞)) := by ac_rfl
      _ ≤ (D.totalCost C.charge (D.step s o).1 os : ℝ≥0∞) +
            ((C.charge s o : ℝ≥0∞) + ∑' p, ν p * (C.potential p.1 p.2 : ℝ≥0∞)) := by
          rw [hstep_split, ← hpot_prep]
          exact add_le_add le_rfl hamort₁
      _ = (D.totalCost C.charge s (o :: os) : ℝ≥0∞) +
            ∑' p, ν p * (C.potential p.1 p.2 : ℝ≥0∞) := by
          simp only [Stateful.Spec.totalCost_cons, Nat.cast_add]
          ac_rfl

/-- **End-to-end expected-amortized theorem from fresh initialization (`seq_expected_amortized`).**
Starting from zeroed `[base, base + C.space)`, `P.initFresh` followed by any admissible operation
sequence `ops : List D.Op` (`D.ValidHistory s₀ ops`) has total expected instruction cost
`C.initTime + T_ops` bounded by
`C.initTime + C.initPotential + D.totalCost C.charge s₀ ops`. -/
theorem seq_expected_amortized (C : SubroutineDS P D w base params s₀)
    {x : Data r_ds} (ops : List D.Op)
    (hx : x.Bounded w) (hfr : x.regs P.frontierReg = base)
    (hpar : ∀ j, x.regs (P.initParams j) = params j)
    (hz : ∀ a ∈ (Block.mk base C.space).footprint, x.mem a = 0)
    (hv : D.ValidHistory s₀ ops) :
    ∃ (ν₀ ν_final : PMF (C.Seed × Data r_ds)) (T_ops : ℝ≥0∞),
      ExecCodeDist w P.initFresh x (ν₀.map Prod.snd) C.initTime ∧
      C.ExecSteps s₀ ops ν₀ ν_final T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ) ∧
      (∀ p ∈ ν_final.support, C.rep p.1 (D.run s₀ ops).1 p.2) ∧
      C.initTime + T_ops + (∑' q, ν_final q * (C.potential q.1 q.2 : ℝ≥0∞)) ≤
        C.initTime + (C.initPotential : ℝ≥0∞) + (D.totalCost C.charge s₀ ops : ℝ≥0∞) := by
  obtain ⟨ν₀, he_init, hseed₀, hsupp₀⟩ := C.initFresh_exec hx hfr hpar hz
  have hrep₀ : ∀ p ∈ ν₀.support, C.rep p.1 s₀ p.2 := fun p hp => (hsupp₀ p hp).2.1
  obtain ⟨ν_final, T_ops, hex_steps, hseed_final, hrep_final, hamort⟩ :=
    C.steps_expected_amortized ops ν₀ hv hseed₀ hrep₀
  have hpot₀ : (∑' p, ν₀ p * (C.potential p.1 p.2 : ℝ≥0∞)) ≤ (C.initPotential : ℝ≥0∞) := by
    calc
      (∑' p, ν₀ p * (C.potential p.1 p.2 : ℝ≥0∞))
        ≤ ∑' p, ν₀ p * (C.initPotential : ℝ≥0∞) := by
          refine tsum_le_tsum fun p => ?_
          by_cases hp : p ∈ ν₀.support
          · exact mul_le_mul_right (Nat.cast_le.mpr (hsupp₀ p hp).2.2.1) _
          · rw [(PMF.apply_eq_zero_iff _ _).mpr hp, zero_mul, zero_mul]
      _ = (C.initPotential : ℝ≥0∞) := by
          rw [ENNReal.tsum_mul_right, ν₀.tsum_coe, one_mul]
  refine ⟨ν₀, ν_final, T_ops, he_init, hex_steps, hseed_final, hrep_final, ?_⟩
  calc
    C.initTime + T_ops + ∑' q, ν_final q * (C.potential q.1 q.2 : ℝ≥0∞)
      = C.initTime + (T_ops + ∑' q, ν_final q * (C.potential q.1 q.2 : ℝ≥0∞)) := by ac_rfl
    _ ≤ C.initTime + ((D.totalCost C.charge s₀ ops : ℝ≥0∞) +
          ∑' p, ν₀ p * (C.potential p.1 p.2 : ℝ≥0∞)) :=
        add_le_add le_rfl hamort
    _ ≤ C.initTime + ((D.totalCost C.charge s₀ ops : ℝ≥0∞) + (C.initPotential : ℝ≥0∞)) :=
        add_le_add le_rfl (add_le_add le_rfl hpot₀)
    _ = C.initTime + (C.initPotential : ℝ≥0∞) + (D.totalCost C.charge s₀ ops : ℝ≥0∞) := by ac_rfl

end Cslib.WordRAM.Randomized.SubroutineDS

end
