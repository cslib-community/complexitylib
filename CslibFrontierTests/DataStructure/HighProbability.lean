/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.WordRAM.Randomized.HighProbability
public import CslibFrontier.DataStructure.Dictionary.Dynamic.Spec

/-!
# With-High-Probability Word-RAM State-Transition Certificate Tests

Exercises `Cslib.DataStructure.WordRAM.Randomized.HighProbStateTransitionImpl`:
1. **Partial-horizon randomized fast/slow subroutine (`fastSlowSubroutine`, `fastSlowImpl`)**:
   - Flips a fair coin `r3 ← rand r4` (`r4 = 1`): on `r3 = 0` (probability `1 / 2`) executes the
     fast path in `3` body instructions (`≤ worstCaseTime = 3`), while on `r3 = 1` (probability
     `1 / 2`) executes a longer fallback branch taking `5` body instructions (`> worstCaseTime`).
   - Exercises `HighProbStateTransitionImpl.ofFn`, `.toStandard`, `initFresh_program`,
     `initClear_exec`, `step_whp_ofFn` (verifying `evalRand` at partial horizon `worstCaseTime + 1`
     reaches `.halted` with probability `≥ 1 - 1 / 2`), `seq_whp_ofFn`, and
     `poly_seq_failureProb_le`.
2. **Negative `.halt` / 1-instruction no-op sanity checks**:
   - `no_noop_highProbImpl_dictionary`: proves that a 1-instruction no-op subroutine body
     (`P.code = .op (.copy 0 0)`, whose flat program is `[.op (.copy 0 0), .halt out]`) **cannot**
     instantiate `HighProbStateTransitionImpl` for `Dictionary.Dynamic.spec 2 2 1` under *any*
     `P.input`, `encode`, `decode`, `Seed`, `worstCaseTime`, or `failureProb`.
   - `halt_program_cannot_distinguish_insert_query`: proves directly on raw `evalRand w [.halt out]`
     that running a 1-instruction `[Instr.halt out]` program across
     `[.query 0, .insert 0 1, .query 0]` returns identical register outputs before and after the
     insertion and therefore cannot decode both `none` and `some 1`.
-/

@[expose] public section

namespace CslibFrontierTests.WordRAMHighProbability

open Cslib Cslib.WordRAM Cslib.Probability
open Cslib.DataStructure Cslib.DataStructure.Dictionary
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.Probability.PMF (uniformOfFintype uniformOfFintype_apply)
open scoped ENNReal

private theorem data_set_self {r : ℕ} (d : Data r) (i : Fin r) : d.set i (d.regs i) = d := by
  cases d
  simp [Data.set]

/-! ## 1. Partial-horizon fast/slow coin subroutine (`worstCaseTime = 3`, slow branch = `5`) -/

/-- Trivial specification with one operation `PUnit` returning `PUnit`. -/
abbrev unitSpec : DataStructure.StateTransitionSpec.{0, 0, 0} :=
  DataStructure.StateTransitionSpec.ofFn (State := PUnit) (Op := PUnit) (Result := fun _ => PUnit)
    fun _ _ => (PUnit.unit, PUnit.unit)

/-- Subroutine body that samples `r3 ← rand r4` (`1` step) and branches on `r3 == r2` (`r2 = 0`):
- Fast path (`r3 = 0`, prob `1/2`): executes `.op (.copy 3 3)` (`1 + 2 = 3` body steps total).
- Slow path (`r3 = 1`, prob `1/2`): executes `.seq (.op (.copy 3 3)) (.op (.copy 3 3))`
  (`1 + 4 = 5` body steps total, strictly exceeding `worstCaseTime = 3`). -/
def fastSlowCode : Code .exact 5 :=
  .seq (.rand 3 4)
    (.branch (.eq 3 2)
      (.op (.copy 3 3))
      (.seq (.op (.copy 3 3)) (.op (.copy 3 3))))

def fastSlowSubroutine : SubroutineCode .exact 5 0 where
  allocSpan := .op (.copy 0 1)
  initSetup := .seq (.op (.const 2 0)) (.op (.const 4 1))
  code := fastSlowCode
  baseReg := 0
  frontierReg := 1
  zeroReg := 2
  oneReg := 4
  curReg := 3
  incCur := Op.exactBin .add 3 3 4
  initParams := Fin.elim0
  input := fun _ => false
  output := 3

def fastSlowRep (w base : ℕ) (_ : Unit) (_ : PUnit) (x : Data 5) : Prop :=
  x.Bounded w ∧ x.regs 0 = base ∧ x.regs 2 = 0 ∧ x.regs 4 = 1

def fastSlowBranch (y : Data 5) : ProbComp (Data 5 × ℕ) :=
  if (Cond.eq (r := 5) 3 2).Holds y then pure (y, 2) else pure (y, 4)

def fastSlowComp (x : Data 5) : ProbComp (Data 5 × ℕ) :=
  do let z₁ ← (do let k ← ProbComp.unifFin (x.regs 4); pure (x.set 3 k.val, 1))
     let z₂ ← fastSlowBranch z₁.1
     pure (z₂.1, z₁.2 + z₂.2)

private theorem execRand_fastSlowCode {w : ℕ} (hw : 1 ≤ w) {x : Data 5} (hx : x.Bounded w)
    (hr2 : x.regs 2 = 0) (hr4 : x.regs 4 = 1) :
    ExecRand w fastSlowCode x (fastSlowComp x) ∧
    (∀ z ∈ (fastSlowComp x).support, z.1.Bounded w ∧ z.1.regs 0 = x.regs 0 ∧
      z.1.regs 2 = 0 ∧ z.1.regs 4 = 1 ∧ z.1.mem = x.mem) ∧
    (fastSlowComp x).eval.toOuterMeasure {z | 3 < z.2} ≤ (2 : ℝ≥0∞)⁻¹ := by
  have hfit4 : Fits w (x.regs 4) := hx.1 4
  have hex : ExecRand w fastSlowCode x (fastSlowComp x) := by
    refine (ExecRand.rand hfit4).seq (m₂ := fastSlowBranch) fun z₁ hz₁ => ?_
    obtain ⟨k, -, hk⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₁
    cases OracleComp.eq_of_mem_supportWith_pure hk
    dsimp only [fastSlowBranch]
    have hcp : Exec (B := .exact) w (.op (.copy 3 3)) (x.set 3 k.val) (x.set 3 k.val) 1 :=
      Exec.op (by rw [Op.eval_copy, data_set_self])
    by_cases hc : (Cond.eq (r := 5) 3 2).Holds (x.set 3 k.val)
    · simp only [hc, ↓reduceIte]
      simpa using ExecRand.branch_pos (neg := .seq (.op (.copy 3 3)) (.op (.copy 3 3))) hc
        hcp.execRand
    · simp only [hc, ↓reduceIte]
      have htwo : Exec (B := .exact) w (.seq (.op (.copy 3 3)) (.op (.copy 3 3)))
          (x.set 3 k.val) (x.set 3 k.val) 2 := hcp.seq hcp
      simpa using ExecRand.branch_neg (pos := .op (.copy 3 3)) hc htwo.execRand
  refine ⟨hex, ?_, ?_⟩
  · intro z hz
    dsimp only [fastSlowComp] at hz
    obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    obtain ⟨k, -, hk⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₁
    cases OracleComp.eq_of_mem_supportWith_pure hk
    obtain ⟨z₂, hz₂, hfin⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
    cases OracleComp.eq_of_mem_supportWith_pure hfin
    dsimp only [fastSlowBranch] at hz₂
    have hk_le : k.val ≤ 1 := by omega
    have hby : (x.set 3 k.val).Bounded w := hx.set ((fits_one (by omega)).of_le hk_le)
    split_ifs at hz₂
    · cases OracleComp.eq_of_mem_supportWith_pure hz₂
      exact ⟨hby, by simp [Data.set], by simp [Data.set, hr2], by simp [Data.set, hr4], rfl⟩
    · cases OracleComp.eq_of_mem_supportWith_pure hz₂
      exact ⟨hby, by simp [Data.set], by simp [Data.set, hr2], by simp [Data.set, hr4], rfl⟩
  · have hm_eval : (fastSlowComp x).eval =
        (uniformOfFintype (Fin 2)).map (fun k : Fin 2 =>
          if k.val = 0 then (x.set 3 0, 3) else (x.set 3 1, 5)) := by
      dsimp only [fastSlowComp, fastSlowBranch]
      rw [hr4]
      simp only [bind_assoc, pure_bind, ProbComp.eval_bind, ProbComp.eval_unifFin, PMF.map]
      refine congrArg ((uniformOfFintype (Fin 2)).bind ·) (funext fun k => ?_)
      fin_cases k
      · have hc0 : (Cond.eq (r := 5) 3 2).Holds (x.set 3 0) := by
          simp [Cond.Holds, Data.set, hr2]
        simp [hc0, ProbComp.eval_pure]
      · have hc1 : ¬(Cond.eq (r := 5) 3 2).Holds (x.set 3 1) := by
          simp [Cond.Holds, Data.set, hr2]
        simp [hc1, ProbComp.eval_pure]
    rw [hm_eval, PMF.toOuterMeasure_map_apply]
    classical
    rw [PMF.toOuterMeasure_apply_fintype, Fin.sum_univ_two]
    simp [uniformOfFintype_apply]

/-- Concrete `HighProbStateTransitionImpl` certificate for `fastSlowSubroutine` with
`worstCaseTime = 3` and `failureProb = 1 / 2`. -/
noncomputable def fastSlowImpl (w base : ℕ) (hw : 1 ≤ w) :
    HighProbStateTransitionImpl fastSlowSubroutine unitSpec w base Fin.elim0 PUnit.unit :=
  HighProbStateTransitionImpl.ofFn
    (Seed := Unit)
    (seedLaw := PMF.pure ())
    (seedSlack := 1)
    (space := 0)
    (spanTime := 1)
    (setupTime := 2)
    (setupRandCalls := 0)
    (worstCaseTime := 3)
    (failureProb := (2 : ℝ≥0∞)⁻¹)
    (rep := fastSlowRep w base)
    (encode := fun _ _ => 0)
    (argMatch := fun _ _ => True)
    (decode := fun _ _ => some PUnit.unit)
    (bounded := fun h => h.1)
    (arguments_fit := fun _ _ _ _ => fits_zero w)
    (encode_matches := fun _ _ => trivial)
    (rep_supported := fun hreg _ hb' hrep =>
      ⟨hb',
        by rw [hreg 0 rfl, hrep.2.1],
        by rw [hreg 2 rfl, hrep.2.2.1],
        by rw [hreg 4 rfl, hrep.2.2.2]⟩)
    (clear_nodup := by decide)
    (params_not_clear := fun j => Fin.elim0 j)
    (incCur_eval := fun {x} h1 hfit => by
      change Data.put w x 3 (x.regs 3 + x.regs 4) =
        some (x.set fastSlowSubroutine.curReg (x.regs fastSlowSubroutine.curReg + 1))
      change x.regs 4 = 1 at h1
      rw [h1]
      exact Data.put_of_fits hfit)
    (span_exec := fun _ hfr _ => by
      refine ⟨_, ExecWithin.copy, rfl, ?_, ?_, fun j => Fin.elim0 j⟩
      · simpa [fastSlowSubroutine, Data.set] using hfr
      · simpa [fastSlowSubroutine, Data.set] using hfr)
    (setup_exec := fun {x₁} hx₁ hb₁ hfr₁ _ _ => by
      let x₂ := (x₁.set 2 0).set 4 1
      have he_setup : Exec (B := .exact) w (.seq (.op (.const 2 0)) (.op (.const 4 1))) x₁ x₂ 2 :=
        (Exec.const (fits_zero w)).seq (Exec.const (fits_one (by omega)))
      refine ⟨pure (x₂, 2), PMF.pure ((), x₂), he_setup.execRand, .pure _ 0, ?_, ?_, ?_, ?_⟩
      · intro z hz; cases OracleComp.eq_of_mem_supportWith_pure hz; exact le_rfl
      · simp [ProbComp.eval_pure]
      · intro θ; cases θ; simp
      · intro p hp
        rw [PMF.support_pure, Set.mem_singleton_iff] at hp
        subst hp
        refine ⟨by simpa [x₂, Data.set, fastSlowSubroutine] using hfr₁, ?_, Modifies.refl _ _⟩
        exact ⟨(hx₁.set (fits_zero w)).set (fits_one (by omega)),
          by simp [x₂, Data.set, ← hb₁, fastSlowSubroutine],
          by simp [x₂, Data.set],
          by simp [x₂, Data.set]⟩)
    (step_exec := fun _ ν _ _ hsupp => by
      let m_step : Unit × Data 5 → ProbComp (Data 5 × ℕ) := fun p => fastSlowComp p.2
      let μ_step : Unit × Data 5 → PMF ((Unit × Data 5) × ℕ) := fun p =>
        (m_step p).eval.map fun z => (((), z.1), z.2)
      refine ⟨m_step, μ_step, ?_, ?_, ?_⟩
      · intro p hp
        obtain ⟨⟨hbp, hb0, hr2, hr4⟩, _⟩ := hsupp p hp
        obtain ⟨hex_p, hinv_p, _⟩ := execRand_fastSlowCode hw hbp hr2 hr4
        refine ⟨hex_p, ?_, ?_⟩
        · dsimp only [μ_step]; rw [PMF.map_comp]; exact PMF.map_id _
        · intro q hq
          dsimp only [μ_step] at hq
          rw [PMF.mem_support_map_iff] at hq
          obtain ⟨z, hz, rfl⟩ := hq
          rw [ProbComp.support_eval] at hz
          obtain ⟨hbz, hr0z, hr2z, hr4z, hmemz⟩ := hinv_p z hz
          exact ⟨rfl, ⟨hbz, hb0 ▸ hr0z, hr2z, hr4z⟩, hmemz ▸ Modifies.refl _ _⟩
      · intro θ'
        cases θ'
        rw [PMF.map_comp, PMF.map_bind]
        simp
      · rw [PMF.toOuterMeasure_bind_apply]
        calc
          (∑' p : Unit × Data 5, ν p * (μ_step p).toOuterMeasure {q | 3 < q.2})
            ≤ ∑' p : Unit × Data 5, ν p * (2 : ℝ≥0∞)⁻¹ := by
                refine tsum_le_tsum fun p => ?_
                by_cases hp : p ∈ ν.support
                · refine mul_le_mul_right ?_ _
                  obtain ⟨⟨hbp, _, hr2, hr4⟩, _⟩ := hsupp p hp
                  obtain ⟨_, _, hfail_p⟩ := execRand_fastSlowCode hw hbp hr2 hr4
                  dsimp only [μ_step, m_step]
                  rw [PMF.toOuterMeasure_map_apply]
                  exact hfail_p
                · simp [(PMF.apply_eq_zero_iff _ _).mpr hp]
          _ = (2 : ℝ≥0∞)⁻¹ := by
                rw [ENNReal.tsum_mul_right, ν.tsum_coe, one_mul])

/-- Standard-basis lifting of `fastSlowImpl`. -/
noncomputable def fastSlowImplStandard (w base : ℕ) (hw : 1 ≤ w) :
    HighProbStateTransitionImpl fastSlowSubroutine.toStandard unitSpec w base
      Fin.elim0 PUnit.unit :=
  (fastSlowImpl w base hw).toStandard

/-- Concrete exercise of `seq_whp_ofFn` on `fastSlowImpl`: on a single operation, execution
completes within `3` worst-case body instructions with probability at least `1 / 2`. -/
example :
    let C := fastSlowImpl 4 0 (by decide)
    ∃ (ν₀ : PMF (C.Seed × Data 5)) (τ_final : PMF (WhpSeqOutcome C.Seed unitSpec 5)),
      RandHaltsWithin 4 (fastSlowSubroutine.initFresh.program 3)
        ⟨0, Data.init []⟩ (C.initTime + 1) ∧
      C.ExecWhpSteps 3 [PUnit.unit]
        (ν₀.map fun p => WhpSeqOutcome.ofCoupled ⟨p.1, PUnit.unit, p.2⟩) τ_final ∧
      (2 : ℝ≥0∞)⁻¹ ≤
        τ_final.toOuterMeasure
          {tr | tr.maxSteps ≤ 3 ∧ tr.transcript = [⟨PUnit.unit, PUnit.unit⟩]} := by
  intro C
  have hx : (Data.init [] : Data 5).Bounded 4 := Data.Bounded.init (by simp [InputFits])
  have hz : ∀ a ∈ (Block.mk 0 C.space).footprint, (Data.init [] : Data 5).mem a = 0 := by
    change ∀ a ∈ (Block.mk 0 0).footprint, _
    simp [Block.footprint]
  obtain ⟨ν₀, τ_final, hhalts, _, _, hex, _, _, hsucc⟩ :=
    C.seq_whp_ofFn 3 [PUnit.unit] hx (by simp [Data.init]) (fun j => Fin.elim0 j) hz
      ⟨trivial, trivial⟩
  refine ⟨ν₀, τ_final, hhalts, hex, ?_⟩
  have hhalf : (2 : ℝ≥0∞)⁻¹ ≤ 1 - ((1 : ℕ) : ℝ≥0∞) * C.failureProb := by
    have hfp : C.failureProb = (2 : ℝ≥0∞)⁻¹ := rfl
    have h1 : (1 : ℝ≥0∞) - (2 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ :=
      ENNReal.sub_eq_of_eq_add (by simp)
        (by simpa [div_eq_mul_inv] using (ENNReal.add_halves 1).symm)
    rw [hfp, Nat.cast_one, one_mul, h1]
  exact hhalf.trans hsucc

/-- Concrete exercise of `reachable_step_whp_ofFn` on `fastSlowImpl`: after any valid oblivious
prefix `ops`, the next operation still halts within `C.worstCaseTime + 1` machine steps (`evalRand`)
with probability at least `1 / 2`. -/
example (ops : List PUnit) (hv : unitSpec.ValidHistory PUnit.unit ops) :
    let C := fastSlowImpl 4 0 (by decide)
    ∃ (ν₀ : PMF (C.Seed × Data 5)) (τ_pref : PMF (WhpSeqOutcome C.Seed unitSpec 5)),
      C.ExecWhpSteps 3 ops
        (ν₀.map fun p => WhpSeqOutcome.ofCoupled ⟨p.1, PUnit.unit, p.2⟩) τ_pref ∧
      (2 : ℝ≥0∞)⁻¹ ≤
        ((τ_pref.map fun tr => (tr.current.seed, tr.current.data)).bind fun p =>
          evalRand 4 (fastSlowSubroutine.code.program 3) (C.worstCaseTime + 1)
            ⟨0, C.prepare PUnit.unit p.2⟩).toOuterMeasure
          {cfg | ∃ p q : C.Seed × Data 5,
            p ∈ (τ_pref.map fun tr => (tr.current.seed, tr.current.data)).support ∧
            cfg = .halted (q.2.regs 3) q.2 ∧
            C.decode PUnit.unit q.2.regs =
              some (unitSpec.stepFn (unitSpec.run PUnit.unit ops).1 PUnit.unit).2 ∧
            C.rep q.1 (unitSpec.stepFn (unitSpec.run PUnit.unit ops).1 PUnit.unit).1 q.2 ∧
            q.2.Bounded 4 ∧
            Modifies (Block.mk 0 C.space).footprint p.2.mem q.2.mem} := by
  intro C
  have hx : (Data.init [] : Data 5).Bounded 4 := Data.Bounded.init (by simp [InputFits])
  have hz : ∀ a ∈ (Block.mk 0 C.space).footprint, (Data.init [] : Data 5).mem a = 0 := by
    change ∀ a ∈ (Block.mk 0 0).footprint, _
    simp [Block.footprint]
  obtain ⟨ν₀, τ_pref, hex, hprob⟩ :=
    C.reachable_step_whp_ofFn 3 ops PUnit.unit hx (by simp [Data.init]) (fun j => Fin.elim0 j)
      hz hv trivial
  refine ⟨ν₀, τ_pref, hex, ?_⟩
  have hhalf : (2 : ℝ≥0∞)⁻¹ ≤ 1 - C.failureProb := by
    have hfp : C.failureProb = (2 : ℝ≥0∞)⁻¹ := rfl
    have h1 : (1 : ℝ≥0∞) - (2 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ :=
      ENNReal.sub_eq_of_eq_add (by simp)
        (by simpa [div_eq_mul_inv] using (ENNReal.add_halves 1).symm)
    rw [hfp, h1]
  exact hhalf.trans hprob

/-! ## 2. Negative `.halt` / 1-instruction no-op sanity checks -/

/-- **Negative sanity check 1 (`no_noop_highProbImpl_dictionary`):**
A subroutine whose operation body `P.code` is the 1-instruction no-op `.op (.copy 0 0)` (compiling
to `[.op (.copy 0 0), .halt out]`) **cannot** instantiate `HighProbStateTransitionImpl` for
`Dictionary.Dynamic.spec 2 2 1` under *any* `P.input`, `encode`, `decode`, `Seed`, `worstCaseTime`,
or `failureProb` (even `failureProb = 1`), because `seq_whp_ofFn` ties every supported execution
trajectory to `ExecRand` on `[.query 0, .insert 0 1, .query 0]`. -/
theorem no_noop_highProbImpl_dictionary {r_ds k_init w base : ℕ}
    {P : SubroutineCode .exact (r_ds + 1) k_init}
    {params : Fin k_init → ℕ}
    (hcode : P.code = .op (.copy 0 0))
    (hx₀ : ∃ x : Data (r_ds + 1), x.Bounded w ∧ x.regs P.frontierReg = base ∧
      (∀ j, x.regs (P.initParams j) = params j) ∧
      (∀ a, x.mem a = 0)) :
    IsEmpty (HighProbStateTransitionImpl P (Dynamic.spec 2 2 1) w base params
      (Dictionary.empty 2)) := by
  refine ⟨fun C => ?_⟩
  obtain ⟨x₀, hbx₀, hfr₀, hpar₀, hz₀⟩ := hx₀
  let k0 : Fin 2 := ⟨0, by decide⟩
  have hv : (Dynamic.spec 2 2 1).ValidHistory (Dictionary.empty 2)
      [.query k0, .insert k0 1, .query k0] := by
    have hcard0 : (Dictionary.dom (Dictionary.empty 2)).card < 1 := by simp
    dsimp only [Dynamic.spec, StateTransitionSpec.ValidHistory,
      StateTransitionSpec.ofFn, Dynamic.valid, Dynamic.step]
    exact ⟨trivial, ⟨Or.inl hcard0, by decide⟩, trivial, trivial⟩
  obtain ⟨ν₀, τ_final, _, _, _, hex, _, _, _⟩ :=
    C.seq_whp_ofFn 0 [.query k0, .insert k0 1, .query k0]
      hbx₀ hfr₀ hpar₀ (fun a _ => hz₀ a) hv
  have hnoop : ∀ {d : Data (r_ds + 1)} {m : ProbComp (Data (r_ds + 1) × ℕ)},
      ExecRand w P.code d m → ∀ z ∈ m.eval.support, z.1 = d := by
    intro d m hm z hz
    rw [hcode] at hm
    cases hm with
    | op ho =>
      rw [ProbComp.support_eval] at hz
      cases OracleComp.eq_of_mem_supportWith_pure hz
      have hcp : (Op.copy (B := .exact) (r := r_ds + 1) 0 0).eval w d = some d := by
        simp [data_set_self]
      rw [hcp] at ho
      injection ho with h_eq
      exact h_eq.symm
  cases hex with
  | @cons _ _ _ _ m₁ μ₁ hstep₁ hrest₁ =>
    obtain ⟨p₀, hp₀⟩ := ν₀.support_nonempty
    let τ₀_pmf : PMF (WhpSeqOutcome C.Seed (Dynamic.spec 2 2 1) (r_ds + 1)) :=
      ν₀.map fun p => WhpSeqOutcome.ofCoupled ⟨p.1, Dictionary.empty 2, p.2⟩
    let tr₀ : WhpSeqOutcome C.Seed (Dynamic.spec 2 2 1) (r_ds + 1) :=
      WhpSeqOutcome.ofCoupled ⟨p₀.1, Dictionary.empty 2, p₀.2⟩
    have htr₀ : tr₀ ∈ τ₀_pmf.support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨p₀, hp₀, rfl⟩
    have ht₀ : tr₀.current ∈ (τ₀_pmf.map WhpSeqOutcome.current).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨tr₀, htr₀, rfl⟩
    obtain ⟨p₁, hp₁⟩ := (μ₁ tr₀.current).support_nonempty
    obtain ⟨_, hm₁, hev₁, _, hq₁⟩ := hstep₁ tr₀.current ht₀
    have hz₁ : (p₁.1.1.data, p₁.2) ∈ (m₁ tr₀.current).eval.support := by
      rw [← hev₁]; exact (PMF.mem_support_map_iff _ _ _).mpr ⟨p₁, hp₁, rfl⟩
    have hd₁ : p₁.1.1.data = C.prepare (.query k0) tr₀.current.data :=
      hnoop hm₁ _ hz₁
    obtain ⟨hst₁, hdec₁, _, _, _⟩ := hq₁ p₁ hp₁
    have ha₁ : p₁.1.2 = none :=
      congrArg Prod.snd (((Dynamic.spec 2 2 1).step_iff_stepFn _ _ _ _).mp hst₁)
    rw [ha₁, hd₁] at hdec₁
    cases hrest₁ with
    | @cons _ _ _ _ m₂ μ₂ hstep₂ hrest₂ =>
      let τ₁_pmf : PMF (WhpSeqOutcome C.Seed (Dynamic.spec 2 2 1) (r_ds + 1)) :=
        τ₀_pmf.bind fun tr => (μ₁ tr.current).map fun p =>
          tr.appendStep (.query k0) p.1.1 p.1.2 p.2
      let tr₁ := tr₀.appendStep (.query k0) p₁.1.1 p₁.1.2 p₁.2
      have htr₁ : tr₁ ∈ τ₁_pmf.support := by
        rw [PMF.mem_support_bind_iff]
        exact ⟨tr₀, htr₀, (PMF.mem_support_map_iff _ _ _).mpr ⟨p₁, hp₁, rfl⟩⟩
      have ht₁ : tr₁.current ∈ (τ₁_pmf.map WhpSeqOutcome.current).support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨tr₁, htr₁, rfl⟩
      obtain ⟨p₂, hp₂⟩ := (μ₂ tr₁.current).support_nonempty
      obtain ⟨_, hm₂, hev₂, _, hq₂⟩ := hstep₂ tr₁.current ht₁
      have hz₂ : (p₂.1.1.data, p₂.2) ∈ (m₂ tr₁.current).eval.support := by
        rw [← hev₂]; exact (PMF.mem_support_map_iff _ _ _).mpr ⟨p₂, hp₂, rfl⟩
      have hd₂ : p₂.1.1.data = C.prepare (.insert k0 1) tr₁.current.data :=
        hnoop hm₂ _ hz₂
      obtain ⟨hst₂, _, _, _, _⟩ := hq₂ p₂ hp₂
      have hs₂ : p₂.1.1.state = Function.update (Dictionary.empty 2) k0 (some 1) := by
        have h1 := congrArg Prod.fst (((Dynamic.spec 2 2 1).step_iff_stepFn _ _ _ _).mp hst₂)
        have hs₁ : tr₁.current.state = Dictionary.empty 2 :=
          congrArg Prod.fst (((Dynamic.spec 2 2 1).step_iff_stepFn _ _ _ _).mp hst₁)
        rw [hs₁] at h1
        exact h1
      cases hrest₂ with
      | @cons _ _ _ _ m₃ μ₃ hstep₃ _ =>
        let τ₂_pmf : PMF (WhpSeqOutcome C.Seed (Dynamic.spec 2 2 1) (r_ds + 1)) :=
          τ₁_pmf.bind fun tr => (μ₂ tr.current).map fun p =>
            tr.appendStep (.insert k0 1) p.1.1 p.1.2 p.2
        let tr₂ := tr₁.appendStep (.insert k0 1) p₂.1.1 p₂.1.2 p₂.2
        have htr₂ : tr₂ ∈ τ₂_pmf.support := by
          rw [PMF.mem_support_bind_iff]
          exact ⟨tr₁, htr₁, (PMF.mem_support_map_iff _ _ _).mpr ⟨p₂, hp₂, rfl⟩⟩
        have ht₂ : tr₂.current ∈ (τ₂_pmf.map WhpSeqOutcome.current).support :=
          (PMF.mem_support_map_iff _ _ _).mpr ⟨tr₂, htr₂, rfl⟩
        obtain ⟨p₃, hp₃⟩ := (μ₃ tr₂.current).support_nonempty
        obtain ⟨_, hm₃, hev₃, _, hq₃⟩ := hstep₃ tr₂.current ht₂
        have hz₃ : (p₃.1.1.data, p₃.2) ∈ (m₃ tr₂.current).eval.support := by
          rw [← hev₃]; exact (PMF.mem_support_map_iff _ _ _).mpr ⟨p₃, hp₃, rfl⟩
        have hd₃ : p₃.1.1.data = C.prepare (.query k0) tr₂.current.data :=
          hnoop hm₃ _ hz₃
        obtain ⟨hst₃, hdec₃, _, _, _⟩ := hq₃ p₃ hp₃
        have ha₃ : p₃.1.2 = some 1 := by
          have h3 := congrArg Prod.snd (((Dynamic.spec 2 2 1).step_iff_stepFn _ _ _ _).mp hst₃)
          change p₃.1.2 = p₂.1.1.state k0 at h3
          rw [hs₂, Function.update_self] at h3
          exact h3
        rw [ha₃, hd₃] at hdec₃
        have hregs_eq :
            (C.prepare (.query k0) tr₂.current.data).regs =
              (C.prepare (.query k0) tr₀.current.data).regs := by
          ext i
          by_cases hi : P.input i = true
          · simp [hi]
          · simp only [Bool.not_eq_true] at hi
            rw [C.prepare_regs_of_not_input hi,
              C.prepare_regs_of_not_input hi]
            dsimp only [tr₂, WhpSeqOutcome.appendStep]
            rw [hd₂, C.prepare_regs_of_not_input hi]
            dsimp only [tr₁, WhpSeqOutcome.appendStep]
            rw [hd₁, C.prepare_regs_of_not_input hi]
        rw [hregs_eq, hdec₁] at hdec₃
        cases hdec₃

/-- **Negative sanity check 2 (`halt_program_cannot_distinguish_insert_query`):**
At the raw clocked flat-machine level (`evalRand`), running the 1-instruction program
`[Instr.halt out]` across `.query k0`, `.insert k0 1`, and `.query k0` produces identical halted
register states on the two queries, so no `decode` can recover both `none` and `some 1`. -/
theorem halt_program_cannot_distinguish_insert_query {B : Basis} {r : ℕ} (w : ℕ)
    (out : Fin r) (input : Fin r → Bool)
    (encode : Dynamic.Op 2 → Fin r → ℕ)
    (decode : (o : Dynamic.Op 2) → (Fin r → ℕ) → Option ((Dynamic.spec 2 2 1).Result o))
    (x₀ : Data r) (T : ℕ) :
    let k0 : Fin 2 := ⟨0, by decide⟩
    let prep (o : Dynamic.Op 2) (d : Data r) : Data r :=
      ⟨fun i => if input i then encode o i else d.regs i, d.mem⟩
    ¬∃ (y₁ y₂ y₃ : Data r),
      RandCfg.halted (y₁.regs out) y₁ ∈
        (evalRand w ([Instr.halt out] : Program B r) (T + 1) ⟨0, prep (.query k0) x₀⟩).support ∧
      decode (.query k0) y₁.regs = some none ∧
      RandCfg.halted (y₂.regs out) y₂ ∈
        (evalRand w ([Instr.halt out] : Program B r) (T + 1) ⟨0, prep (.insert k0 1) y₁⟩).support ∧
      RandCfg.halted (y₃.regs out) y₃ ∈
        (evalRand w ([Instr.halt out] : Program B r) (T + 1) ⟨0, prep (.query k0) y₂⟩).support ∧
      decode (.query k0) y₃.regs = some (some 1) := by
  intro k0 prep ⟨y₁, y₂, y₃, h1, hdec1, h2, h3, hdec3⟩
  have heval_halt : ∀ d : Data r,
      evalRand w ([Instr.halt out] : Program B r) (T + 1) ⟨0, d⟩ =
        PMF.pure (.halted (d.regs out) d) := by
    intro d
    rw [evalRand, runRand_succ, stepRand_halt (i := out) (s := ⟨0, d⟩) (by simp), pure_bind,
      runRand_halted, ProbComp.eval_pure]
  rw [heval_halt, PMF.support_pure, Set.mem_singleton_iff] at h1 h2 h3
  have hy₁ : y₁ = prep (.query k0) x₀ := (RandCfg.halted.inj h1).2
  have hy₂ : y₂ = prep (.insert k0 1) y₁ := (RandCfg.halted.inj h2).2
  have hy₃ : y₃ = prep (.query k0) y₂ := (RandCfg.halted.inj h3).2
  have hregs : y₃.regs = y₁.regs := by
    ext i
    rw [hy₃, hy₂, hy₁]
    dsimp only [prep]
    by_cases hi : input i = true <;> simp [hi]
  rw [hregs, hdec1] at hdec3
  cases hdec3

end CslibFrontierTests.WordRAMHighProbability

end
