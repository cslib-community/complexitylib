/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.Dictionary.ChainedHash

/-!
# Tests for Chained Hash Table on the Randomized Word RAM

Verifies `Cslib.Algorithms.WordRAM.Dictionary.ChainedHash`:
* concrete table parameters (`bucketBits`, `numBuckets`, `hashBits`, `space`, `space_le`);
* concrete hash collisions (`u₁ ≠ u₂` mapping to the same `multiplyShift` bucket), in-place key
  updates at full capacity `n_max`, and absent-key misses via `opCode_spec`;
* `subroutineDS`, `subroutineDSStandard`, `initFresh_exec`, `initClear_exec`, `call_rename`, and
  `seq_expected_amortized` across a multi-operation sequence containing hash collisions, an
  in-place overwrite at full capacity `n_max`, and present/absent lookups.
-/

@[expose] public section

namespace ComplexityTests.WordRAMChainedHash

open Cslib Cslib.WordRAM Cslib.WordRAM.Randomized
open Cslib.Algorithms.Lean
open Cslib.Algorithms.WordRAM.Dictionary
open Cslib.Algorithms.WordRAM.Dictionary.ChainedHash
open Cslib.Algorithms.WordRAM.Dictionary.ChainedHash.Reg
open Cslib.Probability
open scoped ENNReal

/-! ## 1. Concrete dimension and space checks -/

example : bucketBits 2 = 1 := by decide
example : numBuckets 2 = 2 := by decide
example : hashBits 16 2 = 4 := by decide
example : space 2 = 12 := by decide
example (n_max : ℕ) : space n_max ≤ 5 * n_max + 8 := space_le n_max

/-! ## 2. Concrete hash collision, full-capacity in-place update, and absent-key miss -/

/-- Key `1` in `Fin 16`. -/
abbrev u₁ : Fin 16 := ⟨1, by decide⟩

/-- Key `2` in `Fin 16` (distinct from `u₁`). -/
abbrev u₂ : Fin 16 := ⟨2, by decide⟩

/-- Absent key `3` in `Fin 16`. -/
abbrev u₃ : Fin 16 := ⟨3, by decide⟩

/-- Seed `0` in `Fin (2 ^ (hashBits 16 2 - 1)) = Fin 8` (odd multiplier `2 * 0 + 1 = 1`). -/
abbrev seed₀ : Fin (2 ^ (hashBits 16 2 - 1)) := ⟨0, by decide⟩

/-- Distinct keys `u₁`, `u₂`, and `u₃` all collide in bucket `0` under `seed₀`. -/
theorem u₁_u₂_u₃_collide :
    u₁ ≠ u₂ ∧
    multiplyShift (hashBits 16 2) (bucketBits 2) seed₀ (encodeKey (n_max := 2) u₁) = 0 ∧
    multiplyShift (hashBits 16 2) (bucketBits 2) seed₀ (encodeKey (n_max := 2) u₂) = 0 ∧
    multiplyShift (hashBits 16 2) (bucketBits 2) seed₀ (encodeKey (n_max := 2) u₃) = 0 := by
  decide

theorem hw_test : 2 * hashBits 16 2 ≤ 16 := by decide

theorem hS_test : Fits 16 (10 + space 2) := by
  rw [fits_iff]
  decide

theorem hV_test : Fits 16 100 := by
  rw [fits_iff]
  decide

/-- Six-operation workload exercising:
1. `insert u₁ 10` into an empty table (size `0 → 1`),
2. `insert u₂ 20` colliding with `u₁` in bucket `0` and reaching full capacity `n_max = 2`,
3. `insert u₁ 30` performing an in-place key update at full capacity `n_max = 2` (size stays `2`),
4. `get u₁` returning the updated value `some 30`,
5. `get u₂` returning `some 20` along the colliding chain,
6. `get u₃` traversing the colliding chain in bucket `0` and returning `none` (absent-key miss). -/
def ops6 : List (Dictionary.Op 16) :=
  [.insert u₁ 10, .insert u₂ 20, .insert u₁ 30, .get u₁, .get u₂, .get u₃]

/-- Abstract states reached after each prefix of `ops6`. -/
abbrev s₀ : Dictionary.State 16 := Dictionary.empty 16
abbrev s₁ : Dictionary.State 16 := Function.update s₀ u₁ (some 10)
abbrev s₂ : Dictionary.State 16 := Function.update s₁ u₂ (some 20)
abbrev s₃ : Dictionary.State 16 := Function.update s₂ u₁ (some 30)

/-- At `s₂` (after inserting `u₁` and `u₂`), the table is at full capacity `n_max = 2`, yet
inserting `(u₁, 30)` is valid because `u₁` is already present (`(s₂ u₁).isSome`). -/
theorem valid_insert_at_full_capacity :
    (Dictionary.dom s₂).card = 2 ∧
    (Dictionary.spec 16 100 2).valid s₂ (.insert u₁ 30) := by
  refine ⟨by decide, Or.inr ?_, by decide⟩
  decide

/-- The full 6-operation workload `ops6` is a valid history for `Dictionary.spec 16 100 2` from
`Dictionary.empty 16`. -/
theorem ops6_validHistory :
    (Dictionary.spec 16 100 2).ValidHistory (Dictionary.empty 16) ops6 := by
  refine ⟨⟨Or.inl (by decide), by decide⟩, ?_⟩
  refine ⟨⟨Or.inl (by decide), by decide⟩, ?_⟩
  refine ⟨valid_insert_at_full_capacity.2, ?_⟩
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- Running `ops6` on the abstract specification produces final state `s₃` where `u₁ ↦ some 30`,
`u₂ ↦ some 20`, and `u₃ ↦ none`. -/
theorem ops6_run_results :
    let finalState := ((Dictionary.spec 16 100 2).run (Dictionary.empty 16) ops6).1
    finalState u₁ = some 30 ∧ finalState u₂ = some 20 ∧ finalState u₃ = none := by
  decide

/-- Concrete deterministic step-by-step execution under `seed₀` (where `u₁`, `u₂`, `u₃` all collide
in bucket `0`): verifies that `opCode_spec` executes both colliding insertions, the in-place update
at full capacity `n_max = 2`, the two present-key lookups (`some 30` and `some 20`), and the
absent-key lookup (`none`). -/
theorem concrete_collision_update_and_miss_exec {x : Data rHash}
    (hr₀ : Rep 16 100 2 16 10 seed₀ s₀ x) :
    let C := subroutineDS 16 100 2 16 10 hw_test hS_test hV_test
    ∃ z₁ z₂ z₃ z₄ z₅ z₆ : Data rHash,
      ExecWithin 16 (opCode 16 2) (C.toDynamicProgram.prepare (.insert u₁ 10) x) z₁
        (55 + 9 * collCount 2 s₀ u₁ seed₀) ∧
      Rep 16 100 2 16 10 seed₀ s₁ z₁ ∧
      ExecWithin 16 (opCode 16 2) (C.toDynamicProgram.prepare (.insert u₂ 20) z₁) z₂
        (55 + 9 * collCount 2 s₁ u₂ seed₀) ∧
      Rep 16 100 2 16 10 seed₀ s₂ z₂ ∧
      ExecWithin 16 (opCode 16 2) (C.toDynamicProgram.prepare (.insert u₁ 30) z₂) z₃
        (55 + 9 * collCount 2 s₂ u₁ seed₀) ∧
      Rep 16 100 2 16 10 seed₀ s₃ z₃ ∧
      ExecWithin 16 (opCode 16 2) (C.toDynamicProgram.prepare (.get u₁) z₃) z₄
        (55 + 9 * collCount 2 s₃ u₁ seed₀) ∧
      @decode 16 100 2 (.get u₁) z₄.regs = some (some 30) ∧
      ExecWithin 16 (opCode 16 2) (C.toDynamicProgram.prepare (.get u₂) z₄) z₅
        (55 + 9 * collCount 2 s₃ u₂ seed₀) ∧
      @decode 16 100 2 (.get u₂) z₅.regs = some (some 20) ∧
      ExecWithin 16 (opCode 16 2) (C.toDynamicProgram.prepare (.get u₃) z₅) z₆
        (55 + 9 * collCount 2 s₃ u₃ seed₀) ∧
      @decode 16 100 2 (.get u₃) z₆.regs = some none := by
  intro C
  have hv₁ : (Dictionary.spec 16 100 2).valid s₀ (.insert u₁ 10) := ⟨Or.inl (by decide), by decide⟩
  have hv₂ : (Dictionary.spec 16 100 2).valid s₁ (.insert u₂ 20) := ⟨Or.inl (by decide), by decide⟩
  have hv₃ : (Dictionary.spec 16 100 2).valid s₂ (.insert u₁ 30) := valid_insert_at_full_capacity.2
  have hv₄ : (Dictionary.spec 16 100 2).valid s₃ (.get u₁) := trivial
  have hv₅ : (Dictionary.spec 16 100 2).valid s₃ (.get u₂) := trivial
  have hv₆ : (Dictionary.spec 16 100 2).valid s₃ (.get u₃) := trivial
  obtain ⟨z₁, he₁, _, hr₁, _⟩ :=
    opCode_spec hw_test hS_test hV_test (C.prepare_rep hr₀ hv₁) (.insert u₁ 10) hv₁
      (C.prepare_argMatch (.insert u₁ 10) x)
  obtain ⟨z₂, he₂, _, hr₂, _⟩ :=
    opCode_spec hw_test hS_test hV_test (C.prepare_rep hr₁ hv₂) (.insert u₂ 20) hv₂
      (C.prepare_argMatch (.insert u₂ 20) z₁)
  obtain ⟨z₃, he₃, _, hr₃, _⟩ :=
    opCode_spec hw_test hS_test hV_test (C.prepare_rep hr₂ hv₃) (.insert u₁ 30) hv₃
      (C.prepare_argMatch (.insert u₁ 30) z₂)
  obtain ⟨z₄, he₄, hdec₄, hr₄, _⟩ :=
    opCode_spec hw_test hS_test hV_test (C.prepare_rep hr₃ hv₄) (.get u₁) hv₄
      (C.prepare_argMatch (.get u₁) z₃)
  obtain ⟨z₅, he₅, hdec₅, hr₅, _⟩ :=
    opCode_spec hw_test hS_test hV_test (C.prepare_rep hr₄ hv₅) (.get u₂) hv₅
      (C.prepare_argMatch (.get u₂) z₄)
  obtain ⟨z₆, he₆, hdec₆, _, _⟩ :=
    opCode_spec hw_test hS_test hV_test (C.prepare_rep hr₅ hv₆) (.get u₃) hv₆
      (C.prepare_argMatch (.get u₃) z₅)
  have hs₃_u₁ : s₃ u₁ = some 30 := by decide
  have hs₃_u₂ : s₃ u₂ = some 20 := by decide
  have hs₃_u₃ : s₃ u₃ = none := by decide
  exact ⟨z₁, z₂, z₃, z₄, z₅, z₆, he₁, hr₁, he₂, hr₂, he₃, hr₃,
    he₄, hdec₄.trans (congrArg some hs₃_u₁),
    he₅, hdec₅.trans (congrArg some hs₃_u₂),
    he₆, hdec₆.trans (congrArg some hs₃_u₃)⟩

/-! ## 3. `SubroutineDS`, `toStandard`, `initClear_exec`, `call_rename`, `seq_expected_amortized` -/

/-- Concrete `SubroutineDS` instance over `Basis.exact`. -/
noncomputable def testDS :
    Randomized.SubroutineDS (subroutineCode 16 2) (Dictionary.spec 16 100 2)
      16 10 Fin.elim0 (Dictionary.empty 16) :=
  subroutineDS 16 100 2 16 10 hw_test hS_test hV_test

/-- Concrete `SubroutineDS` instance over `Basis.standard`. -/
noncomputable def testDSStandard :
    Randomized.SubroutineDS (subroutineCode 16 2).toStandard (Dictionary.spec 16 100 2)
      16 10 Fin.elim0 (Dictionary.empty 16) :=
  subroutineDSStandard 16 100 2 16 10 hw_test hS_test hV_test

/-- End-to-end expected-time guarantee for `ops6` from zeroed memory: total expected instruction
count of `initFresh` (`16` steps) followed by `ops6` (`6` operations) is at most
`16 + 73 * 6 = 454`. -/
theorem test_seq_expected_amortized {x : Data rHash}
    (hx : x.Bounded 16) (hfr : x.regs frontierReg = 10)
    (hz : ∀ a ∈ (Block.mk 10 (space 2)).footprint, x.mem a = 0) :
    ∃ (ν₀ ν_final : PMF (testDS.Seed × Data rHash)) (T_ops : ℝ≥0∞),
      ExecCodeDist 16 (subroutineCode 16 2).initFresh x (ν₀.map Prod.snd) testDS.initTime ∧
      testDS.ExecSteps (Dictionary.empty 16) ops6 ν₀ ν_final T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ testDS.seedSlack * testDS.seedLaw θ) ∧
      (∀ p ∈ ν_final.support,
        testDS.rep p.1 ((Dictionary.spec 16 100 2).run (Dictionary.empty 16) ops6).1 p.2) ∧
      testDS.initTime + T_ops ≤ 454 := by
  obtain ⟨ν₀, ν_final, T_ops, he_init, hex_steps, hseed, hrep, hbound⟩ :=
    ChainedHash.seq_expected_amortized 16 100 2 16 10 hw_test hS_test hV_test ops6 hx hfr hz
      ops6_validHistory
  refine ⟨ν₀, ν_final, T_ops, he_init, hex_steps, hseed, hrep, hbound.trans ?_⟩
  change (16 : ℝ≥0∞) + ((73 * 6 : ℕ) : ℝ≥0∞) ≤ 454
  norm_num

/-- Dirty-memory initialization via `initClear_exec` for `testDS`. -/
theorem test_initClear {x : Data rHash}
    (hx : x.Bounded 16) (hfr : x.regs frontierReg = 10) :
    ∃ ν₀ : PMF (testDS.Seed × Data rHash),
      ExecCodeDist 16 (subroutineCode 16 2).initClear x (ν₀.map Prod.snd)
        (testDS.initTime + (4 * testDS.space + 6 : ℕ)) ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ testDS.seedSlack * testDS.seedLaw θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs (subroutineCode 16 2).frontierReg = 10 + testDS.space ∧
        testDS.rep p.1 (Dictionary.empty 16) p.2 ∧
        testDS.potential p.1 p.2 ≤ testDS.initPotential ∧
        Modifies (Block.mk 10 testDS.space).footprint x.mem p.2.mem :=
  testDS.initClear_exec hx hfr (fun j => Fin.elim0 j)

/-- Inline subroutine invocation via `call_rename` in a `(rHash + 1)`-register caller
(`Fin rHash → Fin (rHash + 1)` via `Fin.castSucc`), where `prep` writes to the caller's scratch
register `Fin.last rHash`. -/
theorem test_call_rename
    (ν : PMF (testDS.Seed × Data (rHash + 1)))
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤ testDS.seedSlack * testDS.seedLaw θ)
    (hrep : ∀ p ∈ ν.support,
      testDS.rep p.1 (Dictionary.empty 16) (p.2.comap Fin.castSucc))
    (harg : ∀ p ∈ ν.support,
      testDS.argMatch (.get u₁) (p.2.comap Fin.castSucc).regs) :
    let prep : Code .exact (rHash + 1) := .op (.const (Fin.last rHash) 0)
    ∃ (μ_call : testDS.Seed × Data (rHash + 1) → PMF (testDS.Seed × Data (rHash + 1)))
      (T_call : testDS.Seed × Data (rHash + 1) → ℝ≥0∞),
      (∀ p ∈ ν.support,
        ExecCodeDist 16 (.seq prep ((subroutineCode 16 2).code.rename Fin.castSucc))
          p.2 ((μ_call p).map Prod.snd) (T_call p) ∧
        ∀ q ∈ (μ_call p).support,
          testDS.decode (.get u₁) (q.2.comap Fin.castSucc).regs =
            some ((Dictionary.spec 16 100 2).step (Dictionary.empty 16) (.get u₁)).2 ∧
          testDS.rep q.1 ((Dictionary.spec 16 100 2).step (Dictionary.empty 16) (.get u₁)).1
            (q.2.comap Fin.castSucc) ∧
          ∃ x' ∈ (PMF.pure (p.2.set (Fin.last rHash) 0) : PMF (Data (rHash + 1))).support,
            Modifies (Block.mk 10 testDS.space).footprint x'.mem q.2.mem ∧
            ∀ j ∉ Set.range (Fin.castSucc : Fin rHash → Fin (rHash + 1)), q.2.regs j = x'.regs j) ∧
      (∀ θ', ((ν.bind μ_call).map Prod.fst) θ' ≤ testDS.seedSlack * testDS.seedLaw θ') ∧
      (∑' p, ν p * (T_call p +
          ∑' q, μ_call p q * (testDS.potential q.1 (q.2.comap Fin.castSucc) : ℝ≥0∞))) ≤
        1 + (testDS.charge (Dictionary.empty 16) (.get u₁) : ℝ≥0∞) +
          ∑' p, ν p * (testDS.potential p.1 (p.2.comap Fin.castSucc) : ℝ≥0∞) := by
  intro prep
  refine testDS.call_rename (Fin.castSucc_injective rHash) (.get u₁) ν
    (prep := prep) (B_prep := 1)
    (μ_prep := fun p => PMF.pure (p.2.set (Fin.last rHash) 0)) (T_prep := fun _ => 1)
    trivial hseed hrep ?_
  intro p hp
  refine ⟨?_, le_rfl, ?_⟩
  · simpa [prep] using ExecCodeDist.of_exec (B := .exact) (w := 16) (x := p.2)
      (Exec.const (d := Fin.last rHash) (fits_zero 16))
  · intro x' hx'
    rw [PMF.mem_support_pure_iff] at hx'
    subst hx'
    have hbp : (p.2.comap Fin.castSucc).Bounded 16 := testDS.bounded (hrep p hp)
    refine ⟨?_, ?_, fun _ _ => rfl, ?_⟩
    · refine ⟨fun i => ?_, hbp.2⟩
      have hne : Fin.castSucc i ≠ Fin.last rHash := Fin.castSucc_ne_last i
      simp only [Data.comap_regs, Data.set_regs, Function.update_of_ne hne]
      exact hbp.1 i
    · intro i _
      have hne : Fin.castSucc i ≠ Fin.last rHash := Fin.castSucc_ne_last i
      simp [Data.set, hne]
    · have h1 := harg p hp
      have htag : ((p.2.set (Fin.last rHash) 0).comap Fin.castSucc).regs tagReg =
          (p.2.comap Fin.castSucc).regs tagReg := by
        simp [Data.comap_regs, Data.set_regs]
      have hargU : ((p.2.set (Fin.last rHash) 0).comap Fin.castSucc).regs argU =
          (p.2.comap Fin.castSucc).regs argU := by
        simp [Data.comap_regs, Data.set_regs]
      exact ⟨htag.trans h1.1, hargU.trans h1.2⟩

end ComplexityTests.WordRAMChainedHash
