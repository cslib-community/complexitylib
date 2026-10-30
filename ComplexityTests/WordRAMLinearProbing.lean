/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.Dictionary.LinearProbing

/-!
# Linear Probing Word-RAM Dictionary Tests

Exercises the open-addressed linear-probing dictionary implementation in
`Complexity.Algorithms.WordRAM.Dictionary.LinearProbing` and its 5-wise independent dyadic
cluster analysis in `Complexity.Algorithms.WordRAM.Dictionary.LinearProbing.FiveWise`:
* concrete space, table-size (`2 ^ tableLog n_max`), setup-time, and per-operation charge bounds;
* multi-key linear-probe cluster collisions when distinct keys share the same home bucket, forcing
  sequential probing across contiguous occupied runs;
* in-place key updates at full capacity `(Dictionary.dom s).card = n_max`;
* absent-key misses (`get u` halting at the first empty slot `used[pos] = 0` and decoding to
  `none`);
* deterministic step-bounded Word-RAM execution `opCode_execWithin` across inserts, cluster
  collisions, in-place updates at capacity, hits, and misses;
* instantiation of `subroutineDS`, `subroutineDSStandard`, and `seq_expected_amortized` on a
  concrete 6-operation trace.
-/

@[expose] public section

namespace ComplexityTests.WordRAMLinearProbing

open Cslib Cslib.WordRAM Cslib.WordRAM.Randomized Cslib.Probability
open Cslib.Algorithms.Lean
open Cslib.Algorithms.WordRAM.Hashing
open Cslib.Algorithms.WordRAM.Dictionary.LinearProbing
open scoped ENNReal

/-! ## 1. Concrete parameter and table-sizing sanity checks -/

example : tableLog 0 = 3 := by decide
example : tableSize 0 = 8 := by decide
example : tableLog 3 = 5 := by decide
example : tableSize 3 = 32 := by decide
example : space 3 ≤ 49 * max 3 4 + 13 := space_le 3

/-- Concrete machine parameters `U = 16`, `V = 100`, `n_max = 3`, `w = 64`, `base = 32` satisfy
the word-width and address-fit hypotheses of `LinearProbing.subroutineDS`. -/
theorem hw_example : 2 * trinomialDeg 16 (tableLog 3) ≤ 64 := by
  have hle := trinomialDeg_le_three_mul 16 (tableLog 3)
  have hval : 3 * max (Nat.clog 2 (max 16 2)) (max (tableLog 3) 1) = 15 := by decide
  omega

theorem hfit_space_example : Fits 64 (32 + space 3) := by
  have hsp := space_le 3
  have h241 : Fits 64 241 := by dsimp only [Fits]; decide
  exact h241.of_le (by omega)

theorem hfit_V_example : Fits 64 100 := by
  dsimp only [Fits]
  decide

/-! ## 2. Multi-key cluster collisions, in-place updates at capacity `n_max`, and misses -/

abbrev k1 : Fin 16 := ⟨1, by decide⟩
abbrev k2 : Fin 16 := ⟨2, by decide⟩
abbrev k3 : Fin 16 := ⟨5, by decide⟩
abbrev k4 : Fin 16 := ⟨9, by decide⟩

/-- Under the all-zero 5-wise seed `θZero`, every polynomial coefficient is `0`, so all keys
hash to the same home bucket and form a single contiguous linear-probing cluster. -/
def θZero : Seed 16 3 :=
  fun _ => ⟨0, Nat.two_pow_pos _⟩

/-- Concrete 3-key insertion sequence reaching capacity `n_max = 3`, followed by an in-place
update of `k3` at full capacity, a present-key lookup on `k3`, and an absent-key lookup on `k2`. -/
def sampleOps : List (Dictionary.Op 16) :=
  [ .insert k1 10
  , .insert k3 20
  , .insert k4 30
  , .insert k3 25
  , .get k3
  , .get k2 ]

/-- Abstract states along `sampleOps`:
- `s1`: `{k1 ↦ 10}` (size `1 < 3`);
- `s2`: `{k1 ↦ 10, k3 ↦ 20}` (size `2 < 3`);
- `s3`: `{k1 ↦ 10, k3 ↦ 20, k4 ↦ 30}` (at full capacity `3 = n_max`);
- `s4`: `{k1 ↦ 10, k3 ↦ 25, k4 ↦ 30}` (in-place update of `k3` at full capacity `3 = n_max`). -/
def s0 : Dictionary.State 16 := Dictionary.empty 16
def s1 : Dictionary.State 16 := Function.update s0 k1 (some 10)
def s2 : Dictionary.State 16 := Function.update s1 k3 (some 20)
def s3 : Dictionary.State 16 := Function.update s2 k4 (some 30)
def s4 : Dictionary.State 16 := Function.update s3 k3 (some 25)

theorem valid_insert_k1 : (Dictionary.spec 16 100 3).valid s0 (.insert k1 10) := by
  refine ⟨Or.inl ?_, by decide⟩
  simp [s0, Dictionary.dom_empty]

theorem valid_insert_k3 : (Dictionary.spec 16 100 3).valid s1 (.insert k3 20) := by
  refine ⟨Or.inl ?_, by decide⟩
  have hdom : Dictionary.dom s1 = {k1} := by
    simp [s1, s0, Dictionary.dom_insert, Dictionary.dom_empty]
  simp [hdom]

theorem valid_insert_k4 : (Dictionary.spec 16 100 3).valid s2 (.insert k4 30) := by
  refine ⟨Or.inl ?_, by decide⟩
  have hdom : Dictionary.dom s2 = insert k3 {k1} := by
    simp [s2, s1, s0, Dictionary.dom_insert, Dictionary.dom_empty]
  rw [hdom]
  decide

/-- At full capacity `(Dictionary.dom s3).card = 3 = n_max`, updating the existing key `k3`
in-place satisfies `(Dictionary.spec 16 100 3).valid` via `(s3 k3).isSome = true`. -/
theorem card_dom_s3_eq_capacity : (Dictionary.dom s3).card = 3 := by
  have hdom : Dictionary.dom s3 = insert k4 (insert k3 {k1}) := by
    simp [s3, s2, s1, s0, Dictionary.dom_insert, Dictionary.dom_empty]
  rw [hdom]
  decide

theorem valid_update_k3_at_capacity : (Dictionary.spec 16 100 3).valid s3 (.insert k3 25) := by
  refine ⟨Or.inr ?_, by decide⟩
  have hk3 : s3 k3 = some 20 := by
    dsimp only [s3, s2]
    rw [Function.update_of_ne (by decide), Function.update_self]
  simp [hk3]

/-- After the in-place update at capacity `n_max = 3`, `s4 k3 = some 25` (hit) and `s4 k2 = none`
(absent-key miss). -/
theorem s4_lookup_hit_and_miss : s4 k3 = some 25 ∧ s4 k2 = none := by
  refine ⟨?_, ?_⟩
  · dsimp only [s4]
    rw [Function.update_self]
  · dsimp only [s4, s3, s2, s1, s0]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    rfl

/-- The full 6-operation trace `sampleOps` (3 inserts to capacity, 1 in-place update at capacity,
1 hit lookup, 1 miss lookup) is a valid history of `Dictionary.spec 16 100 3`. -/
theorem sampleOps_validHistory :
    (Dictionary.spec 16 100 3).ValidHistory (Dictionary.empty 16) sampleOps := by
  refine ⟨valid_insert_k1, valid_insert_k3, valid_insert_k4,
    valid_update_k3_at_capacity, trivial, trivial, trivial⟩

/-! ## 3. Table invariant preservation across colliding clusters and updates -/

/-- Starting from zeroed memory and any seed `θ`, inserting `k1`, `k3`, `k4` and then updating `k3`
in-place at full capacity preserves `TableInv` and produces a cluster witness for any probe length
`t ≥ 1`. -/
theorem tableInv_cluster_and_update (θ : Seed 16 3) :
    ∃ (mem4 : ℕ → ℕ) (hinv4 : TableInv 16 100 3 32 θ s4 mem4),
      HasClusterWitness (hashFn 16 3) ((Dictionary.dom s4).erase k2) k2 θ
        (hinv4.probeLen k2 (hashFn 16 3 θ k2)) := by
  have hinv0 : TableInv 16 100 3 32 θ s0 (fun _ => 0) :=
    tableInv_empty 16 100 3 32 θ (fun _ => rfl)
  let p1 := probeSlot (tableLog 3) (hashFn 16 3 θ k1) (hinv0.probeLen k1 (hashFn 16 3 θ k1))
  let mem1 := insertMem 32 3 (fun _ => 0) p1 k1.val 10
  have hinv1 : TableInv 16 100 3 32 θ s1 mem1 := hinv0.insert_mem k1 10 valid_insert_k1
  let p2 := probeSlot (tableLog 3) (hashFn 16 3 θ k3) (hinv1.probeLen k3 (hashFn 16 3 θ k3))
  let mem2 := insertMem 32 3 mem1 p2 k3.val 20
  have hinv2 : TableInv 16 100 3 32 θ s2 mem2 := hinv1.insert_mem k3 20 valid_insert_k3
  let p3 := probeSlot (tableLog 3) (hashFn 16 3 θ k4) (hinv2.probeLen k4 (hashFn 16 3 θ k4))
  let mem3 := insertMem 32 3 mem2 p3 k4.val 30
  have hinv3 : TableInv 16 100 3 32 θ s3 mem3 := hinv2.insert_mem k4 30 valid_insert_k4
  let p4 := probeSlot (tableLog 3) (hashFn 16 3 θ k3) (hinv3.probeLen k3 (hashFn 16 3 θ k3))
  let mem4 := insertMem 32 3 mem3 p4 k3.val 25
  have hinv4 : TableInv 16 100 3 32 θ s4 mem4 :=
    hinv3.insert_mem k3 25 valid_update_k3_at_capacity
  exact ⟨mem4, hinv4, fun ht => hinv4.hasClusterWitness_probeLen k2 ht⟩

/-- Concrete collision check under `θZero`: when `k1` and `k3` hash to the same bucket `b`,
inserting `k1` occupies slot `b`, so `k3` must probe past `b` (`probeLen = 1`) and land in the
next slot `probeSlot (tableLog 3) b 1`. -/
theorem collision_probeLen_pos :
    let hinv0 : TableInv 16 100 3 32 θZero s0 (fun _ => 0) :=
      tableInv_empty 16 100 3 32 θZero (fun _ => rfl)
    let b1 := hashFn 16 3 θZero k1
    let p1 := probeSlot (tableLog 3) b1 (hinv0.probeLen k1 b1)
    let mem1 := insertMem 32 3 (fun _ => 0) p1 k1.val 10
    let hinv1 : TableInv 16 100 3 32 θZero s1 mem1 := hinv0.insert_mem k1 10 valid_insert_k1
    hinv1.probeLen k3 b1 = 1 := by
  intro hinv0 b1 p1 mem1 hinv1
  have ht0 : hinv0.probeLen k1 b1 = 0 := by
    by_contra hne
    have hpos : 0 < hinv0.probeLen k1 b1 := Nat.pos_of_ne_zero hne
    have hcont := hinv0.probeContinue_of_lt_probeLen k1 b1 hpos
    dsimp only [probeContinue, usedAt] at hcont
    exact absurd hcont.1 (by decide)
  have hp1_eq : p1 = b1 := by
    dsimp only [p1]
    rw [ht0, probeSlot_zero]
  have hcont0 : probeContinue 32 3 mem1 k3.val b1 0 := by
    dsimp only [probeContinue]
    rw [probeSlot_zero, ← hp1_eq]
    refine ⟨?_, ?_⟩
    · dsimp only [mem1]
      rw [usedAt_insertMem, ite_eq_left_iff.mpr (fun h => (h rfl).elim)]
    · dsimp only [mem1]
      rw [keyAt_insertMem, ite_eq_left_iff.mpr (fun h => (h rfl).elim)]
      decide
  have hnot1 : ¬probeContinue 32 3 mem1 k3.val b1 1 := by
    intro ⟨hused1, _⟩
    dsimp only [mem1] at hused1
    rw [usedAt_insertMem] at hused1
    have hne : probeSlot (tableLog 3) b1 1 ≠ p1 := by
      rw [hp1_eq]
      intro heq
      have heq' : probeSlot (tableLog 3) b1 1 = probeSlot (tableLog 3) b1 0 := by
        simpa only [probeSlot_zero] using heq
      have hinj := probeSlot_injOn_range b1 (len := 2) (by decide)
        (x₁ := 1) (Finset.mem_coe.mpr (Finset.mem_range.mpr (by decide)))
        (x₂ := 0) (Finset.mem_coe.mpr (Finset.mem_range.mpr (by decide))) heq'
      omega
    rw [ite_eq_right_iff.mpr (fun h => absurd h hne)] at hused1
    dsimp only [usedAt] at hused1
    exact absurd hused1 (by decide)
  have hle1 : hinv1.probeLen k3 b1 ≤ 1 := by
    by_contra! hgt
    exact hnot1 (hinv1.probeContinue_of_lt_probeLen k3 b1 hgt)
  have hge1 : 1 ≤ hinv1.probeLen k3 b1 := by
    by_contra! hlt
    have heq0 : hinv1.probeLen k3 b1 = 0 := by omega
    have hnot0 := hinv1.not_probeContinue_probeLen k3 b1
    rw [heq0] at hnot0
    exact hnot0 hcont0
  omega

/-! ## 4. Word-RAM `opCode_execWithin`, `subroutineDS`, `subroutineDSStandard`, and
`seq_expected_amortized` -/

/-- Concrete `SubroutineDS` instance for `(U = 16, V = 100, n_max = 3, w = 64, base = 32)` on
`Basis.exact`. -/
noncomputable def sampleDS :
    Cslib.WordRAM.Randomized.SubroutineDS (subroutineCode 16 3) (Dictionary.spec 16 100 3) 64 32
      Fin.elim0 (Dictionary.empty 16) :=
  subroutineDS 16 100 3 64 32 hw_example hfit_space_example hfit_V_example

/-- Concrete `SubroutineDS` instance on `Basis.standard`. -/
noncomputable def sampleDSStandard :
    Cslib.WordRAM.Randomized.SubroutineDS (subroutineCode 16 3).toStandard
      (Dictionary.spec 16 100 3) 64 32 Fin.elim0 (Dictionary.empty 16) :=
  subroutineDSStandard 16 100 3 64 32 hw_example hfit_space_example hfit_V_example

/-- End-to-end expected-time execution of `initFresh` followed by the 6-operation trace
`sampleOps` (3 inserts to capacity `n_max = 3`, 1 in-place update at capacity, 1 hit lookup, and
1 miss lookup) on a zeroed Word-RAM machine state. -/
theorem sampleOps_seq_expected_amortized :
    let x₀ : Data rLP :=
      { regs := fun i => if i = 18 then 32 else 0
        mem := fun _ => 0 }
    ∃ (ν₀ _ν_f : PMF (Seed 16 3 × Data rLP)) (T_ops : ℝ≥0∞),
      ExecCodeDist 64 (subroutineCode 16 3).initFresh x₀
        (ν₀.map Prod.snd) (3 + setupTime 16 3 : ℕ) ∧
      sampleDS.ExecSteps (Dictionary.empty 16) sampleOps ν₀ _ν_f T_ops ∧
      ((3 + setupTime 16 3 : ℕ) : ℝ≥0∞) + T_ops ≤
        (3 + setupTime 16 3 + sampleOps.length * charge 16 3 : ℕ) := by
  intro x₀
  have hfit_32 : Fits 64 32 := by dsimp only [Fits]; decide
  have hx₀ : x₀.Bounded 64 := by
    refine ⟨fun i => ?_, fun _ => fits_zero 64⟩
    dsimp only [x₀]
    split_ifs
    · exact hfit_32
    · exact fits_zero 64
  have hfr : x₀.regs 18 = 32 := by simp [x₀]
  have hz : ∀ a ∈ (Block.mk 32 (space 3)).footprint, x₀.mem a = 0 := fun _ _ => rfl
  exact seq_expected_amortized 16 100 3 64 32
    hw_example hfit_space_example hfit_V_example
    hx₀ hfr hz sampleOps sampleOps_validHistory

/-- Direct deterministic execution test of `opCode_execWithin` for an in-place update at full
capacity `n_max = 3`, followed by a hit lookup (`get k3 = some 25`) and an absent-key miss lookup
(`get k2 = none`), each completing within `KWise.evalSteps 3 16 (tableLog 3) 5 + 12 * 3 + 27`
deterministic instructions on every seed. -/
theorem opCode_update_hit_miss_from_rep (θ : Seed 16 3) (x : Data rLP)
    (hrep : Rep 16 100 3 64 32 θ s3 x) :
    let x_upd := sampleDS.toDynamicProgram.prepare (.insert k3 25) x
    let B := KWise.evalSteps 3 16 (tableLog 3) 5 + 12 * 3 + 27
    ∃ y_upd y_hit y_miss : Data rLP,
      ExecWithin 64 (opCode 3) x_upd y_upd B ∧
      Rep 16 100 3 64 32 θ s4 y_upd ∧
      ExecWithin 64 (opCode 3) (sampleDS.toDynamicProgram.prepare (.get k3) y_upd) y_hit B ∧
      decodeOp (V := 100) (n_max := 3) (.get k3) y_hit.regs = some (some 25) ∧
      ExecWithin 64 (opCode 3) (sampleDS.toDynamicProgram.prepare (.get k2) y_hit) y_miss B ∧
      decodeOp (V := 100) (n_max := 3) (.get k2) y_miss.regs = some none := by
  intro x_upd B
  have hrep_upd_in : Rep 16 100 3 64 32 θ s3 x_upd :=
    sampleDS.prepare_rep hrep valid_update_k3_at_capacity
  have harg_upd : argMatchOp (.insert k3 25) x_upd.regs :=
    sampleDS.prepare_argMatch (.insert k3 25) x
  obtain ⟨y_upd, ⟨n1, hn1, hex_upd⟩, _, hrep_upd, _⟩ :=
    opCode_execWithin hw_example hfit_space_example hfit_V_example
      hrep_upd_in (.insert k3 25) valid_update_k3_at_capacity harg_upd
  change Rep 16 100 3 64 32 θ s4 y_upd at hrep_upd
  have hle1 : hrep_upd_in.table_inv.probeLen (opKey (.insert k3 25))
      (hashFn 16 3 θ (opKey (.insert k3 25))) ≤ 3 :=
    hrep_upd_in.table_inv.probeLen_le_n_max _ _
  let x_hit := sampleDS.toDynamicProgram.prepare (.get k3) y_upd
  have hrep_hit_in : Rep 16 100 3 64 32 θ s4 x_hit :=
    sampleDS.prepare_rep hrep_upd trivial
  have harg_hit : argMatchOp (.get k3) x_hit.regs :=
    sampleDS.prepare_argMatch (.get k3) y_upd
  obtain ⟨y_hit, ⟨n2, hn2, hex_hit⟩, hdec_hit, hrep_hit, _⟩ :=
    opCode_execWithin hw_example hfit_space_example hfit_V_example
      hrep_hit_in (.get k3) trivial harg_hit
  change Rep 16 100 3 64 32 θ s4 y_hit at hrep_hit
  have hle2 : hrep_hit_in.table_inv.probeLen (opKey (.get k3))
      (hashFn 16 3 θ (opKey (.get k3))) ≤ 3 :=
    hrep_hit_in.table_inv.probeLen_le_n_max _ _
  let x_miss := sampleDS.toDynamicProgram.prepare (.get k2) y_hit
  have hrep_miss_in : Rep 16 100 3 64 32 θ s4 x_miss :=
    sampleDS.prepare_rep hrep_hit trivial
  have harg_miss : argMatchOp (.get k2) x_miss.regs :=
    sampleDS.prepare_argMatch (.get k2) y_hit
  obtain ⟨y_miss, ⟨n3, hn3, hex_miss⟩, hdec_miss, _, _⟩ :=
    opCode_execWithin hw_example hfit_space_example hfit_V_example
      hrep_miss_in (.get k2) trivial harg_miss
  have hle3 : hrep_miss_in.table_inv.probeLen (opKey (.get k2))
      (hashFn 16 3 θ (opKey (.get k2))) ≤ 3 :=
    hrep_miss_in.table_inv.probeLen_le_n_max _ _
  have hhit_val : ((Dictionary.spec 16 100 3).step s4 (.get k3)).2 = some 25 :=
    s4_lookup_hit_and_miss.1
  have hmiss_val : ((Dictionary.spec 16 100 3).step s4 (.get k2)).2 = none :=
    s4_lookup_hit_and_miss.2
  rw [hhit_val] at hdec_hit
  rw [hmiss_val] at hdec_miss
  refine ⟨y_upd, y_hit, y_miss,
    ⟨n1, by dsimp only [B]; omega, hex_upd⟩, hrep_upd,
    ⟨n2, by dsimp only [B]; omega, hex_hit⟩, hdec_hit,
    ⟨n3, by dsimp only [B]; omega, hex_miss⟩, hdec_miss⟩

end ComplexityTests.WordRAMLinearProbing
