/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.CellProbe.StateTransition
public import CslibFrontier.DataStructure.CellProbe.Randomized.StateTransition
public import CslibFrontier.DataStructure.CellProbe.Randomized.ObliviousSequence
public import CslibFrontier.DataStructure.Dictionary.Spec
import CslibFrontier.Probability.PMF.Expect

/-!
# `Cslib.DataStructure.CellProbe` `2×2` `Impl` Layer and Yao Averaging Tests

Kernel-checked concrete instances and non-vacuity witnesses for `Cslib.DataStructure.CellProbe`:

1. **Non-zero-potential amortized deterministic `CellProbe.StateTransitionImpl`:** a 2-bit binary
   counter in `Mem 2 1` whose carry transition (`1 → 2`) incurs `4` probes while paying amortized
   charge `3` via `potential m = (m 0).1`, projected to `toBaseImpl`, `toAmortized`, adaptive
   `run_client_amortized`, multi-step `runSeq_ofFn`, and `padCells`.
2. **Worst-case deterministic `Dictionary.spec` implementation:** direct-mapped `Mem 4 2`
   implementation of `Dictionary.spec 4 3 4` exercising `toBound`, `run_client_bound`,
   `toRandomized`, and `toObliviousSequenceImpl`.
3. **Randomized `StateTransitionImpl` and `ObliviousSequenceImpl` with both initial-memory seed
   randomness and private per-operation coins:** scrambled 2-key dictionary on `Mem 3 2` over
   `Dictionary.spec 2 3 2` (`Seed := Fin 2`, uniform initial swap bit in cell `2`, plus internal
   coin draws on `query`).
4. **`DataStructure`-level zero-error Yao averaging and lower-bound transfer over non-`Fintype`
   `Dictionary.Op`:** instantiates `StateTransitionImpl.exists_det_indexedScheme` over explicit
   `opsAlphabet : Finset (Dictionary.Op 2)` with `correctSeqs` strictly larger than
   `hardDist.support`, exercises the random-initial-memory / coin-free-steps
   `exists_det_scheme` specialization without `opsAlphabet` or `horizon`, and transfers an
   unconditional `3 / 2` probe lower bound from step-indexed `IndexedScheme`s to arbitrary
   zero-error `Randomized.StateTransitionImpl`s of `Dictionary.spec 1 2 1`.
-/

public section

namespace ComplexityTests.DataStructureCellProbe

open Cslib Cslib.CellProbe Cslib.DataStructure
open Cslib.DataStructure.CellProbe
open scoped ENNReal

/-! ### 1. Amortized deterministic `CellProbe.StateTransitionImpl` (2-bit binary counter) -/

/-- Operations on a mod-4 counter (`insert` increments by `1`, `query` reads the value). -/
inductive ModCounterOp : Type where
  | insert
  | query
  deriving DecidableEq

abbrev ModCounterResult : ModCounterOp → Type
  | .insert => Unit
  | .query => Fin 4

def modCounterStep (s : Fin 4) : (o : ModCounterOp) → Fin 4 × ModCounterResult o
  | .insert => (⟨(s.1 + 1) % 4, by omega⟩, ())
  | .query => (s, s)

abbrev modCounterSpec : StateTransitionSpec :=
  StateTransitionSpec.ofFn modCounterStep

/-- 2-cell 1-bit (`Mem 2 1`) binary counter: cell `0` holds `s % 2`, cell `1` holds `s / 2`.
When `b₀ = 0`, `insert` flips cell `0` (`2` probes); when `b₀ = 1` (carry), `insert` clears cell `0`
and toggles cell `1` (`4` probes). -/
def binaryCounterScheme : CellProbe.Scheme ModCounterOp ModCounterResult 2 1 where
  init := zeroMem 2 1
  step
    | .insert => do
        let b₀ ← ProbeTree.read 0
        if b₀.1 == 0 then
          let _ ← ProbeTree.write 0 ⟨1, by decide⟩
          return ()
        else
          let _ ← ProbeTree.write 0 ⟨0, by decide⟩
          let b₁ ← ProbeTree.read 1
          let _ ← ProbeTree.write 1 ⟨1 - b₁.1, by omega⟩
          return ()
    | .query => do
        let b₀ ← ProbeTree.read 0
        let b₁ ← ProbeTree.read 1
        return ⟨b₀.1 + 2 * b₁.1, by omega⟩

-- Non-vacuity of `potential`: on state `s = 1` (`m = ![1, 0]`), `insert` takes `4` actual probes,
-- strictly exceeding the amortized charge `3`, paid by releasing `1` unit of potential on cell `0`.
example : (binaryCounterScheme.step .insert).probes ![⟨1, by decide⟩, ⟨0, by decide⟩] = 4 := by
  decide

def binaryCounterRep (s : Fin 4) (m : Mem 2 1) : Prop :=
  (m 0).1 + 2 * (m 1).1 = s.1

def binaryCounterCharge (_ : Fin 4) : ModCounterOp → ℕ
  | .insert => 3
  | .query => 2

def binaryCounterImpl :
    CellProbe.StateTransitionImpl modCounterSpec binaryCounterScheme (0 : Fin 4) :=
  CellProbe.StateTransitionImpl.ofFn
    (rep := binaryCounterRep)
    (charge := binaryCounterCharge)
    (init_rep := rfl)
    (potential := fun m => (m 0).1)
    (initPotential := 0)
    (init_potential := Nat.le_refl 0)
    (step_exec := by
      intro s m o hr _
      dsimp only [binaryCounterRep] at hr
      have hb0 : (m 0).1 < 2 := (m 0).2
      have hb1 : (m 1).1 < 2 := (m 1).2
      cases o with
      | insert =>
        by_cases h0 : (m 0).1 = 0
        · have hcond : ((m 0).1 == 0) = true := by simp [h0]
          have hne10 : (1 : Fin 2) ≠ 0 := by decide
          simp only [binaryCounterScheme, ProbeTree.run_bind, ProbeTree.run_read,
            ProbeTree.run_write, ProbeTree.run_pure, ProbeTree.probes_bind, ProbeTree.probes_read,
            ProbeTree.probes_write, ProbeTree.probes_pure, hcond, ↓reduceIte,
            StateTransitionSpec.stepFn, modCounterStep, binaryCounterRep, binaryCounterCharge,
            Function.update_self, Function.update_of_ne hne10]
          exact ⟨trivial, by omega, by omega⟩
        · have h1 : (m 0).1 = 1 := by omega
          have hcond : ((m 0).1 == 0) = false := by simp [h1]
          have hne01 : (0 : Fin 2) ≠ 1 := by decide
          have hne10 : (1 : Fin 2) ≠ 0 := by decide
          simp only [binaryCounterScheme, ProbeTree.run_bind, ProbeTree.run_read,
            ProbeTree.run_write, ProbeTree.run_pure, ProbeTree.probes_bind, ProbeTree.probes_read,
            ProbeTree.probes_write, ProbeTree.probes_pure, hcond, Bool.false_eq_true, ↓reduceIte,
            StateTransitionSpec.stepFn, modCounterStep, binaryCounterRep, binaryCounterCharge,
            Function.update_self, Function.update_of_ne hne01, Function.update_of_ne hne10]
          exact ⟨trivial, by omega, by omega⟩
      | query =>
        simp only [binaryCounterScheme, ProbeTree.run_bind, ProbeTree.run_read, ProbeTree.run_pure,
          ProbeTree.probes_bind, ProbeTree.probes_read, ProbeTree.probes_pure,
          StateTransitionSpec.stepFn, modCounterStep, binaryCounterRep, binaryCounterCharge]
        exact ⟨Fin.ext hr, hr, by omega⟩)

-- Projections to `toBaseImpl`, `toAmortized`, adaptive `run_client_amortized`, `runSeq_ofFn`,
-- and `padCells`.
example :
    let ops : List ModCounterOp := [.insert, .insert, .insert, .query]
    (binaryCounterScheme.runSeq ops).1 = (modCounterSpec.run 0 ops).2 ∧
      binaryCounterScheme.seqProbes ops = 10 ∧
      binaryCounterScheme.seqProbes ops ≤
        binaryCounterImpl.initPotential +
          modCounterSpec.totalCost binaryCounterImpl.charge 0 ops := by
  intro ops
  have hv : modCounterSpec.ValidHistory 0 ops := by trivial
  obtain ⟨htr, _, _⟩ := binaryCounterImpl.runSeq_ofFn ops hv
  exact ⟨htr, by decide, binaryCounterImpl.seqProbes_le_ofFn ops hv⟩

example :
    let adaptiveClient : modCounterSpec.Client (Fin 4) := do
      let _ ← modCounterSpec.call .insert
      let v ← modCounterSpec.call .query
      if v == 1 then
        let _ ← modCounterSpec.call .insert
        modCounterSpec.call .query
      else
        return v
    ∃ m' traces,
      DataStructure.Executes (ExecOp binaryCounterScheme) adaptiveClient binaryCounterScheme.init
        2 m' traces ∧
      binaryCounterRep 2 m' ∧
      DataStructure.total OperationTrace.probes traces + (m' 0).1 ≤ 10 := by
  intro adaptiveClient
  have hv : modCounterSpec.ValidHistory 0 (modCounterSpec.clientHistory 0 adaptiveClient) := by
    trivial
  obtain ⟨m', traces, he, hr, hpot⟩ := binaryCounterImpl.run_client_amortized adaptiveClient hv
  have hres : modCounterSpec.clientResult 0 adaptiveClient = 2 := by decide
  have hst : modCounterSpec.clientState 0 adaptiveClient = 2 := by decide
  have hcost :
      modCounterSpec.totalCost binaryCounterImpl.charge 0
        (modCounterSpec.clientHistory 0 adaptiveClient) = 10 := by
    decide
  rw [hres] at he
  rw [hst] at hr
  rw [hcost] at hpot
  exact ⟨m', traces, he, hr, hpot⟩

def paddedCounterImpl :
    CellProbe.StateTransitionImpl modCounterSpec
      (binaryCounterScheme.padCells (by decide : 2 ≤ 4)) 0 :=
  binaryCounterImpl.padCells (by decide : 2 ≤ 4)

/-! ### 2. Worst-case `Dictionary.spec` implementation (`toBound`, `toRandomized`, `toOblivious`) -/

def directDictScheme : CellProbe.Scheme (Dictionary.Op 4) Dictionary.Op.Result 4 2 where
  init := zeroMem 4 2
  step
    | .query u => do
        let w ← ProbeTree.read u
        return if w.1 == 0 then none else some (w.1 - 1)
    | .insert u v => do
        let enc : Fin 4 := if hv : v < 3 then ⟨v + 1, by omega⟩ else ⟨0, by decide⟩
        let _ ← ProbeTree.write u enc
        return ()

def directDictRep (s : Dictionary.State 4) (m : Mem 4 2) : Prop :=
  Dictionary.ValuesBounded 3 s ∧
    ∀ u : Fin 4,
      match s u with
      | none => (m u).1 = 0
      | some v => (m u).1 = v + 1

def directDictImpl :
    CellProbe.StateTransitionImpl (Dictionary.spec 4 3 4) directDictScheme (Dictionary.empty 4) :=
  CellProbe.StateTransitionImpl.ofFn
    (rep := directDictRep)
    (charge := fun _ _ => 1)
    (init_rep := ⟨Dictionary.valuesBounded_empty 4 3, fun _ => rfl⟩)
    (step_exec := by
      intro s m o ⟨hvb, hcells⟩ hval
      cases o with
      | query u =>
        simp only [directDictScheme, ProbeTree.run_bind, ProbeTree.run_read, ProbeTree.run_pure,
          ProbeTree.probes_bind, ProbeTree.probes_read, ProbeTree.probes_pure]
        refine ⟨?_, ⟨hvb, hcells⟩, by omega⟩
        have hmu := hcells u
        cases hsu : s u with
        | none =>
          rw [hsu] at hmu
          simp [hmu]
        | some v =>
          rw [hsu] at hmu
          simp [hmu]
      | insert u v =>
        have hv3 : v < 3 := hval.2
        simp only [directDictScheme, hv3, ↓reduceDIte, ProbeTree.run_bind, ProbeTree.run_write,
          ProbeTree.run_pure, ProbeTree.probes_bind, ProbeTree.probes_write, ProbeTree.probes_pure]
        refine ⟨trivial, ⟨Dictionary.valuesBounded_step_of_valid hvb hval, fun x => ?_⟩, by omega⟩
        by_cases hxu : x = u
        · subst hxu
          simp
        · simp only [Function.update_of_ne hxu]
          exact hcells x)

example :
    DataStructure.Bound directDictImpl.toBaseImpl OperationTrace.probes directDictImpl.charge :=
  directDictImpl.toBound

example :
    let padded := directDictImpl.padCells (by decide : 4 ≤ 6)
    DataStructure.Bound padded.toBaseImpl OperationTrace.probes padded.charge :=
  (directDictImpl.padCells (by decide : 4 ≤ 6)).toBound

example :
    let dictClient : (Dictionary.spec 4 3 4).Client (Option ℕ) := do
      let _ ← (Dictionary.spec 4 3 4).call (.insert 1 2)
      let ans ← (Dictionary.spec 4 3 4).call (.query 1)
      if ans == some 2 then
        (Dictionary.spec 4 3 4).call (.query 0)
      else
        return ans
    ∃ m' traces,
      DataStructure.Executes (ExecOp directDictScheme) dictClient directDictScheme.init
        none m' traces ∧
      directDictRep ((Dictionary.spec 4 3 4).clientState (Dictionary.empty 4) dictClient) m' ∧
      DataStructure.total OperationTrace.probes traces ≤ 3 := by
  intro dictClient
  have hhist :
      (Dictionary.spec 4 3 4).clientHistory (Dictionary.empty 4) dictClient =
        [.insert 1 2, .query 1, .query 0] := by
    simp [dictClient, StateTransitionSpec.clientHistory, StateTransitionSpec.call,
      Dictionary.spec, Dictionary.empty]
  have hv :
      (Dictionary.spec 4 3 4).ValidHistory (Dictionary.empty 4)
        ((Dictionary.spec 4 3 4).clientHistory (Dictionary.empty 4) dictClient) := by
    rw [hhist]
    dsimp [Dictionary.spec, StateTransitionSpec.ValidHistory, StateTransitionSpec.ofFn,
      Dictionary.valid, Dictionary.step]
    exact ⟨⟨Or.inl (by decide), by decide⟩, trivial, trivial, trivial⟩
  obtain ⟨m', traces, he, hr, hpr⟩ := directDictImpl.run_client_bound dictClient hv
  have hres : (Dictionary.spec 4 3 4).clientResult (Dictionary.empty 4) dictClient = none := by
    simp [dictClient, StateTransitionSpec.clientResult, StateTransitionSpec.call,
      Dictionary.spec, Dictionary.empty]
  have hcost :
      (Dictionary.spec 4 3 4).totalCost directDictImpl.charge (Dictionary.empty 4)
        ((Dictionary.spec 4 3 4).clientHistory (Dictionary.empty 4) dictClient) = 3 := by
    simp [directDictImpl, hhist]
  rw [hres] at he
  rw [hcost] at hpr
  exact ⟨m', traces, he, hr, hpr⟩

example :
    directDictImpl.toRandomized.Seed = Unit ∧
      directDictImpl.toRandomized.initPotential = 0 ∧
      directDictImpl.toRandomized.charge = fun _ _ => 1 := by
  simp [directDictImpl]

noncomputable def directDictOblivious :
    Randomized.ObliviousSequenceImpl
      ((Dictionary.spec 4 3 4).toObliviousSequenceSpec (Dictionary.empty 4))
      (Cslib.CellProbe.Randomized.Scheme.ofDeterministic directDictScheme) :=
  directDictImpl.toObliviousSequenceImpl

example :
    directDictOblivious.initPotential = 0 ∧ directDictOblivious.charge = fun _ => 1 := by
  simp [directDictOblivious, directDictImpl]

example :
    let W := directDictOblivious.weaken (ValidOpSeq' := fun ops => ops = [])
      (Contract' := fun _ _ => True)
      (fun ops h => by subst h; trivial)
      (fun _ _ _ _ => trivial)
    W.initPotential = 0 ∧ W.charge = fun _ => 1 := by
  simp [directDictOblivious, directDictImpl]

/-! ### 3. Randomized `StateTransitionImpl` and `ObliviousSequenceImpl` (`Seed := Fin 2` + coins) -/

instance (U : ℕ) : ∀ o : Dictionary.Op U, Inhabited o.Result
  | .query _ => inferInstanceAs (Inhabited (Option ℕ))
  | .insert _ _ => inferInstanceAs (Inhabited Unit)

/-- Slot permutation on `Fin 2` controlled by latent seed `θ : Fin 2`, embedded into `Fin 3`. -/
def scrambledSlot (θ : Fin 2) (u : Fin 2) : Fin 3 :=
  if θ.1 == 0 then ⟨u.1, by omega⟩ else ⟨1 - u.1, by omega⟩

/-- Initial 3-cell 2-bit memory storing `0` in data slots `0, 1` and seed bit `θ` in cell `2`. -/
def scrambledInitMem (θ : Fin 2) : Mem 3 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨0, by decide⟩
  | 2 => ⟨θ.1, by omega⟩

/-- Randomized 2-key dictionary scheme: `init` draws a uniform swap bit `θ ∈ Fin 2` into cell `2`;
`insert` reads cell `2` and writes `scrambledSlot θ u` (`2` probes); `query` flips a private coin
and either reads `scrambledSlot θ u` directly (`2` probes) or prefetches cell `0` first (`3` probes,
expected `5 / 2 ≤ 3`). -/
noncomputable def scrambledDictScheme :
    Cslib.CellProbe.Randomized.Scheme (Dictionary.Op 2) Dictionary.Op.Result 3 2 where
  init := (Probability.PMF.uniformOfFintype (Fin 2)).map scrambledInitMem
  step
    | .insert u v => do
        let tag ← RandProbeTree.read 2
        let slot : Fin 3 := if tag.1 == 0 then ⟨u.1, by omega⟩ else ⟨1 - u.1, by omega⟩
        let enc : Fin 4 := if hv : v < 3 then ⟨v + 1, by omega⟩ else ⟨0, by decide⟩
        let _ ← RandProbeTree.write slot enc
        return ()
    | .query u => do
        let coin ← RandProbeTree.sample (ProbComp.unifFin 1)
        let tag ← RandProbeTree.read 2
        let slot : Fin 3 := if tag.1 == 0 then ⟨u.1, by omega⟩ else ⟨1 - u.1, by omega⟩
        if coin.1 == 0 then
          let w ← RandProbeTree.read slot
          return if w.1 == 0 then none else some (w.1 - 1)
        else
          let _ ← RandProbeTree.read 0
          let w ← RandProbeTree.read slot
          return if w.1 == 0 then none else some (w.1 - 1)

-- `scrambledDictScheme.step (.query 0)` genuinely uses private per-operation coins.
example : ¬ (scrambledDictScheme.step (.query 0)).IsCoinFree :=
  fun h => h

def scrambledDictRep (θ : Fin 2) (s : Dictionary.State 2) (m : Mem 3 2) : Prop :=
  Dictionary.ValuesBounded 3 s ∧
    (m 2).1 = θ.1 ∧
    ∀ u : Fin 2,
      match s u with
      | none => (m (scrambledSlot θ u)).1 = 0
      | some v => (m (scrambledSlot θ u)).1 = v + 1

def scrambledOpCharge : Dictionary.Op 2 → ℕ
  | .insert _ _ => 2
  | .query _ => 3

private theorem decode_scrambledSlot {θ : Fin 2} {s : Dictionary.State 2} {m : Mem 3 2}
    (hrep : scrambledDictRep θ s m) (u : Fin 2) :
    (if (m (scrambledSlot θ u)).1 == 0 then none else some ((m (scrambledSlot θ u)).1 - 1)) =
      s u := by
  have hu := hrep.2.2 u
  cases hsu : s u with
  | none =>
    rw [hsu] at hu
    simp [hu]
  | some v =>
    rw [hsu] at hu
    simp [hu]

private theorem expectedProbes_read_bind {S w : ℕ} {α : Type} (i : Fin S)
    (k : Fin (2 ^ w) → RandProbeTree S w α) (m : Mem S w) :
    (RandProbeTree.read i >>= k).expectedProbes m = 1 + (k (m i)).expectedProbes m := by
  rw [RandProbeTree.expectedProbes_bind]
  simp only [RandProbeTree.expectedProbes_read, RandProbeTree.run_read, PMF.pure_map]
  rw [tsum_eq_single (m i, m) (fun x hx => by simp [PMF.pure_apply, hx])]
  simp

private theorem expectedProbes_write_bind {S w : ℕ} {α : Type} (i : Fin S) (v : Fin (2 ^ w))
    (k : PUnit → RandProbeTree S w α) (m : Mem S w) :
    (RandProbeTree.write i v >>= k).expectedProbes m =
      1 + (k PUnit.unit).expectedProbes (Function.update m i v) := by
  rw [RandProbeTree.expectedProbes_bind]
  simp only [RandProbeTree.expectedProbes_write, RandProbeTree.run_write, PMF.pure_map]
  rw [tsum_eq_single (PUnit.unit, Function.update m i v)
    (fun x hx => by simp [PMF.pure_apply, hx])]
  simp

noncomputable def scrambledDictImpl :
    Randomized.StateTransitionImpl (Dictionary.spec 2 3 2) scrambledDictScheme
      (Dictionary.empty 2) :=
  Randomized.StateTransitionImpl.ofFn
    (Seed := Fin 2)
    (seedLaw := Probability.PMF.uniformOfFintype (Fin 2))
    (charge := fun _ => scrambledOpCharge)
    (rep := scrambledDictRep)
    (init_exec := by
      refine ⟨(Probability.PMF.uniformOfFintype (Fin 2)).map (fun θ => (θ, scrambledInitMem θ)),
        ?_, ?_, ?_⟩
      · rw [PMF.map_comp]
        rfl
      · intro θ
        rw [PMF.map_comp]
        have hid : (Prod.fst ∘ fun x : Fin 2 => (x, scrambledInitMem x)) = id := rfl
        rw [hid, PMF.map_id, one_mul]
      · intro p hp
        rw [PMF.mem_support_map_iff] at hp
        obtain ⟨θ, _, rfl⟩ := hp
        refine ⟨⟨Dictionary.valuesBounded_empty 2 3, rfl, fun u => ?_⟩, Nat.le_refl 0⟩
        rcases θ with ⟨_ | _ | _, _⟩ <;> rcases u with ⟨_ | _ | _, _⟩ <;> try omega
        all_goals rfl)
    (step_exec := by
      intro s o ν hval hseed hsupp
      cases o with
      | insert u v =>
        have hv3 : v < 3 := hval.2
        let enc : Fin 4 := ⟨v + 1, by omega⟩
        let μ_step : Fin 2 × Mem 3 2 → PMF (Fin 2 × Mem 3 2) :=
          fun (θ, m) => PMF.pure (θ, Function.update m (scrambledSlot θ u) enc)
        refine ⟨μ_step, ?_, ?_, ?_⟩
        · rintro ⟨θ, m⟩ hp
          have hrep : scrambledDictRep θ s m := hsupp (θ, m) hp
          have hslot :
              (if (m 2).1 == 0 then (⟨u.1, by omega⟩ : Fin 3) else ⟨1 - u.1, by omega⟩) =
                scrambledSlot θ u := by
            rw [scrambledSlot, hrep.2.1]
          refine ⟨?_, ?_⟩
          · simp only [scrambledDictScheme, hv3, ↓reduceDIte, RandProbeTree.run_bind,
              RandProbeTree.run_read, RandProbeTree.run_write, RandProbeTree.run_pure,
              PMF.pure_bind, PMF.pure_map, hslot, μ_step, enc]
          · intro q hq
            rw [PMF.mem_support_pure_iff] at hq
            subst hq
            refine ⟨Dictionary.valuesBounded_step_of_valid hrep.1 hval, ?_, fun x => ?_⟩
            · have hne2 : (2 : Fin 3) ≠ scrambledSlot θ u := by
                have hu : u.1 < 2 := u.2
                intro h
                have hv := congrArg Fin.val h
                dsimp [scrambledSlot] at hv
                split_ifs at hv <;> simp only at hv <;> omega
              dsimp only
              rw [Function.update_of_ne hne2]
              exact hrep.2.1
            · dsimp only [StateTransitionSpec.stepFn, Dictionary.step]
              by_cases hxu : x = u
              · subst hxu
                simp [enc]
              · have hslot_ne : scrambledSlot θ x ≠ scrambledSlot θ u := by
                  have hu : u.1 < 2 := u.2
                  have hx : x.1 < 2 := x.2
                  intro h
                  have hv := congrArg Fin.val h
                  dsimp [scrambledSlot] at hv
                  split_ifs at hv <;> simp only at hv <;> exact hxu (Fin.ext (by omega))
                rw [Function.update_of_ne hxu, Function.update_of_ne hslot_ne]
                exact hrep.2.2 x
        · intro θ'
          have hbind : (ν.bind μ_step).map Prod.fst = ν.map Prod.fst := by
            rw [PMF.map_bind]
            simp only [μ_step, PMF.pure_map]
            exact PMF.bind_pure_comp Prod.fst ν
          rw [hbind]
          exact hseed θ'
        · simp only [Nat.cast_zero, mul_zero, tsum_zero, add_zero]
          calc
            (∑' p : Fin 2 × Mem 3 2,
                ν p * (scrambledDictScheme.step (.insert u v)).expectedProbes p.2)
              ≤ ∑' p : Fin 2 × Mem 3 2, ν p * (2 : ℝ≥0∞) := by
                  refine tsum_le_tsum fun ⟨θ, m⟩ => ?_
                  refine mul_le_mul_right ?_ _
                  simp only [scrambledDictScheme, hv3, ↓reduceDIte, expectedProbes_read_bind,
                    expectedProbes_write_bind, RandProbeTree.expectedProbes_pure]
                  norm_num
            _ = (scrambledOpCharge (.insert u v) : ℝ≥0∞) := by
                  rw [ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]
                  rfl
      | query u =>
        refine ⟨PMF.pure, ?_, ?_, ?_⟩
        · rintro ⟨θ, m⟩ hp
          have hrep : scrambledDictRep θ s m := hsupp (θ, m) hp
          have hslot :
              (if (m 2).1 == 0 then (⟨u.1, by omega⟩ : Fin 3) else ⟨1 - u.1, by omega⟩) =
                scrambledSlot θ u := by
            rw [scrambledSlot, hrep.2.1]
          have hdec := decode_scrambledSlot hrep u
          refine ⟨?_, ?_⟩
          · simp only [scrambledDictScheme, RandProbeTree.run_bind, RandProbeTree.run_sample,
              ProbComp.eval_unifFin, PMF.bind_map, Function.comp_def, RandProbeTree.run_read,
              PMF.pure_bind, PMF.pure_map, PMF.map_bind, hslot]
            trans ((Probability.PMF.uniformOfFintype (Fin 2)).bind fun _ => PMF.pure (s u, m))
            · refine congrArg _ (funext fun a => ?_)
              rcases a with ⟨_ | _ | _, ha⟩
              · simp only [beq_self_eq_true, ↓reduceIte, RandProbeTree.run_bind,
                  RandProbeTree.run_read, RandProbeTree.run_pure, PMF.pure_bind, PMF.pure_map,
                  hdec]
              · have hc1 : ((0 + 1 : ℕ) == 0) = false := rfl
                simp only [hc1, Bool.false_eq_true, ↓reduceIte, RandProbeTree.run_bind,
                  RandProbeTree.run_read, RandProbeTree.run_pure, PMF.pure_bind, PMF.pure_map,
                  hdec]
              · omega
            · exact PMF.bind_const _ _
          · intro q hq
            rw [PMF.mem_support_pure_iff] at hq
            subst hq
            exact hrep
        · intro θ'
          rw [PMF.bind_pure]
          exact hseed θ'
        · simp only [Nat.cast_zero, mul_zero, tsum_zero, add_zero]
          calc
            (∑' p : Fin 2 × Mem 3 2,
                ν p * (scrambledDictScheme.step (.query u)).expectedProbes p.2)
              ≤ ∑' p : Fin 2 × Mem 3 2, ν p * (3 : ℝ≥0∞) := by
                  refine tsum_le_tsum fun ⟨θ, m⟩ => ?_
                  refine mul_le_mul_right ?_ _
                  rw [scrambledDictScheme, RandProbeTree.expectedProbes_bind]
                  simp only [RandProbeTree.expectedProbes_sample, zero_add,
                    RandProbeTree.run_sample, ProbComp.eval_unifFin, PMF.map_comp,
                    Function.comp_def]
                  rw [Probability.PMF.tsum_map_mul, tsum_fintype]
                  have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
                  rw [huniv, Finset.sum_pair (by decide)]
                  have h0 : ((0 : Fin 2).1 == 0) = true := rfl
                  have h1 : ((1 : Fin 2).1 == 0) = false := rfl
                  simp only [Probability.PMF.uniformOfFintype_apply, Fintype.card_fin,
                    expectedProbes_read_bind, h0, h1, Bool.false_eq_true, ↓reduceIte,
                    RandProbeTree.expectedProbes_pure]
                  rw [← mul_add]
                  exact (ENNReal.inv_mul_le_iff (by norm_num) (by norm_num)).mpr (by norm_num)
            _ = (scrambledOpCharge (.query u) : ℝ≥0∞) := by
                  rw [ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]
                  rfl)

noncomputable def scrambledDictOblivious :
    Randomized.ObliviousSequenceImpl
      ((Dictionary.spec 2 3 2).toObliviousSequenceSpec (Dictionary.empty 2))
      scrambledDictScheme :=
  scrambledDictImpl.toObliviousSequenceImpl scrambledOpCharge (by simp [scrambledDictImpl])

example :
    scrambledDictImpl.Seed = Fin 2 ∧
      scrambledDictImpl.initPotential = 0 ∧
      scrambledDictImpl.charge = (fun _ => scrambledOpCharge) ∧
      scrambledDictImpl.singleState ∧
      (scrambledDictImpl.padCells (by decide : 3 ≤ 5)).Seed = Fin 2 := by
  simp [scrambledDictImpl]

/-! ### 4. Yao averaging on non-`Fintype` `Dictionary.Op` and lower-bound transfer -/

-- `Dictionary.Op 2` is genuinely infinite (not `Fintype`), because `insert 0` embeds `ℕ`.
theorem not_fintype_dictionary_op : ¬ Nonempty (Fintype (Dictionary.Op 2)) := by
  rintro ⟨inst⟩
  let _ : Fintype (Dictionary.Op 2) := inst
  let emb : ℕ ↪ Dictionary.Op 2 := ⟨Dictionary.Op.insert 0, fun _ _ h => by cases h; rfl⟩
  have hle : (Finset.range (Fintype.card (Dictionary.Op 2) + 1)).card ≤
      Fintype.card (Dictionary.Op 2) := by
    rw [← Finset.card_map emb]
    exact Finset.card_le_univ _
  rw [Finset.card_range] at hle
  omega

/-- Explicit finite alphabet of admissible operations on `Dictionary.spec 2 3 2` (`8` ops). -/
def validDictOps2 : Finset (Dictionary.Op 2) :=
  ((Finset.univ : Finset (Fin 2)).image Dictionary.Op.query) ∪
    ((Finset.univ : Finset (Fin 2)).biUnion fun u =>
      (Finset.range 3).image fun v => Dictionary.Op.insert u v)

def dictSeq0 : List (Dictionary.Op 2) := [.insert 0 2, .query 0]
def dictSeq1 : List (Dictionary.Op 2) := [.insert 1 1, .query 1]
def dictSeqExtra : List (Dictionary.Op 2) := [.insert 0 1, .insert 1 2, .query 0]

noncomputable def dictHardDist2 : PMF (List (Dictionary.Op 2)) :=
  (Probability.PMF.uniformOfFintype Bool).map fun b => cond b dictSeq1 dictSeq0

-- `DataStructure`-level zero-error Yao averaging over non-`Fintype` `Dictionary.Op 2` with
-- `dictSeqExtra ∈ correctSeqs \ dictHardDist2.support`.
theorem exists_det_indexedScheme_scrambledDict :
    let correctSeqs : Set (List (Dictionary.Op 2)) := {dictSeq0, dictSeq1, dictSeqExtra}
    dictSeqExtra ∈ correctSeqs ∧
      dictSeqExtra ∉ dictHardDist2.support ∧
      ∃ D_det ∈ (scrambledDictScheme.indexedSchemeLaw 3 validDictOps2).support,
        (∀ ops ∈ correctSeqs,
          (D_det.runSeq ops).1 = ((Dictionary.spec 2 3 2).run (Dictionary.empty 2) ops).2) ∧
        (∑' ops, dictHardDist2 ops * (D_det.seqProbes ops : ℝ≥0∞)) ≤ 5 := by
  intro correctSeqs
  have hnot_supp : dictSeqExtra ∉ dictHardDist2.support := by
    simp only [dictHardDist2, PMF.mem_support_map_iff, not_exists, not_and]
    intro b _
    cases b <;> simp [dictSeq0, dictSeq1, dictSeqExtra]
  have hvalid0 : (Dictionary.spec 2 3 2).ValidHistory (Dictionary.empty 2) dictSeq0 := by
    dsimp [dictSeq0, Dictionary.spec, StateTransitionSpec.ValidHistory,
      StateTransitionSpec.ofFn, Dictionary.valid, Dictionary.step]
    refine ⟨⟨Or.inl (by decide), by decide⟩, trivial, trivial⟩
  have hvalid1 : (Dictionary.spec 2 3 2).ValidHistory (Dictionary.empty 2) dictSeq1 := by
    dsimp [dictSeq1, Dictionary.spec, StateTransitionSpec.ValidHistory,
      StateTransitionSpec.ofFn, Dictionary.valid, Dictionary.step]
    refine ⟨⟨Or.inl (by decide), by decide⟩, trivial, trivial⟩
  have hvalidE : (Dictionary.spec 2 3 2).ValidHistory (Dictionary.empty 2) dictSeqExtra := by
    dsimp [dictSeqExtra, Dictionary.spec, StateTransitionSpec.ValidHistory,
      StateTransitionSpec.ofFn, Dictionary.valid, Dictionary.step]
    refine ⟨⟨Or.inl (by decide), by decide⟩, ⟨Or.inl (by decide), by decide⟩, trivial, trivial⟩
  have halph0 : ∀ o ∈ dictSeq0, o ∈ validDictOps2 := by simp [dictSeq0, validDictOps2]
  have halph1 : ∀ o ∈ dictSeq1, o ∈ validDictOps2 := by simp [dictSeq1, validDictOps2]
  have halphE : ∀ o ∈ dictSeqExtra, o ∈ validDictOps2 := by simp [dictSeqExtra, validDictOps2]
  have hcorrectSeqs : ∀ ops ∈ correctSeqs,
      (Dictionary.spec 2 3 2).ValidHistory (Dictionary.empty 2) ops ∧
        ops.length ≤ 3 ∧ ∀ o ∈ ops, o ∈ validDictOps2 := by
    rintro ops (rfl | rfl | rfl)
    · exact ⟨hvalid0, by decide, halph0⟩
    · exact ⟨hvalid1, by decide, halph1⟩
    · exact ⟨hvalidE, by decide, halphE⟩
  have hhardDist : ∀ ops ∈ dictHardDist2.support,
      (Dictionary.spec 2 3 2).ValidHistory (Dictionary.empty 2) ops ∧
        ops.length ≤ 3 ∧ ∀ o ∈ ops, o ∈ validDictOps2 := by
    intro ops hops
    rw [dictHardDist2, PMF.mem_support_map_iff] at hops
    obtain ⟨b, _, rfl⟩ := hops
    cases b
    · exact ⟨hvalid0, by decide, halph0⟩
    · exact ⟨hvalid1, by decide, halph1⟩
  obtain ⟨D_det, hmem, hcorr, hle⟩ :=
    scrambledDictImpl.exists_det_indexedScheme validDictOps2 3 correctSeqs hcorrectSeqs
      dictHardDist2 hhardDist
  refine ⟨Or.inr (Or.inr rfl), hnot_supp, D_det, hmem, hcorr, hle.trans ?_⟩
  rw [dictHardDist2, Probability.PMF.tsum_map_mul, tsum_fintype]
  have hbool : (Finset.univ : Finset Bool) = {false, true} := by decide
  rw [hbool, Finset.sum_pair (by decide)]
  have hc0 : (Dictionary.spec 2 3 2).totalCost scrambledDictImpl.charge (Dictionary.empty 2)
      dictSeq0 = 5 := by
    simp [scrambledDictImpl, scrambledOpCharge, dictSeq0, Dictionary.spec]
  have hc1 : (Dictionary.spec 2 3 2).totalCost scrambledDictImpl.charge (Dictionary.empty 2)
      dictSeq1 = 5 := by
    simp [scrambledDictImpl, scrambledOpCharge, dictSeq1, Dictionary.spec]
  have hip : scrambledDictImpl.initPotential = 0 := by
    simp [scrambledDictImpl]
  simp only [hip, Nat.cast_zero, zero_add, Bool.cond_false, Bool.cond_true, hc0, hc1,
    Probability.PMF.uniformOfFintype_apply, Fintype.card_bool]
  rw [← mul_add]
  exact (ENNReal.inv_mul_le_iff (by norm_num) (by norm_num)).mpr (by norm_num)

/-! #### Concrete lower-bound transfer sanity test (`Dictionary.spec 1 2 1`) -/

def lbOps0 : List (Dictionary.Op 1) := [.insert 0 0, .query 0]
def lbOps1 : List (Dictionary.Op 1) := [.insert 0 1, .query 0]

noncomputable def lbHardDist : PMF (List (Dictionary.Op 1)) :=
  (Probability.PMF.uniformOfFintype Bool).map fun b => cond b lbOps1 lbOps0

def lbAlphabet : Finset (Dictionary.Op 1) := {.insert 0 0, .insert 0 1, .query 0}

/-- Every deterministic step-indexed `IndexedScheme` (at **any** cell count `cells` and word width
`w`) that correctly answers both `lbOps0` and `lbOps1` makes at least `3` probes in total across the
pair: `D_det.step 1 (.query 0)` must probe at least `1` cell on each memory to distinguish `some 0`
from `some 1`, and at least one of the two step-`0` `insert` trees must probe at least `1` cell so
their post-memories are not both equal to `D_det.init`. -/
theorem three_le_seqProbes_pair_of_correct {cells w : ℕ}
    (D_det : IndexedScheme (Dictionary.Op 1) Dictionary.Op.Result cells w)
    (h0 : (D_det.runSeq lbOps0).1 =
      ((Dictionary.spec 1 2 1).run (Dictionary.empty 1) lbOps0).2)
    (h1 : (D_det.runSeq lbOps1).1 =
      ((Dictionary.spec 1 2 1).run (Dictionary.empty 1) lbOps1).2) :
    3 ≤ D_det.seqProbes lbOps0 + D_det.seqProbes lbOps1 := by
  set t0 := D_det.step 0 (.insert 0 0)
  set t1 := D_det.step 0 (.insert 0 1)
  set tq := D_det.step 1 (.query 0)
  set m0 := (t0.run D_det.init).2
  set m1 := (t1.run D_det.init).2
  have hq0 : (tq.run m0).1 = some 0 := by
    have hcons := congrArg List.tail h0
    have hhead := congrArg List.head? hcons
    simpa [IndexedScheme.runSeq, lbOps0, Dictionary.spec, StateTransitionSpec.run,
      StateTransitionSpec.ofFn, Dictionary.step, t0, tq, m0] using hhead
  have hq1 : (tq.run m1).1 = some 1 := by
    have hcons := congrArg List.tail h1
    have hhead := congrArg List.head? hcons
    simpa [IndexedScheme.runSeq, lbOps1, Dictionary.spec, StateTransitionSpec.run,
      StateTransitionSpec.ofFn, Dictionary.step, t1, tq, m1] using hhead
  have htq_pos : ∀ m : Mem cells w, 1 ≤ tq.probes m := by
    intro m
    cases htq : tq with
    | pure ans =>
      rw [htq] at hq0 hq1
      have heq : (some 0 : Option ℕ) = some 1 := hq0.symm.trans hq1
      cases heq
    | liftBind q cont =>
      cases q <;> change 1 ≤ 1 + _ <;> omega
  have hins_pos : 1 ≤ t0.probes D_det.init + t1.probes D_det.init := by
    by_contra hlt
    have hp0 : t0.probes D_det.init = 0 := by omega
    have hp1 : t1.probes D_det.init = 0 := by omega
    have hm0 : m0 = D_det.init := by
      funext i
      refine t0.nextMem_eq_of_notMem_probedCells D_det.init fun hi => ?_
      have hcard := t0.card_probedCells_le_probes D_det.init
      rw [hp0, Nat.le_zero, Finset.card_eq_zero] at hcard
      rw [hcard] at hi
      exact Finset.notMem_empty i hi
    have hm1 : m1 = D_det.init := by
      funext i
      refine t1.nextMem_eq_of_notMem_probedCells D_det.init fun hi => ?_
      have hcard := t1.card_probedCells_le_probes D_det.init
      rw [hp1, Nat.le_zero, Finset.card_eq_zero] at hcard
      rw [hcard] at hi
      exact Finset.notMem_empty i hi
    have heq : (some 0 : Option ℕ) = some 1 := by
      rw [← hq0, ← hq1, hm0, hm1]
    cases heq
  have hpr0 : D_det.seqProbes lbOps0 = t0.probes D_det.init + tq.probes m0 := by
    simp [IndexedScheme.seqProbes, lbOps0, t0, tq, m0]
  have hpr1 : D_det.seqProbes lbOps1 = t1.probes D_det.init + tq.probes m1 := by
    simp [IndexedScheme.seqProbes, lbOps1, t1, tq, m1]
  have hqm0 := htq_pos m0
  have hqm1 := htq_pos m1
  omega

/-- Lower-bound transfer sanity check: **every** zero-error `Randomized.StateTransitionImpl` of
`Dictionary.spec 1 2 1` (for any `cells, w : ℕ`, including internal-coin schemes) satisfies
`3 / 2 ≤ C.initPotential + E_{lbHardDist}[totalCost C.charge]`. -/
theorem three_halves_le_any_randomized_impl {cells w : ℕ}
    (P : Cslib.CellProbe.Randomized.Scheme (Dictionary.Op 1) Dictionary.Op.Result cells w)
    (C : Randomized.StateTransitionImpl (Dictionary.spec 1 2 1) P (Dictionary.empty 1)) :
    (3 : ℝ≥0∞) / 2 ≤
      (C.initPotential : ℝ≥0∞) +
        ∑' ops, lbHardDist ops *
          ((Dictionary.spec 1 2 1).totalCost C.charge (Dictionary.empty 1) ops : ℝ≥0∞) := by
  have hv0 : (Dictionary.spec 1 2 1).ValidHistory (Dictionary.empty 1) lbOps0 := by
    dsimp [lbOps0, Dictionary.spec, StateTransitionSpec.ValidHistory,
      StateTransitionSpec.ofFn, Dictionary.valid, Dictionary.step]
    exact ⟨⟨Or.inl (by decide), by decide⟩, trivial, trivial⟩
  have hv1 : (Dictionary.spec 1 2 1).ValidHistory (Dictionary.empty 1) lbOps1 := by
    dsimp [lbOps1, Dictionary.spec, StateTransitionSpec.ValidHistory,
      StateTransitionSpec.ofFn, Dictionary.valid, Dictionary.step]
    exact ⟨⟨Or.inl (by decide), by decide⟩, trivial, trivial⟩
  have halph0 : ∀ o ∈ lbOps0, o ∈ lbAlphabet := by simp [lbOps0, lbAlphabet]
  have halph1 : ∀ o ∈ lbOps1, o ∈ lbAlphabet := by simp [lbOps1, lbAlphabet]
  let correctSeqs : Set (List (Dictionary.Op 1)) := {lbOps0, lbOps1}
  have hcorr : ∀ ops ∈ correctSeqs,
      (Dictionary.spec 1 2 1).ValidHistory (Dictionary.empty 1) ops ∧
        ops.length ≤ 2 ∧ ∀ o ∈ ops, o ∈ lbAlphabet := by
    rintro ops (rfl | rfl)
    · exact ⟨hv0, by decide, halph0⟩
    · exact ⟨hv1, by decide, halph1⟩
  have hhard : ∀ ops ∈ lbHardDist.support,
      (Dictionary.spec 1 2 1).ValidHistory (Dictionary.empty 1) ops ∧
        ops.length ≤ 2 ∧ ∀ o ∈ ops, o ∈ lbAlphabet := by
    intro ops hops
    rw [lbHardDist, PMF.mem_support_map_iff] at hops
    obtain ⟨b, _, rfl⟩ := hops
    cases b
    · exact ⟨hv0, by decide, halph0⟩
    · exact ⟨hv1, by decide, halph1⟩
  refine C.le_expected_totalCost_of_det_indexedScheme lbAlphabet 2 correctSeqs hcorr
    lbHardDist hhard fun D_det hD => ?_
  have hpair := three_le_seqProbes_pair_of_correct D_det (hD lbOps0 (Or.inl rfl))
    (hD lbOps1 (Or.inr rfl))
  rw [lbHardDist, Probability.PMF.tsum_map_mul, tsum_fintype]
  have hbool : (Finset.univ : Finset Bool) = {false, true} := by decide
  rw [hbool, Finset.sum_pair (by decide)]
  simp only [Bool.cond_false, Bool.cond_true, Probability.PMF.uniformOfFintype_apply,
    Fintype.card_bool]
  rw [← mul_add, ← Nat.cast_add]
  have hcast : (3 : ℝ≥0∞) ≤ ((D_det.seqProbes lbOps0 + D_det.seqProbes lbOps1 : ℕ) : ℝ≥0∞) :=
    Nat.cast_le.mpr hpair
  calc
    (3 : ℝ≥0∞) / 2 = (2 : ℝ≥0∞)⁻¹ * 3 := by rw [div_eq_mul_inv, mul_comm]
    _ ≤ (2 : ℝ≥0∞)⁻¹ * ((D_det.seqProbes lbOps0 + D_det.seqProbes lbOps1 : ℕ) : ℝ≥0∞) :=
        mul_le_mul_right hcast _

-- Random initial memory / coin-free steps specialization (`exists_det_scheme`, no `opsAlphabet`
-- or `horizon` needed).
example :
    let P_det := Cslib.CellProbe.Randomized.Scheme.ofDeterministic directDictScheme
    let hstep : ∀ o, (P_det.step o).IsCoinFree :=
      fun o => RandProbeTree.isCoinFree_ofProbeTree (directDictScheme.step o)
    let seq : List (Dictionary.Op 4) := [.insert 0 2, .query 0]
    ∃ D_det ∈ (P_det.schemeLaw hstep).support,
      (D_det.runSeq seq).1 = ((Dictionary.spec 4 3 4).run (Dictionary.empty 4) seq).2 ∧
      (D_det.seqProbes seq : ℝ≥0∞) ≤ 2 := by
  intro P_det hstep seq
  have hv : (Dictionary.spec 4 3 4).ValidHistory (Dictionary.empty 4) seq := by
    dsimp [seq, Dictionary.spec, StateTransitionSpec.ValidHistory,
      StateTransitionSpec.ofFn, Dictionary.valid, Dictionary.step]
    exact ⟨⟨Or.inl (by decide), by decide⟩, trivial, trivial⟩
  obtain ⟨D_det, hmem, hcorr, hle⟩ :=
    directDictImpl.toRandomized.exists_det_scheme hstep {seq}
      (fun _ h => h ▸ hv) (PMF.pure seq)
      (fun _ h => ((PMF.mem_support_pure_iff _ _).mp h) ▸ hv)
  refine ⟨D_det, hmem, hcorr seq rfl, ?_⟩
  rw [tsum_eq_single seq (fun x hx => by simp [PMF.pure_apply, hx])] at hle
  rw [tsum_eq_single seq (fun x hx => by simp [PMF.pure_apply, hx])] at hle
  have hcost : (Dictionary.spec 4 3 4).totalCost directDictImpl.charge (Dictionary.empty 4)
      seq = 2 := by
    simp [directDictImpl, CellProbe.StateTransitionImpl.ofFn, seq, Dictionary.spec]
  have hip : directDictImpl.initPotential = 0 := rfl
  simpa only [PMF.pure_apply_self, one_mul, StateTransitionImpl.toRandomized_initPotential,
    StateTransitionImpl.toRandomized_charge, hip, hcost, Nat.cast_zero, zero_add,
    Nat.cast_ofNat] using hle

end ComplexityTests.DataStructureCellProbe
