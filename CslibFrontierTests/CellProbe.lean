/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.CellProbe.Defs
public import CslibFrontier.Computability.CellProbe.DecisionTree
public import CslibFrontier.Computability.CellProbe.Randomized
import CslibFrontier.Probability.PMF.Expect

/-!
# Cell-Probe Model, Locality, Decision-Tree Adapter, Counting Bound, and Yao Averaging Tests

Kernel-checked concrete instances and non-vacuity witnesses for `Cslib.CellProbe`:

1. Adaptive read/write `ProbeTree` execution, `run_eq_of_eq_on_probedCells`, and multi-step
   `IndexedScheme.runInterval_eq_of_eq_on_probedCellsInterval` /
   `nextMem_runInterval_eq_of_notMem_probedCellsInterval` on distinct memories `m₁ ≠ m₂`.
2. Static 1-bit `DecisionTree` adapter (`ProbeTree.ofDecisionTree`) agreement on output, pathwise
   `probes`, `probedCells`, and structural `depth`.
3. Tight information-theoretic cell-probe lower bound (`3 ≤ t.depth` for every `t : ProbeTree 3 2`
   distinguishing `K = 17` memory states, matched by an explicit depth-`3` decoder, plus `w = 0`).
4. Randomized `RandProbeTree` coin-fixing and zero-error Yao averaging
   (`Randomized.Scheme.exists_det_indexedScheme_le_expectedSeqProbes`) over an infinite operation
   type `InfDictOp` with explicit finite `opsAlphabet` and oblivious correctness domain
   `correctSeqs` strictly larger than `hardDist.support`, plus the random-initial-memory /
   coin-free-step `exists_det_scheme_le_expectedSeqProbes` specialization.
-/

public section

namespace CslibFrontierTests.CellProbe

open Cslib Cslib.CellProbe
open scoped ENNReal

/-! ### 1. Adaptive read/write `ProbeTree` execution and locality / replay -/

/-- Adaptive 4-cell, 3-bit (`2 ^ 3 = 8`) tree: read cell `0`; if `< 4`, write `v + 1` to cell `1`
and return `v + 1`; otherwise read cell `2` and overwrite cell `0` with it. -/
def adaptiveProg : ProbeTree 4 3 (Fin 8) := do
  let v₀ ← ProbeTree.read 0
  if h : v₀.1 < 4 then
    let next : Fin 8 := ⟨v₀.1 + 1, by omega⟩
    ProbeTree.write 1 next
    return next
  else
    let v₂ ← ProbeTree.read 2
    ProbeTree.write 0 v₂
    return v₂

def memA : Mem 4 3
  | 0 => 2
  | 1 => 0
  | 2 => 5
  | 3 => 7

def memB : Mem 4 3
  | 0 => 2
  | 1 => 0
  | 2 => 6
  | 3 => 1

-- Concrete branch 1 (`v₀ = 2 < 4`): 2 probes (read 0, write 1), cell 2 and 3 untouched.
example :
    (adaptiveProg.run memA).1 = 3 ∧
      (adaptiveProg.run memA).2 1 = 3 ∧
      (adaptiveProg.run memA).2 3 = 7 ∧
      adaptiveProg.probes memA = 2 ∧
      adaptiveProg.probedCells memA = {0, 1} ∧
      adaptiveProg.depth = 3 := by
  decide

-- Non-vacuity of `run_eq_of_eq_on_probedCells`: `memA ≠ memB` (they differ on cells 2 and 3),
-- yet they agree on `adaptiveProg.probedCells memA = {0, 1}` and therefore replay identically.
example :
    memA ≠ memB ∧
      (∀ i ∈ adaptiveProg.probedCells memA, memB i = memA i) ∧
      (adaptiveProg.run memB).1 = (adaptiveProg.run memA).1 ∧
      adaptiveProg.probes memB = adaptiveProg.probes memA ∧
      adaptiveProg.probedCells memB = adaptiveProg.probedCells memA ∧
      (∀ i ∈ adaptiveProg.probedCells memA,
        (adaptiveProg.run memB).2 i = (adaptiveProg.run memA).2 i) := by
  have hagree : ∀ i ∈ adaptiveProg.probedCells memA, memB i = memA i := by decide
  obtain ⟨hout, hpr, hcells, hmem_in⟩ := adaptiveProg.run_eq_of_eq_on_probedCells hagree
  refine ⟨?_, hagree, hout, hpr, hcells, hmem_in⟩
  intro heq
  have h3 : memA 3 = memB 3 := congrFun heq 3
  revert h3; decide

/-! ### 2. Multi-step `IndexedScheme.runInterval_eq_of_eq_on_probedCellsInterval` -/

inductive CounterOp : Type where
  | insert (cell : Fin 3) (val : Fin 4)
  | query (cell : Fin 3)
  deriving DecidableEq

abbrev CounterResult : CounterOp → Type
  | .insert _ _ => PUnit
  | .query _ => Fin 4

def counterIndexed : IndexedScheme CounterOp CounterResult 3 2 where
  init := zeroMem 3 2
  step _t
    | .insert i v => ProbeTree.write i v
    | .query i => ProbeTree.read i

example :
    let m₁ : Mem 3 2 := ![1, 2, 3]
    let m₂ : Mem 3 2 := ![1, 2, 0]
    let slice : List CounterOp := [.query 0, .insert 1 3, .query 1]
    m₁ ≠ m₂ ∧
      counterIndexed.probedCellsInterval 5 m₁ slice = {0, 1} ∧
      (counterIndexed.runInterval 5 m₂ slice).1 = (counterIndexed.runInterval 5 m₁ slice).1 ∧
      counterIndexed.probesInterval 5 m₂ slice = 3 ∧
      (counterIndexed.runInterval 5 m₁ slice).2 2 = 3 := by
  intro m₁ m₂ slice
  have hagree : ∀ i ∈ counterIndexed.probedCellsInterval 5 m₁ slice, m₂ i = m₁ i := by decide
  obtain ⟨hout, hpr, _, _⟩ :=
    counterIndexed.runInterval_eq_of_eq_on_probedCellsInterval 5 slice hagree
  refine ⟨?_, by decide, hout, ?_, ?_⟩
  · intro heq
    have h2 : m₁ 2 = m₂ 2 := congrFun heq 2
    revert h2; decide
  · rw [hpr]; decide
  · exact counterIndexed.nextMem_runInterval_eq_of_notMem_probedCellsInterval 5 m₁ slice (by decide)

/-! ### 3. Static 1-bit `DecisionTree` read-only adapter -/

/-- Unbalanced 1-bit decision tree on `Fin 3`: query bit `0`; if `false` return `true` (depth 1),
if `true` query bit `2` and return `!x₂` (depth 2). -/
def muxDT : DecisionTree (Fin 3) Bool :=
  .node 0 (.leaf true) (.node 2 (.leaf true) (.leaf false))

example :
    let xFalse : Fin 3 → Bool := ![false, true, true]
    let xTrue : Fin 3 → Bool := ![true, false, true]
    (ProbeTree.ofDecisionTree muxDT).depth = 2 ∧
      (ProbeTree.ofDecisionTree muxDT).run (boolToMem xFalse) = (true, boolToMem xFalse) ∧
      (ProbeTree.ofDecisionTree muxDT).probes (boolToMem xFalse) = 1 ∧
      (ProbeTree.ofDecisionTree muxDT).probedCells (boolToMem xFalse) = {0} ∧
      (ProbeTree.ofDecisionTree muxDT).run (boolToMem xTrue) = (false, boolToMem xTrue) ∧
      (ProbeTree.ofDecisionTree muxDT).probes (boolToMem xTrue) = 2 ∧
      (ProbeTree.ofDecisionTree muxDT).probedCells (boolToMem xTrue) = {0, 2} := by
  decide

/-! ### 4. Tight information-theoretic cell-probe counting lower bound (`K = 17` in `Mem 3 2`) -/

/-- Base-4 encoding of `x : Fin 17` across `3` cells of width `w = 2` (`2 ^ 2 = 4`,
capacity `64`). -/
def enc17 (x : Fin 17) : Mem 3 2
  | 0 => ⟨x.1 % 4, by omega⟩
  | 1 => ⟨(x.1 / 4) % 4, by omega⟩
  | 2 => ⟨(x.1 / 16) % 4, by omega⟩

/-- Explicit depth-3 cell-probe decoder recovering `x : Fin 17` from `enc17 x`. -/
def decode17Tree : ProbeTree 3 2 (Fin 17) := do
  let d₀ ← ProbeTree.read 0
  let d₁ ← ProbeTree.read 1
  let d₂ ← ProbeTree.read 2
  let val := d₀.1 + 4 * d₁.1 + 16 * d₂.1
  if h : val < 17 then
    return ⟨val, h⟩
  else
    return ⟨0, by decide⟩

-- Upper bound: `decode17Tree` has depth 3 and decodes all 17 inputs exactly.
theorem decode17Tree_correct :
    decode17Tree.depth = 3 ∧ ∀ x : Fin 17, (decode17Tree.run (enc17 x)).1 = x := by
  decide

-- Lower bound: EVERY deterministic `ProbeTree 3 2 α` distinguishing all 17 encoded inputs MUST
-- have worst-case depth at least `⌈log_4 17⌉ = 3` (since `4 ^ 2 = 16 < 17 ≤ 64 = 4 ^ 3`).
theorem depth_ge_three_of_distinguishes_17 {α : Type} (t : ProbeTree 3 2 α)
    (hinj : Function.Injective (fun x : Fin 17 => (t.run (enc17 x)).1)) :
    3 ≤ t.depth := by
  have hclog := t.clog_le_depth_of_injective enc17 hinj
  have heq : Nat.clog (2 ^ 2) (Fintype.card (Fin 17)) = 3 := by decide
  rwa [heq] at hclog

-- `w = 0` boundary check: `clog_le_depth_of_injective` needs no `0 < w` hypothesis.
example {α : Type} (t : ProbeTree 3 0 α)
    (hinj : Function.Injective (fun _ : Fin 1 => (t.run (zeroMem 3 0)).1)) :
    Nat.clog (2 ^ 0) (Fintype.card (Fin 1)) ≤ t.depth :=
  t.clog_le_depth_of_injective (fun _ => zeroMem 3 0) hinj

example (t : ProbeTree 3 2 (Fin 17)) (hdec : ∀ x : Fin 17, (t.run (enc17 x)).1 = x) :
    17 ≤ (2 ^ 2) ^ t.depth ∧ 3 ≤ t.depth := by
  have hinj : Function.Injective (fun x : Fin 17 => (t.run (enc17 x)).1) :=
    fun x y hxy => (hdec x).symm.trans (hxy.trans (hdec y))
  exact ⟨by simpa using t.card_le_pow_depth_of_injective enc17 hinj,
    depth_ge_three_of_distinguishes_17 t hinj⟩

/-! ### 5. `RandProbeTree` coin-fixing and zero-error Yao averaging over an infinite `Op` type -/

/-- Coin-flipping probe tree: draw a uniform bit `b ∈ Fin 2`; on `0` return `0` in `0` probes,
on `1` read cell `0` and write cell `1` (`2` probes), giving exact `expectedProbes = 1`. -/
noncomputable def coinProbeTree : RandProbeTree 2 2 (Fin 4) := do
  let b ← RandProbeTree.sample (ProbComp.unifFin 1)
  if b.1 == 0 then
    return 0
  else
    let v ← RandProbeTree.read 0
    RandProbeTree.write 1 v
    return v

theorem coinProbeTree_expectedProbes (m : Mem 2 2) :
    coinProbeTree.expectedProbes m = 1 := by
  rw [coinProbeTree, RandProbeTree.expectedProbes_bind]
  simp only [RandProbeTree.expectedProbes_sample, zero_add, RandProbeTree.run_sample,
    PMF.map_comp, Function.comp_def, ProbComp.eval_unifFin]
  rw [Probability.PMF.tsum_map_mul, tsum_fintype]
  have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  rw [huniv, Finset.sum_pair (by decide)]
  have h0 : ((0 : Fin 2).1 == 0) = true := rfl
  have h1 : ((1 : Fin 2).1 == 0) = false := rfl
  simp only [Probability.PMF.uniformOfFintype_apply, Fintype.card_fin, h0, ↓reduceIte,
    RandProbeTree.expectedProbes_pure, mul_zero, zero_add, h1, Bool.false_eq_true,
    RandProbeTree.expectedProbes_bind, RandProbeTree.expectedProbes_read,
    RandProbeTree.expectedProbes_write, RandProbeTree.run_read, PMF.pure_map,
    tsum_zero, add_zero, mul_one, PMF.tsum_coe]
  norm_num [ENNReal.inv_mul_cancel]

/-- Infinite operation type (mirroring `Dictionary.Dynamic.Op.insert (u : Fin U) (v : ℕ)`):
`insert` carries an unbounded `val : ℕ`, with `val < 4` enforced on admissible operations. -/
inductive InfDictOp : Type where
  | insert (key : Fin 2) (val : ℕ)
  | query (key : Fin 2)
  deriving DecidableEq

abbrev InfDictResult : InfDictOp → Type
  | .insert _ _ => PUnit
  | .query _ => Fin 4

instance : ∀ o, Inhabited (InfDictResult o)
  | .insert _ _ => inferInstanceAs (Inhabited PUnit)
  | .query _ => inferInstanceAs (Inhabited (Fin 4))

/-- Explicit finite alphabet of admissible operations (`val < 4`), size `2 * 4 + 2 = 10`. -/
def validInfDictOps : Finset InfDictOp :=
  ((Finset.univ : Finset (Fin 2)).biUnion fun k =>
    (Finset.range 4).image fun v => InfDictOp.insert k v) ∪
  (Finset.univ : Finset (Fin 2)).image InfDictOp.query

/-- Reference specification for 2-key bounded-value dictionary starting from `(0, 0)`. -/
def refRunFrom : (Fin 2 → Fin 4) → List InfDictOp → List (Sigma InfDictResult)
  | _, [] => []
  | st, .insert k v :: ops =>
      let fv : Fin 4 := if hv : v < 4 then ⟨v, hv⟩ else 0
      ⟨.insert k v, PUnit.unit⟩ :: refRunFrom (Function.update st k fv) ops
  | st, .query k :: ops =>
      ⟨.query k, st k⟩ :: refRunFrom st ops

def GoodInfDict (ops : List InfDictOp) (tr : List (Sigma InfDictResult)) : Prop :=
  tr = refRunFrom (fun _ => 0) ops

/-- Zero-error randomized scheme on `Mem 2 2`: `insert k v` writes `⟨v, hv⟩` when `v < 4` (and `0`
otherwise) to cell `k` (`1` probe); `query k` flips a private coin — with prob `1/2` reads cell `k`
directly (`1` probe), and with prob `1/2` reads the sibling cell `1 - k` first and then reads
cell `k` (`2` probes, expected `3/2`). -/
noncomputable def randDictScheme : Randomized.Scheme InfDictOp InfDictResult 2 2 where
  init := PMF.pure (zeroMem 2 2)
  step
    | .insert k v =>
        let fv : Fin 4 := if hv : v < 4 then ⟨v, hv⟩ else 0
        RandProbeTree.write k fv
    | .query k => do
        let c ← RandProbeTree.sample (ProbComp.unifFin 1)
        if c.1 == 0 then
          RandProbeTree.read k
        else
          let _ ← RandProbeTree.read ⟨1 - k.1, by omega⟩
          RandProbeTree.read k

private theorem randDictScheme_step_support (m : Mem 2 2) (o : InfDictOp)
    {out : (InfDictResult o × Mem 2 2) × ℕ}
    (hout : out ∈ ((randDictScheme.step o).run m).support) :
    match o, out with
    | .insert k v, ((u, m'), _) =>
        let fv : Fin 4 := if hv : v < 4 then ⟨v, hv⟩ else 0
        u = PUnit.unit ∧ m' = Function.update m k fv
    | .query k, ((ans, m'), _) =>
        ans = m k ∧ m' = m := by
  cases o with
  | insert k v =>
    simp only [randDictScheme, RandProbeTree.run_write, PMF.mem_support_pure_iff] at hout
    rcases hout with rfl
    exact ⟨rfl, rfl⟩
  | query k =>
    simp only [randDictScheme, RandProbeTree.run_bind, RandProbeTree.run_sample,
      ProbComp.eval_unifFin, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hout
    obtain ⟨z, ⟨b, _, rfl⟩, hcont⟩ := hout
    by_cases hb : b.1 == 0
    · simp only [hb, ↓reduceIte] at hcont
      obtain ⟨a, ha, rfl⟩ := hcont
      change a ∈ (RandProbeTree.run (RandProbeTree.read (w := 2) k) m).support at ha
      rw [RandProbeTree.run_read, PMF.mem_support_pure_iff] at ha
      rcases ha with rfl
      exact ⟨rfl, rfl⟩
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, RandProbeTree.run_bind,
        RandProbeTree.run_read, PMF.pure_bind, PMF.mem_support_map_iff] at hcont
      obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hcont
      change a ∈ (RandProbeTree.run (RandProbeTree.read (w := 2) k) m).support at ha
      rw [RandProbeTree.run_read, PMF.mem_support_pure_iff] at ha
      rcases ha with rfl
      exact ⟨rfl, rfl⟩

private theorem randDictScheme_runFrom_good (m : Mem 2 2) (ops : List InfDictOp)
    {z : (List (Sigma InfDictResult) × Mem 2 2) × ℕ}
    (hz : z ∈ (randDictScheme.runFrom m ops).support) :
    z.1.1 = refRunFrom m ops := by
  induction ops generalizing m z with
  | nil =>
    simp only [Randomized.Scheme.runFrom_nil, PMF.mem_support_pure_iff] at hz
    rcases hz with rfl
    rfl
  | cons o rest ih =>
    simp only [Randomized.Scheme.runFrom_cons, PMF.mem_support_bind_iff,
      PMF.mem_support_map_iff] at hz
    obtain ⟨⟨⟨a, m'⟩, p₁⟩, h1, ⟨⟨tr, m''⟩, p₂⟩, h2, rfl⟩ := hz
    have hstep := randDictScheme_step_support m o h1
    have htail : tr = refRunFrom m' rest := ih m' h2
    cases o with
    | insert k v =>
      rcases hstep with ⟨rfl, rfl⟩
      simp [refRunFrom, htail]
    | query k =>
      rcases hstep with ⟨rfl, rfl⟩
      simp [refRunFrom, htail]

theorem randDictScheme_zero_error (ops : List InfDictOp)
    {tr : List (Sigma InfDictResult)}
    (htr : tr ∈ ((randDictScheme.runSeq ops).map Prod.fst).support) :
    GoodInfDict ops tr := by
  simp only [Randomized.Scheme.runSeq, PMF.mem_support_map_iff, PMF.mem_support_bind_iff] at htr
  obtain ⟨zp, ⟨m₀, hm₀, z, hz, rfl⟩, rfl⟩ := htr
  simp only [randDictScheme, PMF.mem_support_pure_iff] at hm₀
  subst hm₀
  exact randDictScheme_runFrom_good (zeroMem 2 2) ops hz

/-- Non-vacuous zero-error Yao averaging check: `correctSeqs` contains single-step decode queries
`[.query 0]`, `[.query 1]` OUTSIDE `hardDist.support = {[.insert 0 3, .query 0]}`, over infinite
`InfDictOp`. -/
theorem exists_det_indexedScheme_infDict_test :
    let correctSeqs : Set (List InfDictOp) :=
      {[.query 0], [.query 1], [.insert 0 3, .query 0]}
    let hardDist : PMF (List InfDictOp) := PMF.pure [.insert 0 3, .query 0]
    ∃ D_det : IndexedScheme InfDictOp InfDictResult 2 2,
      (∀ ops ∈ correctSeqs, GoodInfDict ops (D_det.runSeq ops).1) ∧
      (∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) ≤
        ∑' ops, hardDist ops * randDictScheme.expectedSeqProbes ops := by
  intro correctSeqs hardDist
  have hS : ∀ ops ∈ correctSeqs, ops.length ≤ 2 ∧ ∀ o ∈ ops, o ∈ validInfDictOps := by
    intro ops hops
    simp only [correctSeqs, Set.mem_insert_iff, Set.mem_singleton_iff] at hops
    rcases hops with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      intro o ho <;> revert o ho <;> decide
  have hν : ∀ ops ∈ hardDist.support, ops.length ≤ 2 ∧ ∀ o ∈ ops, o ∈ validInfDictOps := by
    intro ops hops
    rw [PMF.mem_support_pure_iff] at hops
    subst hops
    exact ⟨by decide, fun o ho => by revert o ho; decide⟩
  obtain ⟨D_det, _, hgood, hcost⟩ :=
    randDictScheme.exists_det_indexedScheme_le_expectedSeqProbes
      validInfDictOps 2 correctSeqs hS GoodInfDict
      (fun ops _ tr htr => randDictScheme_zero_error ops htr) hardDist hν
  exact ⟨D_det, hgood, hcost⟩

/-- Random-initial-memory / coin-free-step averaging specialization
(`exists_det_scheme_le_expectedSeqProbes`): uniformly random initial memory `init` paired with the
coin-free `counterIndexed` operations (observed only by probing cells). Regardless of the random
initial memory, writing `2` to cell `0` and querying cell `0` always returns `2`. -/
noncomputable def randomInitScheme : Randomized.Scheme CounterOp CounterResult 3 2 where
  init := Probability.PMF.uniformOfFintype (Mem 3 2)
  step o := RandProbeTree.ofProbeTree (counterIndexed.step 0 o)

def GoodWriteRead (ops : List CounterOp) (tr : List (Sigma CounterResult)) : Prop :=
  ops = [.insert 0 2, .query 0] → tr = [⟨.insert 0 2, PUnit.unit⟩, ⟨.query 0, 2⟩]

theorem exists_det_scheme_randomInit_test :
    let seq : List CounterOp := [.insert 0 2, .query 0]
    ∃ D_det : Scheme CounterOp CounterResult 3 2,
      (∀ ops ∈ ({seq} : Set (List CounterOp)), GoodWriteRead ops (D_det.runSeq ops).1) ∧
      (∑' ops, (PMF.pure seq : PMF (List CounterOp)) ops * (D_det.seqProbes ops : ℝ≥0∞)) ≤
        ∑' ops, (PMF.pure seq : PMF (List CounterOp)) ops *
          randomInitScheme.expectedSeqProbes ops := by
  intro seq
  have hstep : ∀ o, (randomInitScheme.step o).IsCoinFree :=
    fun _ => RandProbeTree.isCoinFree_ofProbeTree _
  have hcorr : ∀ ops ∈ ({seq} : Set (List CounterOp)),
      ∀ tr ∈ ((randomInitScheme.runSeq ops).map Prod.fst).support, GoodWriteRead ops tr := by
    intro ops hops tr htr
    rw [Set.mem_singleton_iff] at hops
    subst hops
    rw [randomInitScheme.runSeq_eq_schemeLaw_bind hstep] at htr
    simp only [Randomized.Scheme.schemeLaw, PMF.mem_support_map_iff,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at htr
    obtain ⟨_, ⟨_, ⟨m₀, _, rfl⟩, rfl⟩, rfl⟩ := htr
    intro _
    simp only [Scheme.runSeq, IndexedScheme.runSeq, Scheme.toIndexed,
      randomInitScheme, counterIndexed, seq]
    congr 2
  obtain ⟨D_det, _, hgood, hcost⟩ :=
    randomInitScheme.exists_det_scheme_le_expectedSeqProbes
      hstep {seq} GoodWriteRead hcorr (PMF.pure seq)
  exact ⟨D_det, hgood, hcost⟩

end CslibFrontierTests.CellProbe
