/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.CellProbe.Defs
public import Complexity.Languages.Probabilistic.Oracle.CoinFixing
import Complexity.Probability.Minimax
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Expect

/-!
# Randomized Cell-Probe Trees, Schemes, and Yao Averaging

This file extends `Cslib.CellProbe` with internal-coin randomized cell-probe trees
(`RandProbeTree S w α := ProbOracleComp (@ProbeOp.Result S w) α`), randomized cell-probe schemes
(`Randomized.Scheme`), and Yao averaging (the easy direction of Yao's principle) for zero-error
randomized schemes [Yao1977; Yao1981; Miltersen1999].

Private coin draws (`unifSpec`) incur `0` cell probes, while each cell read or write incurs `1`
probe. Because every `ProbeOp.Result q` is finite (`Fin (2 ^ w)` or `PUnit`),
`ProbOracleComp.coinLaw` and `ProbOracleComp.fixCoins` represent any `RandProbeTree` as a finite
mixture of deterministic `ProbeTree`s (`RandProbeTree.run_eq_coinLaw_bind_fixCoins`). Averaging
over coin-fixed deterministic schemes via
`Cslib.Probability.PMF.exists_mem_support_tsum_mul_le_tsum_mul` and
`Cslib.Probability.PMF.exists_mem_support_tsum_mul_le` (the easy direction of Yao's principle,
not a minimax theorem) converts any **zero-error** randomized scheme `P` into a deterministic
`IndexedScheme` (or a time-invariant `CellProbe.Scheme` when per-operation trees draw no private
coins) that preserves sequence correctness across an arbitrary set `correctSeqs` of oblivious
operation sequences while incurring at most `P`'s expected probes under a fixed input sequence
distribution `hardDist`. Bounded-error (Monte Carlo) schemes and adaptive sequence adversaries are
not covered by these zero-error oblivious-sequence reductions, and deterministic lower bounds
paired with `exists_det_indexedScheme_le_expectedSeqProbes` must hold against `IndexedScheme`
(whose `step` receives the operation index `t : ℕ` for free).

## Main definitions

* `Cslib.CellProbe.RandProbeTree`, `Cslib.CellProbe.RandProbeTree.read`,
  `Cslib.CellProbe.RandProbeTree.write`, `Cslib.CellProbe.RandProbeTree.sample`,
  `Cslib.CellProbe.RandProbeTree.ofProbeTree`, `Cslib.CellProbe.RandProbeTree.run`,
  `Cslib.CellProbe.RandProbeTree.expectedProbes`, `Cslib.CellProbe.RandProbeTree.IsCoinFree`,
  `Cslib.CellProbe.RandProbeTree.toProbeTree`, `Cslib.CellProbe.RandProbeTree.padCells`:
  adaptive cell-probe trees with private finite-uniform coins, joint `(output, postMem, probes)`
  semantics, `ℝ≥0∞` expected probes, coin-free projection, and cell padding.
* `Cslib.CellProbe.Randomized.Scheme`, `Cslib.CellProbe.Randomized.Scheme.ofDeterministic`,
  `Cslib.CellProbe.Randomized.Scheme.runFrom`, `Cslib.CellProbe.Randomized.Scheme.runSeq`,
  `Cslib.CellProbe.Randomized.Scheme.expectedProbesFrom`,
  `Cslib.CellProbe.Randomized.Scheme.expectedSeqProbes`,
  `Cslib.CellProbe.Randomized.Scheme.padCells`: randomized cell-probe schemes with initial memory
  distribution `init : PMF (Mem cells w)` and per-operation `RandProbeTree`s.
* `Cslib.CellProbe.Randomized.Scheme.fixIndexedScheme`,
  `Cslib.CellProbe.Randomized.Scheme.indexedSchemeLaw`,
  `Cslib.CellProbe.Randomized.Scheme.schemeLaw`: coin-fixed deterministic scheme laws over a finite
  `horizon` and finite operation alphabet `opsAlphabet : Finset Op` (or coin-free steps).

## Main results

* `Cslib.CellProbe.RandProbeTree.run_eq_coinLaw_bind_fixCoins`,
  `Cslib.CellProbe.RandProbeTree.expectedProbes_eq_coinLaw_tsum`: fixing private coins of a
  `RandProbeTree` reproduces its exact joint `(output, postMem, probes)` law and expected probes.
* `Cslib.CellProbe.Randomized.Scheme.runSeq_eq_indexedSchemeLaw_bind`,
  `Cslib.CellProbe.Randomized.Scheme.expectedSeqProbes_eq_indexedSchemeLaw_tsum`: multi-step
  coin-fixing equivalence over `Fin horizon × ↥opsAlphabet`.
* `Cslib.CellProbe.Randomized.Scheme.exists_det_indexedScheme_le_expectedSeqProbes`,
  `Cslib.CellProbe.Randomized.Scheme.exists_det_indexedScheme_tsum_mul_le`,
  `Cslib.CellProbe.Randomized.Scheme.exists_det_indexedScheme_le_expectedSeqProbes_of_fintype`:
  Yao averaging (easy direction) for zero-error schemes against oblivious operation sequences,
  producing a deterministic `IndexedScheme` in the coin-law support that satisfies
  `Good ops (D_det.runSeq ops).1` for all `ops ∈ correctSeqs` and incurs at most the expected
  probes of `P` over `hardDist`.
* `Cslib.CellProbe.Randomized.Scheme.exists_det_scheme_le_expectedSeqProbes`:
  random-initial-memory / coin-free-step specialization producing a time-invariant deterministic
  `CellProbe.Scheme` without needing `opsAlphabet` or `horizon` (where randomness lives only in
  `init` and operations observe it only by probing cells).

## References

* [A. C.-C. Yao, *Probabilistic Computations: Toward a Unified Measure of Complexity*][Yao1977]
* [A. C.-C. Yao, *Should Tables Be Sorted?*][Yao1981]
* [P. B. Miltersen, *Cell Probe Complexity — a Survey*][Miltersen1999]
-/

public section

namespace Cslib.CellProbe

open scoped ENNReal

universe u

/-! ### Internal-coin randomized cell-probe trees -/

/-- Adaptive cell-probe tree on `S` cells of `w`-bit words with private finite-uniform coin draws
(`unifSpec`), defined as `ProbOracleComp (@ProbeOp.Result S w) α`. -/
abbrev RandProbeTree (S w : ℕ) (α : Type) : Type :=
  ProbOracleComp (@ProbeOp.Result S w) α

namespace RandProbeTree

variable {S S' w : ℕ} {α β : Type}

/-- Read cell `i : Fin S` (`1` probe). -/
@[expose] def read (i : Fin S) : RandProbeTree S w (Fin (2 ^ w)) :=
  ProbOracleComp.query (ProbeOp.read (w := w) i)

/-- Write `v : Fin (2 ^ w)` to cell `i : Fin S` (`1` probe). -/
@[expose] def write (i : Fin S) (v : Fin (2 ^ w)) : RandProbeTree S w PUnit :=
  ProbOracleComp.query (ProbeOp.write i v)

/-- Embed a closed `ProbComp` sampler (`0` probes). -/
@[expose] def sample (p : ProbComp α) : RandProbeTree S w α :=
  ProbOracleComp.sample p

/-- Embed a deterministic `ProbeTree` into `RandProbeTree` with zero coin draws. -/
@[expose] def ofProbeTree (t : ProbeTree S w α) : RandProbeTree S w α :=
  OracleComp.interpret ProbOracleComp.query t

/-- Joint distribution of `((result, postMem), probeCount)` executed from pre-memory `m`, charging
`0` probes for private coin samples (`.inl n`) and `1` probe per cell read/write (`.inr q`). -/
@[expose] noncomputable def run : RandProbeTree S w α → Mem S w → PMF ((α × Mem S w) × ℕ)
  | .pure a, m => PMF.pure ((a, m), 0)
  | .liftBind (.inl n) k, m =>
      (ProbComp.unifOracle n).bind fun c => run (k c) m
  | .liftBind (.inr (.read i)) k, m =>
      (run (k (m i)) m).map fun (out, p) => (out, p + 1)
  | .liftBind (.inr (.write i v)) k, m =>
      (run (k PUnit.unit) (Function.update m i v)).map fun (out, p) => (out, p + 1)

/-- Expected number of cell probes executed from pre-memory `m`, valued in `ℝ≥0∞`. -/
@[expose] noncomputable def expectedProbes (t : RandProbeTree S w α) (m : Mem S w) : ℝ≥0∞ :=
  ∑' z, (t.run m) z * (z.2 : ℝ≥0∞)

@[simp]
theorem run_pure (a : α) (m : Mem S w) :
    run (pure a : RandProbeTree S w α) m = PMF.pure ((a, m), 0) :=
  rfl

@[simp]
theorem run_read (i : Fin S) (m : Mem S w) :
    run (read i : RandProbeTree S w _) m = PMF.pure ((m i, m), 1) := by
  change (PMF.pure ((m i, m), 0)).map (fun (out, p) => (out, p + 1)) = _
  simp

@[simp]
theorem run_write (i : Fin S) (v : Fin (2 ^ w)) (m : Mem S w) :
    run (write i v) m = PMF.pure ((PUnit.unit, Function.update m i v), 1) := by
  change (PMF.pure ((PUnit.unit, Function.update m i v), 0)).map (fun (out, p) => (out, p + 1)) = _
  simp

@[simp]
theorem run_bind (t : RandProbeTree S w α) (k : α → RandProbeTree S w β) (m : Mem S w) :
    run (t >>= k) m =
      (t.run m).bind fun ((a, m'), p₁) =>
        ((k a).run m').map fun (out, p₂) => (out, p₁ + p₂) := by
  induction t generalizing m with
  | pure a =>
    change (k a).run m = (PMF.pure ((a, m), 0)).bind _
    rw [PMF.pure_bind]
    simp only [zero_add]
    exact (PMF.map_id _).symm
  | liftBind q cont ih =>
    rcases q with n | ⟨i⟩ | ⟨i, v⟩
    · change (ProbComp.unifOracle n).bind (fun c => run (cont c >>= k) m) =
        ((ProbComp.unifOracle n).bind fun c => run (cont c) m).bind _
      simp only [ih, PMF.bind_bind]
    · change (run (cont (m i) >>= k) m).map (fun (out, p) => (out, p + 1)) =
        ((run (cont (m i)) m).map (fun (out, p) => (out, p + 1))).bind _
      rw [ih (m i) m, PMF.map_bind, PMF.bind_map]
      refine congrArg (PMF.bind (run (cont (m i)) m)) (funext fun ((a, m'), p₁) => ?_)
      simp only [Function.comp_def, PMF.map_comp]
      refine congrArg (fun f => PMF.map f ((k a).run m')) (funext fun (out, p₂) => ?_)
      exact Prod.ext rfl (by omega)
    · change (run (cont PUnit.unit >>= k) (Function.update m i v)).map
          (fun (out, p) => (out, p + 1)) =
        ((run (cont PUnit.unit) (Function.update m i v)).map
          (fun (out, p) => (out, p + 1))).bind _
      rw [ih PUnit.unit (Function.update m i v), PMF.map_bind, PMF.bind_map]
      refine congrArg (PMF.bind (run (cont PUnit.unit) (Function.update m i v)))
        (funext fun ((a, m'), p₁) => ?_)
      simp only [Function.comp_def, PMF.map_comp]
      refine congrArg (fun f => PMF.map f ((k a).run m')) (funext fun (out, p₂) => ?_)
      exact Prod.ext rfl (by omega)

@[simp]
theorem run_map (f : α → β) (t : RandProbeTree S w α) (m : Mem S w) :
    run (f <$> t) m = (t.run m).map fun ((a, m'), p) => ((f a, m'), p) := by
  rw [← bind_pure_comp, run_bind, ← PMF.bind_pure_comp]
  refine congrArg (PMF.bind (t.run m)) (funext fun ((a, m'), p) => ?_)
  simp [PMF.pure_map]

@[simp]
theorem run_sample (p : ProbComp α) (m : Mem S w) :
    run (sample p : RandProbeTree S w α) m = (ProbComp.eval p).map fun a => ((a, m), 0) := by
  induction p with
  | pure a => simp [sample]
  | liftBind n cont ih =>
    change (ProbComp.unifOracle n).bind (fun c => run (sample (cont c)) m) =
      ((ProbComp.unifOracle n).bind fun c => ProbComp.eval (cont c)).map _
    simp only [ih, PMF.map_bind]

@[simp]
theorem run_ofProbeTree (t : ProbeTree S w α) (m : Mem S w) :
    (ofProbeTree t).run m = PMF.pure (t.run m, t.probes m) := by
  induction t generalizing m with
  | pure a => rfl
  | liftBind q cont ih =>
    cases q with
    | read i =>
      change ((ofProbeTree (cont (m i))).run m).map (fun (out, p) => (out, p + 1)) = _
      rw [ih (m i) m, PMF.pure_map]
      exact congrArg PMF.pure (Prod.ext rfl (Nat.add_comm _ 1))
    | write i v =>
      change ((ofProbeTree (cont PUnit.unit)).run (Function.update m i v)).map
        (fun (out, p) => (out, p + 1)) = _
      rw [ih PUnit.unit (Function.update m i v), PMF.pure_map]
      exact congrArg PMF.pure (Prod.ext rfl (Nat.add_comm _ 1))

private theorem tsum_pure_snd {γ : Type*} (x : γ × ℕ) :
    (∑' z : γ × ℕ, (PMF.pure x) z * (z.2 : ℝ≥0∞)) = (x.2 : ℝ≥0∞) := by
  rw [tsum_eq_single x]
  · simp
  · intro z hz
    simp [PMF.pure_apply, hz]

@[simp]
theorem expectedProbes_pure (a : α) (m : Mem S w) :
    (pure a : RandProbeTree S w α).expectedProbes m = 0 := by
  simp [expectedProbes]

@[simp]
theorem expectedProbes_read (i : Fin S) (m : Mem S w) :
    (read i : RandProbeTree S w _).expectedProbes m = 1 := by
  rw [expectedProbes, run_read, tsum_pure_snd]
  simp

@[simp]
theorem expectedProbes_write (i : Fin S) (v : Fin (2 ^ w)) (m : Mem S w) :
    (write i v).expectedProbes m = 1 := by
  rw [expectedProbes, run_write, tsum_pure_snd]
  simp

@[simp]
theorem expectedProbes_sample (p : ProbComp α) (m : Mem S w) :
    (sample p : RandProbeTree S w α).expectedProbes m = 0 := by
  rw [expectedProbes, run_sample, Probability.PMF.tsum_map_mul]
  simp

@[simp]
theorem expectedProbes_ofProbeTree (t : ProbeTree S w α) (m : Mem S w) :
    (ofProbeTree t).expectedProbes m = (t.probes m : ℝ≥0∞) := by
  rw [expectedProbes, run_ofProbeTree, tsum_pure_snd]

@[simp]
theorem expectedProbes_map (f : α → β) (t : RandProbeTree S w α) (m : Mem S w) :
    (f <$> t).expectedProbes m = t.expectedProbes m := by
  rw [expectedProbes, run_map, Probability.PMF.tsum_map_mul]
  rfl

theorem expectedProbes_bind (t : RandProbeTree S w α) (k : α → RandProbeTree S w β)
    (m : Mem S w) :
    (t >>= k).expectedProbes m =
      t.expectedProbes m +
        ∑' am : α × Mem S w,
          ((t.run m).map Prod.fst) am * (k am.1).expectedProbes am.2 := by
  rw [expectedProbes, run_bind, Probability.PMF.tsum_bind_mul, Probability.PMF.tsum_map_mul]
  have hterm : ∀ z : (α × Mem S w) × ℕ,
      (t.run m) z *
        (∑' z₂ : (β × Mem S w) × ℕ,
          (((k z.1.1).run z.1.2).map (fun (out, p₂) => (out, z.2 + p₂))) z₂ * (z₂.2 : ℝ≥0∞)) =
      (t.run m) z * (z.2 : ℝ≥0∞) +
        (t.run m) z * (k z.1.1).expectedProbes z.1.2 := by
    rintro ⟨⟨a, m'⟩, p₁⟩
    rw [Probability.PMF.tsum_map_mul]
    simp only [Nat.cast_add, mul_add, tsum_add, ENNReal.tsum_mul_right,
      ((k a).run m').tsum_coe, one_mul, expectedProbes]
  simp only [hterm, tsum_add]
  rfl

/-! ### Coin-fixing, coin-free projection, and cell padding for `RandProbeTree` -/

/-- Fixing private coins `ω ← ProbOracleComp.coinLaw t` reproduces the exact joint
`((result, postMem), probes)` distribution of `t.run m`. -/
theorem run_eq_coinLaw_bind_fixCoins (t : RandProbeTree S w α) (m : Mem S w) :
    t.run m = (ProbOracleComp.coinLaw t).bind fun ω =>
      PMF.pure
        (ProbeTree.run (ProbOracleComp.fixCoins t ω) m,
         ProbeTree.probes (ProbOracleComp.fixCoins t ω) m) := by
  induction t generalizing m with
  | pure a =>
    have hpure : ProbOracleComp.coinLaw (.pure a : RandProbeTree S w α) = PMF.pure PUnit.unit :=
      ProbOracleComp.coinLaw_pure a
    dsimp only [ProbOracleComp.Coins, ProbOracleComp.fixCoins] at hpure ⊢
    rw [hpure]
    simp
  | liftBind q cont ih =>
    rcases q with n | ⟨i⟩ | ⟨i, v⟩
    · dsimp only [ProbOracleComp.Coins, ProbOracleComp.fixCoins]
      rw [ProbOracleComp.coinLaw_liftBind_inl]
      change (ProbComp.unifOracle n).bind (fun c => run (cont c) m) = _
      simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
      refine congrArg (PMF.bind (ProbComp.unifOracle n)) (funext fun c => ?_)
      exact ih c m
    · dsimp only [ProbOracleComp.Coins, ProbOracleComp.fixCoins]
      rw [ProbOracleComp.coinLaw_liftBind_inr]
      change (run (cont (m i)) m).map (fun (out, p) => (out, p + 1)) = _
      have hstep : ∀ f : ∀ y : Fin (2 ^ w), ProbOracleComp.Coins (cont y),
          (ProbeTree.run
            (PFunctor.FreeM.liftBind (ProbeOp.read i)
              fun y => ProbOracleComp.fixCoins (cont y) (f y)) m,
           ProbeTree.probes
            (PFunctor.FreeM.liftBind (ProbeOp.read i)
              fun y => ProbOracleComp.fixCoins (cont y) (f y)) m) =
          (ProbeTree.run (ProbOracleComp.fixCoins (cont (m i)) (f (m i))) m,
           ProbeTree.probes (ProbOracleComp.fixCoins (cont (m i)) (f (m i))) m + 1) :=
        fun _ => Prod.ext rfl (Nat.add_comm 1 _)
      simp_rw [hstep]
      have heval :=
        Probability.PMF.pi_map_eval (fun y : Fin (2 ^ w) => ProbOracleComp.coinLaw (cont y)) (m i)
      have hpull :
          (Probability.PMF.pi fun y => ProbOracleComp.coinLaw (cont y)).bind
            (fun f => PMF.pure
              (ProbeTree.run (ProbOracleComp.fixCoins (cont (m i)) (f (m i))) m,
               ProbeTree.probes (ProbOracleComp.fixCoins (cont (m i)) (f (m i))) m + 1)) =
          (ProbOracleComp.coinLaw (cont (m i))).bind
            (fun ω => PMF.pure
              (ProbeTree.run (ProbOracleComp.fixCoins (cont (m i)) ω) m,
               ProbeTree.probes (ProbOracleComp.fixCoins (cont (m i)) ω) m + 1)) := by
        rw [← heval, PMF.bind_map]
        rfl
      rw [hpull, ih (m i) m, PMF.map_bind]
      simp only [PMF.pure_map]
    · dsimp only [ProbOracleComp.Coins, ProbOracleComp.fixCoins]
      rw [ProbOracleComp.coinLaw_liftBind_inr]
      set m' := Function.update m i v
      change (run (cont PUnit.unit) m').map (fun (out, p) => (out, p + 1)) = _
      have hstep : ∀ f : ∀ y : PUnit, ProbOracleComp.Coins (cont y),
          (ProbeTree.run
            (PFunctor.FreeM.liftBind (ProbeOp.write i v)
              fun y => ProbOracleComp.fixCoins (cont y) (f y)) m,
           ProbeTree.probes
            (PFunctor.FreeM.liftBind (ProbeOp.write i v)
              fun y => ProbOracleComp.fixCoins (cont y) (f y)) m) =
          (ProbeTree.run (ProbOracleComp.fixCoins (cont PUnit.unit) (f PUnit.unit)) m',
           ProbeTree.probes (ProbOracleComp.fixCoins (cont PUnit.unit) (f PUnit.unit)) m' + 1) :=
        fun _ => Prod.ext rfl (Nat.add_comm 1 _)
      simp_rw [hstep]
      have heval :=
        Probability.PMF.pi_map_eval (fun y : PUnit => ProbOracleComp.coinLaw (cont y)) PUnit.unit
      have hpull :
          (Probability.PMF.pi fun y => ProbOracleComp.coinLaw (cont y)).bind
            (fun f => PMF.pure
              (ProbeTree.run (ProbOracleComp.fixCoins (cont PUnit.unit) (f PUnit.unit)) m',
               ProbeTree.probes (ProbOracleComp.fixCoins (cont PUnit.unit) (f PUnit.unit)) m' +
                 1)) =
          (ProbOracleComp.coinLaw (cont PUnit.unit)).bind
            (fun ω => PMF.pure
              (ProbeTree.run (ProbOracleComp.fixCoins (cont PUnit.unit) ω) m',
               ProbeTree.probes (ProbOracleComp.fixCoins (cont PUnit.unit) ω) m' + 1)) := by
        rw [← heval, PMF.bind_map]
        rfl
      rw [hpull, ih PUnit.unit m', PMF.map_bind]
      simp only [PMF.pure_map]

/-- Expected probe count of `t` from `m` equals the `coinLaw t`-average of
`ProbeTree.probes (fixCoins t ω) m`. -/
theorem expectedProbes_eq_coinLaw_tsum (t : RandProbeTree S w α) (m : Mem S w) :
    t.expectedProbes m =
      ∑' ω, ProbOracleComp.coinLaw t ω *
        (ProbeTree.probes (ProbOracleComp.fixCoins t ω) m : ℝ≥0∞) := by
  rw [expectedProbes, run_eq_coinLaw_bind_fixCoins, Probability.PMF.tsum_bind_mul]
  exact tsum_congr fun _ => congrArg (_ * ·) (tsum_pure_snd _)

/-- Predicate that a `RandProbeTree` makes no private coin draws (`Sum.inl`). -/
@[expose] def IsCoinFree : RandProbeTree S w α → Prop
  | .pure _ => True
  | .liftBind (.inl _) _ => False
  | .liftBind (.inr _) k => ∀ y, IsCoinFree (k y)

/-- Project a coin-free `RandProbeTree` to a deterministic `ProbeTree`. -/
@[expose] def toProbeTree : (t : RandProbeTree S w α) → t.IsCoinFree → ProbeTree S w α
  | .pure a, _ => .pure a
  | .liftBind (.inl _) _, h => False.elim h
  | .liftBind (.inr q) k, h => .liftBind q fun y => toProbeTree (k y) (h y)

@[simp]
theorem isCoinFree_pure (a : α) : (pure a : RandProbeTree S w α).IsCoinFree :=
  trivial

@[simp]
theorem isCoinFree_read (i : Fin S) : (read i : RandProbeTree S w _).IsCoinFree :=
  fun _ => trivial

@[simp]
theorem isCoinFree_write (i : Fin S) (v : Fin (2 ^ w)) : (write i v).IsCoinFree :=
  fun _ => trivial

@[simp]
theorem isCoinFree_ofProbeTree (t : ProbeTree S w α) : (ofProbeTree t).IsCoinFree := by
  induction t with
  | pure _ => trivial
  | liftBind _ _ ih => exact ih

@[simp]
theorem toProbeTree_ofProbeTree (t : ProbeTree S w α) :
    toProbeTree (ofProbeTree t) (isCoinFree_ofProbeTree t) = t := by
  induction t with
  | pure _ => rfl
  | liftBind q cont ih =>
    change PFunctor.FreeM.liftBind q
      (fun y => toProbeTree (ofProbeTree (cont y)) (isCoinFree_ofProbeTree (cont y))) = _
    exact congrArg (PFunctor.FreeM.liftBind q) (funext ih)

theorem run_eq_pure_of_isCoinFree (t : RandProbeTree S w α) (ht : t.IsCoinFree) (m : Mem S w) :
    t.run m = PMF.pure ((toProbeTree t ht).run m, (toProbeTree t ht).probes m) := by
  induction t generalizing m with
  | pure a => rfl
  | liftBind q cont ih =>
    rcases q with n | ⟨i⟩ | ⟨i, v⟩
    · exact False.elim ht
    · change (run (cont (m i)) m).map (fun (out, p) => (out, p + 1)) = _
      rw [ih (m i) (ht (m i)) m, PMF.pure_map]
      exact congrArg PMF.pure (Prod.ext rfl (Nat.add_comm _ 1))
    · change (run (cont PUnit.unit) (Function.update m i v)).map (fun (out, p) => (out, p + 1)) = _
      rw [ih PUnit.unit (ht PUnit.unit) (Function.update m i v), PMF.pure_map]
      exact congrArg PMF.pure (Prod.ext rfl (Nat.add_comm _ 1))

theorem expectedProbes_eq_of_isCoinFree (t : RandProbeTree S w α) (ht : t.IsCoinFree)
    (m : Mem S w) :
    t.expectedProbes m = ((toProbeTree t ht).probes m : ℝ≥0∞) := by
  rw [expectedProbes, run_eq_pure_of_isCoinFree t ht m, tsum_pure_snd]

/-- Lift a `RandProbeTree S w α` to `S'` cells (`S ≤ S'`) via `Fin.castLE`. -/
@[expose] def padCells (h : S ≤ S') : RandProbeTree S w α → RandProbeTree S' w α
  | .pure a => .pure a
  | .liftBind (.inl n) k => .liftBind (.inl n) fun c => padCells h (k c)
  | .liftBind (.inr (.read i)) k =>
      .liftBind (.inr (.read (Fin.castLE h i))) fun v => padCells h (k v)
  | .liftBind (.inr (.write i v)) k =>
      .liftBind (.inr (.write (Fin.castLE h i) v)) fun u => padCells h (k u)

theorem run_padCells (h : S ≤ S') (t : RandProbeTree S w α) (m : Mem S w) :
    (t.padCells h).run (padMem h m) =
      (t.run m).map fun ((a, m₁), p) => ((a, padMem h m₁), p) := by
  induction t generalizing m with
  | pure a => simp [padCells]
  | liftBind q cont ih =>
    rcases q with n | ⟨i⟩ | ⟨i, v⟩
    · change (ProbComp.unifOracle n).bind (fun c => run (padCells h (cont c)) (padMem h m)) =
        ((ProbComp.unifOracle n).bind fun c => run (cont c) m).map _
      simp only [ih, PMF.map_bind]
    · change (run (padCells h (cont (padMem h m (Fin.castLE h i)))) (padMem h m)).map
          (fun (out, p) => (out, p + 1)) =
        ((run (cont (m i)) m).map (fun (out, p) => (out, p + 1))).map _
      rw [padMem_castLE, ih (m i) m, PMF.map_comp, PMF.map_comp]
      rfl
    · change (run (padCells h (cont PUnit.unit))
          (Function.update (padMem h m) (Fin.castLE h i) v)).map (fun (out, p) => (out, p + 1)) =
        ((run (cont PUnit.unit) (Function.update m i v)).map (fun (out, p) => (out, p + 1))).map _
      rw [padMem_update, ih PUnit.unit (Function.update m i v), PMF.map_comp, PMF.map_comp]
      rfl

@[simp]
theorem expectedProbes_padCells (h : S ≤ S') (t : RandProbeTree S w α) (m : Mem S w) :
    (t.padCells h).expectedProbes (padMem h m) = t.expectedProbes m := by
  rw [expectedProbes, run_padCells, Probability.PMF.tsum_map_mul]
  rfl

end RandProbeTree

/-! ### Randomized cell-probe schemes and Yao averaging for zero-error schemes -/

namespace Randomized

/-- Randomized cell-probe scheme with `cells` cells of `w`-bit words, consisting of an initial
memory distribution `init : PMF (Mem cells w)` (`0` probes) and per-operation internal-coin probe
trees `step : (o : Op) → RandProbeTree cells w (Result o)`. -/
structure Scheme (Op : Type u) (Result : Op → Type) (cells w : ℕ) where
  /-- Initial cell memory distribution (`0` probes; persistent state lives in `cells` words). -/
  init : PMF (Mem cells w)
  /-- Adaptive randomized cell-probe decision tree executed for each operation `o : Op`. -/
  step : (o : Op) → RandProbeTree cells w (Result o)

namespace Scheme

variable {Op : Type u} {Result : Op → Type} {cells cells' w : ℕ}

/-- Embed a deterministic `CellProbe.Scheme` as a `Randomized.Scheme`. -/
@[expose] noncomputable def ofDeterministic (D : CellProbe.Scheme Op Result cells w) :
    Scheme Op Result cells w where
  init := PMF.pure D.init
  step o := RandProbeTree.ofProbeTree (D.step o)

/-- Joint distribution of `((transcript, postMem), probeCount)` executed across `ops` starting from
pre-memory `m`. -/
@[expose] noncomputable def runFrom (P : Scheme Op Result cells w) :
    Mem cells w → List Op → PMF ((List (Sigma Result) × Mem cells w) × ℕ)
  | m, [] => PMF.pure (([], m), 0)
  | m, o :: ops =>
      ((P.step o).run m).bind fun ((a, m'), p₁) =>
        (P.runFrom m' ops).map fun ((tr, m''), p₂) => ((⟨o, a⟩ :: tr, m''), p₁ + p₂)

/-- Joint distribution of `(transcript, totalProbes)` across `ops` starting from `P.init`. -/
@[expose] noncomputable def runSeq (P : Scheme Op Result cells w) (ops : List Op) :
    PMF (List (Sigma Result) × ℕ) :=
  P.init.bind fun m₀ => (P.runFrom m₀ ops).map fun ((tr, _), p) => (tr, p)

/-- Expected total cell probes across `ops` starting from pre-memory `m`, valued in `ℝ≥0∞`. -/
@[expose] noncomputable def expectedProbesFrom (P : Scheme Op Result cells w) (m : Mem cells w)
    (ops : List Op) : ℝ≥0∞ :=
  ∑' z, (P.runFrom m ops) z * (z.2 : ℝ≥0∞)

/-- Expected total cell probes across `ops` starting from `P.init`, valued in `ℝ≥0∞`. -/
@[expose] noncomputable def expectedSeqProbes (P : Scheme Op Result cells w) (ops : List Op) :
    ℝ≥0∞ :=
  ∑' z, (P.runSeq ops) z * (z.2 : ℝ≥0∞)

@[simp]
theorem runFrom_nil (P : Scheme Op Result cells w) (m : Mem cells w) :
    P.runFrom m [] = PMF.pure (([], m), 0) :=
  rfl

@[simp]
theorem runFrom_cons (P : Scheme Op Result cells w) (m : Mem cells w) (o : Op) (ops : List Op) :
    P.runFrom m (o :: ops) =
      ((P.step o).run m).bind fun ((a, m'), p₁) =>
        (P.runFrom m' ops).map fun ((tr, m''), p₂) => ((⟨o, a⟩ :: tr, m''), p₁ + p₂) :=
  rfl

@[simp]
theorem runSeq_nil (P : Scheme Op Result cells w) :
    P.runSeq [] = PMF.pure ([], 0) := by
  simp [runSeq]

@[simp]
theorem expectedSeqProbes_nil (P : Scheme Op Result cells w) :
    P.expectedSeqProbes [] = 0 := by
  simp [expectedSeqProbes]

theorem expectedSeqProbes_eq_init_tsum (P : Scheme Op Result cells w) (ops : List Op) :
    P.expectedSeqProbes ops = ∑' m₀, P.init m₀ * P.expectedProbesFrom m₀ ops := by
  rw [expectedSeqProbes, runSeq, Probability.PMF.tsum_bind_mul]
  refine tsum_congr fun m₀ => congrArg (P.init m₀ * ·) ?_
  rw [Probability.PMF.tsum_map_mul]
  refine tsum_congr fun ((_, _), _) => rfl

/-- Pad a `Randomized.Scheme` from `cells` cells to `cells'` cells (`cells ≤ cells'`). -/
@[expose] noncomputable def padCells (h : cells ≤ cells') (P : Scheme Op Result cells w) :
    Scheme Op Result cells' w where
  init := P.init.map (padMem h)
  step o := (P.step o).padCells h

@[simp]
theorem padCells_step (h : cells ≤ cells') (P : Scheme Op Result cells w) (o : Op) :
    (P.padCells h).step o = (P.step o).padCells h :=
  rfl

theorem runFrom_padCells (h : cells ≤ cells') (P : Scheme Op Result cells w) (m : Mem cells w)
    (ops : List Op) :
    (P.padCells h).runFrom (padMem h m) ops =
      (P.runFrom m ops).map fun ((tr, m₁), p) => ((tr, padMem h m₁), p) := by
  induction ops generalizing m with
  | nil => simp [runFrom]
  | cons o rest ih =>
    simp only [runFrom_cons, padCells_step, RandProbeTree.run_padCells, PMF.bind_map,
      PMF.map_bind]
    refine congrArg (PMF.bind ((P.step o).run m)) (funext fun ((a, m'), p₁) => ?_)
    simp only [Function.comp_def, ih m', PMF.map_comp]

@[simp]
theorem runSeq_padCells (h : cells ≤ cells') (P : Scheme Op Result cells w) (ops : List Op) :
    (P.padCells h).runSeq ops = P.runSeq ops := by
  simp only [runSeq, padCells, PMF.bind_map]
  refine congrArg (PMF.bind P.init) (funext fun m₀ => ?_)
  change ((P.padCells h).runFrom (padMem h m₀) ops).map (fun ((tr, _), p) => (tr, p)) = _
  rw [runFrom_padCells, PMF.map_comp]
  rfl

@[simp]
theorem expectedSeqProbes_padCells (h : cells ≤ cells') (P : Scheme Op Result cells w)
    (ops : List Op) :
    (P.padCells h).expectedSeqProbes ops = P.expectedSeqProbes ops := by
  simp only [expectedSeqProbes, runSeq_padCells]

/-! #### Multi-step private-coin fixing over `Fin horizon × ↥opsAlphabet` -/

/-- Fix an initial memory `m₀` and an array `Ω` of step-and-operation-indexed private coin trees
over `Fin horizon × ↥opsAlphabet` into a deterministic `IndexedScheme` (returning `pure default`
outside `horizon` or outside `opsAlphabet`). -/
@[expose] def fixIndexedScheme [DecidableEq Op] [∀ o, Inhabited (Result o)]
    (P : Scheme Op Result cells w) (horizon : ℕ) (opsAlphabet : Finset Op)
    (m₀ : Mem cells w)
    (Ω : ∀ idx : Fin horizon × ↥opsAlphabet, ProbOracleComp.Coins (P.step idx.2.1)) :
    IndexedScheme Op Result cells w where
  init := m₀
  step t o :=
    if ht : t < horizon then
      if ho : o ∈ opsAlphabet then
        ProbOracleComp.fixCoins (P.step o) (Ω (⟨t, ht⟩, ⟨o, ho⟩))
      else
        pure default
    else
      pure default

/-- Product distribution over deterministic `IndexedScheme`s obtained by sampling `m₀ ← P.init`
and independent private coins `ProbOracleComp.coinLaw (P.step o)` for each `(t, o)` in
`Fin horizon × ↥opsAlphabet`. -/
@[expose] noncomputable def indexedSchemeLaw [DecidableEq Op] [∀ o, Inhabited (Result o)]
    (P : Scheme Op Result cells w) (horizon : ℕ) (opsAlphabet : Finset Op) :
    PMF (IndexedScheme Op Result cells w) :=
  P.init.bind fun m₀ =>
    (Probability.PMF.pi fun idx : Fin horizon × ↥opsAlphabet =>
      ProbOracleComp.coinLaw (P.step idx.2.1)).map
      (P.fixIndexedScheme horizon opsAlphabet m₀)

private theorem runFrom_eq_pi_bind_runInterval [DecidableEq Op] [∀ o, Inhabited (Result o)]
    (P : Scheme Op Result cells w) (horizon : ℕ) (opsAlphabet : Finset Op)
    (m₀ m : Mem cells w) (t₀ : ℕ) (ops : List Op)
    (p : ∀ idx : Fin horizon × ↥opsAlphabet, PMF (ProbOracleComp.Coins (P.step idx.2.1)))
    (hlen : t₀ + ops.length ≤ horizon)
    (halph : ∀ o ∈ ops, o ∈ opsAlphabet)
    (hfresh : ∀ (t : Fin horizon) (o : ↥opsAlphabet),
      t₀ ≤ t.1 → p (t, o) = ProbOracleComp.coinLaw (P.step o.1)) :
    (Probability.PMF.pi p).bind (fun Ω =>
      let D := P.fixIndexedScheme horizon opsAlphabet m₀ Ω
      PMF.pure (D.runInterval t₀ m ops, D.probesInterval t₀ m ops)) =
      P.runFrom m ops := by
  induction ops generalizing t₀ m p with
  | nil =>
    simp [runFrom]
  | cons o rest ih =>
    simp only [List.length_cons] at hlen
    have ht₀ : t₀ < horizon := by omega
    have ho : o ∈ opsAlphabet := halph o List.mem_cons_self
    set idx₀ : Fin horizon × ↥opsAlphabet := (⟨t₀, ht₀⟩, ⟨o, ho⟩)
    rw [← Probability.PMF.pi_bind_update p idx₀, PMF.bind_bind]
    have hp₀ : p idx₀ = ProbOracleComp.coinLaw (P.step o) :=
      hfresh ⟨t₀, ht₀⟩ ⟨o, ho⟩ le_rfl
    rw [hp₀]
    have hstep : ∀ ω₀ : ProbOracleComp.Coins (P.step o),
        (Probability.PMF.pi (Function.update p idx₀ (PMF.pure ω₀))).bind (fun Ω =>
          let D := P.fixIndexedScheme horizon opsAlphabet m₀ Ω
          PMF.pure (D.runInterval t₀ m (o :: rest), D.probesInterval t₀ m (o :: rest))) =
        let d₀ : ProbeTree cells w (Result o) := ProbOracleComp.fixCoins (P.step o) ω₀
        (P.runFrom (d₀.run m).2 rest).map fun ((tr, m''), p₂) =>
          ((⟨o, (d₀.run m).1⟩ :: tr, m''), d₀.probes m + p₂) := by
      intro ω₀
      set p' := Function.update p idx₀ (PMF.pure ω₀)
      set d₀ : ProbeTree cells w (Result o) := ProbOracleComp.fixCoins (P.step o) ω₀
      set f₀ : (List (Sigma Result) × Mem cells w) × ℕ →
          (List (Sigma Result) × Mem cells w) × ℕ :=
        fun ((tr, m''), p₂) => ((⟨o, (d₀.run m).1⟩ :: tr, m''), d₀.probes m + p₂)
      have hcongr :
          (Probability.PMF.pi p').bind (fun Ω =>
            let D := P.fixIndexedScheme horizon opsAlphabet m₀ Ω
            PMF.pure (D.runInterval t₀ m (o :: rest), D.probesInterval t₀ m (o :: rest))) =
          (Probability.PMF.pi p').bind (fun Ω =>
            let D := P.fixIndexedScheme horizon opsAlphabet m₀ Ω
            PMF.pure (f₀ (D.runInterval (t₀ + 1) (d₀.run m).2 rest,
              D.probesInterval (t₀ + 1) (d₀.run m).2 rest))) := by
        refine Probability.PMF.bind_congr_on_support (Probability.PMF.pi p') _ _ fun Ω hΩ => ?_
        have hΩ₀ : Ω idx₀ = ω₀ := by
          have hmem := (Probability.PMF.mem_support_pi_iff p' Ω).mp hΩ idx₀
          simpa only [p', Function.update_self, PMF.mem_support_pure_iff] using hmem
        have hDstep : (P.fixIndexedScheme horizon opsAlphabet m₀ Ω).step t₀ o = d₀ := by
          simp only [fixIndexedScheme, ht₀, ↓reduceDIte, ho, idx₀] at hΩ₀ ⊢
          rw [hΩ₀]
        simp only [IndexedScheme.runInterval_cons, IndexedScheme.probesInterval_cons, hDstep, f₀]
      rw [hcongr]
      have hmap :
          (Probability.PMF.pi p').bind (fun Ω =>
            let D := P.fixIndexedScheme horizon opsAlphabet m₀ Ω
            PMF.pure (f₀ (D.runInterval (t₀ + 1) (d₀.run m).2 rest,
              D.probesInterval (t₀ + 1) (d₀.run m).2 rest))) =
          ((Probability.PMF.pi p').bind (fun Ω =>
            let D := P.fixIndexedScheme horizon opsAlphabet m₀ Ω
            PMF.pure (D.runInterval (t₀ + 1) (d₀.run m).2 rest,
              D.probesInterval (t₀ + 1) (d₀.run m).2 rest))).map f₀ := by
        rw [PMF.map_bind]
        simp only [PMF.pure_map]
      rw [hmap, ih (d₀.run m).2 (t₀ + 1) p' (by omega)
        (fun o' ho' => halph o' (List.mem_cons_of_mem o ho'))]
      intro t o' ht
      have hne : (t, o') ≠ idx₀ := by
        intro heq
        have hval : t.1 = t₀ := congrArg (fun x => x.1.1) heq
        omega
      simp only [p', Function.update_of_ne hne]
      exact hfresh t o' (by omega)
    simp_rw [hstep]
    rw [runFrom_cons, RandProbeTree.run_eq_coinLaw_bind_fixCoins, PMF.bind_bind]
    refine congrArg (PMF.bind (ProbOracleComp.coinLaw (P.step o))) (funext fun ω₀ => ?_)
    simp only [PMF.pure_bind]

/-- Sampling `D ← P.indexedSchemeLaw horizon opsAlphabet` and running `D` deterministically on any
sequence `ops` of length `≤ horizon` over `opsAlphabet` reproduces the exact `(transcript, probes)`
distribution `P.runSeq ops`. -/
theorem runSeq_eq_indexedSchemeLaw_bind [DecidableEq Op] [∀ o, Inhabited (Result o)]
    (P : Scheme Op Result cells w) {horizon : ℕ} {opsAlphabet : Finset Op} {ops : List Op}
    (hlen : ops.length ≤ horizon) (halph : ∀ o ∈ ops, o ∈ opsAlphabet) :
    P.runSeq ops =
      (P.indexedSchemeLaw horizon opsAlphabet).bind fun D =>
        PMF.pure ((D.runSeq ops).1, D.seqProbes ops) := by
  simp only [runSeq, indexedSchemeLaw, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  refine congrArg (PMF.bind P.init) (funext fun m₀ => ?_)
  have hpi := P.runFrom_eq_pi_bind_runInterval horizon opsAlphabet m₀ m₀ 0 ops
    (fun idx => ProbOracleComp.coinLaw (P.step idx.2.1))
    (by omega) halph (fun _ _ _ => rfl)
  rw [← hpi, PMF.map_bind]
  congr 1
  funext Ω
  simp only [PMF.pure_map]
  rfl

/-- Expected sequence probes of `P` on `ops` equals the `indexedSchemeLaw`-average of
`D.seqProbes ops` whenever `ops.length ≤ horizon` and `∀ o ∈ ops, o ∈ opsAlphabet`. -/
theorem expectedSeqProbes_eq_indexedSchemeLaw_tsum [DecidableEq Op] [∀ o, Inhabited (Result o)]
    (P : Scheme Op Result cells w) {horizon : ℕ} {opsAlphabet : Finset Op} {ops : List Op}
    (hlen : ops.length ≤ horizon) (halph : ∀ o ∈ ops, o ∈ opsAlphabet) :
    P.expectedSeqProbes ops =
      ∑' D, (P.indexedSchemeLaw horizon opsAlphabet) D * (D.seqProbes ops : ℝ≥0∞) := by
  rw [expectedSeqProbes, P.runSeq_eq_indexedSchemeLaw_bind hlen halph,
    Probability.PMF.tsum_bind_mul]
  exact tsum_congr fun _ => congrArg (_ * ·) (RandProbeTree.tsum_pure_snd _)

private theorem good_of_mem_support_law {SchemeType : Type*}
    (P : Scheme Op Result cells w) (μ : PMF SchemeType)
    (evalSeq : SchemeType → List Op → List (Sigma Result) × ℕ)
    (correctSeqs : Set (List Op)) (Good : List Op → List (Sigma Result) → Prop)
    (hcorr : ∀ ops ∈ correctSeqs, ∀ tr ∈ ((P.runSeq ops).map Prod.fst).support, Good ops tr)
    (hlaw : ∀ ops ∈ correctSeqs, P.runSeq ops = μ.bind fun D => PMF.pure (evalSeq D ops))
    {D_det : SchemeType} (hD_mem : D_det ∈ μ.support) :
    ∀ ops ∈ correctSeqs, Good ops (evalSeq D_det ops).1 := by
  intro ops hops
  have hmap : (P.runSeq ops).map Prod.fst = μ.map (fun D => (evalSeq D ops).1) := by
    rw [hlaw ops hops, PMF.map_bind]
    simp only [PMF.pure_map]
    exact PMF.bind_pure_comp (fun D => (evalSeq D ops).1) μ
  apply hcorr ops hops
  rw [hmap, PMF.mem_support_map_iff]
  exact ⟨D_det, hD_mem, rfl⟩

/-- **Yao averaging (easy direction) for zero-error schemes (`IndexedScheme` over explicit finite
`opsAlphabet`):** Suppose `opsAlphabet : Finset Op` is a finite set of admissible operations,
`correctSeqs` is any set of oblivious operation sequences of length `≤ horizon` over `opsAlphabet`
on which **every** supported transcript of `P.runSeq ops` satisfies `Good ops` (zero-error;
bounded-error Monte Carlo schemes are not covered), and `hardDist : PMF (List Op)` is any fixed
sequence distribution supported on sequences of length `≤ horizon` over `opsAlphabet`.

Then there exists a single deterministic `D_det : IndexedScheme Op Result cells w` in the support
of `P.indexedSchemeLaw horizon opsAlphabet` that satisfies `Good ops (D_det.runSeq ops).1` for
every `ops ∈ correctSeqs` and incurs expected probes over `hardDist` at most that of `P`. -/
theorem exists_det_indexedScheme_le_expectedSeqProbes
    [DecidableEq Op] [∀ o, Inhabited (Result o)]
    (P : Scheme Op Result cells w)
    (opsAlphabet : Finset Op) (horizon : ℕ)
    (correctSeqs : Set (List Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs, ops.length ≤ horizon ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (Good : List Op → List (Sigma Result) → Prop)
    (hcorr : ∀ ops ∈ correctSeqs, ∀ tr ∈ ((P.runSeq ops).map Prod.fst).support, Good ops tr)
    (hardDist : PMF (List Op))
    (hhardDist : ∀ ops ∈ hardDist.support, ops.length ≤ horizon ∧ ∀ o ∈ ops, o ∈ opsAlphabet) :
    ∃ D_det ∈ (P.indexedSchemeLaw horizon opsAlphabet).support,
      (∀ ops ∈ correctSeqs, Good ops (D_det.runSeq ops).1) ∧
      (∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) ≤
        ∑' ops, hardDist ops * P.expectedSeqProbes ops := by
  set μ := P.indexedSchemeLaw horizon opsAlphabet
  obtain ⟨D_det, hD_mem, hD_le⟩ :=
    Probability.PMF.exists_mem_support_tsum_mul_le_tsum_mul μ hardDist
      (fun D ops => (D.seqProbes ops : ℝ≥0∞))
  refine ⟨D_det, hD_mem, P.good_of_mem_support_law μ
    (fun D ops => ((D.runSeq ops).1, D.seqProbes ops)) correctSeqs Good hcorr
    (fun ops hops =>
      P.runSeq_eq_indexedSchemeLaw_bind (hcorrectSeqs ops hops).1 (hcorrectSeqs ops hops).2)
    hD_mem, hD_le.trans (tsum_le_tsum fun ops => ?_)⟩
  by_cases hops : ops ∈ hardDist.support
  · obtain ⟨hlen, halph⟩ := hhardDist ops hops
    rw [← P.expectedSeqProbes_eq_indexedSchemeLaw_tsum hlen halph]
  · simp [(PMF.apply_eq_zero_iff hardDist ops).mpr hops]

/-- Uniform-budget Yao averaging (easy direction) for zero-error schemes against oblivious
operation sequences (`Cslib.Probability.PMF.exists_mem_support_tsum_mul_le`): if
`P.expectedSeqProbes ops ≤ ε` for every `ops ∈ hardDist.support`, then some
`D_det ∈ (P.indexedSchemeLaw horizon opsAlphabet).support` satisfies `Good` on `correctSeqs` and
has average probe count `≤ ε` under `hardDist`. -/
theorem exists_det_indexedScheme_tsum_mul_le
    [DecidableEq Op] [∀ o, Inhabited (Result o)]
    (P : Scheme Op Result cells w)
    (opsAlphabet : Finset Op) (horizon : ℕ)
    (correctSeqs : Set (List Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs, ops.length ≤ horizon ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (Good : List Op → List (Sigma Result) → Prop)
    (hcorr : ∀ ops ∈ correctSeqs, ∀ tr ∈ ((P.runSeq ops).map Prod.fst).support, Good ops tr)
    (hardDist : PMF (List Op))
    (hhardDist : ∀ ops ∈ hardDist.support, ops.length ≤ horizon ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    {ε : ℝ≥0∞} (hε : ∀ ops ∈ hardDist.support, P.expectedSeqProbes ops ≤ ε) :
    ∃ D_det ∈ (P.indexedSchemeLaw horizon opsAlphabet).support,
      (∀ ops ∈ correctSeqs, Good ops (D_det.runSeq ops).1) ∧
      (∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) ≤ ε := by
  set μ := P.indexedSchemeLaw horizon opsAlphabet
  obtain ⟨D_det, hD_mem, hD_le⟩ :=
    Probability.PMF.exists_mem_support_tsum_mul_le μ hardDist
      (fun D ops => (D.seqProbes ops : ℝ≥0∞)) (ε := ε) fun ops hops => by
        obtain ⟨hlen, halph⟩ := hhardDist ops hops
        rw [← P.expectedSeqProbes_eq_indexedSchemeLaw_tsum hlen halph]
        exact hε ops hops
  exact ⟨D_det, hD_mem, P.good_of_mem_support_law μ
    (fun D ops => ((D.runSeq ops).1, D.seqProbes ops)) correctSeqs Good hcorr
    (fun ops hops =>
      P.runSeq_eq_indexedSchemeLaw_bind (hcorrectSeqs ops hops).1 (hcorrectSeqs ops hops).2)
    hD_mem, hD_le⟩

/-- `[Fintype Op]` convenience wrapper for `exists_det_indexedScheme_le_expectedSeqProbes`,
instantiating `opsAlphabet := Finset.univ`. -/
theorem exists_det_indexedScheme_le_expectedSeqProbes_of_fintype
    [Fintype Op] [DecidableEq Op] [∀ o, Inhabited (Result o)]
    (P : Scheme Op Result cells w)
    (horizon : ℕ)
    (correctSeqs : Set (List Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs, ops.length ≤ horizon)
    (Good : List Op → List (Sigma Result) → Prop)
    (hcorr : ∀ ops ∈ correctSeqs, ∀ tr ∈ ((P.runSeq ops).map Prod.fst).support, Good ops tr)
    (hardDist : PMF (List Op))
    (hhardDist : ∀ ops ∈ hardDist.support, ops.length ≤ horizon) :
    ∃ D_det ∈ (P.indexedSchemeLaw horizon Finset.univ).support,
      (∀ ops ∈ correctSeqs, Good ops (D_det.runSeq ops).1) ∧
      (∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) ≤
        ∑' ops, hardDist ops * P.expectedSeqProbes ops :=
  P.exists_det_indexedScheme_le_expectedSeqProbes Finset.univ horizon correctSeqs
    (fun ops hops => ⟨hcorrectSeqs ops hops, fun _ _ => Finset.mem_univ _⟩)
    Good hcorr hardDist
    (fun ops hops => ⟨hhardDist ops hops, fun _ _ => Finset.mem_univ _⟩)

/-! #### Random-initial-memory / coin-free-step specialization (`CellProbe.Scheme`) -/

/-- Distribution over time-invariant deterministic `CellProbe.Scheme`s induced by `P.init` when
every per-operation probe tree `P.step o` makes no private coin draws (`IsCoinFree`). -/
@[expose] noncomputable def schemeLaw (P : Scheme Op Result cells w)
    (hstep : ∀ o, (P.step o).IsCoinFree) :
    PMF (CellProbe.Scheme Op Result cells w) :=
  P.init.map fun m₀ => ⟨m₀, fun o => RandProbeTree.toProbeTree (P.step o) (hstep o)⟩

private theorem runFrom_eq_pure_of_isCoinFree (P : Scheme Op Result cells w)
    (hstep : ∀ o, (P.step o).IsCoinFree) (m₀ m : Mem cells w) (ops : List Op) :
    P.runFrom m ops =
      let D : CellProbe.Scheme Op Result cells w :=
        ⟨m₀, fun o => RandProbeTree.toProbeTree (P.step o) (hstep o)⟩
      PMF.pure (D.runFrom m ops, D.probesFrom m ops) := by
  induction ops generalizing m with
  | nil => rfl
  | cons o rest ih =>
    simp only [runFrom_cons, RandProbeTree.run_eq_pure_of_isCoinFree (P.step o) (hstep o) m,
      PMF.pure_bind]
    rw [ih ((RandProbeTree.toProbeTree (P.step o) (hstep o)).run m).2, PMF.pure_map]
    simp only [CellProbe.Scheme.runFrom_cons, CellProbe.Scheme.probesFrom_cons]

theorem runSeq_eq_schemeLaw_bind (P : Scheme Op Result cells w)
    (hstep : ∀ o, (P.step o).IsCoinFree) (ops : List Op) :
    P.runSeq ops =
      (P.schemeLaw hstep).bind fun D => PMF.pure ((D.runSeq ops).1, D.seqProbes ops) := by
  simp only [runSeq, schemeLaw, PMF.bind_map, Function.comp_def]
  refine congrArg (PMF.bind P.init) (funext fun m₀ => ?_)
  rw [P.runFrom_eq_pure_of_isCoinFree hstep m₀ m₀ ops, PMF.pure_map]
  rfl

theorem expectedSeqProbes_eq_schemeLaw_tsum (P : Scheme Op Result cells w)
    (hstep : ∀ o, (P.step o).IsCoinFree) (ops : List Op) :
    P.expectedSeqProbes ops =
      ∑' D, (P.schemeLaw hstep) D * (D.seqProbes ops : ℝ≥0∞) := by
  rw [expectedSeqProbes, P.runSeq_eq_schemeLaw_bind hstep ops, Probability.PMF.tsum_bind_mul]
  exact tsum_congr fun _ => congrArg (_ * ·) (RandProbeTree.tsum_pure_snd _)

/-- **Random-initial-memory / coin-free-step Yao averaging (`CellProbe.Scheme`):** when randomness
lives only in initial memory `P.init` and per-operation trees draw no private coins
(`∀ o, (P.step o).IsCoinFree`, so operations observe `P.init` only by probing cells), zero-error
averaging against oblivious operation sequences yields a time-invariant deterministic
`D_det : CellProbe.Scheme Op Result cells w` in `(P.schemeLaw hstep).support` preserving `Good` on
all `ops ∈ correctSeqs` and incurring at most `P`'s expected probes over `hardDist` — without
requiring `[DecidableEq Op]`, `opsAlphabet`, or `horizon` (bounded-error schemes are not
covered). -/
theorem exists_det_scheme_le_expectedSeqProbes
    (P : Scheme Op Result cells w)
    (hstep : ∀ o, (P.step o).IsCoinFree)
    (correctSeqs : Set (List Op))
    (Good : List Op → List (Sigma Result) → Prop)
    (hcorr : ∀ ops ∈ correctSeqs, ∀ tr ∈ ((P.runSeq ops).map Prod.fst).support, Good ops tr)
    (hardDist : PMF (List Op)) :
    ∃ D_det ∈ (P.schemeLaw hstep).support,
      (∀ ops ∈ correctSeqs, Good ops (D_det.runSeq ops).1) ∧
      (∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) ≤
        ∑' ops, hardDist ops * P.expectedSeqProbes ops := by
  set μ := P.schemeLaw hstep
  obtain ⟨D_det, hD_mem, hD_le⟩ :=
    Probability.PMF.exists_mem_support_tsum_mul_le_tsum_mul μ hardDist
      (fun D ops => (D.seqProbes ops : ℝ≥0∞))
  refine ⟨D_det, hD_mem, P.good_of_mem_support_law μ
    (fun D ops => ((D.runSeq ops).1, D.seqProbes ops)) correctSeqs Good hcorr
    (fun ops _ => P.runSeq_eq_schemeLaw_bind hstep ops) hD_mem, hD_le.trans ?_⟩
  exact le_of_eq (tsum_congr fun ops =>
    congrArg (hardDist ops * ·) (P.expectedSeqProbes_eq_schemeLaw_tsum hstep ops).symm)

end Scheme

end Randomized

end Cslib.CellProbe
