/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.PrefixSums.CellProbe.LowerBound

/-!
# Fredman–Saks lower bound tests

Kernel-checked instances for `Cslib.DataStructure.PrefixSums.CellProbe`:

1. the layout of the hard instance for `β = 2`, `L = 2`, and the answer formula on one input;
2. a correct scheme, `naive`, with one `w`-bit cell per bit. Updates write their bit (depth `1`)
   and queries read the whole prefix (depth at most `n`). It satisfies every hypothesis of
   `exists_le_mul_probes`, both with one epoch (`n = 64`, `w = 1`, `L = 1`, `β = 64`, `t_u = 1`,
   since `129 ^ 8 ≤ 2 ^ 64`) and with two (`n = 131072`, `w = 1`, `L = 2`, `β = 256`), and of
   `log_le_of_answersQueries` (with `n ≤ 2 ^ w`), so neither theorem is vacuous;
3. a scheme, `zeroScheme`, that ignores updates and answers `0` with no probes. It meets every
   hypothesis of `exists_le_mul_probes` except `AnswersQueries`, and the theorem refutes
   correctness, so that hypothesis cannot be dropped.
-/

public section

namespace ComplexityTests.CellProbeFredmanSaks

open Cslib Cslib.CellProbe Cslib.DataStructure.PrefixSums.CellProbe Finset

/-! ### 1. The hard instance -/

/-- With `β = 2`, `L = 2`: epoch `0` writes positions `0, 2, 4, 6`, epoch `1` writes positions
`1, 5`, and the queries ask positions `1, 3, 5, 7`; there are `2 ^ 2 + 2 ^ 1 = 6` updates. -/
example :
    (List.range 4).map (hardPos 2 2 0) = [0, 2, 4, 6] ∧
      (List.range 2).map (hardPos 2 2 1) = [1, 5] ∧
      (List.range 4).map (hardQueryPos 2) = [1, 3, 5, 7] ∧ hardTime 2 2 = 6 := by
  decide

/-- The all-ones input of the instance `β = 2`, `L = 2`. -/
def onesInput : HardInput 2 2 := fun _ _ => 1

theorem hn8 : 2 * 2 ^ 2 ≤ 8 := by norm_num

/-- After the hard updates of the all-ones input, the array is `1, 1, 1, 0, 1, 1, 1, 0`, so query
`1` (position `3`) answers `1`, matching the answer formula
`(X 0 0 + X 0 1) + X 1 0 = 0 + 1`. -/
example :
    prefixParity (arrayOf (hardUpdates hn8 onesInput)) (hardQueryIdx hn8 two_pos 1) = 1 ∧
      hardAnswer onesInput 1 = 1 := by
  refine ⟨?_, ?_⟩
  · rw [prefixParity_hardUpdates hn8 two_pos two_pos]
    decide
  · decide

/-! ### 2. A correct scheme: one cell per bit -/

/-- The `w`-bit word storing bit `b`. -/
def enc (w : ℕ) (b : ZMod 2) : Fin (2 ^ w) :=
  ⟨b.val % 2 ^ w, Nat.mod_lt _ (Nat.two_pow_pos w)⟩

theorem enc_val {w : ℕ} (hw : 0 < w) (b : ZMod 2) : (((enc w b).val : ℕ) : ZMod 2) = b := by
  have hb : b.val < 2 ^ w :=
    lt_of_lt_of_le (ZMod.val_lt b) ((pow_one 2).symm.le.trans (Nat.pow_le_pow_right two_pos hw))
  simp only [enc, Nat.mod_eq_of_lt hb, ZMod.natCast_zmod_val]

/-- Read the cells of `l` and return the sum of the bits they store. -/
def readSum {n w : ℕ} : List (Fin n) → ProbeTree n w (ZMod 2)
  | [] => pure 0
  | c :: l => do
      let v ← ProbeTree.read c
      let s ← readSum l
      pure ((v.val : ZMod 2) + s)

theorem run_readSum {n w : ℕ} (l : List (Fin n)) (m : Mem n w) :
    (readSum l).run m = ((l.map fun c => ((m c).val : ZMod 2)).sum, m) := by
  induction l with
  | nil => rfl
  | cons c l ih => simp [readSum, ih]

theorem depth_readSum_le {n w : ℕ} (l : List (Fin n)) :
    (readSum (w := w) l).depth ≤ l.length := by
  induction l with
  | nil => simp [readSum]
  | cons c l ih =>
    change (ProbeTree.read c >>= fun v => readSum l >>= fun s =>
      pure ((v.val : ZMod 2) + s)).depth ≤ _
    refine (ProbeTree.depth_bind_le (d := l.length) _ _ fun v =>
      (ProbeTree.depth_bind_le (d := 0) _ _ fun s => (ProbeTree.depth_pure _).le).trans
        (by simpa using ih)).trans ?_
    simp only [ProbeTree.depth_read, List.length_cons]
    omega

/-- The trivial scheme with one cell per bit: an update writes its bit with one probe, and a query
reads the whole prefix. -/
def naive (n w : ℕ) : IndexedScheme (Op n) Result n w where
  init := zeroMem n w
  step _
    | .update i b => ProbeTree.write i (enc w b)
    | .query i => readSum ((List.finRange n).filter fun c => c ≤ i)

theorem naive_init {n w : ℕ} : (naive n w).init = enc w ∘ (0 : Fin n → ZMod 2) := by
  funext c
  apply Fin.ext
  simp [naive, zeroMem, enc]

theorem runInterval_naive {n w : ℕ} (ops : List (Op n)) (t : ℕ) (A : Fin n → ZMod 2) :
    ((naive n w).runInterval t (enc w ∘ A) ops).2 = enc w ∘ ops.foldl applyOp A := by
  induction ops generalizing t A with
  | nil => rfl
  | cons o ops ih =>
    have hM : (((naive n w).step t o).run (enc w ∘ A)).2 = enc w ∘ applyOp A o := by
      cases o with
      | update i b =>
        change Function.update (enc w ∘ A) i (enc w b) = enc w ∘ Function.update A i b
        funext c
        by_cases hc : c = i
        · subst hc
          simp
        · simp [Function.update_of_ne hc]
      | query i =>
        change ((readSum ((List.finRange n).filter fun c => c ≤ i)).run (enc w ∘ A)).2 =
          enc w ∘ A
        rw [run_readSum]
    rw [IndexedScheme.runInterval_cons, List.foldl_cons, hM, ih]

theorem naive_answersQueries {n w : ℕ} (hw : 0 < w) : AnswersQueries (naive n w) := by
  intro ops i
  have hmem : ((naive n w).runSeq ops).2 = enc w ∘ arrayOf ops := by
    rw [IndexedScheme.runSeq, naive_init, runInterval_naive]
    rfl
  rw [hmem]
  change ((readSum ((List.finRange n).filter fun c => c ≤ i)).run (enc w ∘ arrayOf ops)).1 = _
  rw [run_readSum]
  simp only [Function.comp_apply, enc_val hw]
  have hI : Iic i = ((List.finRange n).filter fun c => decide (c ≤ i)).toFinset := by
    ext c
    simp
  rw [prefixParity, hI, List.sum_toFinset _ ((List.nodup_finRange n).filter _)]

theorem naive_update_depth {n w : ℕ} (t : ℕ) (i : Fin n) (b : ZMod 2) :
    ((naive n w).step t (.update i b)).depth ≤ 1 :=
  (ProbeTree.depth_write i (enc w b)).le

theorem naive_query_depth {n w : ℕ} (t : ℕ) (i : Fin n) :
    ((naive n w).step t (.query i)).depth ≤ n :=
  (depth_readSum_le _).trans ((List.length_filter_le _ _).trans (by simp))

theorem hn64 : 1 * 64 ^ 1 ≤ 64 := by norm_num

/-- **Nonvacuity of the hard-instance form**: `naive 64 1` satisfies every hypothesis of
`exists_le_mul_probes` with `L = 1`, `β = 64` and `t_u = 1`, since `(64 · 2 + 1) ^ 8 ≤ 2 ^ 64`. -/
example : ∃ (X : HardInput 64 1) (q : Fin (64 ^ 1)),
    1 ≤ 64 * ((naive 64 1).step (hardUpdates hn64 X).length
      (.query (hardQueryIdx hn64 one_pos q))).probes ((naive 64 1).runSeq (hardUpdates hn64 X)).2 :=
  exists_le_mul_probes hn64 one_pos (naive 64 1) (naive_answersQueries one_pos) (by norm_num)
    naive_update_depth (by norm_num)

theorem hn131072 : 2 * 256 ^ 2 ≤ 131072 := by norm_num

/-- **Two-epoch nonvacuity**: `naive 131072 1` satisfies every hypothesis of `exists_le_mul_probes`
with `L = 2`, `β = 256` and `t_u = 1`, a genuine two-epoch chronogram, so some query of the hard
instance makes at least one probe. -/
example : ∃ (X : HardInput 256 2) (q : Fin (256 ^ 2)),
    2 ≤ 64 * ((naive 131072 1).step (hardUpdates hn131072 X).length
      (.query (hardQueryIdx hn131072 two_pos q))).probes
        ((naive 131072 1).runSeq (hardUpdates hn131072 X)).2 :=
  exists_le_mul_probes hn131072 two_pos (naive 131072 1) (naive_answersQueries one_pos)
    (by norm_num) naive_update_depth (by norm_num)

/-- **Nonvacuity of the logarithmic form**: on `n ≤ 2 ^ w` bits, `naive n w` satisfies every
hypothesis of `log_le_of_answersQueries` with `t_u = 1` and `t_q = n`. -/
example {n w : ℕ} (hw : 0 < w) (hn : n ≤ 2 ^ w) :
    Nat.log (max 4 (8 * 1 * (2 * w + 1))) n ≤ 128 * n + 1 :=
  log_le_of_answersQueries (naive n w) (naive_answersQueries hw) hn naive_update_depth
    naive_query_depth

/-! ### 3. Correctness cannot be dropped -/

/-- A scheme that ignores updates and answers `0` to every query, with no probes. -/
def zeroScheme (n : ℕ) : IndexedScheme (Op n) Result 1 1 where
  init := zeroMem 1 1
  step _
    | .update _ _ => pure PUnit.unit
    | .query _ => pure 0

theorem hn4 : 1 * 4 ^ 1 ≤ 4 := by norm_num

/-- `zeroScheme 4` meets every hypothesis of `exists_le_mul_probes` (with `L = 1`, `β = 4`,
`t_u = 0`) except correctness, and its queries make no probes; so the theorem shows that it does
not answer queries. -/
example : ¬ AnswersQueries (zeroScheme 4) := by
  intro hD
  obtain ⟨X, q, h⟩ := exists_le_mul_probes hn4 one_pos (zeroScheme 4) hD le_rfl (tu := 0)
    (fun _ _ _ => (ProbeTree.depth_pure _).le) (by norm_num)
  change 1 ≤ 64 * (pure 0 : ProbeTree 1 1 (ZMod 2)).probes _ at h
  rw [ProbeTree.probes_pure] at h
  omega

end ComplexityTests.CellProbeFredmanSaks
