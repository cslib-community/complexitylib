/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Complexity.FineGrained.DisjointInstances
public import CslibFrontier.Computability.Complexity.Reduction.BoundedOracle
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Worked clients for `DisjointInstances` and `BoundedOracle`

Kernel-checked strict-`module` examples (with no `import all`, `sorry`, `axiom`, or
`native_decide`) exercising:

1. `SizeSensitiveReduction`: non-identity linear-parameter bit-duplication map, composition
   multiplying scales, exponential/subexponential transfer, and polynomial-space preservation.
2. `InstanceBatch`, `CNFInstanceBatch` (`encCNFInstanceBatch`), `CappedNatAcc` (`encCappedNatAcc`),
   and `DisjointBatchReduction`: empty, singleton, and multi-element batches, exact below-cap sums
   versus clamped above-cap sums, disjoint CNF variable-measure aggregation, OR decision transfer,
   and capped summed-counting transfer in polynomial live workspace.
3. `StackAccumulationSpec` and `BinaryBranching`: concrete depth-bounded binary branching tree
   accumulating exact leaf counts `2 ^ d` via `CappedNatAcc` without materializing the leaf list.
4. `OracleCallBound` (`encOracleCallBound`), `BoundedOracleProgram` (on a genuine multi-bit word
   oracle returning `w ++ [true]`), and `BoundedOracleReduction`: zero-query, single-query,
   composed, and affine-total-length call profiles, bridges to `PolyTimeTuringReducible` and
   `PWithOracleQueries`, and polynomial-time, polynomial-space, and parameterized exponential /
   subexponential transfer.
-/

public section

namespace CslibFrontierTests.DisjointInstancesAndOracleReduction

open Cslib Cslib.Complexity Cslib.Logic.PL _root_.Turing _root_.Turing.MultiTapeTM

/-! ### 1. `SizeSensitiveReduction` -/

/-- Concrete size-sensitive reduction duplicating a bit word (`|w ++ w| = 2 * |w|`). -/
def dupBitsReduction : SizeSensitiveReduction encBits encBits List.length List.length where
  toFun w := w ++ w
  scale := 2
  offset := 0
  computableInPolyTime_toFun :=
    (ComputableTidilyInPolyTime.bitsAppend .id' .id').computableInPolyTime
  measure_le w := by
    simp only [List.length_append]
    omega

/-- Composing `dupBitsReduction` with itself produces scale `2 * 2 = 4` and maps `[true, false]`
to a word of length `8`. -/
example :
    (dupBitsReduction.trans dupBitsReduction).scale = 4 ∧
      (dupBitsReduction.trans dupBitsReduction).offset = 0 ∧
      ((dupBitsReduction.trans dupBitsReduction).toFun [true, false]).length = 8 ∧
      (SizeSensitiveReduction.refl encBits List.length).toFun [true] = [true] := by
  refine ⟨rfl, by simp [SizeSensitiveReduction.trans, dupBitsReduction], ?_, rfl⟩
  decide

/-- Exponential and polynomial-space transfer along `dupBitsReduction` on the nonempty-word
language (`w ≠ [] ↔ w ++ w ≠ []`). -/
example {δ : ℝ} (hδ : 0 ≤ δ)
    (hExp : DecidableInExpTime {w : List Bool | w ≠ []} encBits List.length δ)
    (hPS : ComputableInPolySpace List.reverse encBits encBits) :
    DecidableInExpTime {w : List Bool | w ≠ []} encBits List.length (2 * δ) ∧
      ComputableInPolySpace (fun w => (w ++ w).reverse) encBits encBits := by
  have hiff (w : List Bool) : w ∈ {u : List Bool | u ≠ []} ↔
      dupBitsReduction.toFun w ∈ {u : List Bool | u ≠ []} := by
    cases w <;> simp [dupBitsReduction]
  have hexp' := dupBitsReduction.decidableInExpTime hiff hδ hExp
  simp only [dupBitsReduction, Nat.cast_ofNat] at hexp'
  exact ⟨hexp', dupBitsReduction.computableInPolySpace_comp hPS⟩

/-! ### 2. `InstanceBatch`, `CNFInstanceBatch`, `CappedNatAcc`, and `DisjointBatchReduction` -/

/-- `InstanceBatch`: empty, singleton, and multi-element `sumMeasure` and `maxMeasure` checks. -/
example :
    (InstanceBatch.nil : InstanceBatch (List Bool)).sumMeasure List.length = 0 ∧
      (InstanceBatch.nil : InstanceBatch (List Bool)).maxMeasure List.length = 0 ∧
      (InstanceBatch.singleton [true, false, true]).sumMeasure List.length = 3 ∧
      (⟨[[true], [false, true], [true, true, false]]⟩ :
          InstanceBatch (List Bool)).sumMeasure List.length = 6 ∧
      (⟨[[true], [false, true], [true, true, false]]⟩ :
          InstanceBatch (List Bool)).maxMeasure List.length = 3 := by
  decide

/-- `CappedNatAcc` (`encCappedNatAcc`): exact folding below cap (`2 + 3 + 4 = 9 ≤ 10`), clamping
above cap (`6 + 7 ↦ 10`), and polynomial-time `enc_structure` projections. -/
example :
    (((CappedNatAcc.init 10).add 2).add 3).add 4 = ⟨10, 9⟩ ∧
      (((CappedNatAcc.init 10).add 6).add 7) = ⟨10, 10⟩ ∧
      ([2, 3, 4].foldl CappedNatAcc.add (CappedNatAcc.init 10)).total = 9 ∧
      ([6, 7].foldl CappedNatAcc.add (CappedNatAcc.init 10)).total = 10 ∧
      ComputableInPolyTime CappedNatAcc.total encCappedNatAcc encNat ∧
      ComputableInPolyTime CappedNatAcc.cap encCappedNatAcc encNat := by
  refine ⟨rfl, rfl, by decide, by decide,
    encCappedNatAcc_total_polyTime .id', encCappedNatAcc_cap_polyTime .id'⟩

/-- `CNFInstanceBatch` (`encCNFInstanceBatch`): empty batch vs disjoint variable-splitting batch
`[[[(0, true)]], [[(0, false)]]]` over `2` declared variables. -/
def emptyCNFBatch : CNFInstanceBatch := ⟨2, []⟩
def singletonCNFBatch : CNFInstanceBatch := ⟨2, [[[(0, true)]]]⟩
def splitCNFBatch : CNFInstanceBatch := ⟨2, [[[(0, true)]], [[(0, false)]]]⟩

example :
    emptyCNFBatch.sumNumVars = 0 ∧
      singletonCNFBatch.sumNumVars = 1 ∧
      splitCNFBatch.sumNumVars = 2 ∧
      ComputableInPolyTime CNFInstanceBatch.declaredVars encCNFInstanceBatch encUnary ∧
      ComputableInPolyTime CNFInstanceBatch.formulas encCNFInstanceBatch (encList encCNF) := by
  refine ⟨by decide, by decide, by decide,
    encCNFInstanceBatch_declaredVars_polyTime .id',
    encCNFInstanceBatch_formulas_polyTime .id'⟩

/-- Concrete 2-way word-splitting `DisjointBatchReduction` (`w ↦ [w.take 1, w.drop 1]`) whose
summed subinstance length equals `|w|` (`scale = 1`, `offset = 0`). -/
def splitWordBatchReduction :
    DisjointBatchReduction encBits encBits List.length List.length where
  toBatch w := ⟨[w.take 1, w.drop 1]⟩
  scale := 1
  offset := 0
  computableInPolyTime_toBatch := by
    have htake : ComputableTidilyInPolyTime (fun w : List Bool => w.take 1) encBits encBits :=
      ComputableTidilyInPolyTime.bitsTake.comp
        (ComputableTidilyInPolyTime.id'.prod (.const 1))
    have hdrop : ComputableTidilyInPolyTime (fun w : List Bool => w.drop 1) encBits encBits :=
      ComputableTidilyInPolyTime.bitsDropWithInput .id' (.const 1)
    have hlist : ComputableInPolyTime (fun w : List Bool => [w.take 1, w.drop 1])
        encBits (encList encBits) :=
      (ComputableTidilyInPolyTime.cons' htake
        (ComputableTidilyInPolyTime.cons' hdrop (.const []))).computableInPolyTime
    exact computableInPolyTime_instanceBatch_mk hlist
  sumMeasure_le w := by
    simp only [InstanceBatch.sumMeasure, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero, one_mul]
    have h := congrArg List.length (List.take_append_drop 1 w)
    rw [List.length_append] at h
    omega

/-- Empty, singleton, and multi-bit behavior of `splitWordBatchReduction`, plus OR exponential
transfer (`{w | true ∈ w}`). -/
example {δ : ℝ} (hδ : 0 ≤ δ)
    (hExp : DecidableInExpTime {w : List Bool | true ∈ w} encBits List.length δ) :
    (splitWordBatchReduction.toBatch []).sumMeasure List.length = 0 ∧
      (splitWordBatchReduction.toBatch [true]).sumMeasure List.length = 1 ∧
      (splitWordBatchReduction.toBatch [false, true, false]).sumMeasure List.length = 3 ∧
      DecidableInExpTime {w : List Bool | true ∈ w} encBits List.length δ := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  have hor : ∀ w : List Bool,
      w ∈ {u : List Bool | true ∈ u} ↔
        ∃ sub ∈ (splitWordBatchReduction.toBatch w).items,
          sub ∈ {u : List Bool | true ∈ u} := by
    intro w
    change (true ∈ w) ↔
      ∃ sub ∈ (splitWordBatchReduction.toBatch w).items, true ∈ sub
    simp only [splitWordBatchReduction, List.mem_cons,
      List.not_mem_nil, or_false]
    conv_lhs => rw [← List.take_append_drop 1 w, List.mem_append]
    constructor
    · rintro (h | h)
      · exact ⟨w.take 1, Or.inl rfl, h⟩
      · exact ⟨w.drop 1, Or.inr rfl, h⟩
    · rintro ⟨sub, rfl | rfl, h⟩
      · exact Or.inl h
      · exact Or.inr h
  have htr := splitWordBatchReduction.decidableInExpTime_or hor hδ hExp
  simpa only [splitWordBatchReduction, Nat.cast_one, one_mul] using htr

/-! ### 3. `StackAccumulationSpec` and `BinaryBranching` -/

/-- Complete binary branching tree of height `n` on countdown depth `s : ℕ`: `0` is a leaf, and
`s + 1` branches to `(s, s)`. -/
@[expose]
def countdownBranching : BinaryBranching ℕ where
  IsLeaf s := s = 0
  next s _ := s - 1

theorem countdownBranching_terminating : countdownBranching.Terminating :=
  BinaryBranching.Terminating.of_lt (T := countdownBranching) id fun s hs _ => by
    change ¬(s = 0) at hs
    change s - 1 < s
    omega

/-- Concrete `StackAccumulationSpec` traversing `countdownBranching` from depth `n` (given in
unary so `rounds n = 2 * 2 ^ n` has linear binary length) and summing `1` at every leaf into a
`CappedNatAcc` with cap `2 ^ n`. -/
@[expose]
def countdownStackSpec :
    StackAccumulationSpec encUnary (encFinEnum Unit) encNat encNat encNat encCappedNatAcc where
  defaultNode := 0
  initCtx _ := ()
  initStack n := [n]
  initAcc n := CappedNatAcc.init (2 ^ n)
  rounds n := 2 * 2 ^ n
  isLeaf p := decide (p.node = 0)
  leafInstance p := p.node
  expand p := [p.node - 1, p.node - 1]
  combine p := p.acc.add p.leafVal
  computableInPolyTime_initCtx := .const ()
  computableInPolyTime_initStack := by
    exact (ComputableTidilyInPolyTime.cons' ComputableTidilyInPolyTime.unary_to_binary
      (.const [])).computableInPolyTime
  computableInPolyTime_initAcc := by
    exact CappedNatAcc.computableInPolyTime_init
      ComputableTidilyInPolyTime.binary_two_pow.computableInPolyTime
  computableInPolyTime_rounds := by
    have hpow := ComputableTidilyInPolyTime.binary_two_pow
    exact ((ComputableTidilyInPolyTime.const 2).binary_mul' hpow).computableInPolyTime
  computableInPolyTime_isLeaf := by
    have hnd := computableInPolyTime_stackNodeInput_node
      (encK := encFinEnum Unit) (encS := encNat) .id'
    exact (hnd.tidy.decide_eq' (.const 0)).computableInPolyTime
  computableInPolyTime_leafInstance :=
    computableInPolyTime_stackNodeInput_node (encK := encFinEnum Unit) (encS := encNat) .id'
  computableInPolyTime_expand := by
    have hnd := computableInPolyTime_stackNodeInput_node
      (encK := encFinEnum Unit) (encS := encNat) .id'
    have hsub := hnd.tidy.binary_sub' (.const 1)
    exact (ComputableTidilyInPolyTime.cons' hsub
      (ComputableTidilyInPolyTime.cons' hsub (.const []))).computableInPolyTime
  computableInPolyTime_combine := by
    have hacc := computableInPolyTime_stackCombineInput_acc
      (encK := encFinEnum Unit) (encD := encCappedNatAcc) (encG := encNat) .id'
    have hlv := computableInPolyTime_stackCombineInput_leafVal
      (encK := encFinEnum Unit) (encD := encCappedNatAcc) (encG := encNat) .id'
    exact (CappedNatAcc.computableInPolyTime_add.comp (hacc.prod hlv)).of_enc_eq fun _ => rfl

/-- Exact proof for ALL `n : ℕ` via `StackAccumulationSpec.run_cappedSum_eq_root`, instantiated at
`n = 0, 1, 2, 3` (`1, 2, 4, 8` leaves). -/
theorem countdownStackSpec_run_total (n : ℕ) :
    (StackAccumulationSpec.run (encG := encNat) countdownStackSpec (fun _ => 1) n).total =
      2 ^ n := by
  have hwalk_len : ∀ s w, countdownBranching.IsLeafWord s w → w.length ≤ s := by
    intro s w hw
    induction w generalizing s with
    | nil => exact Nat.zero_le s
    | cons b ws ih =>
      obtain ⟨hnot, htail⟩ := hw
      change ¬(s = 0) at hnot
      have hsub := ih (s - 1) htail
      simp only [List.length_cons]
      omega
  refine StackAccumulationSpec.run_cappedSum_eq_root countdownStackSpec (fun _ => 1) n
    countdownBranching countdownBranching_terminating rfl rfl (fun _ _ => rfl)
    (fun _ => decide_eq_true_eq.to_iff)
    (fun _ _ => rfl) (hwalk_len n) ?_
    (val := fun s => 2 ^ s)
    (fun t ht => by
      change ¬(t = 0) at ht
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht
      change 2 ^ (m + 1) = 2 ^ m + 2 ^ m
      omega)
    (fun t ht => by
      change t = 0 at ht
      subst ht
      rfl)
    le_rfl
  intro L hnd hL
  have hcard : L.toFinset.card ≤ ∑ j ∈ Finset.range (n + 1), n.choose j :=
    countdownBranching.card_le_sum_choose_of_isLeafWord
      (fun w hw => (hL w).mp (List.mem_toFinset.mp hw))
      (fun w hw => hwalk_len n w ((hL w).mp (List.mem_toFinset.mp hw)))
      (fun w hw => (Finset.card_filter_le _ _).trans (by
        rw [Finset.card_range]
        exact hwalk_len n w ((hL w).mp (List.mem_toFinset.mp hw))))
  rw [Nat.sum_range_choose, List.toFinset_card_of_nodup hnd] at hcard
  change 2 * L.length ≤ 2 * 2 ^ n + 1
  omega

example :
    (StackAccumulationSpec.run (encG := encNat) countdownStackSpec (fun _ => 1) 0).total = 1 ∧
      (StackAccumulationSpec.run (encG := encNat) countdownStackSpec (fun _ => 1) 1).total = 2 ∧
      (StackAccumulationSpec.run (encG := encNat) countdownStackSpec (fun _ => 1) 2).total = 4 ∧
      (StackAccumulationSpec.run (encG := encNat) countdownStackSpec (fun _ => 1) 3).total = 8 :=
  ⟨countdownStackSpec_run_total 0, countdownStackSpec_run_total 1,
    countdownStackSpec_run_total 2, countdownStackSpec_run_total 3⟩

/-! ### 4. `OracleCallBound`, `BoundedOracleProgram`, and `BoundedOracleReduction` -/

/-- `OracleCallBound` (`encOracleCallBound`) concrete profile & `ComputableInPolyTime` fields. -/
example :
    OracleCallBound.zero = ⟨0, 0, 0, 0⟩ ∧
      OracleCallBound.single 5 3 = ⟨1, 5, 5, 3⟩ ∧
      ComputableInPolyTime OracleCallBound.qcount encOracleCallBound encNat ∧
      ComputableInPolyTime OracleCallBound.qlen encOracleCallBound encNat ∧
      ComputableInPolyTime OracleCallBound.totalQlen encOracleCallBound encNat ∧
      ComputableInPolyTime OracleCallBound.alen encOracleCallBound encNat :=
  ⟨rfl, rfl,
    encOracleCallBound_qcount_polyTime .id',
    encOracleCallBound_qlen_polyTime .id',
    encOracleCallBound_totalQlen_polyTime .id',
    encOracleCallBound_alen_polyTime .id'⟩

/-- Genuine multi-bit word oracle appending `true` (`|appendTrueOracle w| = |w| + 1 ≥ 1`). -/
def appendTrueOracle (w : List Bool) : List Bool := w ++ [true]

theorem computableInPolyTime_appendTrueOracle :
    ComputableInPolyTime appendTrueOracle encBits encBits :=
  (ComputableTidilyInPolyTime.bitsAppend .id' (.const [true])).computableInPolyTime

/-- Identity multi-bit `BoundedOracleProgram` for `appendTrueOracle` (`alenCap w = |w| + 1`). -/
@[expose]
noncomputable def appendTrueIdProg :
    BoundedOracleProgram encBits encBits appendTrueOracle appendTrueOracle :=
  BoundedOracleProgram.id
    (alenCap := fun w => w.length + 1)
    (by
      exact ((ComputableInPolyTime.unary_eval (Polynomial.X + 1)).comp
        (ComputableInPolyTime.encoding_length encBits)).of_enc_eq fun w => by simp)
    (by intro w; simp [appendTrueOracle])

/-- Composing `appendTrueIdProg` with itself computes `w ↦ w ++ [true]` via `1` inner query of
length `|w|` and transfers to both `ComputableInPolyTime` and `ComputableInPolySpace`. -/
example :
    (appendTrueIdProg.comp appendTrueIdProg).qcount [false, true] = 1 ∧
      ((appendTrueIdProg.compAffine appendTrueIdProg (scale := 1) (offset := 0)
        (fun w => by simp [appendTrueIdProg, BoundedOracleProgram.id,
          BoundedOracleProgram.ofSingleQuery, BoundedOracleProgram.totalQlen,
          OracleCallBound.single])).totalQlen [false, true]) = 2 ∧
      ComputableInPolyTime appendTrueOracle encBits encBits ∧
      ComputableInPolySpace appendTrueOracle encBits encBits := by
  have hcomp := appendTrueIdProg.comp appendTrueIdProg
  have hpt := hcomp.computableInPolyTime computableInPolyTime_appendTrueOracle
  have hps := hcomp.computableInPolySpace
    (ComputableInPolySpace.of_polyTime computableInPolyTime_appendTrueOracle)
  refine ⟨?_, rfl, hpt, hps⟩
  rw [BoundedOracleProgram.qcount_comp]
  have hqc1 : appendTrueIdProg.qcount [false, true] = 1 := rfl
  have hql1 : appendTrueIdProg.qlen [false, true] = 2 := rfl
  have hqc2 : appendTrueIdProg.qcount = fun _ => 1 := rfl
  rw [hqc1, hql1, hqc2, one_mul]
  apply le_antisymm
  · exact csSup_le ⟨1, ⟨[], Nat.zero_le 2, rfl⟩⟩ (by rintro _ ⟨w, _, rfl⟩; exact le_rfl)
  · exact le_wordMax (fun _ => 1) (w := []) (Nat.zero_le 2)

/-- `BoundedOracleReduction`: lift `dupBitsReduction`, compose via `trans`, bridge to
`PolyTimeTuringReducible` and `PWithOracleQueries`, and transfer `P`, `PSPACE`, and
`DecidableInExpTime`. -/
noncomputable def nonemptyOracleRed :
    BoundedOracleReduction encBits encBits {w : List Bool | w ≠ []} {w : List Bool | w ≠ []} :=
  BoundedOracleReduction.ofSizeSensitive dupBitsReduction fun w => by
    cases w <;> simp [dupBitsReduction]

example {δ : ℝ} (hδ : 0 ≤ δ)
    (hB_P : {w : List Bool | w ≠ []} ∈ P encBits)
    (hB_PS : {w : List Bool | w ≠ []} ∈ PSPACE encBits)
    (hB_Exp : DecidableInExpTime {w : List Bool | w ≠ []} encBits List.length δ) :
    PolyTimeTuringReducible encBits encBits
      {w : List Bool | w ≠ []} {w : List Bool | w ≠ []} ∧
    {w : List Bool | w ≠ []} ∈
      PWithOracleQueries (encBits '' {w : List Bool | w ≠ []}) (fun _ => 1) encBits ∧
    {w : List Bool | w ≠ []} ∈ P encBits ∧
    {w : List Bool | w ≠ []} ∈ PSPACE encBits ∧
    DecidableInExpTime {w : List Bool | w ≠ []} encBits List.length (2 * δ) := by
  have hlen_pt : ComputableInPolyTime List.length encBits encNat :=
    (ComputableTidilyInPolyTime.unary_to_binary.comp
      (ComputableTidilyInPolyTime.encoding_length encBits)).computableInPolyTime
  have hcomp := nonemptyOracleRed.trans nonemptyOracleRed
  have hExpA := nonemptyOracleRed.decidableInExpTime Decoder.bits hlen_pt hlen_pt
    (scale := 2) (offset := 0)
    (fun w q hq b hb => by
      simp only [nonemptyOracleRed, BoundedOracleReduction.ofSizeSensitive,
        BoundedOracleReduction.ofProgram, BoundedOracleProgram.ofSingleQuery,
        OracleComp.queriesWith_map, OracleComp.queriesWith_query, List.mem_singleton] at hq
      subst hq
      change b = w ++ w at hb
      subst hb
      simp only [List.length_append]
      omega)
    hδ hB_Exp
  simp only [Nat.cast_ofNat] at hExpA
  exact ⟨hcomp.polyTimeTuringReducible,
    nonemptyOracleRed.mem_PWithOracleQueries (fun _ => le_rfl),
    hcomp.mem_P Decoder.bits hB_P,
    hcomp.mem_PSPACE Decoder.bits hB_PS,
    hExpA⟩





def dummyStackSpec :
    StackAccumulationSpec encUnary (encFinEnum Unit) encNat encNat encNat encNat where
  defaultNode := 0
  initCtx _ := ()
  initStack _ := []
  initAcc _ := 0
  rounds n := 2 ^ n
  isLeaf _ := true
  leafInstance _ := 0
  expand _ := []
  combine _ := 0
  computableInPolyTime_initCtx := .const ()
  computableInPolyTime_initStack := .const []
  computableInPolyTime_initAcc := .const 0
  computableInPolyTime_rounds := ComputableTidilyInPolyTime.binary_two_pow.computableInPolyTime
  computableInPolyTime_isLeaf := .const true
  computableInPolyTime_leafInstance := .const 0
  computableInPolyTime_expand := .const []
  computableInPolyTime_combine := .const 0

example : ∃ c e : ℕ, ∃ Space : ℕ → ℕ,
    PolyBounded (fun a => (encUnary a).length) Space ∧
    ComputableInO (dummyStackSpec.run id) encUnary encNat
      (fun a => c * ((encUnary a).length + 1) ^ e +
        (dummyStackSpec.rounds a + 1) *
          (c * ((encUnary a).length + 1) ^ e + (encNat 0).length)) Space ∧
    ComputableInPolySpace (dummyStackSpec.run id) encUnary encNat := by
  have h := StackAccumulationSpec.exists_computableInO_run dummyStackSpec
    (g := id) (Tg := fun x => (encNat x).length) (Sg := fun x => (encNat x).length)
    (ComputableInO.id')
    (⟨id, Cslib.PolynomiallyBounded.id, fun _ => le_rfl⟩)
    (stateBound := fun _ => 1000) (ansBound := fun _ => 1000)
    (leafMax := fun _ => (encNat 0).length)
    (⟨fun _ => 1000, Cslib.PolynomiallyBounded.const 1000, fun _ => le_rfl⟩)
    (⟨fun _ => 1000, Cslib.PolynomiallyBounded.const 1000, fun _ => le_rfl⟩)
    (by
      intro a i hi
      cases i with
      | zero =>
        have heq : (dummyStackSpec.step id)^[0] (dummyStackSpec.initState a) = ⟨(), [], 0⟩ := rfl
        rw [heq]
        exact (by decide)
      | succ j =>
        have heq : (dummyStackSpec.step id)^[j + 1] (dummyStackSpec.initState a) =
          (dummyStackSpec.step id)^[j] ⟨(), [], 0⟩ := rfl
        rw [heq]
        rw [StackAccumulationSpec.iterate_step_empty]
        exact (by decide))
    (by
      intro a i hi st H
      cases i with
      | zero =>
        cases H.1
      | succ j =>
        have heq : st = (dummyStackSpec.step id)^[j] ⟨(), [], 0⟩ := rfl
        rw [heq] at H
        rw [StackAccumulationSpec.iterate_step_empty] at H
        cases H.1)
    (by
      intro a i hi st H
      cases i with
      | zero =>
        cases H.1
      | succ j =>
        have heq : st = (dummyStackSpec.step id)^[j] ⟨(), [], 0⟩ := rfl
        rw [heq] at H
        rw [StackAccumulationSpec.iterate_step_empty] at H
        cases H.1)
  exact h

end CslibFrontierTests.DisjointInstancesAndOracleReduction
