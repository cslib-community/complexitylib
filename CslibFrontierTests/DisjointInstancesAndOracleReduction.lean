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

private theorem countdownBranching_leafWord_length_le (s : ℕ) (w : List Bool)
    (hw : countdownBranching.IsLeafWord s w) : w.length ≤ s := by
  induction w generalizing s with
  | nil => exact Nat.zero_le s
  | cons b ws ih =>
    obtain ⟨hnot, htail⟩ := hw
    change ¬(s = 0) at hnot
    have hsub := ih (s - 1) htail
    simp only [List.length_cons]
    omega

private theorem countdownStackSpec_rounds_sufficient (n : ℕ)
    (L : List (List Bool)) (hnd : L.Nodup)
    (hL : ∀ w, w ∈ L ↔ countdownBranching.IsLeafWord n w) :
    2 * L.length ≤ countdownStackSpec.rounds n + 1 := by
  have hcard : L.toFinset.card ≤ ∑ j ∈ Finset.range (n + 1), n.choose j :=
    countdownBranching.card_le_sum_choose_of_isLeafWord
      (fun w hw => (hL w).mp (List.mem_toFinset.mp hw))
      (fun w hw => countdownBranching_leafWord_length_le n w
        ((hL w).mp (List.mem_toFinset.mp hw)))
      (fun w hw => (Finset.card_filter_le _ _).trans (by
        rw [Finset.card_range]
        exact countdownBranching_leafWord_length_le n w
          ((hL w).mp (List.mem_toFinset.mp hw))))
  rw [Nat.sum_range_choose, List.toFinset_card_of_nodup hnd] at hcard
  change 2 * L.length ≤ 2 * 2 ^ n + 1
  omega

/-- Exact proof for ALL `n : ℕ` via `StackAccumulationSpec.run_cappedSum_eq_root`, instantiated at
`n = 0, 1, 2, 3` (`1, 2, 4, 8` leaves). -/
theorem countdownStackSpec_run_total (n : ℕ) :
    (StackAccumulationSpec.run (encG := encNat) countdownStackSpec (fun _ => 1) n).total =
      2 ^ n := by
  refine StackAccumulationSpec.run_cappedSum_eq_root countdownStackSpec (fun _ => 1) n
    countdownBranching countdownBranching_terminating rfl rfl (fun _ _ => rfl)
    (fun _ => decide_eq_true_eq.to_iff)
    (fun _ _ => rfl) (countdownBranching_leafWord_length_le n)
    (countdownStackSpec_rounds_sufficient n)
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


lemma countdownStackSpec_foldl_acc (a : ℕ) (L' : List (List Bool)) :
    ((L'.map (countdownBranching.walk a)).foldl
      (fun (d : CappedNatAcc) (_s : ℕ) => countdownStackSpec.combine ⟨(), d, 1⟩)
      (countdownStackSpec.initAcc a)).cap = 2 ^ a ∧
    ((L'.map (countdownBranching.walk a)).foldl
      (fun (d : CappedNatAcc) (_s : ℕ) => countdownStackSpec.combine ⟨(), d, 1⟩)
      (countdownStackSpec.initAcc a)).total ≤ 2 ^ a := by
  simp only [countdownStackSpec]
  simp only [CappedNatAcc.foldl_add_eq (fun _ : ℕ => 1)
    (L'.map (countdownBranching.walk a)) (CappedNatAcc.init (2 ^ a)) (Nat.zero_le _)]
  exact ⟨rfl, Nat.min_le_left _ _⟩

lemma countdownStackSpec_stateBound (a i : ℕ) (hi : i ≤ countdownStackSpec.rounds a) :
    (encStackSearchState (encFinEnum Unit) encNat encCappedNatAcc
      ((countdownStackSpec.step (fun _ => 1))^[i] (countdownStackSpec.initState a))).length ≤
        1000 * (a + 1) ^ 2 := by
  have H := StackAccumulationSpec.run_eq_foldl_leafWords countdownStackSpec (fun _ => 1) a
    countdownBranching countdownBranching_terminating rfl
    (fun _ => decide_eq_true_eq.to_iff)
    (fun _ _ => rfl) (countdownBranching_leafWord_length_le a)
    (countdownStackSpec_rounds_sufficient a)
  obtain ⟨L, hnd, hL, hrun_eq, hstate⟩ := H
  obtain ⟨hlen, helem, ⟨L', hsub, hacc⟩⟩ := hstate i hi
  have hcap := countdownStackSpec_foldl_acc a L'
  rw [← hacc] at hcap
  obtain ⟨hcap1, hcap2⟩ := hcap
  have hlen_cap := CappedNatAcc.length_encCappedNatAcc_le_of_le_two_pow
    (by rw [hcap1]; exact hcap2) (by rw [hcap1])
  have hlen_stack : (encList encNat ((countdownStackSpec.step (fun _ => 1))^[i]
    (countdownStackSpec.initState a)).stack).length ≤ (a + 1) * (2 * (a + 1) + 1) + 1 := by
    have h_enc_list := length_encList_le encNat ((countdownStackSpec.step (fun _ => 1))^[i]
      (countdownStackSpec.initState a)).stack (b := a + 1) (by
      intro x hx
      obtain ⟨w, hw1, hw2, hw3⟩ := helem x hx
      have hwalk : ∀ (s : ℕ) (w : List Bool), countdownBranching.walk s w ≤ s := by
        intro s w
        induction w generalizing s with
        | nil => exact le_rfl
        | cons b ws ih => exact (ih (s - 1)).trans (by omega)
      have hx_eq : x = countdownBranching.walk a w := hw3.symm
      rw [hx_eq]
      have hx_le : countdownBranching.walk a w ≤ a := hwalk a w
      have hx2 : (encNat (countdownBranching.walk a w)).length ≤ a + 1 := by
        have h := length_encNat_mono hx_le
        have hpow : (encNat a).length ≤ a + 1 := (length_encNat_le_self a).trans (by omega)
        exact h.trans hpow
      exact hx2)
    have h_mul := Nat.mul_le_mul_right (2 * (a + 1) + 1) hlen
    omega
  have H_mul2 : (a + 1) * (2 * (a + 1) + 1) = 2 * (a + 1)^2 + (a + 1) := by ring
  rw [H_mul2] at hlen_stack
  simp only [encStackSearchState_apply, length_encPair]
  have hctx : ((encFinEnum Unit) ((countdownStackSpec.step (fun _ => 1))^[i]
    (countdownStackSpec.initState a)).ctx).length ≤ 10 := by
    have h := length_encFinEnum_lt ((countdownStackSpec.step (fun _ => 1))^[i]
      (countdownStackSpec.initState a)).ctx
    have hc : Nat.card Unit ≤ 10 := by simp
    omega
  have H_sq : a + 1 ≤ (a + 1)^2 := by
    have h1 : (a + 1) * 1 ≤ (a + 1) * (a + 1) :=
      Nat.mul_le_mul_left (a + 1) (Nat.le_add_left 1 a)
    have h2 : (a + 1) * 1 = a + 1 := by ring
    have h3 : (a + 1) * (a + 1) = (a + 1)^2 := by ring
    omega
  have H_sq2 : 1 ≤ (a + 1)^2 := by
    have h1 : 1 * 1 ≤ (a + 1) * (a + 1) :=
      Nat.mul_le_mul (Nat.le_add_left 1 a) (Nat.le_add_left 1 a)
    have h2 : (a + 1) * (a + 1) = (a + 1)^2 := by ring
    omega
  omega

example : ∃ c e : ℕ, ∃ Space : ℕ → ℕ,
    PolyBounded (fun a => (encUnary a).length) Space ∧
    ComputableInO (countdownStackSpec.run (fun _ => 1)) encUnary encCappedNatAcc
      (fun a => c * ((encUnary a).length + 1) ^ e +
        (countdownStackSpec.rounds a + 1) *
          (c * ((encUnary a).length + 1) ^ e + (encNat 1).length)) Space ∧
    ComputableInPolySpace (countdownStackSpec.run (fun _ => 1)) encUnary encCappedNatAcc := by
  have h := StackAccumulationSpec.exists_computableInO_run countdownStackSpec
    (g := fun _ => 1) (Tg := fun x => (encNat x).length) (Sg := fun x => (encNat x).length)
    (ComputableInO.const 1)
    (PolyBounded.self)
    (stateBound := fun a => 1000 * (a + 1) ^ 2) (ansBound := fun _ => (encNat 1).length)
    (leafMax := fun _ => (encNat 1).length)
    (PolyBounded.of_forall_le 1000 2 (fun a => by
      simp only [encUnary_apply, List.length_replicate]; exact le_rfl))
    (PolyBounded.const (encNat 1).length)
    countdownStackSpec_stateBound
    (by
      intro a i hi st H
      exact le_rfl)
    (by
      intro a i hi st H
      obtain ⟨hnot, hleaf⟩ := H
      change decide (st.stack.headD 0 = 0) = true at hleaf
      rw [decide_eq_true_eq] at hleaf
      change (encNat (st.stack.headD 0)).length ≤ _
      rw [hleaf]
      decide)
  exact h


end CslibFrontierTests.DisjointInstancesAndOracleReduction
