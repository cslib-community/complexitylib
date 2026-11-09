/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORDecision
public import CslibFrontier.Cryptanalysis.AddXNORSubsetSum
public import CslibFrontier.Computability.Complexity.Problems.SubsetSum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# The encoded Add/XNOR reduction

[WangLvShenZhang2027], Theorem 1, PDF pp. 9–11. Zero source numbers
are discarded, retaining indexed positive entries. Targets above the total map
to a fixed no-instance. All other inputs use the actual guarded construction,
including the empty source list and target zero.

## Main results

* `toAddXNOR_mem_iff`, `toAddXNOR_polyTime`, `Decision_npComplete`:
  the actual total polynomial-time reduction and balanced NP-completeness.
* `toAddXNOR_width_le_input`, `toAddXNOR_encoding_length_le`:
  explicit linear width and quadratic output-encoding bounds.
* `threeSATToAddXNOR_mem_iff`, `threeSATToAddXNOR_polyTime`,
  `threeSATToAddXNOR_width_le`: the direct linear-parameter 3-SAT reduction.

-/

public section

namespace Cslib.Cryptanalysis.AddXNOR

open Turing.MultiTapeTM Cslib.Complexity
open scoped List

/-- Natural-number implementation of the alternating gadget operands. -/
@[expose] def rawGadgets (m : ℕ) (numbers : List ℕ) : List ℕ :=
  numbers.zipIdx.flatMap fun (s, i) =>
    let u := (3 * 2 ^ (4 * i + 2)) % 2 ^ m
    let v := (s * 2 ^ (4 * numbers.length + 2) - 3 * 2 ^ (4 * i + 2)) % 2 ^ m
    [u, v, u, v]

/-- All natural operands, including the initial constant and final correction. -/
@[expose] def rawOperands (m q : ℕ) (numbers : List ℕ) (target : ℕ) : List ℕ :=
  guardConstant numbers.length % 2 ^ m ::
    (rawGadgets m numbers ++ List.replicate q 0 ++
      [(2 ^ m - (guardConstant numbers.length + target * 2 ^ (4 * numbers.length + 3))
        % 2 ^ m) % 2 ^ m])

/-- The raw implementation is exactly the list of actual word operands. -/
theorem rawOperands_eq (m q : ℕ) (numbers : List ℕ) (target : ℕ) :
    rawOperands m q numbers target =
      (BitVec.ofNat m (guardConstant numbers.length)).toNat ::
        (subsetOperands m q numbers target).map BitVec.toNat := by
  simp only [rawOperands, subsetOperands, List.map_append, List.map_singleton,
    BitVec.toNat_neg, subsetTarget, BitVec.toNat_ofNat]
  congr 1
  congr 1
  · simp [rawGadgets, guardedOperands, subsetGuards, List.flatMap_map, List.map_flatMap,
      GuardBlock.operands, subsetGuard, BitVec.toNat_ofNat]

theorem rawOperands_mem_WordDecision {m q h : ℕ} (numbers : List ℕ) (target : ℕ)
    (hm : 4 * numbers.length + h + 3 ≤ m)
    (hpos : ∀ s ∈ numbers, 0 < s)
    (hsource : numbers.sum < 2 ^ h) (htarget : target ≤ numbers.sum) :
    (m, rawOperands m q numbers target) ∈ WordDecision ↔
      ∃ chosen : List ℕ, chosen <+ numbers ∧ chosen.sum = target := by
  rw [rawOperands_eq]
  have hfit : ∀ a ∈ (BitVec.ofNat m (guardConstant numbers.length)).toNat ::
      (subsetOperands m q numbers target).map BitVec.toNat, a < 2 ^ m := by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact BitVec.isLt _
    · obtain ⟨w, _, rfl⟩ := List.mem_map.1 ha
      exact w.isLt
  have hround : ((subsetOperands m q numbers target).map BitVec.toNat).map (BitVec.ofNat m) =
      subsetOperands m q numbers target := by
    simp only [List.map_map, Function.comp_def
      , BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id']
  have hinit : BitVec.ofNat m (BitVec.ofNat m (guardConstant numbers.length)).toNat =
      BitVec.ofNat m (guardConstant numbers.length) := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp only [WordDecision, Set.mem_ofPred_eq, List.tail_cons, List.headD_cons,
    hround, hinit]
  have hcount : 2 ≤ ((BitVec.ofNat m (guardConstant numbers.length)).toNat ::
      (subsetOperands m q numbers target).map BitVec.toNat).length := by
    simp only [List.length_cons, List.length_map]
    have h := subsetOperands_length m q numbers target
    omega
  exact ⟨fun h => (subset_reduction_iff numbers target hpos hsource htarget hm).1 h.2.2.2,
    fun h => ⟨by omega, hcount, hfit,
      (subset_reduction_iff numbers target hpos hsource htarget hm).2 h⟩⟩


private theorem rawOperands_mem_Decision {m q h : ℕ} (numbers : List ℕ) (target : ℕ)
    (hm : 4 * numbers.length + h + 3 ≤ m)
    (hlen : 4 * numbers.length + q + 2 = m) (hpos : ∀ s ∈ numbers, 0 < s)
    (hsource : numbers.sum < 2 ^ h) (htarget : target ≤ numbers.sum) :
    (m, rawOperands m q numbers target) ∈ Decision ↔
      ∃ chosen : List ℕ, chosen <+ numbers ∧ chosen.sum = target := by
  have hw := rawOperands_mem_WordDecision (q := q) numbers target hm hpos hsource htarget
  have hl : (rawOperands m q numbers target).length = m := by
    rw [rawOperands_eq]
    simpa only [List.length_cons, List.length_map, Nat.add_comm] using
      (subsetOperands_length m q numbers target).trans hlen
  have hdec : (m, rawOperands m q numbers target) ∈ Decision ↔
      (m, rawOperands m q numbers target) ∈ WordDecision := by
    simp only [Decision, WordDecision, Set.mem_ofPred_eq, hl]
    constructor
    · rintro ⟨hm, _, hfit, hs⟩
      exact ⟨by omega, hm, hfit, hs⟩
    · rintro ⟨_, hm, hfit, hs⟩
      exact ⟨hm, trivial, hfit, hs⟩
  exact hdec.trans hw

/-- Positive entries of the source list, retaining order and repetitions. -/
@[expose] def positiveNumbers (numbers : List ℕ) : List ℕ :=
  numbers.filter (fun s => decide (0 < s))

theorem positiveNumbers_sum (numbers : List ℕ) :
    (positiveNumbers numbers).sum = numbers.sum := by
  induction numbers with
  | nil => rfl
  | cons n ns ih =>
    by_cases hn : 0 < n
    · simpa [positiveNumbers, hn] using congrArg (n + ·) ih
    · have : n = 0 := by omega
      subst n
      simpa [positiveNumbers] using ih

theorem positiveNumbers_sublist_iff (numbers : List ℕ) (target : ℕ) :
    (∃ chosen : List ℕ, chosen <+ positiveNumbers numbers ∧ chosen.sum = target) ↔
      ∃ chosen : List ℕ, chosen <+ numbers ∧ chosen.sum = target := by
  constructor
  · rintro ⟨chosen, hc, ht⟩
    exact ⟨chosen, hc.trans List.filter_sublist, ht⟩
  · rintro ⟨chosen, hc, ht⟩
    exact ⟨positiveNumbers chosen, hc.filter _, (positiveNumbers_sum chosen).trans ht⟩

/-- Total reduction from binary Subset-Sum to balanced Add/XNOR. The word
width is `4r + size(S) + 3`, where `S` is the sum of the positive source numbers. -/
@[expose] def toAddXNOR (x : List ℕ × ℕ) : ℕ × List ℕ :=
  let numbers := positiveNumbers x.1
  let h := numbers.sum.size
  let m := 4 * numbers.length + h + 3
  if x.2 ≤ numbers.sum then (m, rawOperands m (h + 1) numbers x.2) else (2, [1, 0])

private theorem fixed_no_instance : (2, [1, 0]) ∉ Decision := by
  rintro ⟨_, _, _, bs, hlen, he⟩
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.length_cons, List.length_nil]
    at hlen he
  rcases bs with _ | ⟨b, bs⟩
  · simp at hlen
  have : bs = [] := by simpa using hlen
  subst bs
  cases b <;> simp [eval, step] at he

/-- Correctness on every source instance, including zeros, an empty list and
targets outside the attainable interval. -/
theorem toAddXNOR_mem_iff (x : List ℕ × ℕ) : toAddXNOR x ∈ Decision ↔ x ∈ SubsetSum := by
  rw [mem_SubsetSum_iff_sublist]
  unfold toAddXNOR
  dsimp only
  split_ifs with ht
  · rw [rawOperands_mem_Decision _ _ le_rfl (by omega)]
    · exact positiveNumbers_sublist_iff x.1 x.2
    · intro s hs
      exact of_decide_eq_true (List.mem_filter.1 hs).2
    · exact Nat.lt_size_self _
    · exact ht
  · constructor
    · exact fun h => (fixed_no_instance h).elim
    · rintro ⟨chosen, hc, he⟩
      have hsum : chosen.sum ≤ x.1.sum := hc.sum_le_sum (fun _ _ => Nat.zero_le _)
      rw [positiveNumbers_sum] at ht
      omega

private theorem guardConstant_eq_sum (r : ℕ) :
    guardConstant r = 1 + ((List.range r).map fun i => 2 ^ (4 * i + 2)).sum := by
  induction r with
  | zero => rfl
  | succ r ih => simp [guardConstant, ih, List.range_succ, List.map_append, Nat.add_assoc]

/-- Computing the guard word is polynomial-time from its unary guard count. -/
@[fun_prop] theorem guardConstant_polyTime :
    ComputableInPolyTime guardConstant encUnary encNat := by
  have h : ComputableInPolyTime
      (fun r => 1 + ((List.range r).map fun i => 2 ^ (4 * i + 2)).sum) encUnary encNat := by
    fun_prop
  exact h.of_enc_eq fun r => congrArg encNat (guardConstant_eq_sum r)

private theorem rawGadgets_polyTime :
    ComputableInPolyTime (fun p : ℕ × List ℕ => rawGadgets p.1 p.2)
      (encPair encUnary (encList encNat)) (encList encNat) := by
  unfold rawGadgets
  apply ComputableInPolyTime.flatMapWithInput
    (encA := encPair encNat encUnary)
  · exact .of_tidy ((ComputableTidilyInPolyTime.zipIdx encNat).comp
      (ComputableTidilyInPolyTime.snd encUnary (encList encNat)))
  · let input := encPair (encPair encUnary (encList encNat)) (encPair encNat encUnary)
    have hi : ComputableInPolyTime (fun p : (ℕ × List ℕ) × (ℕ × ℕ) => p.2.2)
        input encUnary := by fun_prop
    have hm : ComputableInPolyTime (fun p : (ℕ × List ℕ) × (ℕ × ℕ) => p.1.1)
        input encUnary := by fun_prop
    have hs : ComputableInPolyTime (fun p : (ℕ × List ℕ) × (ℕ × ℕ) => p.2.1)
        input encNat := by fun_prop
    have hn : ComputableInPolyTime (fun p : (ℕ × List ℕ) × (ℕ × ℕ) => p.1.2.length)
        input encUnary := .of_tidy ((ComputableTidilyInPolyTime.length encNat).comp (by fun_prop))
    have hpi := ComputableInPolyTime.binary_two_pow.comp
      (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' (.const 4) hi) (.const 2))
    have hpK := ComputableInPolyTime.binary_two_pow.comp
      (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' (.const 4) hn) (.const 2))
    have hM := ComputableInPolyTime.binary_two_pow.comp hm
    have hU := ComputableInPolyTime.binary_mul' (.const 3) hpi
    have hV := ComputableInPolyTime.binary_sub'
      (ComputableInPolyTime.binary_mul' hs hpK) hU
    have hu := ComputableInPolyTime.binary_mod.comp (hU.prod hM)
    have hv := ComputableInPolyTime.binary_mod.comp (hV.prod hM)
    exact ComputableInPolyTime.cons' hu (ComputableInPolyTime.cons' hv
      (ComputableInPolyTime.cons' hu (ComputableInPolyTime.cons' hv (.const []))))

theorem rawOperands_polyTime :
    ComputableInPolyTime
      (fun ((((m, q), numbers), target) : ((ℕ × ℕ) × List ℕ) × ℕ) =>
        rawOperands m q numbers target)
      (encPair (encPair (encPair encUnary encUnary) (encList encNat)) encNat) (encList encNat) := by
  let input := encPair (encPair (encPair encUnary encUnary) (encList encNat)) encNat
  have hm : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × ℕ => p.1.1.1) input encUnary := by
    fun_prop
  have hq : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × ℕ => p.1.1.2) input encUnary := by
    fun_prop
  have hn : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × ℕ => p.1.2)
      input (encList encNat) := by
    fun_prop
  have ht : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × ℕ => p.2) input encNat := by fun_prop
  have hM := ComputableInPolyTime.binary_two_pow.comp hm
  have hlen : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × ℕ => p.1.2.length)
    input encUnary :=
    .of_tidy ((ComputableTidilyInPolyTime.length encNat).comp hn.tidy)
  have hconstant := guardConstant_polyTime.comp hlen
  have hpow := ComputableInPolyTime.binary_two_pow.comp
    (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' (.const 4) hlen) (.const 3))
  have hP := ComputableInPolyTime.binary_add.comp
    (hconstant.prod (ComputableInPolyTime.binary_mul' ht hpow))
  have hD := ComputableInPolyTime.binary_mod.comp
    ((ComputableInPolyTime.binary_sub' hM
      (ComputableInPolyTime.binary_mod.comp (hP.prod hM))).prod hM)
  have hraw : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × List ℕ) × ℕ => rawGadgets p.1.1.1 p.1.2) input (encList encNat) := by
    have h := rawGadgets_polyTime.comp (hm.prod hn)
    dsimp only [Function.comp_def] at h
    exact h
  have hpadding : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × List ℕ) × ℕ => List.replicate p.1.1.2 (0 : ℕ)) input (encList encNat) :=
        by
    fun_prop
  exact ComputableInPolyTime.cons' (ComputableInPolyTime.binary_mod.comp (hconstant.prod hM))
    (ComputableInPolyTime.listAppend' (ComputableInPolyTime.listAppend' hraw hpadding)
      (ComputableInPolyTime.cons' hD (.const [])))

/-- The actual total construction is computed in polynomial time under the
binary Subset-Sum encoding and the explicit unary-width/binary-operand encoding. -/
@[fun_prop] theorem toAddXNOR_polyTime :
    ComputableInPolyTime toAddXNOR (encPair (encList encNat) encNat) encInstance := by
  let input := encPair (encList encNat) encNat
  have hnums : ComputableInPolyTime (fun p : List ℕ × ℕ => positiveNumbers p.1)
      input (encList encNat) := by
    unfold positiveNumbers
    fun_prop
  have hsum : ComputableInPolyTime (fun p : List ℕ × ℕ => (positiveNumbers p.1).sum)
      input encNat := by fun_prop
  have hh : ComputableInPolyTime (fun p : List ℕ × ℕ => (positiveNumbers p.1).sum.size)
      input encUnary := ComputableInPolyTime.binary_size.comp hsum
  have hlen := (ComputableTidilyInPolyTime.length encNat).comp hnums.tidy
  have hm : ComputableInPolyTime
      (fun p : List ℕ × ℕ => 4 * (positiveNumbers p.1).length + (positiveNumbers p.1).sum.size + 3)
      input encUnary :=
    ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.unary_mul' (.const 4) (.of_tidy hlen)) hh) (.const 3)
  have hraw : ComputableInPolyTime
      (fun p : List ℕ × ℕ => rawOperands
        (4 * (positiveNumbers p.1).length + (positiveNumbers p.1).sum.size + 3)
        ((positiveNumbers p.1).sum.size + 1) (positiveNumbers p.1) p.2)
      input (encList encNat) :=
    by
      have harg := ((hm.prod (ComputableInPolyTime.unary_add' hh (.const 1))).prod hnums).prod
        (ComputableInPolyTime.snd (encList encNat) encNat)
      have h := rawOperands_polyTime.comp harg
      dsimp only [Function.comp_def] at h
      exact h
  have htest : ComputableInPolyTime
      (fun p : List ℕ × ℕ => decide (p.2 ≤ (positiveNumbers p.1).sum)) input encBool := by
    fun_prop
  have h := htest.ite (hm.prod hraw) (.const (2, [1, 0]))
  unfold toAddXNOR
  dsimp only
  change ComputableInPolyTime _ input (encPair encUnary (encList encNat))
  simpa only [decide_eq_true_eq] using h

/-- Binary Subset-Sum many-one reduces to balanced Add/XNOR by the actual
constructed operand list. -/
theorem polyTimeReducible_SubsetSum_AddXNOR :
    PolyTimeReducible (encPair (encList encNat) encNat) encInstance SubsetSum Decision :=
  ⟨toAddXNOR, toAddXNOR_polyTime, fun x => (toAddXNOR_mem_iff x).symm⟩

/-- Theorem 1: balanced Add/XNOR is NP-complete under deterministic
polynomial-time many-one reductions, for the explicit encoding `encInstance`. -/
theorem Decision_npComplete : NPComplete encInstance Decision :=
  ⟨Decision_mem_NP, SubsetSum_npHard.trans polyTimeReducible_SubsetSum_AddXNOR⟩


/-- The concrete polynomial-time 3-SAT map, through the library's checked
base-eight digit construction (a carry-free variant of the source's decimal map). -/
@[expose] def threeSATToAddXNOR (φ : Cslib.Logic.PL.CNF ℕ) : ℕ × List ℕ :=
  toAddXNOR (ThreeSAT.toSubsetSum φ)

/-- The mapped instance is solvable exactly when the input is a 3-SAT instance. -/
theorem threeSATToAddXNOR_mem_iff (φ : Cslib.Logic.PL.CNF ℕ) :
    threeSATToAddXNOR φ ∈ Decision ↔ φ ∈ ThreeSAT := by
  rw [threeSATToAddXNOR, toAddXNOR_mem_iff, ThreeSAT.toSubsetSum_mem_iff]

/-- Polynomial time for the actual composed map. -/
@[fun_prop] theorem threeSATToAddXNOR_polyTime :
    ComputableInPolyTime threeSATToAddXNOR encCNF encInstance :=
  toAddXNOR_polyTime.comp ThreeSAT.computableInPolyTime_toSubsetSum

private theorem toAddXNOR_width_le (numbers : List ℕ) (target : ℕ) :
    (toAddXNOR (numbers, target)).1 ≤ 4 * numbers.length + numbers.sum.size + 3 := by
  unfold toAddXNOR
  dsimp only
  split_ifs
  · have hlen : (positiveNumbers numbers).length ≤ numbers.length := List.filter_sublist.length_le
    rw [positiveNumbers_sum]
    omega
  · omega

private theorem digitNumbers_length (φ : Cslib.Logic.PL.CNF ℕ) :
    (ThreeSAT.digitNumbers φ).length = 2 * (φ.distinctVars.length + φ.length) := by
  simp [ThreeSAT.digitNumbers, List.length_flatMap]
  omega

private theorem digitNumbers_sum_size (φ : Cslib.Logic.PL.CNF ℕ) :
    (ThreeSAT.digitNumbers φ).sum.size ≤ 5 * (φ.distinctVars.length + φ.length) := by
  have hb : ∀ n ∈ ThreeSAT.digitNumbers φ, n.size ≤ 3 * (φ.distinctVars.length + φ.length) := by
    intro n hn
    apply Nat.size_le.2
    have h := ThreeSAT.lt_of_mem_digitNumbers hn
    rwa [show 8 ^ (φ.distinctVars.length + φ.length) =
      2 ^ (3 * (φ.distinctVars.length + φ.length)) by rw [pow_mul]; rfl] at h
  have h := Nat.size_sum_le hb
  have hs := Nat.size_le_self (ThreeSAT.digitNumbers φ).length
  rw [digitNumbers_length] at h hs
  omega

/-- Theorem 2's linear-parameter 3-SAT reduction, with the explicit bound
`n ≤ 13(v + c) + 3`. Variables are counted by distinct occurrence; no dense
variable-label assumption is used. The library's base-eight construction also
handles repeated literals and tautological clauses without preprocessing. This
is the first conclusion of Theorem 2, not its sparsification consequence. -/
theorem threeSATToAddXNOR_width_le (φ : Cslib.Logic.PL.CNF ℕ) :
    (threeSATToAddXNOR φ).1 ≤ 13 * (φ.distinctVars.length + φ.length) + 3 := by
  unfold threeSATToAddXNOR ThreeSAT.toSubsetSum
  split_ifs
  · have h := toAddXNOR_width_le (ThreeSAT.digitNumbers φ) (ThreeSAT.digitTarget φ)
    have hs := digitNumbers_sum_size φ
    rw [digitNumbers_length] at h
    omega
  · have h := toAddXNOR_width_le [] 1
    simp only [List.length_nil, List.sum_nil, Nat.size_zero, Nat.mul_zero, Nat.zero_add] at h
    omega

/-- Exact encoded-length control for every fitting balanced instance. A word
has at most `m` binary digits; framing and unary width add the displayed terms. -/
theorem encoded_length_le {m : ℕ} {as : List ℕ} (hlen : as.length = m)
    (hfit : ∀ a ∈ as, a < 2 ^ m) :
    (encInstance (m, as)).length ≤ 2 * m ^ 2 + 3 * m + 1 := by
  have hsum : (as.map fun a => 2 * (encNat a).length + 1).sum ≤ as.length * (2 * m + 1) := by
    have hb : ∀ a ∈ as, 2 * (encNat a).length + 1 ≤ 2 * m + 1 := by
      intro a ha
      have h := Nat.size_le.2 (hfit a ha)
      change 2 * a.bits.length + 1 ≤ 2 * m + 1
      rw [Nat.size_eq_bits_len]
      omega
    calc
      _ ≤ (as.map fun _ => 2 * m + 1).sum := List.sum_le_sum hb
      _ = _ := by simp
  rw [encInstance, length_encPair]
  change 2 * (encUnary m).length + 1 + (encList encNat as).length ≤ _
  change 2 * (List.replicate m true).length + 1 + (encList encNat as).length ≤ _
  rw [List.length_replicate]
  rw [length_encList]
  rw [hlen] at hsum
  nlinarith


private theorem sum_size_le_encoding (numbers : List ℕ) :
    numbers.sum.size ≤ (encList encNat numbers).length := by
  have hsize : numbers.sum.size ≤ (numbers.map fun n => n.size + 1).sum := by
    induction numbers with
    | nil => simp
    | cons n ns ih =>
      simp only [List.sum_cons, List.map_cons]
      have h := Nat.size_add_le n ns.sum
      omega
  have hlen : (numbers.map fun n => n.size + 1).sum ≤ (encList encNat numbers).length := by
    rw [length_encList]
    apply List.sum_le_sum
    intro n _
    change n.size + 1 ≤ 2 * n.bits.length + 1
    rw [Nat.size_eq_bits_len]
    omega
  exact hsize.trans hlen

/-- Explicit linear construction width in the binary source encoding length. -/
theorem toAddXNOR_width_le_input (x : List ℕ × ℕ) :
    (toAddXNOR x).1 ≤ 5 * (encPair (encList encNat) encNat x).length + 3 := by
  have h := toAddXNOR_width_le x.1 x.2
  change (toAddXNOR x).1 ≤ 4 * x.1.length + x.1.sum.size + 3 at h
  have hsize := sum_size_le_encoding x.1
  have hlen := length_le_length_encList encNat x.1
  rw [length_encPair]
  omega

/-- Explicit quadratic encoded-output bound; the computation itself has the
separate machine-level polynomial-time certificate `toAddXNOR_polyTime`. -/
theorem toAddXNOR_encoding_length_le (x : List ℕ × ℕ) :
    (encInstance (toAddXNOR x)).length ≤
      2 * (5 * (encPair (encList encNat) encNat x).length + 3) ^ 2 +
        3 * (5 * (encPair (encList encNat) encNat x).length + 3) + 1 := by
  have hvalid : (toAddXNOR x).2.length = (toAddXNOR x).1 ∧
      ∀ a ∈ (toAddXNOR x).2, a < 2 ^ (toAddXNOR x).1 := by
    unfold toAddXNOR
    dsimp only
    split_ifs
    · rw [rawOperands_eq]
      constructor
      · simp only [List.length_cons, List.length_map]
        have h := subsetOperands_length
          (4 * (positiveNumbers x.1).length + (positiveNumbers x.1).sum.size + 3)
          ((positiveNumbers x.1).sum.size + 1) (positiveNumbers x.1) x.2
        omega
      · intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact BitVec.isLt _
        · obtain ⟨w, _, rfl⟩ := List.mem_map.1 ha
          exact w.isLt
    · norm_num
  have hlen := encoded_length_le hvalid.1 hvalid.2
  have hwidth := toAddXNOR_width_le_input x
  exact hlen.trans (by nlinarith)


end Cslib.Cryptanalysis.AddXNOR
