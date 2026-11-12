/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy
public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.IndependentSet
import CslibFrontier.Computability.Circuit.Boolean.Unbounded.Kleene
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.Nat.Doubling
import Mathlib.Data.Nat.Bitwise

/-!
# `W[P]` and slicewise polynomial time for the W-hierarchy

`Cslib.Complexity.WP`, denoted `W[P]` here, is the library's closure under `FPTReducible` of
weighted satisfiability of circuits over the unbounded fan-in basis of arbitrary weft and depth
(`WeightedCircuitSAT`). It inherits the arbitrary, potentially ineffective time and parameter
bounds of `FPTReducible`. Equivalence with the effective literature class is not established here:
[Flum and Grohe, Definition 3.1, p. 45][FlumGrohe2006] instead use restricted nondeterministic
multitape machines and computable bound functions. Dropping the weft and depth bounds of `WCS t d`
preserves encoded instances (`fptReducible_WCS_WeightedCircuitSAT`), so
`FPT ⊆ W[t] ⊆ W[P]` for every `t` (`W_subset_WP`, `FPT_subset_WP`), under the library's convention.

Exhaustive search over `k`-tuples of input positions places `WeightedCircuitSAT` in `XP`
(`WeightedCircuitSAT_mem_XP`) adapts [Cygan et al., Section 13.3, p. 436][CyganEtAl2015].
Their Definition 13.16 on p. 437 defines `W[t]`, not `W[P]`. The canonical
`WeightedCircuitSATInstance` encoding frames the circuit before the binary weight; the circuit
input count is unary. Circuits are straight-line programs with the basis conventions documented
in `CslibFrontier/Computability/Complexity/Parameterized/WHierarchy.lean`.
For a circuit on `n` inputs with encoded length `L`, we have `n ≤ L` and
`2 ^ n.size ≤ 2 (L + 1)`. Capping the weight at `k' = min n k`, a candidate tuple of `k'` input
indices is packed into `k' * n.size` bits, unpacked into `k'` coordinates via `BitString.listRows`
and `BitString.boundedBinaryValue`, turned into an `n`-bit assignment, checked for exact weight
`k`, and evaluated on the circuit's gate list in polynomial time by `Unbounded.kleeneEval`. With
`2 ^ (k' * n.size)` unary padding (`ComputableInPolyTime.exists_computableInO_pad`), the machine
runs within time `C 2 ^ (D k) (L + 1) ^ (D k + D)`. Closing `XP` under fpt-reductions then yields
`WP ⊆ XP` (`WP_subset_XP`), `W[t] ⊆ XP` (`W_subset_XP`), `WCS t d ∈ XP` (`WCS_mem_XP`), and
`IndependentSet, Clique ∈ XP` (`IndependentSet_mem_XP`, `Clique_mem_XP`).

## Main definitions

* `Cslib.Complexity.WP`: the library's reduction-closure convention for `W[P]`.
* `Cslib.Complexity.WPHard`: `W[P]`-hardness under fpt-reductions, the instance `FPTHard WP` of
  `Cslib.Complexity.FPTHard`.

## Main results

* `Cslib.Complexity.FPTReducible.mem_WP`: `W[P]` is closed under fpt-reductions.
* `Cslib.Complexity.WeightedCircuitSAT_mem_WP`, `Cslib.Complexity.WeightedCircuitSAT_wPHard`:
  `WeightedCircuitSAT` is `W[P]`-complete.
* `Cslib.Complexity.W_subset_WP`, `Cslib.Complexity.FPT_subset_WP`: `FPT ⊆ W[t] ⊆ W[P]`.
* `Cslib.Complexity.WP_eq_FPT_iff`: `W[P] = FPT` iff `WeightedCircuitSAT ∈ FPT`.
* `Cslib.Complexity.WeightedCircuitSAT_mem_XP`: `WeightedCircuitSAT ∈ XP`.
* `Cslib.Complexity.WP_subset_XP`, `Cslib.Complexity.W_subset_XP`, `Cslib.Complexity.WCS_mem_XP`:
  `W[P] ⊆ XP`, `W[t] ⊆ XP`, and `WCS t d ∈ XP`.
* `Cslib.Complexity.IndependentSet_mem_XP`, `Cslib.Complexity.Clique_mem_XP`: `IndependentSet` and
  `Clique` lie in `XP`.

## References

* [M. Cygan et al., *Parameterized Algorithms*, Section 13.3, pp. 436–437][CyganEtAl2015]
  (authors' May 30, 2016 PDF).
* [J. Flum, M. Grohe, *Parameterized Complexity Theory*, Definition 3.1, p. 45][FlumGrohe2006]
  (the effective machine definition, used only to contrast conventions).
-/

public section

namespace Cslib.Complexity

open Circuits Circuits.Boolean Circuits.Boolean.Unbounded Turing.MultiTapeTM

/-! ### The class `W[P]` -/

/-- The library's **`W[P]`**: the `FPTReducible` closure of `WeightedCircuitSAT`, with its binary
weight as parameter. Bounds may be arbitrary and potentially ineffective, as in `FPTReducible`;
equivalence with the effective literature class is not claimed. -/
@[expose] def WP {α : Type} (enc : α ↪ List Bool) (κ : α → ℕ) : Set (Set α) :=
  {A | FPTReducible enc encWeightedCircuitSAT κ WeightedCircuitSATInstance.weight
    A WeightedCircuitSAT}

/-- **`W[P]`-hardness**: every problem of `W[P]` fpt-reduces to `B`. The general lemmas, such as
`FPTHard.trans` and `FPTHard.subset_FPT`, apply through dot notation. -/
abbrev WPHard {β : Type} (enc : β ↪ List Bool) (κ : β → ℕ) (B : Set β) : Prop :=
  FPTHard @WP enc κ B

section WPBasic

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {κA : α → ℕ} {κB : β → ℕ}
  {A : Set α} {B : Set β}

/-- Membership in `W[P]`. -/
theorem mem_WP :
    A ∈ WP encA κA ↔ FPTReducible encA encWeightedCircuitSAT κA WeightedCircuitSATInstance.weight
      A WeightedCircuitSAT :=
  Iff.rfl

/-- **`W[P]` is closed under fpt-reductions.** -/
theorem FPTReducible.mem_WP (hAB : FPTReducible encA encB κA κB A B) (hB : B ∈ WP encB κB) :
    A ∈ WP encA κA :=
  hAB.trans hB

/-- `WeightedCircuitSAT` belongs to `W[P]`. -/
theorem WeightedCircuitSAT_mem_WP :
    WeightedCircuitSAT ∈ WP encWeightedCircuitSAT WeightedCircuitSATInstance.weight :=
  FPTReducible.refl _ _ _

/-- Forgetting the weft and depth bounds is an fpt-reduction from `WCS t d` to
`WeightedCircuitSAT`. -/
theorem fptReducible_WCS_WeightedCircuitSAT (t d : ℕ) :
    FPTReducible (encWCS t d) encWeightedCircuitSAT WCSInstance.weight
      WeightedCircuitSATInstance.weight (WCS t d) WeightedCircuitSAT :=
  FPTReducible.of_computableInPolyTime
    (f := fun x : WCSInstance t d => ⟨x.circuit.toCircuit, x.weight⟩)
    (encWeightedCircuitSAT_mk_polyTime
      ((encWCS_circuit_polyTime .id').of_enc_eq fun _ => rfl)
      (encWCS_weight_polyTime .id'))
    (h := id) (fun _ => le_rfl) fun _ => Iff.rfl

/-- **`W[t] ⊆ W[P]`** for every `t`. -/
theorem W_subset_WP (t : ℕ) : W t encA κA ⊆ WP encA κA :=
  fun _ ⟨d, hA⟩ => hA.trans (fptReducible_WCS_WeightedCircuitSAT t d)

/-- **`FPT ⊆ W[P]`.** -/
theorem FPT_subset_WP : FPT encA κA ⊆ WP encA κA :=
  (FPT_subset_W 0).trans (W_subset_WP 0)

/-- **`W[P]`-hardness is hardness for `WeightedCircuitSAT`.** -/
theorem wPHard_iff :
    WPHard encB κB B ↔
      FPTReducible encWeightedCircuitSAT encB WeightedCircuitSATInstance.weight κB
        WeightedCircuitSAT B :=
  ⟨fun h => h _ _ _ WeightedCircuitSAT_mem_WP, fun h _ _ _ _ hA => hA.trans h⟩

/-- `WeightedCircuitSAT` is `W[P]`-hard, hence `W[P]`-complete. -/
theorem WeightedCircuitSAT_wPHard :
    WPHard encWeightedCircuitSAT WeightedCircuitSATInstance.weight WeightedCircuitSAT :=
  wPHard_iff.2 (FPTReducible.refl _ _ _)

/-- Every `W[P]`-hard problem is `W[t]`-hard for every `t`. -/
theorem WPHard.wHard (hB : WPHard encB κB B) (t : ℕ) : WHard t encB κB B :=
  hB.mono fun _ _ => W_subset_WP t

/-- **`W[P] = FPT` iff `WeightedCircuitSAT ∈ FPT`.** -/
theorem WP_eq_FPT_iff :
    (∀ ⦃γ : Type⦄ (enc : γ ↪ List Bool) (κ : γ → ℕ), WP enc κ = FPT enc κ) ↔
      WeightedCircuitSAT ∈ FPT encWeightedCircuitSAT WeightedCircuitSATInstance.weight := by
  constructor
  · intro h
    rw [← h encWeightedCircuitSAT WeightedCircuitSATInstance.weight]
    exact WeightedCircuitSAT_mem_WP
  · intro h γ enc κ
    exact Set.Subset.antisymm (WeightedCircuitSAT_wPHard.subset_FPT h) FPT_subset_WP

end WPBasic

/-! ### Exhaustive search for `WeightedCircuitSAT` -/

namespace WeightedCircuitSAT

/-- On known Boolean inputs, Kleene evaluation of a well-formed gate list agrees with Boolean
`evalCode` mapped by `some`. -/
private theorem kleeneEval_map_some {n : ℕ} {x : List Bool} (hx : x.length = n)
    {gates : List (Unbounded.Op × List ℕ)}
    (h : Program.IsCodeFrom Unbounded.signature n 0 gates) :
    kleeneEval (x.map some) gates =
      (evalCode Unbounded.interpretation false x gates).map some := by
  induction gates using List.reverseRecOn with
  | nil => rfl
  | append_singleton gates g ih =>
    rw [Program.isCodeFrom_append, Program.isCodeFrom_cons, Nat.zero_add] at h
    obtain ⟨hgates, ⟨hg_len, hg_lt⟩, -⟩ := h
    rw [kleeneEval, List.foldl_append, List.foldl_cons, List.foldl_nil, ← kleeneEval,
      ih hgates, evalCode_append_singleton, List.map_append, List.map_singleton, kleeneStep]
    congr 2
    set vals := evalCode Unbounded.interpretation false x gates
    have hvals_len : vals.length = n + gates.length := by
      rw [length_evalCode, hx]
    have hargs : g.2.map ((vals.map some).getD · none) =
        (g.2.map (vals.getD · false)).map some := by
      rw [List.map_map]
      refine List.map_congr_left fun i hi => ?_
      have hi_lt : i < vals.length := hvals_len ▸ hg_lt i hi
      simp only [Function.comp_apply, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hi_lt, Option.map_some, Option.getD_some]
    have hlen' : g.2.length = Unbounded.signature.Arity g.1 := hg_len
    rw [hargs, ← ofFn_elim_eq_map (σ := Unbounded.signature) false vals g hlen', List.map_ofFn]
    exact kleeneInterpretation_some g.1 _

/-- Evaluating a circuit on an `n`-bit list via `kleeneEval` reads `some` of the circuit's output
at the first output wire of its code. -/
private theorem kleeneEval_circuit_eq_some {n : ℕ} (c : Circuit Unbounded.signature n 1)
    {x : List Bool} (hx : x.length = n) :
    (kleeneEval (x.map some) c.code.1).getD (c.code.2.getD 0 0) none =
      some (c.eval Unbounded.interpretation (BitString.ofList n x) 0) := by
  have hc : (Circuit.ofCode n 1 c.code).isSome := by simp
  obtain ⟨hcode, houts_len, houts_lt⟩ := Circuit.isSome_ofCode_iff.1 hc
  have ho : c.code.2.getD 0 0 = (c.outputs 0).toNat := by simp [Circuit.code]
  have hout_lt :
      (c.outputs 0).toNat < (evalCode Unbounded.interpretation false x c.code.1).length := by
    rw [length_evalCode, hx]
    exact houts_lt _ (by rw [← ho]; exact List.getElem_mem (by omega : 0 < c.code.2.length))
  rw [ho, kleeneEval_map_some hx hcode, Circuit.eval_eq_getD _ _ false,
    BitString.ofFn_ofList hx, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_eq_getElem hout_lt]
  rfl

/-- Number of bits used to encode a candidate `k'`-tuple of input indices below `n`. -/
private def searchBits (n k : ℕ) : ℕ :=
  min n k * n.size

/-- Unpack candidate index `r` into `k'` input positions, each capped at `n`. -/
private def candPositions (n k' r : ℕ) : List ℕ :=
  (BitString.listRows k' n.size (BitString.lowBits (k' * n.size) r)).map
    (BitString.boundedBinaryValue n)

/-- Characteristic `n`-bit input list of the positions unpacked from `r`. -/
private def candInput (n k' r : ℕ) : List Bool :=
  (List.range n).map fun i => decide (i ∈ candPositions n k' r)

/-- Check whether candidate `r` unpacks to a weight-`k` assignment satisfying `(n, gates, o)`. -/
private def checkCand (n : ℕ) (gates : List (Unbounded.Op × List ℕ)) (o k r : ℕ) : Bool :=
  let k' := min n k
  let x := candInput n k' r
  decide (k' = k) && decide (x.count true = k') &&
    ((kleeneEval (x.map some) gates).getD o none == some true)

/-- Search `N` candidate tuples for a weight-`k` satisfying assignment. -/
private def searchPadded (n : ℕ) (gates : List (Unbounded.Op × List ℕ)) (o k N : ℕ) : Bool :=
  (List.range N).any (checkCand n gates o k)

@[simp]
private theorem length_candInput (n k' r : ℕ) : (candInput n k' r).length = n := by
  simp [candInput]

/-- Correctness of the exhaustive search on `2 ^ searchBits n k` candidates. -/
private theorem searchPadded_eq_true_iff {n : ℕ} (c : Circuit Unbounded.signature n 1) (k : ℕ) :
    searchPadded n c.code.1 (c.code.2.getD 0 0) k (2 ^ searchBits n k) = true ↔
      c.SatisfiableWithWeight Unbounded.interpretation k := by
  simp only [searchPadded, List.any_eq_true, List.mem_range, checkCand, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨r, -, ⟨hk', hcnt⟩, heval⟩
    set x := candInput n (min n k) r
    have hx_len : x.length = n := length_candInput n (min n k) r
    rw [kleeneEval_circuit_eq_some c hx_len, Option.some.injEq] at heval
    refine ⟨BitString.ofList n x, ?_, heval⟩
    rw [← BitString.count_true_ofFn, BitString.ofFn_ofList hx_len, hcnt, hk']
  · rintro ⟨v, hwt, heval⟩
    have hkn : k ≤ n := hwt ▸ BitString.weight_le_length v
    have hk' : min n k = k := Nat.min_eq_right hkn
    let pos0 : List ℕ := ((List.finRange n).filter fun i => v i).map Fin.val
    have hpos0_len : pos0.length = k := by
      have hcnt : (List.ofFn v).count true = pos0.length := by
        simp only [pos0, List.length_map, List.ofFn_eq_map, List.count_eq_length_filter]
        rw [List.filter_map]
        simp [Function.comp_def]
      rw [← hcnt, BitString.count_true_ofFn, hwt]
    have hpos0_lt : ∀ j ∈ pos0, j < n := by
      intro j hj
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hj
      exact i.isLt
    have hpos0_mem : ∀ i : Fin n, i.val ∈ pos0 ↔ v i = true := by
      intro i
      simp only [pos0, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
      exact ⟨fun ⟨i', hi', heq⟩ => Fin.ext heq ▸ hi', fun hi => ⟨i, hi, rfl⟩⟩
    let words : List (List Bool) := pos0.map (BitString.binaryWord n.size)
    have hwords_len : ∀ w ∈ words, w.length = n.size := by
      intro w hw
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hw
      exact BitString.length_binaryWord ((hpos0_lt j hj).trans (Nat.lt_size_self n))
    let bs : List Bool := words.flatten
    have hbs_len : bs.length = k * n.size := by
      have hmap : words.map List.length = List.replicate pos0.length n.size := by
        refine List.ext_getElem (by simp [words]) fun idx h1 h2 => ?_
        simp only [List.getElem_map, List.getElem_replicate]
        exact hwords_len _ (List.getElem_mem _)
      rw [List.length_flatten, hmap, List.sum_replicate, smul_eq_mul, hpos0_len]
    let r : ℕ := (BitVec.ofBoolListLE bs).toNat
    have hr_lt : r < 2 ^ searchBits n k := by
      rw [searchBits, hk']
      exact (BitVec.isLt _).trans_eq (by simp [hbs_len])
    have hlow : BitString.lowBits (k * n.size) r = bs := by
      refine List.ext_getElem (by simp [hbs_len]) fun j hj1 hj2 => ?_
      simp only [BitString.lowBits, List.getElem_map, List.getElem_range, r, BitVec.testBit_toNat,
        BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hj2, Option.getD_some]
    have hcandPos : candPositions n k r = pos0 := by
      rw [candPositions, hlow]
      refine List.ext_getElem (by simp [hpos0_len]) fun idx h1 h2 => ?_
      simp only [BitString.length_listRows, List.length_map] at h1
      have hidx_words : idx < words.length := by simpa [words, hpos0_len] using h1
      simp only [List.getElem_map, BitString.listRows, List.getElem_range]
      rw [BitString.listRow_flatten hwords_len hidx_words,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx_words, Option.getD_some]
      simp only [words, List.getElem_map, BitString.boundedBinaryValue_eq,
        BitString.binaryValue_binaryWord]
      exact Nat.min_eq_right (hpos0_lt _ (List.getElem_mem _)).le
    have hcandIn : candInput n k r = List.ofFn v := by
      refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
      simp only [candInput, hcandPos, List.getElem_map, List.getElem_range, List.getElem_ofFn]
      rw [Bool.eq_iff_iff, decide_eq_true_eq]
      exact hpos0_mem ⟨i, by simpa using hi2⟩
    refine ⟨r, hr_lt, ⟨hk', ?_⟩, ?_⟩
    · rw [hk', hcandIn, BitString.count_true_ofFn, hwt]
    · rw [hk', kleeneEval_circuit_eq_some c (length_candInput n k r), hcandIn,
        BitString.ofList_ofFn, heval]

/-- Raw serialized representation of a `WeightedCircuitSAT` instance. -/
private abbrev RawIn : Type := (ℕ × (List (Unbounded.Op × List ℕ) × List ℕ)) × ℕ

private abbrev encRaw : RawIn ↪ List Bool :=
  encPair (encPair encUnary (Circuit.encCode Unbounded.encOp)) encNat

private theorem computableInPolyTime_searchBits_raw :
    ComputableInPolyTime (fun x : RawIn => searchBits x.1.1 x.2) encRaw encUnary := by
  have hn : ComputableInPolyTime (fun x : RawIn => x.1.1) encRaw encUnary := by fun_prop
  have hk : ComputableInPolyTime (fun x : RawIn => x.2) encRaw encNat := by fun_prop
  have hk' := ComputableInPolyTime.binary_min_unary' hn hk
  have hs := ComputableInPolyTime.binary_size.comp (ComputableInPolyTime.unary_to_binary.comp hn)
  exact ComputableInPolyTime.unary_mul' hk' hs

private abbrev CandState : Type := (RawIn × ℕ) × ℕ

private abbrev encCandState : CandState ↪ List Bool :=
  encPair (encPair encRaw encUnary) encUnary

private theorem computableInPolyTime_checkCand_state :
    ComputableInPolyTime
      (fun q : CandState =>
        checkCand q.1.1.1.1 q.1.1.1.2.1 (q.1.1.1.2.2.getD 0 0) q.1.1.2 q.2)
      encCandState encBool := by
  have hn : ComputableInPolyTime (fun q : CandState => q.1.1.1.1) encCandState encUnary := by
    fun_prop
  have hg : ComputableInPolyTime (fun q : CandState => q.1.1.1.2.1) encCandState
      (encList (Circuit.encGate Unbounded.encOp)) := by fun_prop
  have ho : ComputableInPolyTime (fun q : CandState => q.1.1.1.2.2.getD 0 0) encCandState
      encNat := by fun_prop
  have hk : ComputableInPolyTime (fun q : CandState => q.1.1.2) encCandState encNat := by
    fun_prop
  have hr_un : ComputableInPolyTime (fun q : CandState => q.2) encCandState encUnary := by
    fun_prop
  have hr_bin : ComputableInPolyTime (fun q : CandState => q.2) encCandState encNat :=
    ComputableInPolyTime.unary_to_binary.comp hr_un
  have hk' : ComputableInPolyTime (fun q : CandState => min q.1.1.1.1 q.1.1.2)
      encCandState encUnary :=
    ComputableInPolyTime.binary_min_unary' hn hk
  have hs : ComputableInPolyTime (fun q : CandState => q.1.1.1.1.size) encCandState encUnary :=
    ComputableInPolyTime.binary_size.comp (ComputableInPolyTime.unary_to_binary.comp hn)
  have hwidth : ComputableInPolyTime
      (fun q : CandState => min q.1.1.1.1 q.1.1.2 * q.1.1.1.1.size) encCandState encUnary :=
    ComputableInPolyTime.unary_mul' hk' hs
  have hlow := ComputableInPolyTime.bitsLow hwidth hr_bin
  have hrows := ComputableInPolyTime.bitsRowsWithInput hk' hs hlow
  have hpos : ComputableInPolyTime
      (fun q : CandState => candPositions q.1.1.1.1 (min q.1.1.1.1 q.1.1.2) q.2)
      encCandState (encList encUnary) :=
    ComputableInPolyTime.mapWithInput hrows
      (ComputableInPolyTime.bitsBoundedBinaryValueWithInput
        (hn.comp (ComputableInPolyTime.fst _ _)) (ComputableInPolyTime.snd _ _))
  have hx_bits : ComputableInPolyTime
      (fun q : CandState => candInput q.1.1.1.1 (min q.1.1.1.1 q.1.1.2) q.2)
      encCandState encBits :=
    ComputableInPolyTime.mapToBitsWithInput (ComputableInPolyTime.range.comp hn)
      (ComputableInPolyTime.decide_mem
        (hpos.comp (ComputableInPolyTime.fst _ _)) (ComputableInPolyTime.snd _ _))
  have hcnt : ComputableInPolyTime
      (fun q : CandState => (candInput q.1.1.1.1 (min q.1.1.1.1 q.1.1.2) q.2).count true)
      encCandState encUnary :=
    ComputableInPolyTime.bitsCountWithInput hx_bits (ComputableInPolyTime.const true)
  have hx_some : ComputableInPolyTime
      (fun q : CandState => (candInput q.1.1.1.1 (min q.1.1.1.1 q.1.1.2) q.2).map some)
      encCandState (encList (encOption encBool)) :=
    (ComputableInPolyTime.map
      (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.optionSome encBool))).comp
      (ComputableInPolyTime.bitsToList.comp hx_bits)
  have hkleene := computableInPolyTime_kleeneEval hx_some hg
  have hout_opt : ComputableInPolyTime
      (fun q : CandState =>
        (kleeneEval ((candInput q.1.1.1.1 (min q.1.1.1.1 q.1.1.2) q.2).map some)
          q.1.1.1.2.1).getD (q.1.1.1.2.2.getD 0 0) none)
      encCandState (encOption encBool) :=
    ComputableInPolyTime.listGetD_binary (encA := encOption encBool) none hkleene ho
  have hout_true : ComputableInPolyTime
      (fun q : CandState =>
        (kleeneEval ((candInput q.1.1.1.1 (min q.1.1.1.1 q.1.1.2) q.2).map some)
          q.1.1.1.2.1).getD (q.1.1.1.2.2.getD 0 0) none == some true)
      encCandState encBool :=
    (ComputableInPolyTime.of_finite (fun v : Option Bool => v == some true)).comp hout_opt
  have hk_eq : ComputableInPolyTime
      (fun q : CandState => decide (min q.1.1.1.1 q.1.1.2 = q.1.1.2)) encCandState encBool :=
    ((ComputableInPolyTime.unary_to_binary.comp hk').beq hk).of_enc_eq fun _ => by
      simp [beq_eq_decide]
  have hcnt_eq : ComputableInPolyTime
      (fun q : CandState =>
        decide ((candInput q.1.1.1.1 (min q.1.1.1.1 q.1.1.2) q.2).count true =
          min q.1.1.1.1 q.1.1.2))
      encCandState encBool :=
    (ComputableInPolyTime.unary_beq' hcnt hk').of_enc_eq fun _ => by simp [beq_eq_decide]
  exact ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' hk_eq hcnt_eq) hout_true

private theorem computableInPolyTime_searchPadded_raw :
    ComputableInPolyTime
      (fun p : RawIn × ℕ => searchPadded p.1.1.1 p.1.1.2.1 (p.1.1.2.2.getD 0 0) p.1.2 p.2)
      (encPair encRaw encUnary) encBool :=
  ComputableInPolyTime.anyWithInput
    (ComputableInPolyTime.range.comp (ComputableInPolyTime.snd encRaw encUnary))
    computableInPolyTime_checkCand_state

end WeightedCircuitSAT

/-! ### Membership in `XP` and inclusions -/

/-- **`WeightedCircuitSAT` is slicewise polynomial (`XP`)**
[Cygan et al., Section 13.3, p. 436][CyganEtAl2015]: brute force over
`k`-tuples of input wires runs in time `O(2 ^ (D k) * (L + 1) ^ (D k + D))` for encoded input
length `L` and target weight `k`. -/
theorem WeightedCircuitSAT_mem_XP :
    WeightedCircuitSAT ∈ XP encWeightedCircuitSAT WeightedCircuitSATInstance.weight := by
  have hpre : ComputableInPolyTime
      (fun x : WeightedCircuitSATInstance =>
        (((x.circuit.1, x.circuit.2.code), x.weight) : WeightedCircuitSAT.RawIn))
      encWeightedCircuitSAT WeightedCircuitSAT.encRaw :=
    encWeightedCircuitSAT_fields_deg.computableInPolyTime.of_enc_eq fun _ => rfl
  have hf : ComputableInPolyTime
      (fun p : WeightedCircuitSATInstance × ℕ =>
        WeightedCircuitSAT.searchPadded p.1.circuit.1 p.1.circuit.2.code.1
          (p.1.circuit.2.code.2.getD 0 0) p.1.weight p.2)
      (encPair encWeightedCircuitSAT encUnary) encBool :=
    WeightedCircuitSAT.computableInPolyTime_searchPadded_raw.comp
      ((hpre.comp (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _))
  have hν : ComputableInPolyTime
      (fun x : WeightedCircuitSATInstance =>
        WeightedCircuitSAT.searchBits x.circuit.1 x.weight)
      encWeightedCircuitSAT encUnary :=
    WeightedCircuitSAT.computableInPolyTime_searchBits_raw.comp hpre
  obtain ⟨C, D, hO⟩ := hf.exists_computableInO_pad hν
  have hbound (a : WeightedCircuitSATInstance) :
      C * 2 ^ (D * WeightedCircuitSAT.searchBits a.circuit.1 a.weight) *
          ((encWeightedCircuitSAT a).length + 1) ^ D ≤
        C * 2 ^ (D * a.weight) * ((encWeightedCircuitSAT a).length + 1) ^ (D * a.weight + D) := by
    set L := (encWeightedCircuitSAT a).length
    have hnL : a.circuit.1 ≤ L := by
      have h1 := Circuit.le_length_encCircuit (σ := Unbounded.signature) Unbounded.encOp a.circuit
      have h2 : (Unbounded.encCircuit 1 a.circuit).length ≤ L := by
        simpa only [L, encWeightedCircuitSAT_apply] using
          length_le_encPair_left (Unbounded.encCircuit 1) encNat (a.circuit, a.weight)
      exact h1.trans h2
    have h2s : 2 ^ a.circuit.1.size ≤ 2 * (L + 1) :=
      (Nat.two_pow_size_le a.circuit.1).trans (by omega)
    have hexp : 2 ^ (D * WeightedCircuitSAT.searchBits a.circuit.1 a.weight) ≤
        2 ^ (D * a.weight) * (L + 1) ^ (D * a.weight) := by
      calc 2 ^ (D * (min a.circuit.1 a.weight * a.circuit.1.size))
          = 2 ^ (a.circuit.1.size * (D * min a.circuit.1 a.weight)) := by
            rw [← Nat.mul_assoc, Nat.mul_comm (D * min a.circuit.1 a.weight) a.circuit.1.size]
        _ = (2 ^ a.circuit.1.size) ^ (D * min a.circuit.1 a.weight) :=
            Nat.pow_mul 2 a.circuit.1.size (D * min a.circuit.1 a.weight)
        _ ≤ (2 * (L + 1)) ^ (D * min a.circuit.1 a.weight) :=
            Nat.pow_le_pow_left h2s _
        _ ≤ (2 * (L + 1)) ^ (D * a.weight) :=
            Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left D (Nat.min_le_right _ _))
        _ = 2 ^ (D * a.weight) * (L + 1) ^ (D * a.weight) :=
            Nat.mul_pow 2 (L + 1) (D * a.weight)
    calc C * 2 ^ (D * WeightedCircuitSAT.searchBits a.circuit.1 a.weight) * (L + 1) ^ D
        ≤ C * (2 ^ (D * a.weight) * (L + 1) ^ (D * a.weight)) * (L + 1) ^ D :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left C hexp)
      _ = C * 2 ^ (D * a.weight) * ((L + 1) ^ (D * a.weight) * (L + 1) ^ D) := by ring
      _ = C * 2 ^ (D * a.weight) * (L + 1) ^ (D * a.weight + D) := by rw [← Nat.pow_add]
  refine mem_XP_iff_exists_computableInO.mpr
    ⟨_, fun k => C * 2 ^ (D * k), fun k => D * k + D, hO.mono_le hbound hbound, fun ⟨⟨n, c⟩, k⟩ =>
      (WeightedCircuitSAT.searchPadded_eq_true_iff c k).symm⟩

section XPConsequences

variable {α : Type} {encA : α ↪ List Bool} {κA : α → ℕ}

/-- **`W[P] ⊆ XP`.** -/
theorem WP_subset_XP : WP encA κA ⊆ XP encA κA :=
  fun _ hA => hA.mem_XP WeightedCircuitSAT_mem_XP

/-- **`W[t] ⊆ XP`** for every `t`, adapting [Cygan et al., Section 13.3,
pp. 436–437][CyganEtAl2015] to the library's reduction convention. -/
theorem W_subset_XP (t : ℕ) : W t encA κA ⊆ XP encA κA :=
  (W_subset_WP t).trans WP_subset_XP

/-- **`WCS t d ∈ XP`** for every weft bound `t` and depth bound `d`. -/
theorem WCS_mem_XP (t d : ℕ) : WCS t d ∈ XP (encWCS t d) WCSInstance.weight :=
  W_subset_XP t (WCS_mem_W t d)

/-- **`IndependentSet ∈ XP`** for the target size parameter `k`. -/
theorem IndependentSet_mem_XP :
    IndependentSet ∈ XP encIndependentSetInstance IndependentSetInstance.m :=
  W_subset_XP 1 IndependentSet_mem_W

/-- **`Clique ∈ XP`** for the target size parameter `k`. -/
theorem Clique_mem_XP : Clique ∈ XP encCliqueInstance CliqueInstance.m :=
  W_subset_XP 1 Clique_mem_W

end XPConsequences

end Cslib.Complexity
