/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.ModP.GapP
public import Complexity.Computability.Complexity.Classes.SBP
public import Complexity.Computability.Complexity.Classes.US
public import Complexity.Computability.Complexity.Classes.WPP.Lowness
import Complexity.Computability.Complexity.Classes.Oracle.PolyTime
import Complexity.Computability.Complexity.Classes.SharpP.Aggregation
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Complexity.Classes.SharpP.Products
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Oracle
import Mathlib.Data.List.OfFn

/-!
# Oracle lowness of `#P`, `UP ∩ coUP`, `SPP`, and modular counting classes

This module completes the unsigned and signed counting oracle-lowness characterizations building on
`SharpP.Oracle` and `WPP.Lowness`:

* **Precomposition of `#P` and `GapP` with `FP^(UP ∩ coUP)` functions
  (`SharpP.encoded_comp_mem_of_computableInPolyTimeWithOracle`,
  `SharpP.comp_mem_of_computableInPolyTimeWithOracle`,
  `GapP.encoded_comp_mem_of_computableInPolyTimeWithOracle`,
  `GapP.comp_mem_of_computableInPolyTimeWithOracle`):** when `A ∈ UP ∩ coUP`, the
  instruction-by-step replay product `replayPathCount` of a deterministic polynomial-time oracle
  machine is an unsigned `#P` function that evaluates to `1` on the canonical oracle reply
  transcript and `0` on every other transcript. Multiplying by any outer `#P` function `F` of the
  replayed output and summing over all transcripts of length equal to the polynomial clock
  certifies `a ↦ F(a, output(f a))` in `#P` without subtraction.
* **Exact characterization of `#P` oracle lowness (`Low(#P) = UP ∩ coUP`,
  `SharpPWithOracle_eq_SharpP_of_mem_UP_of_mem_coUP`, `SharpPWithOracle_eq_SharpP_iff`,
  [Köbler, Schöning, Toda and Torán][KoeblerSchoeningTodaToran1992]):** an oracle `A` satisfies
  `#P^A = #P` if and only if `A ∈ UP ∩ coUP`.
* **Relativized unsigned counting decision classes (`UPWithOracle`, `coUPWithOracle`,
  `FewPWithOracle`, `USWithOracle`, `SBPWithFixedTarget`) and their `UP ∩ coUP` lowness:**
  relativizing `UP`, `coUP`, `FewP`, `US`, and fixed-threshold `SBP` via `SharpPWithOracle A enc`
  (with `SBPWithFixedTarget` retaining an unrelativized `FP` threshold `k : α → ℕ`, matching the
  fixed-target convention of `LWPPWithFixedTarget` and `WPPWithFixedTarget`) makes `UP ∩ coUP`
  low for each class, and characterizes `UP ∩ coUP` as the exact self-low class for `UP` and `coUP`
  (`UPWithOracle_eq_UP_and_coUPWithOracle_eq_coUP_iff`,
  `UPWithOracle_inter_coUPWithOracle_eq_iff`).
* **Exact characterization of `GapP` and `SPP` oracle lowness (`Low(GapP) = Low(SPP) = SPP`,
  `GapPWithOracle_eq_GapP_iff`, `SPPWithOracle_eq_SPP_iff`,
  [Fenner, Fortnow and Kurtz, Section 5][FennerFortnowKurtz1994]):** an oracle `A` satisfies
  `GapP^A = GapP` (equivalently `SPP^A = SPP`) if and only if `A ∈ SPP`, and every `FewP` oracle is
  low for `GapP`, `SPP`, `LWPPWithFixedTarget`, `WPPWithFixedTarget`, `C=P`, and `PP`.
* **Relativized modular counting classes (`ModPWithOracle`, `coModPWithOracle`,
  `ParityPWithOracle`), their `GapPWithOracle` residue characterizations, and `SPP` / `FewP` /
  `UP ∩ coUP` lowness:** for every positive modulus `0 < k`, `GapPWithOracle` functions have
  congruent `SharpPWithOracle` representatives (`GapPWithOracle.exists_SharpPWithOracle_emod`), so
  `ModPWithOracle k` and `coModPWithOracle k` are characterized by nonzero and zero residues of
  `GapPWithOracle` functions (`mem_ModPWithOracle_iff_exists_GapPWithOracle`,
  `mem_coModPWithOracle_iff_exists_GapPWithOracle`). `UP ∩ coUP` is low for `ModPWithOracle k` and
  `coModPWithOracle k` at every modulus `k : ℕ`, while for `0 < k`, `SPP` (and hence `FewP`) is low
  for `ModPWithOracle k`, `coModPWithOracle k`, and `ParityPWithOracle` via
  `GapPWithOracle_eq_GapP_of_mem_SPP` and `mem_ModP_iff_exists_GapP`.

All results use the library's strict polynomial-time adaptive word-oracle verifier model; no
nondeterministic oracle-machine counting characterization or `FP^A`-threshold `SBP` relativization
is claimed.

## Main definitions

* `Cslib.Complexity.UPWithOracle`, `Cslib.Complexity.coUPWithOracle`: unambiguous polynomial time
  and its complement relative to a language oracle.
* `Cslib.Complexity.FewPWithOracle`: polynomially bounded ambiguity relative to a language oracle.
* `Cslib.Complexity.USWithOracle`: unique-solution polynomial time relative to a language oracle.
* `Cslib.Complexity.SBPWithFixedTarget`: small bounded-error polynomial time relative to a language
  oracle with an unrelativized `FP` threshold.
* `Cslib.Complexity.ModPWithOracle`, `Cslib.Complexity.coModPWithOracle`,
  `Cslib.Complexity.ParityPWithOracle`: modular and parity counting classes relative to a language
  oracle.

## Main results

* `Cslib.Complexity.SharpP.encoded_comp_mem_of_computableInPolyTimeWithOracle`,
  `Cslib.Complexity.SharpP.comp_mem_of_computableInPolyTimeWithOracle`,
  `Cslib.Complexity.GapP.encoded_comp_mem_of_computableInPolyTimeWithOracle`,
  `Cslib.Complexity.GapP.comp_mem_of_computableInPolyTimeWithOracle`: `#P` and `GapP`
  precomposition with `FP^(UP ∩ coUP)` functions.
* `Cslib.Complexity.SharpPWithOracle_eq_SharpP_of_mem_UP_of_mem_coUP`,
  `Cslib.Complexity.SharpPWithOracle_eq_SharpP_iff`,
  `Cslib.Complexity.forall_SharpPWithOracle_eq_SharpP_iff`,
  `Cslib.Complexity.iUnion_SharpPWithOracle_UP_inter_coUP`: `#P^(UP ∩ coUP) = #P` and
  `Low(#P) = UP ∩ coUP`.
* `Cslib.Complexity.UPWithOracle_eq_UP_of_mem_UP_of_mem_coUP`,
  `Cslib.Complexity.coUPWithOracle_eq_coUP_of_mem_UP_of_mem_coUP`,
  `Cslib.Complexity.UPWithOracle_eq_UP_and_coUPWithOracle_eq_coUP_iff`,
  `Cslib.Complexity.UPWithOracle_inter_coUPWithOracle_eq_iff`,
  `Cslib.Complexity.FewPWithOracle_eq_FewP_of_mem_UP_of_mem_coUP`,
  `Cslib.Complexity.USWithOracle_eq_US_of_mem_UP_of_mem_coUP`,
  `Cslib.Complexity.SBPWithFixedTarget_eq_SBP_of_mem_UP_of_mem_coUP`.
* `Cslib.Complexity.GapPWithOracle_eq_GapP_iff`,
  `Cslib.Complexity.forall_GapPWithOracle_eq_GapP_iff`,
  `Cslib.Complexity.SPPWithOracle_eq_SPP_iff`,
  `Cslib.Complexity.forall_SPPWithOracle_eq_SPP_iff`,
  `Cslib.Complexity.iUnion_GapPWithOracle_SPP`,
  `Cslib.Complexity.iUnion_SPPWithOracle_SPP`.
* `Cslib.Complexity.GapPWithOracle.exists_SharpPWithOracle_emod`,
  `Cslib.Complexity.mem_ModPWithOracle_iff_exists_GapPWithOracle`,
  `Cslib.Complexity.mem_coModPWithOracle_iff_exists_GapPWithOracle`,
  `Cslib.Complexity.ModPWithOracle_eq_ModP_of_mem_UP_of_mem_coUP`,
  `Cslib.Complexity.ModPWithOracle_eq_ModP_of_mem_SPP`,
  `Cslib.Complexity.coModPWithOracle_eq_coModP_of_mem_SPP`,
  `Cslib.Complexity.ParityPWithOracle_eq_ParityP_of_mem_SPP`,
  `Cslib.Complexity.ModPWithOracle_eq_ModP_of_mem_FewP`,
  `Cslib.Complexity.ParityPWithOracle_eq_ParityP_of_mem_FewP`.

## References

* [J. Köbler, U. Schöning, S. Toda, J. Torán, *Turing Machines with Few Accepting Computations and
  Low Sets for PP*][KoeblerSchoeningTodaToran1992]
* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994]
* [U. Schöning, *Probabilistic Complexity Classes and Lowness*][Schoening1989]
* [L. Fortnow, *Counting Complexity*][Fortnow1997]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeMachine
  _root_.Turing.MultiTapePTM Finset

variable {α β : Type} {enc : α ↪ List Bool} {output : β ↪ List Bool} {A : Set (List Bool)} {k : ℕ}

/-! ### Unsigned step-certified oracle replay and `#P` precomposition with `FP^(UP ∩ coUP)` -/

section Replay

variable {tapes : ℕ} {Control Operation : Type} [DecidableEq Operation]

/-- The `#P` factor certifying instruction `x.2` of transcript `x.1.2` on instance `x.1.1`. -/
private def replayStepFactor (machine : MultiTapePTM tapes Bool Control Operation)
    (input : α → List Bool) (fYes fNo : List Bool → ℕ)
    (x : (α × List Bool) × ℕ) : ℕ :=
  let cfg := machine.replayPrefix (input x.1.1) x.1.2 x.2
  if (machine.pendingQuery cfg).isSome then
    let q := machine.pendingRequest cfg
    if x.1.2.getD x.2 false then fYes q else fNo q
  else
    if x.1.2.getD x.2 false then 0 else 1

/-- The `#P` product certifying all instructions of transcript `x.2` on instance `x.1`. -/
private def replayPathCount (machine : MultiTapePTM tapes Bool Control Operation)
    (input : α → List Bool) (fYes fNo : List Bool → ℕ)
    (x : α × List Bool) : ℕ :=
  ∏ i ∈ range x.2.length, replayStepFactor machine input fYes fNo (x, i)

/-- The `#P` sum over all transcripts of length `T a` weighted by an outer `#P` function `F` of the
replayed output. -/
private def replayWeightedSum (machine : MultiTapePTM tapes Bool Control Operation)
    (input : α → List Bool) (T : α → ℕ) (fYes fNo : List Bool → ℕ)
    (F : α × List Bool → ℕ) (a : α) : ℕ :=
  ∑ w : Fin (T a) → Bool,
    replayPathCount machine input fYes fNo (a, List.ofFn w) *
      F (a, machine.replayOutput (input a) (List.ofFn w))

private theorem replayStepFactor_mem_SharpP [Finite Control] [Finite Operation]
    (machine : MultiTapePTM tapes Bool Control Operation) {input : α → List Bool}
    {fYes fNo : List Bool → ℕ}
    (hinput : ComputableInPolyTime input enc encBits)
    (hYes : fYes ∈ SharpP encBits) (hNo : fNo ∈ SharpP encBits) :
    replayStepFactor machine input fYes fNo ∈ SharpP (encPair (encPair enc encBits) encUnary) := by
  let _ := Fintype.ofFinite Operation
  let cfg : (α × List Bool) × ℕ → FiniteConfig tapes Bool Control Operation :=
    fun x => machine.replayPrefix (input x.1.1) x.1.2 x.2
  have hcfg : ComputableInPolyTime cfg
      (encPair (encPair enc encBits) encUnary) encFiniteConfig :=
    machine.computableInPolyTime_replayPrefix.comp (g := fun x : (α × List Bool) × ℕ =>
      ((input x.1.1, x.1.2), x.2)) (by fun_prop)
  have hquery : ComputableInPolyTime
      (fun x => (machine.pendingQuery (cfg x)).isSome)
      (encPair (encPair enc encBits) encUnary) encBool :=
    (ComputableInPolyTime.of_finite Option.isSome).comp
      (machine.pendingQuery_pt.computableInPolyTime.comp hcfg)
  have hreq : ComputableInPolyTime
      (fun x => machine.pendingRequest (cfg x))
      (encPair (encPair enc encBits) encUnary) encBits :=
    machine.pendingRequest_pt.computableInPolyTime.comp hcfg
  have hbit : ComputableInPolyTime
      (fun x : (α × List Bool) × ℕ => x.1.2.getD x.2 false)
      (encPair (encPair enc encBits) encUnary) encBool := by fun_prop
  exact SharpP.ite_mem hquery
    (SharpP.ite_mem hbit (SharpP.comp_mem hYes hreq)
      (SharpP.comp_mem hNo hreq))
    (SharpP.ite_mem hbit SharpP.zero_mem SharpP.one_mem)

private theorem replayPathCount_mem_SharpP [Finite Control] [Finite Operation]
    (machine : MultiTapePTM tapes Bool Control Operation) {input : α → List Bool}
    {fYes fNo : List Bool → ℕ}
    (hinput : ComputableInPolyTime input enc encBits)
    (hYes : fYes ∈ SharpP encBits) (hNo : fNo ∈ SharpP encBits) :
    replayPathCount machine input fYes fNo ∈ SharpP (encPair enc encBits) :=
  SharpP.prod_range_mem (replayStepFactor_mem_SharpP machine hinput hYes hNo)
    (r := fun x : α × List Bool => x.2.length) (by fun_prop)

private theorem replayWeightedSum_mem_SharpP [Finite Control] [Finite Operation]
    (machine : MultiTapePTM tapes Bool Control Operation) {input : α → List Bool}
    {T : α → ℕ} {fYes fNo : List Bool → ℕ} {F : α × List Bool → ℕ}
    (hinput : ComputableInPolyTime input enc encBits)
    (hT : ComputableInPolyTime T enc encUnary)
    (hYes : fYes ∈ SharpP encBits) (hNo : fNo ∈ SharpP encBits)
    (hF : F ∈ SharpP (encPair enc encBits)) :
    replayWeightedSum machine input T fYes fNo F ∈ SharpP enc := by
  have hpath := replayPathCount_mem_SharpP machine hinput hYes hNo
  have hpair : ComputableInPolyTime
      (fun x : α × List Bool => (input x.1, x.2))
      (encPair enc encBits) (encPair encBits encBits) := by fun_prop
  have hout : (fun x : α × List Bool => F (x.1, machine.replayOutput (input x.1) x.2)) ∈
      SharpP (encPair enc encBits) :=
    SharpP.comp_mem hF ((ComputableInPolyTime.fst enc encBits).prod
      (machine.computableInPolyTime_replayOutput.comp hpair))
  exact SharpP.sum_bits_mem (SharpP.mul_mem hpath hout) hT

private theorem replayStepFactor_pos_iff (machine : MultiTapePTM tapes Bool Control Operation)
    (input : α → List Bool) {fYes fNo : List Bool → ℕ} {g : List Bool → Bool}
    (hYes : ∀ q, g q = true ↔ 0 < fYes q) (hNo : ∀ q, g q = false ↔ 0 < fNo q)
    (a : α) (answers : List Bool) (i : ℕ) :
    0 < replayStepFactor machine input fYes fNo ((a, answers), i) ↔
      answers.getD i false =
        let cfg := machine.replayPrefix (input a) answers i
        if (machine.pendingQuery cfg).isSome then g (machine.pendingRequest cfg) else false := by
  unfold replayStepFactor
  dsimp only
  set cfg := machine.replayPrefix (input a) answers i
  cases hq : (machine.pendingQuery cfg).isSome
  · cases hb : answers.getD i false <;> simp
  · cases hb : answers.getD i false
    · simp [← hNo (machine.pendingRequest cfg)]
    · simp [← hYes (machine.pendingRequest cfg)]

private theorem take_eq_take_oracleReplies_of_forall_getD
    (machine : MultiTapePTM tapes Bool Control Operation) (g : List Bool → Bool)
    (input answers : List Bool)
    (h : ∀ i < answers.length, answers.getD i false =
      let cfg := machine.replayPrefix input answers i
      if (machine.pendingQuery cfg).isSome then g (machine.pendingRequest cfg) else false) :
    ∀ m ≤ answers.length,
      answers.take m = (machine.oracleReplies g answers.length input).take m := by
  set oracle := machine.oracleReplies g answers.length input
  have hlen_or : oracle.length = answers.length :=
    machine.length_oracleReplies g answers.length input
  intro m hm
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm_lt : m < answers.length := Nat.lt_of_succ_le hm
    have hm_or : m < oracle.length := hlen_or ▸ hm_lt
    have ih_m : answers.take m = oracle.take m := ih hm_lt.le
    have hcfg : machine.replayPrefix input answers m =
        machine.replayPrefix input oracle m := by
      simp only [replayPrefix, ih_m]
    have hbit : answers[m] = oracle[m] := by
      rw [← List.getD_eq_getElem answers false hm_lt,
        ← List.getD_eq_getElem oracle false hm_or,
        h m hm_lt, machine.getD_oracleReplies g answers.length input m hm_lt, hcfg]
    calc
      answers.take (m + 1) = answers.take m ++ [answers[m]] :=
        List.take_succ_eq_append_getElem hm_lt
      _ = oracle.take m ++ [oracle[m]] := by rw [ih_m, hbit]
      _ = oracle.take (m + 1) := (List.take_succ_eq_append_getElem hm_or).symm

private theorem replayPathCount_pos_iff (machine : MultiTapePTM tapes Bool Control Operation)
    (input : α → List Bool) {fYes fNo : List Bool → ℕ} {g : List Bool → Bool}
    (hYes : ∀ q, g q = true ↔ 0 < fYes q) (hNo : ∀ q, g q = false ↔ 0 < fNo q)
    (a : α) (answers : List Bool) :
    0 < replayPathCount machine input fYes fNo (a, answers) ↔
      answers = machine.oracleReplies g answers.length (input a) := by
  unfold replayPathCount
  rw [CanonicallyOrderedAdd.prod_pos]
  simp only [mem_range,
    replayStepFactor_pos_iff machine input hYes hNo a answers]
  constructor
  · intro h
    have htake := take_eq_take_oracleReplies_of_forall_getD machine g (input a) answers h
      answers.length le_rfl
    have hlen : (machine.oracleReplies g answers.length (input a)).length = answers.length :=
      machine.length_oracleReplies g answers.length (input a)
    rwa [List.take_length, List.take_of_length_le hlen.le] at htake
  · intro h i hi
    have hstep := machine.getD_oracleReplies g answers.length (input a) i hi
    rwa [← h] at hstep

private theorem replayStepFactor_le_one (machine : MultiTapePTM tapes Bool Control Operation)
    (input : α → List Bool) {fYes fNo : List Bool → ℕ}
    (hYes_le : ∀ q, fYes q ≤ 1) (hNo_le : ∀ q, fNo q ≤ 1)
    (x : (α × List Bool) × ℕ) :
    replayStepFactor machine input fYes fNo x ≤ 1 := by
  unfold replayStepFactor
  dsimp only
  split_ifs <;> first | exact hYes_le _ | exact hNo_le _ | omega

private theorem replayPathCount_le_one (machine : MultiTapePTM tapes Bool Control Operation)
    (input : α → List Bool) {fYes fNo : List Bool → ℕ}
    (hYes_le : ∀ q, fYes q ≤ 1) (hNo_le : ∀ q, fNo q ≤ 1)
    (x : α × List Bool) :
    replayPathCount machine input fYes fNo x ≤ 1 :=
  Finset.prod_le_one fun i _ =>
    replayStepFactor_le_one machine input hYes_le hNo_le (x, i)

private theorem replayWeightedSum_eq_of_le_one
    (machine : MultiTapePTM tapes Bool Control Operation)
    (input : α → List Bool) (T : α → ℕ) {fYes fNo : List Bool → ℕ} {g : List Bool → Bool}
    (hYes_le : ∀ q, fYes q ≤ 1) (hNo_le : ∀ q, fNo q ≤ 1)
    (hYes : ∀ q, g q = true ↔ 0 < fYes q) (hNo : ∀ q, g q = false ↔ 0 < fNo q)
    (F : α × List Bool → ℕ) (a : α) :
    replayWeightedSum machine input T fYes fNo F a =
      F (a, machine.replayOutput (input a) (machine.oracleReplies g (T a) (input a))) := by
  have hlen : (machine.oracleReplies g (T a) (input a)).length = T a :=
    machine.length_oracleReplies g (T a) (input a)
  let w₀ : Fin (T a) → Bool :=
    fun i => (machine.oracleReplies g (T a) (input a))[i.val]'(by omega)
  have hw₀ : List.ofFn w₀ = machine.oracleReplies g (T a) (input a) :=
    (List.ofFn_congr hlen.symm _).trans List.ofFn_getElem
  unfold replayWeightedSum
  rw [Finset.sum_eq_single w₀]
  · have hpos : 0 < replayPathCount machine input fYes fNo (a, List.ofFn w₀) := by
      rw [replayPathCount_pos_iff machine input hYes hNo, List.length_ofFn]
      exact hw₀
    have hle := replayPathCount_le_one machine input hYes_le hNo_le (a, List.ofFn w₀)
    have heq : replayPathCount machine input fYes fNo (a, List.ofFn w₀) = 1 := by omega
    rw [heq, one_mul, hw₀]
  · intro w _ hw
    have hnot : ¬0 < replayPathCount machine input fYes fNo (a, List.ofFn w) := by
      rw [replayPathCount_pos_iff machine input hYes hNo, List.length_ofFn, ← hw₀]
      exact fun h => hw (List.ofFn_injective h)
    have hz : replayPathCount machine input fYes fNo (a, List.ofFn w) = 0 := by omega
    rw [hz, zero_mul]
  · intro hmem
    exact False.elim (hmem (mem_univ w₀))

end Replay

open Classical in
/-- **`#P` precomposition with encoded `FP^(UP ∩ coUP)` outputs.** If `A ∈ UP ∩ coUP`,
`f : α → β` is computable in polynomial time relative to `A`, and `F : α × List Bool → ℕ` belongs to
`SharpP (encPair enc encBits)`, then `a ↦ F (a, output (f a))` belongs to `SharpP enc`. -/
theorem SharpP.encoded_comp_mem_of_computableInPolyTimeWithOracle
    {f : α → β} {F : α × List Bool → ℕ}
    (hA_up : A ∈ UP encBits) (hA_coup : A ∈ coUP encBits)
    (hf : ComputableInPolyTimeWithOracle A f enc output)
    (hF : F ∈ SharpP (encPair enc encBits)) :
    (fun a => F (a, output (f a))) ∈ SharpP enc := by
  obtain ⟨fYes, hYes_mem, hYes_le, hYes_iff⟩ := hA_up
  obtain ⟨fNo, hNo_mem, hNo_le, hNo_iff⟩ := hA_coup
  obtain ⟨program, hcert, hprogram⟩ := hf
  obtain ⟨tapes, m, machine, c, d, hrun⟩ := hcert.exists_fin_run_pure_false
  let g : List Bool → Bool := fun q => decide (q ∈ A)
  have hYes' (q : List Bool) : g q = true ↔ 0 < fYes q := by
    have hle := hYes_le q
    rw [show (0 < fYes q) ↔ fYes q = 1 by omega]
    simp only [g, decide_eq_true_eq, hYes_iff q]
  have hNo' (q : List Bool) : g q = false ↔ 0 < fNo q := by
    have hle := hNo_le q
    rw [show (0 < fNo q) ↔ fNo q = 1 by omega]
    simp only [g, decide_eq_false_iff_not, ← Set.mem_compl_iff, hNo_iff q]
  let T : α → ℕ := fun a => c * ((enc a).length + 1) ^ d
  have hT : ComputableInPolyTime T enc encUnary :=
    ((ComputableInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
      (ComputableInPolyTime.encoding_length enc)).of_enc_eq fun a => by simp [T]
  have hinput : ComputableInPolyTime (fun a : α => enc a) enc encBits :=
    ComputableInPolyTime.id'
  have hmem := replayWeightedSum_mem_SharpP machine hinput hT hYes_mem hNo_mem hF
  convert hmem using 1
  funext a
  rw [replayWeightedSum_eq_of_le_one machine (fun a => enc a) T hYes_le hNo_le hYes' hNo' F a,
    machine.replayOutput_oracleReplies g (T a) (enc a)]
  have hrun_a := hrun a (languageOracle A)
  rw [hprogram a] at hrun_a
  change F (a, output (f a)) = _
  rw [← hrun_a]
  rfl

/-- **`#P` precomposition with word-valued `FP^(UP ∩ coUP)` functions.** -/
theorem SharpP.comp_mem_of_computableInPolyTimeWithOracle
    {f : α → List Bool} {F : List Bool → ℕ}
    (hA_up : A ∈ UP encBits) (hA_coup : A ∈ coUP encBits)
    (hf : ComputableInPolyTimeWithOracle A f enc encBits)
    (hF : F ∈ SharpP encBits) :
    (F ∘ f) ∈ SharpP enc :=
  SharpP.encoded_comp_mem_of_computableInPolyTimeWithOracle hA_up hA_coup hf
    (SharpP.comp_mem hF (.snd enc encBits))

/-- **`GapP` precomposition with encoded `FP^(UP ∩ coUP)` outputs.** -/
theorem GapP.encoded_comp_mem_of_computableInPolyTimeWithOracle
    {f : α → β} {G : α × List Bool → ℤ}
    (hA_up : A ∈ UP encBits) (hA_coup : A ∈ coUP encBits)
    (hf : ComputableInPolyTimeWithOracle A f enc output)
    (hG : G ∈ GapP (encPair enc encBits)) :
    (fun a => G (a, output (f a))) ∈ GapP enc := by
  obtain ⟨F₁, hF₁, F₂, hF₂, hG_eq⟩ := hG
  refine ⟨_, SharpP.encoded_comp_mem_of_computableInPolyTimeWithOracle hA_up hA_coup hf hF₁,
    _, SharpP.encoded_comp_mem_of_computableInPolyTimeWithOracle hA_up hA_coup hf hF₂,
    fun a => hG_eq (a, output (f a))⟩

/-- **`GapP` precomposition with word-valued `FP^(UP ∩ coUP)` functions.** -/
theorem GapP.comp_mem_of_computableInPolyTimeWithOracle
    {f : α → List Bool} {G : List Bool → ℤ}
    (hA_up : A ∈ UP encBits) (hA_coup : A ∈ coUP encBits)
    (hf : ComputableInPolyTimeWithOracle A f enc encBits)
    (hG : G ∈ GapP encBits) :
    (G ∘ f) ∈ GapP enc :=
  GapP.encoded_comp_mem_of_computableInPolyTimeWithOracle hA_up hA_coup hf
    (GapP.comp_mem hG (.snd enc encBits))

/-! ### Exact characterization of `#P` oracle lowness (`Low(#P) = UP ∩ coUP`) -/

/-- **`UP ∩ coUP` is low for `#P`**
([Köbler, Schöning, Toda and Torán][KoeblerSchoeningTodaToran1992]): for every oracle
`A ∈ UP encBits ∩ coUP encBits` and every instance encoding `enc`,
`SharpPWithOracle A enc = SharpP enc`. -/
theorem SharpPWithOracle_eq_SharpP_of_mem_UP_of_mem_coUP
    (hA_up : A ∈ UP encBits) (hA_coup : A ∈ coUP encBits) (enc : α ↪ List Bool) :
    SharpPWithOracle A enc = SharpP enc := by
  apply Set.Subset.antisymm ?_ (SharpP_subset_SharpPWithOracle A enc)
  rintro f ⟨p, V, hV, hf⟩
  have hbit : ComputableInPolyTime
      (fun x : (α × List Bool) × List Bool => x.2.headD false)
      (encPair (encPair enc encBits) encBits) encBool := by fun_prop
  have hF_ind : (fun x : (α × List Bool) × List Bool => if x.2.headD false then 1 else 0) ∈
      SharpP (encPair (encPair enc encBits) encBits) :=
    SharpP.ite_mem hbit SharpP.one_mem SharpP.zero_mem
  have hV_sharp : (fun x : α × List Bool => if V x then 1 else 0) ∈
      SharpP (encPair enc encBits) := by
    convert SharpP.encoded_comp_mem_of_computableInPolyTimeWithOracle hA_up hA_coup hV hF_ind
      using 1
    funext x
    simp [encBool_apply]
  have hr : ComputableInPolyTime (fun a : α => p.eval (enc a).length) enc encUnary := by
    fun_prop
  have hsum := SharpP.sum_bits_mem hV_sharp hr
  convert hsum using 1
  funext a
  simp only [hf a, acceptCount, card_filter]

/-- **`UP ∩ coUP` is low for `GapP`** (`GapPWithOracle A enc = GapP enc`). -/
theorem GapPWithOracle_eq_GapP_of_mem_UP_of_mem_coUP
    (hA_up : A ∈ UP encBits) (hA_coup : A ∈ coUP encBits) (enc : α ↪ List Bool) :
    GapPWithOracle A enc = GapP enc := by
  simp only [GapPWithOracle, SharpPWithOracle_eq_SharpP_of_mem_UP_of_mem_coUP hA_up hA_coup, GapP]

open Classical in
/-- The `0`/`1` indicator of an oracle `A` belongs to `SharpPWithOracle A encBits`, using the
zero-bit witness length `p = 0`. -/
theorem indicator_mem_SharpPWithOracle_self (A : Set (List Bool)) :
    (fun q : List Bool => if q ∈ A then 1 else 0) ∈ SharpPWithOracle A encBits := by
  obtain ⟨fA, hfA, hA_iff⟩ := mem_PWithOracle_self A
  refine ⟨0, fun x => fA x.1, hfA.preprocess (by fun_prop), fun q => ?_⟩
  simp only [Polynomial.eval_zero, acceptCount_zero, hA_iff q]

open Classical in
/-- The `0`/`1` indicator of the complement `Aᶜ` belongs to `SharpPWithOracle A encBits`. -/
theorem indicator_compl_mem_SharpPWithOracle_self (A : Set (List Bool)) :
    (fun q : List Bool => if q ∉ A then 1 else 0) ∈ SharpPWithOracle A encBits := by
  obtain ⟨fA, hfA, hA_iff⟩ := mem_PWithOracle_self A
  refine ⟨0, fun x => !fA x.1, (hfA.preprocess (by fun_prop)).map
    (by fun_prop), fun q => ?_⟩
  simp only [Polynomial.eval_zero, acceptCount_zero, hA_iff q]
  cases fA q <;> simp

/-- **Exact characterization of `#P` oracle lowness (`Low(#P) = UP ∩ coUP`)**
([Köbler, Schöning, Toda and Torán][KoeblerSchoeningTodaToran1992]):
`SharpPWithOracle A encBits = SharpP encBits` if and only if `A ∈ UP encBits ∩ coUP encBits`. -/
theorem SharpPWithOracle_eq_SharpP_iff :
    SharpPWithOracle A encBits = SharpP encBits ↔ A ∈ UP encBits ∩ coUP encBits := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · refine ⟨open Classical in fun q => if q ∈ A then 1 else 0,
        h ▸ indicator_mem_SharpPWithOracle_self A, fun q => ?_, fun q => ?_⟩
      · dsimp only
        split_ifs <;> omega
      · dsimp only
        split_ifs with hq <;> simp [hq]
    · refine ⟨open Classical in fun q => if q ∉ A then 1 else 0,
        h ▸ indicator_compl_mem_SharpPWithOracle_self A, fun q => ?_, fun q => ?_⟩
      · dsimp only
        split_ifs <;> omega
      · dsimp only
        rw [Set.mem_compl_iff]
        split_ifs with hq <;> simp [hq]
  · rintro ⟨hA_up, hA_coup⟩
    exact SharpPWithOracle_eq_SharpP_of_mem_UP_of_mem_coUP hA_up hA_coup encBits

/-- **`#P^A = #P` for all instance encodings if and only if `A ∈ UP ∩ coUP`.** -/
theorem forall_SharpPWithOracle_eq_SharpP_iff :
    (∀ {α : Type} (enc : α ↪ List Bool), SharpPWithOracle A enc = SharpP enc) ↔
      A ∈ UP encBits ∩ coUP encBits :=
  ⟨fun h => SharpPWithOracle_eq_SharpP_iff.mp (h encBits),
    fun ⟨hA_up, hA_coup⟩ _ enc =>
      SharpPWithOracle_eq_SharpP_of_mem_UP_of_mem_coUP hA_up hA_coup enc⟩

/-- **The union of `#P^A` over `A ∈ UP ∩ coUP` is `#P`.** -/
theorem iUnion_SharpPWithOracle_UP_inter_coUP (enc : α ↪ List Bool) :
    (⋃ A ∈ UP encBits ∩ coUP encBits, SharpPWithOracle A enc) = SharpP enc := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun A hA =>
      (SharpPWithOracle_eq_SharpP_of_mem_UP_of_mem_coUP hA.1 hA.2 enc).le
  · intro f hf
    have hempty : (∅ : Set (List Bool)) ∈ P encBits :=
      ⟨fun _ => false, .const false, fun _ => by simp⟩
    refine Set.mem_iUnion₂.mpr ⟨∅, ⟨P_subset_UP hempty, P_subset_coUP hempty⟩, ?_⟩
    exact SharpP_subset_SharpPWithOracle ∅ enc hf

/-! ### Relativized `UP`, `coUP`, `FewP`, `US`, and `SBPWithFixedTarget` -/

/-- Unambiguous polynomial time relative to a language oracle `A`: languages whose characteristic
function belongs to `SharpPWithOracle A enc`. -/
def UPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ f ∈ SharpPWithOracle A enc, (∀ a, f a ≤ 1) ∧ ∀ a, a ∈ L ↔ f a = 1}

/-- Complements of unambiguous polynomial-time languages relative to `A`. -/
def coUPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | Lᶜ ∈ UPWithOracle A enc}

/-- Polynomially bounded ambiguity relative to a language oracle `A`. -/
def FewPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ f ∈ SharpPWithOracle A enc, ∃ p : Polynomial ℕ,
    (∀ a, f a ≤ p.eval (enc a).length) ∧ ∀ a, a ∈ L ↔ 0 < f a}

/-- Unique-solution polynomial time relative to a language oracle `A`. -/
def USWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ f ∈ SharpPWithOracle A enc, ∀ a, a ∈ L ↔ f a = 1}

/-- Small bounded-error polynomial time relative to a language oracle `A` with an unrelativized
`FP` threshold `k : α → ℕ` (analogous to `LWPPWithFixedTarget` and `WPPWithFixedTarget`). -/
def SBPWithFixedTarget (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ f ∈ SharpPWithOracle A enc, ∃ k : α → ℕ, ComputableInPolyTime k enc encNat ∧
    ∀ a, (a ∈ L → k a ≤ f a) ∧ (a ∉ L → 2 * f a < k a)}

/-- `UPWithOracle` through oracle verifiers: at most one certificate of the specified length
accepts on each input, and exactly one accepts on members. -/
theorem mem_UPWithOracle {L : Set α} :
    L ∈ UPWithOracle A enc ↔ ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTimeWithOracle A V (encPair enc encBits) encBool ∧
      (∀ a, acceptCount V a (p.eval (enc a).length) ≤ 1) ∧
      ∀ a, a ∈ L ↔ acceptCount V a (p.eval (enc a).length) = 1 := by
  constructor
  · rintro ⟨f, ⟨p, V, hV, hf⟩, hle, hL⟩
    exact ⟨p, V, hV, fun a => hf a ▸ hle a, fun a => (hL a).trans (by rw [hf a])⟩
  · rintro ⟨p, V, hV, hle, hL⟩
    exact ⟨_, ⟨p, V, hV, fun _ => rfl⟩, hle, hL⟩

theorem mem_coUPWithOracle {L : Set α} :
    L ∈ coUPWithOracle A enc ↔ Lᶜ ∈ UPWithOracle A enc := Iff.rfl

@[simp]
theorem compl_mem_coUPWithOracle {L : Set α} :
    Lᶜ ∈ coUPWithOracle A enc ↔ L ∈ UPWithOracle A enc := by simp [coUPWithOracle]

/-- `FewPWithOracle` through oracle verifiers with a polynomial bound on accepting counts. -/
theorem mem_FewPWithOracle {L : Set α} :
    L ∈ FewPWithOracle A enc ↔ ∃ (p q : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTimeWithOracle A V (encPair enc encBits) encBool ∧
      (∀ a, acceptCount V a (p.eval (enc a).length) ≤ q.eval (enc a).length) ∧
      ∀ a, a ∈ L ↔ 0 < acceptCount V a (p.eval (enc a).length) := by
  constructor
  · rintro ⟨f, ⟨p, V, hV, hf⟩, q, hle, hL⟩
    exact ⟨p, q, V, hV, fun a => hf a ▸ hle a, fun a => by rw [hL a, hf a]⟩
  · rintro ⟨p, q, V, hV, hle, hL⟩
    exact ⟨_, ⟨p, V, hV, fun _ => rfl⟩, q, hle, hL⟩

/-- Ordinary `UP` verifiers can ignore every oracle. -/
theorem UP_subset_UPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    UP enc ⊆ UPWithOracle A enc := fun _ ⟨f, hf, hle, hL⟩ =>
  ⟨f, SharpP_subset_SharpPWithOracle A enc hf, hle, hL⟩

/-- Ordinary `coUP` verifiers can ignore every oracle. -/
theorem coUP_subset_coUPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    coUP enc ⊆ coUPWithOracle A enc := fun _ hL =>
  UP_subset_UPWithOracle A enc hL

/-- Ordinary `FewP` verifiers can ignore every oracle. -/
theorem FewP_subset_FewPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    FewP enc ⊆ FewPWithOracle A enc := fun _ ⟨f, hf, p, hle, hL⟩ =>
  ⟨f, SharpP_subset_SharpPWithOracle A enc hf, p, hle, hL⟩

/-- Ordinary `US` verifiers can ignore every oracle. -/
theorem US_subset_USWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    US enc ⊆ USWithOracle A enc := fun _ ⟨f, hf, hL⟩ =>
  ⟨f, SharpP_subset_SharpPWithOracle A enc hf, hL⟩

/-- Ordinary `SBP` verifiers can ignore every oracle in `SBPWithFixedTarget`. -/
theorem SBP_subset_SBPWithFixedTarget (A : Set (List Bool)) (enc : α ↪ List Bool) :
    SBP enc ⊆ SBPWithFixedTarget A enc := fun _ ⟨f, hf, k, hk, hL⟩ =>
  ⟨f, SharpP_subset_SharpPWithOracle A enc hf, k, hk, hL⟩

/-- `PWithOracle` is contained in `UPWithOracle` via the empty certificate `p = 0`. -/
theorem PWithOracle_subset_UPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    PWithOracle A enc ⊆ UPWithOracle A enc := by
  rintro L ⟨f, hf, hL⟩
  refine mem_UPWithOracle.mpr ⟨0, fun x => f x.1, hf.preprocess (by fun_prop), ?_, ?_⟩
  · intro a
    simp only [Polynomial.eval_zero, acceptCount_zero]
    split <;> omega
  · intro a
    simp [Polynomial.eval_zero, acceptCount_zero, hL a]

/-- `UPWithOracle` is contained in `FewPWithOracle` with constant polynomial bound `1`. -/
theorem UPWithOracle_subset_FewPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    UPWithOracle A enc ⊆ FewPWithOracle A enc := by
  rintro L ⟨f, hf, hle, hL⟩
  refine ⟨f, hf, 1, by simpa using hle, fun a => ?_⟩
  rw [hL a]
  have := hle a
  omega

/-- `FewPWithOracle` is contained in `NPWithOracle`. -/
theorem FewPWithOracle_subset_NPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    FewPWithOracle A enc ⊆ NPWithOracle A enc := by
  rintro L ⟨f, ⟨p, V, hV, hf⟩, -, -, hL⟩
  refine ⟨p, V, hV, fun a => ?_⟩
  rw [hL a, hf a, acceptCount_pos_iff]

/-- `UPWithOracle` is contained in `NPWithOracle`. -/
theorem UPWithOracle_subset_NPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    UPWithOracle A enc ⊆ NPWithOracle A enc :=
  (UPWithOracle_subset_FewPWithOracle A enc).trans (FewPWithOracle_subset_NPWithOracle A enc)

/-- `UPWithOracle` is contained in `USWithOracle`. -/
theorem UPWithOracle_subset_USWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    UPWithOracle A enc ⊆ USWithOracle A enc := fun _ ⟨f, hf, _, hL⟩ =>
  ⟨f, hf, hL⟩

/-- `UPWithOracle` is contained in `SPPWithOracle`. -/
theorem UPWithOracle_subset_SPPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    UPWithOracle A enc ⊆ SPPWithOracle A enc := by
  rintro L ⟨f, hf, hle, hL⟩
  refine ⟨fun a => (f a : ℤ),
    ⟨f, hf, 0, SharpP_subset_SharpPWithOracle A enc SharpP.zero_mem, fun _ => by simp⟩,
    fun a => ?_, fun a => ?_⟩
  · dsimp only
    have := hle a
    omega
  · dsimp only
    rw [hL a]
    omega

/-- `A` belongs to `UPWithOracle A encBits`. -/
theorem mem_UPWithOracle_self (A : Set (List Bool)) : A ∈ UPWithOracle A encBits :=
  PWithOracle_subset_UPWithOracle A encBits (mem_PWithOracle_self A)

/-- `Aᶜ` belongs to `UPWithOracle A encBits`. -/
theorem mem_UPWithOracle_compl_self (A : Set (List Bool)) : Aᶜ ∈ UPWithOracle A encBits := by
  refine ⟨open Classical in fun q => if q ∉ A then 1 else 0,
    indicator_compl_mem_SharpPWithOracle_self A, fun q => ?_, fun q => ?_⟩
  · dsimp only
    split_ifs <;> omega
  · dsimp only
    rw [Set.mem_compl_iff]
    split_ifs with hq <;> simp [hq]

/-- `A` belongs to `coUPWithOracle A encBits`. -/
theorem mem_coUPWithOracle_self (A : Set (List Bool)) : A ∈ coUPWithOracle A encBits :=
  mem_UPWithOracle_compl_self A

/-- A polynomial-time oracle adds no `UP` languages. -/
theorem UPWithOracle_eq_UP (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    UPWithOracle A enc = UP enc := by
  simp only [UPWithOracle, SharpPWithOracle_eq_SharpP hA, UP]

/-- A polynomial-time oracle adds no `coUP` languages. -/
theorem coUPWithOracle_eq_coUP (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    coUPWithOracle A enc = coUP enc := by
  simp only [coUPWithOracle, UPWithOracle_eq_UP hA, coUP]

/-- A polynomial-time oracle adds no `FewP` languages. -/
theorem FewPWithOracle_eq_FewP (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    FewPWithOracle A enc = FewP enc := by
  simp only [FewPWithOracle, SharpPWithOracle_eq_SharpP hA, FewP]

/-- A polynomial-time oracle adds no `US` languages. -/
theorem USWithOracle_eq_US (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    USWithOracle A enc = US enc := by
  simp only [USWithOracle, SharpPWithOracle_eq_SharpP hA, US]

/-- A polynomial-time oracle adds no `SBPWithFixedTarget` languages. -/
theorem SBPWithFixedTarget_eq_SBP (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    SBPWithFixedTarget A enc = SBP enc := by
  simp only [SBPWithFixedTarget, SharpPWithOracle_eq_SharpP hA, SBP]

/-- **`UP^(UP ∩ coUP) = UP`**: an oracle in `UP ∩ coUP` adds nothing to `UP`. -/
theorem UPWithOracle_eq_UP_of_mem_UP_of_mem_coUP
    (hA_up : A ∈ UP encBits) (hA_coup : A ∈ coUP encBits) (enc : α ↪ List Bool) :
    UPWithOracle A enc = UP enc := by
  simp only [UPWithOracle, SharpPWithOracle_eq_SharpP_of_mem_UP_of_mem_coUP hA_up hA_coup, UP]

/-- **`coUP^(UP ∩ coUP) = coUP`**: an oracle in `UP ∩ coUP` adds nothing to `coUP`. -/
theorem coUPWithOracle_eq_coUP_of_mem_UP_of_mem_coUP
    (hA_up : A ∈ UP encBits) (hA_coup : A ∈ coUP encBits) (enc : α ↪ List Bool) :
    coUPWithOracle A enc = coUP enc := by
  simp only [coUPWithOracle, UPWithOracle_eq_UP_of_mem_UP_of_mem_coUP hA_up hA_coup, coUP]

/-- **`UP^A = UP` and `coUP^A = coUP` on bit strings if and only if `A ∈ UP ∩ coUP`.** -/
theorem UPWithOracle_eq_UP_and_coUPWithOracle_eq_coUP_iff :
    (UPWithOracle A encBits = UP encBits ∧ coUPWithOracle A encBits = coUP encBits) ↔
      A ∈ UP encBits ∩ coUP encBits := by
  constructor
  · rintro ⟨hUP, hcoUP⟩
    exact ⟨hUP ▸ mem_UPWithOracle_self A, hcoUP ▸ mem_coUPWithOracle_self A⟩
  · rintro ⟨hA_up, hA_coup⟩
    exact ⟨UPWithOracle_eq_UP_of_mem_UP_of_mem_coUP hA_up hA_coup encBits,
      coUPWithOracle_eq_coUP_of_mem_UP_of_mem_coUP hA_up hA_coup encBits⟩

/-- **`UP^A ∩ coUP^A = UP ∩ coUP` on bit strings if and only if `A ∈ UP ∩ coUP`.** -/
theorem UPWithOracle_inter_coUPWithOracle_eq_iff :
    UPWithOracle A encBits ∩ coUPWithOracle A encBits = UP encBits ∩ coUP encBits ↔
      A ∈ UP encBits ∩ coUP encBits := by
  constructor
  · intro h
    rw [← h]
    exact ⟨mem_UPWithOracle_self A, mem_coUPWithOracle_self A⟩
  · rintro ⟨hA_up, hA_coup⟩
    rw [UPWithOracle_eq_UP_of_mem_UP_of_mem_coUP hA_up hA_coup encBits,
      coUPWithOracle_eq_coUP_of_mem_UP_of_mem_coUP hA_up hA_coup encBits]

/-- **`FewP^(UP ∩ coUP) = FewP`**: an oracle in `UP ∩ coUP` adds nothing to `FewP`. -/
theorem FewPWithOracle_eq_FewP_of_mem_UP_of_mem_coUP
    (hA_up : A ∈ UP encBits) (hA_coup : A ∈ coUP encBits) (enc : α ↪ List Bool) :
    FewPWithOracle A enc = FewP enc := by
  simp only [FewPWithOracle, SharpPWithOracle_eq_SharpP_of_mem_UP_of_mem_coUP hA_up hA_coup, FewP]

/-- **`US^(UP ∩ coUP) = US`**: an oracle in `UP ∩ coUP` adds nothing to `US`. -/
theorem USWithOracle_eq_US_of_mem_UP_of_mem_coUP
    (hA_up : A ∈ UP encBits) (hA_coup : A ∈ coUP encBits) (enc : α ↪ List Bool) :
    USWithOracle A enc = US enc := by
  simp only [USWithOracle, SharpPWithOracle_eq_SharpP_of_mem_UP_of_mem_coUP hA_up hA_coup, US]

/-- **`UP ∩ coUP` is low for fixed-threshold `SBP`** (`SBPWithFixedTarget A enc = SBP enc`). -/
theorem SBPWithFixedTarget_eq_SBP_of_mem_UP_of_mem_coUP
    (hA_up : A ∈ UP encBits) (hA_coup : A ∈ coUP encBits) (enc : α ↪ List Bool) :
    SBPWithFixedTarget A enc = SBP enc := by
  simp only [SBPWithFixedTarget,
    SharpPWithOracle_eq_SharpP_of_mem_UP_of_mem_coUP hA_up hA_coup, SBP]

/-- **The union of `UP^A` over `A ∈ UP ∩ coUP` is `UP`.** -/
theorem iUnion_UPWithOracle_UP_inter_coUP (enc : α ↪ List Bool) :
    (⋃ A ∈ UP encBits ∩ coUP encBits, UPWithOracle A enc) = UP enc := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun A hA =>
      (UPWithOracle_eq_UP_of_mem_UP_of_mem_coUP hA.1 hA.2 enc).le
  · intro L hL
    have hempty : (∅ : Set (List Bool)) ∈ P encBits :=
      ⟨fun _ => false, .const false, fun _ => by simp⟩
    exact Set.mem_iUnion₂.mpr
      ⟨∅, ⟨P_subset_UP hempty, P_subset_coUP hempty⟩, UP_subset_UPWithOracle ∅ enc hL⟩

/-- **The union of `coUP^A` over `A ∈ UP ∩ coUP` is `coUP`.** -/
theorem iUnion_coUPWithOracle_UP_inter_coUP (enc : α ↪ List Bool) :
    (⋃ A ∈ UP encBits ∩ coUP encBits, coUPWithOracle A enc) = coUP enc := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun A hA =>
      (coUPWithOracle_eq_coUP_of_mem_UP_of_mem_coUP hA.1 hA.2 enc).le
  · intro L hL
    have hempty : (∅ : Set (List Bool)) ∈ P encBits :=
      ⟨fun _ => false, .const false, fun _ => by simp⟩
    exact Set.mem_iUnion₂.mpr
      ⟨∅, ⟨P_subset_UP hempty, P_subset_coUP hempty⟩, coUP_subset_coUPWithOracle ∅ enc hL⟩

/-- **The union of `FewP^A` over `A ∈ UP ∩ coUP` is `FewP`.** -/
theorem iUnion_FewPWithOracle_UP_inter_coUP (enc : α ↪ List Bool) :
    (⋃ A ∈ UP encBits ∩ coUP encBits, FewPWithOracle A enc) = FewP enc := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun A hA =>
      (FewPWithOracle_eq_FewP_of_mem_UP_of_mem_coUP hA.1 hA.2 enc).le
  · intro L hL
    have hempty : (∅ : Set (List Bool)) ∈ P encBits :=
      ⟨fun _ => false, .const false, fun _ => by simp⟩
    exact Set.mem_iUnion₂.mpr
      ⟨∅, ⟨P_subset_UP hempty, P_subset_coUP hempty⟩, FewP_subset_FewPWithOracle ∅ enc hL⟩

/-- **The union of `US^A` over `A ∈ UP ∩ coUP` is `US`.** -/
theorem iUnion_USWithOracle_UP_inter_coUP (enc : α ↪ List Bool) :
    (⋃ A ∈ UP encBits ∩ coUP encBits, USWithOracle A enc) = US enc := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun A hA =>
      (USWithOracle_eq_US_of_mem_UP_of_mem_coUP hA.1 hA.2 enc).le
  · intro L hL
    have hempty : (∅ : Set (List Bool)) ∈ P encBits :=
      ⟨fun _ => false, .const false, fun _ => by simp⟩
    exact Set.mem_iUnion₂.mpr
      ⟨∅, ⟨P_subset_UP hempty, P_subset_coUP hempty⟩, US_subset_USWithOracle ∅ enc hL⟩

/-- **The union of `SBPWithFixedTarget A` over `A ∈ UP ∩ coUP` is `SBP`.** -/
theorem iUnion_SBPWithFixedTarget_UP_inter_coUP (enc : α ↪ List Bool) :
    (⋃ A ∈ UP encBits ∩ coUP encBits, SBPWithFixedTarget A enc) = SBP enc := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun A hA =>
      (SBPWithFixedTarget_eq_SBP_of_mem_UP_of_mem_coUP hA.1 hA.2 enc).le
  · intro L hL
    have hempty : (∅ : Set (List Bool)) ∈ P encBits :=
      ⟨fun _ => false, .const false, fun _ => by simp⟩
    exact Set.mem_iUnion₂.mpr
      ⟨∅, ⟨P_subset_UP hempty, P_subset_coUP hempty⟩, SBP_subset_SBPWithFixedTarget ∅ enc hL⟩

/-! ### Exact characterizations of `GapP` and `SPP` oracle lowness (`Low(GapP) = Low(SPP) = SPP`) -/

open Classical in
/-- The `0`/`1` integer indicator of an oracle `A` belongs to `GapPWithOracle A encBits`. -/
theorem indicator_mem_GapPWithOracle_self (A : Set (List Bool)) :
    (fun q : List Bool => if q ∈ A then (1 : ℤ) else 0) ∈ GapPWithOracle A encBits := by
  refine ⟨fun q => if q ∈ A then 1 else 0, indicator_mem_SharpPWithOracle_self A,
    0, SharpP_subset_SharpPWithOracle A encBits SharpP.zero_mem, fun q => ?_⟩
  dsimp only
  split_ifs <;> rfl

/-- Every oracle `A` belongs to `SPPWithOracle A encBits`. -/
theorem mem_SPPWithOracle_self (A : Set (List Bool)) : A ∈ SPPWithOracle A encBits := by
  refine ⟨open Classical in fun q => if q ∈ A then (1 : ℤ) else 0,
    indicator_mem_GapPWithOracle_self A, fun q => ?_, fun q => ?_⟩
  · dsimp only
    split_ifs with hq
    · exact Or.inr rfl
    · exact Or.inl rfl
  · dsimp only
    split_ifs with hq <;> simp [hq]

/-- **Exact characterization of `GapP` oracle lowness (`Low(GapP) = SPP`)**
([Fenner, Fortnow and Kurtz, Section 5][FennerFortnowKurtz1994]):
`GapPWithOracle A encBits = GapP encBits` if and only if `A ∈ SPP encBits`. -/
theorem GapPWithOracle_eq_GapP_iff :
    GapPWithOracle A encBits = GapP encBits ↔ A ∈ SPP encBits := by
  constructor
  · intro h
    refine ⟨open Classical in fun q => if q ∈ A then (1 : ℤ) else 0,
      h ▸ indicator_mem_GapPWithOracle_self A, fun q => ?_, fun q => ?_⟩
    · dsimp only
      split_ifs with hq
      · exact Or.inr rfl
      · exact Or.inl rfl
    · dsimp only
      split_ifs with hq <;> simp [hq]
  · intro hA
    exact GapPWithOracle_eq_GapP_of_mem_SPP hA encBits

/-- **`GapP^A = GapP` for all instance encodings if and only if `A ∈ SPP`.** -/
theorem forall_GapPWithOracle_eq_GapP_iff :
    (∀ {α : Type} (enc : α ↪ List Bool), GapPWithOracle A enc = GapP enc) ↔ A ∈ SPP encBits :=
  ⟨fun h => GapPWithOracle_eq_GapP_iff.mp (h encBits),
    fun hA _ enc => GapPWithOracle_eq_GapP_of_mem_SPP hA enc⟩

/-- **Exact characterization of `SPP` oracle lowness (`Low(SPP) = SPP`)**
([Fenner, Fortnow and Kurtz, Section 5][FennerFortnowKurtz1994]):
`SPPWithOracle A encBits = SPP encBits` if and only if `A ∈ SPP encBits`. -/
theorem SPPWithOracle_eq_SPP_iff :
    SPPWithOracle A encBits = SPP encBits ↔ A ∈ SPP encBits :=
  ⟨fun h => h ▸ mem_SPPWithOracle_self A, fun hA => SPPWithOracle_eq_SPP_of_mem_SPP hA encBits⟩

/-- **`SPP^A = SPP` for all instance encodings if and only if `A ∈ SPP`.** -/
theorem forall_SPPWithOracle_eq_SPP_iff :
    (∀ {α : Type} (enc : α ↪ List Bool), SPPWithOracle A enc = SPP enc) ↔ A ∈ SPP encBits :=
  ⟨fun h => SPPWithOracle_eq_SPP_iff.mp (h encBits),
    fun hA _ enc => SPPWithOracle_eq_SPP_of_mem_SPP hA enc⟩

/-- **The union of `GapP^A` over `A ∈ SPP` is `GapP`.** -/
theorem iUnion_GapPWithOracle_SPP (enc : α ↪ List Bool) :
    (⋃ A ∈ SPP encBits, GapPWithOracle A enc) = GapP enc := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun A hA => (GapPWithOracle_eq_GapP_of_mem_SPP hA enc).le
  · intro g hg
    have hempty : (∅ : Set (List Bool)) ∈ P encBits :=
      ⟨fun _ => false, .const false, fun _ => by simp⟩
    exact Set.mem_iUnion₂.mpr
      ⟨∅, UP_subset_SPP (P_subset_UP hempty), GapP_subset_GapPWithOracle ∅ enc hg⟩

/-- **The union of `SPP^A` over `A ∈ SPP` is `SPP`.** -/
theorem iUnion_SPPWithOracle_SPP (enc : α ↪ List Bool) :
    (⋃ A ∈ SPP encBits, SPPWithOracle A enc) = SPP enc := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun A hA => (SPPWithOracle_eq_SPP_of_mem_SPP hA enc).le
  · intro L hL
    have hempty : (∅ : Set (List Bool)) ∈ P encBits :=
      ⟨fun _ => false, .const false, fun _ => by simp⟩
    exact Set.mem_iUnion₂.mpr
      ⟨∅, UP_subset_SPP (P_subset_UP hempty), SPP_subset_SPPWithOracle ∅ enc hL⟩

/-- **`FewP` is low for `GapP`** (`GapP^FewP = GapP`, via `FewP ⊆ SPP`). -/
theorem GapPWithOracle_eq_GapP_of_mem_FewP (hA : A ∈ FewP encBits) (enc : α ↪ List Bool) :
    GapPWithOracle A enc = GapP enc :=
  GapPWithOracle_eq_GapP_of_mem_SPP (FewP_subset_SPP hA) enc

/-- **`FewP` is low for `SPP`** (`SPP^FewP = SPP`, via `FewP ⊆ SPP`). -/
theorem SPPWithOracle_eq_SPP_of_mem_FewP (hA : A ∈ FewP encBits) (enc : α ↪ List Bool) :
    SPPWithOracle A enc = SPP enc :=
  SPPWithOracle_eq_SPP_of_mem_SPP (FewP_subset_SPP hA) enc

/-- **`FewP` is low for fixed-target `LWPP`** (`LWPPWithFixedTarget A enc = LWPP enc`). -/
theorem LWPPWithFixedTarget_eq_LWPP_of_mem_FewP (hA : A ∈ FewP encBits) (enc : α ↪ List Bool) :
    LWPPWithFixedTarget A enc = LWPP enc :=
  LWPPWithFixedTarget_eq_LWPP_of_mem_SPP (FewP_subset_SPP hA) enc

/-- **`FewP` is low for fixed-target `WPP`** (`WPPWithFixedTarget A enc = WPP enc`). -/
theorem WPPWithFixedTarget_eq_WPP_of_mem_FewP (hA : A ∈ FewP encBits) (enc : α ↪ List Bool) :
    WPPWithFixedTarget A enc = WPP enc :=
  WPPWithFixedTarget_eq_WPP_of_mem_SPP (FewP_subset_SPP hA) enc

/-- **`FewP` is low for `C=P`** (`C=P^FewP = C=P`). -/
theorem CeqPWithOracle_eq_CeqP_of_mem_FewP (hA : A ∈ FewP encBits) (enc : α ↪ List Bool) :
    CeqPWithOracle A enc = CeqP enc :=
  CeqPWithOracle_eq_CeqP_of_mem_SPP (FewP_subset_SPP hA) enc

/-- **`FewP` is low for `PP`** (`PP^FewP = PP`, [Köbler et al.][KoeblerSchoeningTodaToran1992]). -/
theorem PPWithOracle_eq_PP_of_mem_FewP (hA : A ∈ FewP encBits) (enc : α ↪ List Bool) :
    PPWithOracle A enc = PP enc :=
  PPWithOracle_eq_PP_of_mem_SPP (FewP_subset_SPP hA) enc

/-! ### Relativized modular counting classes and `SPP` / `FewP` / `UP ∩ coUP` lowness -/

/-- Modular counting relative to a language oracle `A`: nonzero residues modulo `k` of functions in
`SharpPWithOracle A enc`. -/
def ModPWithOracle (k : ℕ) (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ f ∈ SharpPWithOracle A enc, ∀ a, a ∈ L ↔ f a % k ≠ 0}

/-- Complements of modular counting languages relative to `A` (zero residues modulo `k`). -/
def coModPWithOracle (k : ℕ) (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | Lᶜ ∈ ModPWithOracle k A enc}

/-- Parity polynomial time (`⊕P`) relative to a language oracle `A`. -/
def ParityPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ f ∈ SharpPWithOracle A enc, ∀ a, a ∈ L ↔ Odd (f a)}

theorem mem_coModPWithOracle {L : Set α} :
    L ∈ coModPWithOracle k A enc ↔ Lᶜ ∈ ModPWithOracle k A enc := Iff.rfl

@[simp]
theorem compl_mem_coModPWithOracle {L : Set α} :
    Lᶜ ∈ coModPWithOracle k A enc ↔ L ∈ ModPWithOracle k A enc := by simp [coModPWithOracle]

/-- Constant functions belong to `SharpPWithOracle A enc`. -/
theorem SharpPWithOracle.natCast_mem (n : ℕ) : (n : α → ℕ) ∈ SharpPWithOracle A enc :=
  SharpP_subset_SharpPWithOracle A enc (SharpP.natCast_mem n)

/-- A positive fixed modulus admits a `SharpPWithOracle` count with the same residue as any
`GapPWithOracle` function. The modulus is fixed before the input, so scaling by `k - 1` uses
`SharpPWithOracle` constant multiplication. -/
theorem GapPWithOracle.exists_SharpPWithOracle_emod {g : α → ℤ}
    (hg : g ∈ GapPWithOracle A enc) (hk : 0 < k) :
    ∃ f ∈ SharpPWithOracle A enc, ∀ a, (f a : ℤ) % k = g a % k := by
  obtain ⟨f₁, h₁, f₂, h₂, hg⟩ := hg
  refine ⟨f₁ + (fun _ => k - 1) * f₂,
    SharpPWithOracle.add_mem h₁
      (SharpPWithOracle.mul_mem (SharpPWithOracle.natCast_mem (k - 1)) h₂),
    fun a => ?_⟩
  have heq : ((f₁ a + (k - 1) * f₂ a : ℕ) : ℤ) =
      (f₁ a : ℤ) - f₂ a + k * f₂ a := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by lia : 1 ≤ k)]
    push_cast
    ring
  change ((f₁ a + (k - 1) * f₂ a : ℕ) : ℤ) % k = g a % k
  rw [heq, hg a, Int.add_mul_emod_self_left]

/-- For a positive fixed modulus, nonzero residues of `GapPWithOracle` functions define
`ModPWithOracle`. -/
theorem mem_ModPWithOracle_iff_exists_GapPWithOracle (hk : 0 < k) {L : Set α} :
    L ∈ ModPWithOracle k A enc ↔ ∃ g ∈ GapPWithOracle A enc, ∀ a, a ∈ L ↔ g a % k ≠ 0 := by
  constructor
  · rintro ⟨f, hf, hL⟩
    exact ⟨fun a => (f a : ℤ), SharpPWithOracle.natCast_mem_GapPWithOracle hf,
      fun a => by simpa only [← Int.natCast_emod, ne_eq, Int.natCast_eq_zero] using hL a⟩
  · rintro ⟨g, hg, hL⟩
    obtain ⟨f, hf, hfg⟩ := GapPWithOracle.exists_SharpPWithOracle_emod hg hk
    refine ⟨f, hf, fun a => ?_⟩
    rw [hL a, ← hfg a]
    simp only [← Int.natCast_emod, ne_eq, Int.natCast_eq_zero]

/-- For a positive fixed modulus, zero residues of `GapPWithOracle` functions define
`coModPWithOracle`. -/
theorem mem_coModPWithOracle_iff_exists_GapPWithOracle (hk : 0 < k) {L : Set α} :
    L ∈ coModPWithOracle k A enc ↔ ∃ g ∈ GapPWithOracle A enc, ∀ a, a ∈ L ↔ g a % k = 0 :=
  (mem_ModPWithOracle_iff_exists_GapPWithOracle hk).trans
    (exists_forall_mem_compl_iff fun _ _ => not_not)

/-- Modulo two, nonzero residue is oddness: `ModPWithOracle 2 A enc = ParityPWithOracle A enc`. -/
theorem ModPWithOracle_two (A : Set (List Bool)) (enc : α ↪ List Bool) :
    ModPWithOracle 2 A enc = ParityPWithOracle A enc := by
  ext L
  simp only [ModPWithOracle, ParityPWithOracle, Set.mem_ofPred_eq]
  congr! 3
  simp [← Nat.not_odd_iff]

/-- Ordinary `ModP k` verifiers can ignore every oracle. -/
theorem ModP_subset_ModPWithOracle (k : ℕ) (A : Set (List Bool)) (enc : α ↪ List Bool) :
    ModP k enc ⊆ ModPWithOracle k A enc := fun _ ⟨f, hf, hL⟩ =>
  ⟨f, SharpP_subset_SharpPWithOracle A enc hf, hL⟩

/-- Ordinary `coModP k` verifiers can ignore every oracle. -/
theorem coModP_subset_coModPWithOracle (k : ℕ) (A : Set (List Bool)) (enc : α ↪ List Bool) :
    coModP k enc ⊆ coModPWithOracle k A enc := fun _ hL =>
  ModP_subset_ModPWithOracle k A enc hL

/-- Ordinary `ParityP` verifiers can ignore every oracle. -/
theorem ParityP_subset_ParityPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    ParityP enc ⊆ ParityPWithOracle A enc := by
  rw [← ModP_two, ← ModPWithOracle_two]
  exact ModP_subset_ModPWithOracle 2 A enc

/-- A polynomial-time oracle adds no `ModP k` languages. -/
theorem ModPWithOracle_eq_ModP (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    ModPWithOracle k A enc = ModP k enc := by
  simp only [ModPWithOracle, SharpPWithOracle_eq_SharpP hA, ModP]

/-- A polynomial-time oracle adds no `coModP k` languages. -/
theorem coModPWithOracle_eq_coModP (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    coModPWithOracle k A enc = coModP k enc := by
  simp only [coModPWithOracle, ModPWithOracle_eq_ModP hA, coModP]

/-- A polynomial-time oracle adds no `ParityP` languages. -/
theorem ParityPWithOracle_eq_ParityP (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    ParityPWithOracle A enc = ParityP enc := by
  rw [← ModPWithOracle_two, ← ModP_two, ModPWithOracle_eq_ModP hA]

/-- **`UP ∩ coUP` is low for `ModP k`** at every modulus `k : ℕ` (including `k = 0`). -/
theorem ModPWithOracle_eq_ModP_of_mem_UP_of_mem_coUP
    (hA_up : A ∈ UP encBits) (hA_coup : A ∈ coUP encBits) (enc : α ↪ List Bool) :
    ModPWithOracle k A enc = ModP k enc := by
  simp only [ModPWithOracle, SharpPWithOracle_eq_SharpP_of_mem_UP_of_mem_coUP hA_up hA_coup, ModP]

/-- **`UP ∩ coUP` is low for `coModP k`** at every modulus `k : ℕ`. -/
theorem coModPWithOracle_eq_coModP_of_mem_UP_of_mem_coUP
    (hA_up : A ∈ UP encBits) (hA_coup : A ∈ coUP encBits) (enc : α ↪ List Bool) :
    coModPWithOracle k A enc = coModP k enc := by
  simp only [coModPWithOracle,
    ModPWithOracle_eq_ModP_of_mem_UP_of_mem_coUP hA_up hA_coup, coModP]

/-- **`UP ∩ coUP` is low for `ParityP`** (`⊕P^(UP ∩ coUP) = ⊕P`). -/
theorem ParityPWithOracle_eq_ParityP_of_mem_UP_of_mem_coUP
    (hA_up : A ∈ UP encBits) (hA_coup : A ∈ coUP encBits) (enc : α ↪ List Bool) :
    ParityPWithOracle A enc = ParityP enc := by
  rw [← ModPWithOracle_two, ← ModP_two,
    ModPWithOracle_eq_ModP_of_mem_UP_of_mem_coUP hA_up hA_coup]

/-- **`SPP` is low for `ModP k`** for every positive modulus `0 < k`
([Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994]). -/
theorem ModPWithOracle_eq_ModP_of_mem_SPP (hk : 0 < k) (hA : A ∈ SPP encBits)
    (enc : α ↪ List Bool) :
    ModPWithOracle k A enc = ModP k enc := by
  ext L
  rw [mem_ModPWithOracle_iff_exists_GapPWithOracle hk,
    GapPWithOracle_eq_GapP_of_mem_SPP hA enc,
    mem_ModP_iff_exists_GapP hk]

/-- **`SPP` is low for `coModP k`** for every positive modulus `0 < k`. -/
theorem coModPWithOracle_eq_coModP_of_mem_SPP (hk : 0 < k) (hA : A ∈ SPP encBits)
    (enc : α ↪ List Bool) :
    coModPWithOracle k A enc = coModP k enc := by
  simp only [coModPWithOracle, ModPWithOracle_eq_ModP_of_mem_SPP hk hA, coModP]

/-- **`SPP` is low for `ParityP`** (`⊕P^SPP = ⊕P`,
[Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994]). -/
theorem ParityPWithOracle_eq_ParityP_of_mem_SPP (hA : A ∈ SPP encBits) (enc : α ↪ List Bool) :
    ParityPWithOracle A enc = ParityP enc := by
  rw [← ModPWithOracle_two, ← ModP_two, ModPWithOracle_eq_ModP_of_mem_SPP two_pos hA]

/-- **`FewP` is low for `ModP k`** for every positive modulus `0 < k`. -/
theorem ModPWithOracle_eq_ModP_of_mem_FewP (hk : 0 < k) (hA : A ∈ FewP encBits)
    (enc : α ↪ List Bool) :
    ModPWithOracle k A enc = ModP k enc :=
  ModPWithOracle_eq_ModP_of_mem_SPP hk (FewP_subset_SPP hA) enc

/-- **`FewP` is low for `coModP k`** for every positive modulus `0 < k`. -/
theorem coModPWithOracle_eq_coModP_of_mem_FewP (hk : 0 < k) (hA : A ∈ FewP encBits)
    (enc : α ↪ List Bool) :
    coModPWithOracle k A enc = coModP k enc :=
  coModPWithOracle_eq_coModP_of_mem_SPP hk (FewP_subset_SPP hA) enc

/-- **`FewP` is low for `ParityP`** (`⊕P^FewP = ⊕P`). -/
theorem ParityPWithOracle_eq_ParityP_of_mem_FewP (hA : A ∈ FewP encBits) (enc : α ↪ List Bool) :
    ParityPWithOracle A enc = ParityP enc :=
  ParityPWithOracle_eq_ParityP_of_mem_SPP (FewP_subset_SPP hA) enc

end Cslib.Complexity
