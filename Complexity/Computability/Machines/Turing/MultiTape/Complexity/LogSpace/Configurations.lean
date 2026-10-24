/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Space
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Padding
public import Complexity.Foundations.Data.BitString.Enumeration
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith

/-!
# Codes of views without the input

A view of a nondeterministic machine (`Turing.FiniteCfg`, as in
`Turing.MultiTapeNTM.accepts_iff_reflTransGen_viewStep`) stores its input, so its encoding is at
least as long as the input. All the views reachable on one input share that input, and the rest
of a view is short under a small space bound: `Turing.MultiTapeNTM.coreCode` encodes the input
head position in binary, the control, the work tapes relative to their heads and the output
summary. It identifies views with the same input (`Turing.MultiTapeNTM.coreCode_injective`), and
on views reachable within space `s` on an input of length `n` it has length
`O(log n + s)` (`Turing.MultiTapeNTM.length_coreCode_le`). So at most `2 ^ O(log n + s)` distinct
views are reachable (`Turing.MultiTapeNTM.length_le_of_nodup_reachable`), polynomially many in
`n` under a logarithmic space bound [Sipser, Section 8.4][Sipser2013].

## Main definitions

* `Turing.MultiTapeNTM.coreCode`: the code of a view without its input.
* `Turing.MultiTapeNTM.coreLengthBound`: the bound on the codes of reachable views.

## Main results

* `Turing.MultiTapeNTM.spaceUsed_workTapes_le`: reachable views store few cells per work tape.
* `Turing.MultiTapeNTM.coreCode_injective`: the code identifies views with the same input.
* `Turing.MultiTapeNTM.length_coreCode_le`: reachable views have short codes.
* `Turing.MultiTapeNTM.length_le_of_nodup_reachable`: few distinct views are reachable.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.4][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 4.1][AroraBarak09]
-/

@[expose] public section

open Cslib.Turing

namespace Turing.MultiTapeNTM

open MultiTapeTM

variable {k : ℕ} {State : Type} [Finite State] {ntm : MultiTapeNTM k Bool State}
  {input : List Bool} {s : ℕ}

omit [Finite State] in
/-- **Reachable views store few cells per work tape**: under a space bound `s`, every work tape of
a view reachable from the initial view is stored in at most `4 * s + 1` cells. -/
theorem spaceUsed_workTapes_le (hs : ntm.RunsInSpace input s) {finite : FiniteCfg k Bool State}
    (h : Relation.ReflTransGen ntm.ViewStep (ntm.initView input) finite) (tape : Fin k) :
    (finite.workTapes tape).spaceUsed ≤ 4 * s + 1 := by
  obtain ⟨p, hrep⟩ := exists_computationPath_of_viewStep h
  have hle : RunPath.spaceUsedByTape p.toRunPath tape ≤ s :=
    (Finset.single_le_sum (f := fun i => RunPath.spaceUsedByTape p.toRunPath i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ tape)).trans (hs p)
  obtain ⟨hhead, hcells⟩ := RunPath.natAbs_lt_spaceUsedByTape p.toRunPath
    (fun i z => by rw [p.head_eq]; rfl) (fun i => by rw [p.head_eq]; rfl) tape
  exact (hrep.workTapes tape).spaceUsed_le (hhead.trans_le hle)
    fun z hz => (hcells z hz).trans_le hle

/-- The encoding of a view without its input: the input head position in binary, the control,
the work tapes and the output. -/
noncomputable def encCore : ℕ × Option State × (Fin k → BiTape Bool) × List Bool ↪ List Bool :=
  encPair encNat (encPair (encFinite (Option State)) (encPair (encPi (encBiTape encBool)) encBits))

/-- **The code of a view without its input**: its input head position in binary, its control, its
work tapes relative to their heads and its output. -/
noncomputable def coreCode (finite : FiniteCfg k Bool State) : List Bool :=
  encCore (finite.inputPos.val, finite.state, finite.workTapes, finite.output)

/-- **The code identifies views with the same input.** -/
theorem coreCode_injective {finite finite' : FiniteCfg k Bool State}
    (hinput : finite.input = finite'.input) (h : coreCode finite = coreCode finite') :
    finite = finite' := by
  obtain ⟨input, state, pos, work, output⟩ := finite
  obtain ⟨input', state', pos', work', output'⟩ := finite'
  obtain rfl : input = input' := hinput
  have heq := encCore.injective h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hpos, rfl, rfl, rfl⟩ := heq
  obtain rfl := Fin.ext hpos
  rfl

/-- The bound on the codes of the views reachable within space `s` on inputs of length `n`:
logarithmic in `n` and linear in `s`, with a constant depending only on `k` and `State`. -/
noncomputable def coreLengthBound (k : ℕ) (State : Type) (n s : ℕ) : ℕ :=
  (8 + 2 * Nat.card (Option State) + 200 * k) * (Nat.log2 n + s + 1)

/-- **Reachable views have short codes**: under a space bound `s`, the code of every view reachable
from the initial view has length at most `coreLengthBound k State n s`. -/
theorem length_coreCode_le (hs : ntm.RunsInSpace input s) {finite : FiniteCfg k Bool State}
    (h : Relation.ReflTransGen ntm.ViewStep (ntm.initView input) finite) :
    (coreCode finite).length ≤ coreLengthBound k State input.length s := by
  obtain ⟨p, hrep⟩ := exists_computationPath_of_viewStep h
  have hwork : (encPi (encBiTape encBool) finite.workTapes).length ≤
      k * (2 * (12 * (4 * s + 1)) + 1) := by
    simpa using length_encPi_le (encBiTape encBool) finite.workTapes fun tape =>
      (length_encBiTape_le encBool _ (bound := 1) (by simp)).trans
        (by have := spaceUsed_workTapes_le hs h tape; nlinarith)
  have hcontrol := length_encFinite_lt finite.state
  have hpos : (encNat finite.inputPos.val).length ≤ Nat.log2 input.length + 2 :=
    length_encNat_le_log2_add_two (by
      have hlt := finite.inputPos.isLt
      have hlen : finite.input.length = input.length := congrArg List.length hrep.input
      omega)
  have hout : finite.output.length ≤ 1 := hrep.output ▸ length_outputClass_le _
  simp only [coreCode, encCore, coreLengthBound, length_encPair, encBits_apply]
  nlinarith

/-- **Few distinct views are reachable**: under a space bound `s`, a list of distinct views
reachable from the initial view has at most `2 ^ (2 * coreLengthBound k State n s + 1)` entries,
since padding their codes to one length identifies no two of them. -/
theorem length_le_of_nodup_reachable (hs : ntm.RunsInSpace input s)
    {views : List (FiniteCfg k Bool State)} (hnodup : views.Nodup)
    (hreach : ∀ finite ∈ views,
      Relation.ReflTransGen ntm.ViewStep (ntm.initView input) finite) :
    views.length ≤ 2 ^ (2 * coreLengthBound k State input.length s + 1) := by
  set L := coreLengthBound k State input.length s
  have hinput (finite) (hf : finite ∈ views) : finite.input = input := by
    obtain ⟨p, hrep⟩ := exists_computationPath_of_viewStep (hreach finite hf)
    exact hrep.input
  have hcodes : (views.map fun finite => Cslib.BitString.padWord L (coreCode finite)).Nodup :=
    (List.nodup_map_iff_inj_on hnodup).mpr fun f hf g hg hfg =>
      coreCode_injective ((hinput f hf).trans (hinput g hg).symm)
        (Cslib.BitString.word_eq_of_padWord_eq hfg)
  have hsub : (views.map fun finite => Cslib.BitString.padWord L (coreCode finite)) ⊆
      Cslib.BitString.enumList (2 * L + 1) := by
    intro word hword
    obtain ⟨finite, hf, rfl⟩ := List.mem_map.mp hword
    exact Cslib.BitString.mem_enumList.mpr
      (Cslib.BitString.length_padWord (length_coreCode_le hs (hreach finite hf)))
  simpa using hcodes.length_le_of_subset hsub

end Turing.MultiTapeNTM
