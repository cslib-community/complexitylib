/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Quantum.Classical
public import Complexity.Computability.Circuit.Quantum.PathSum

/-!
# Computational-basis output patterns

An output pattern specifies the bits on a list of wires. Its probability uses the existing
computational-basis measurement. Flipping the wires specified as zero converts a pattern on
distinct wires into the all-one event of `onesProb`, without adding Hadamard gates.

The partition identities below are the elementary measurement facts used by exact output
sampling. These are original implementation lemmas for the circuit model, not a new simulation
algorithm.

## Main definitions

* `Cslib.Quantum.patternAt`: measurement outcomes agreeing with a wire-bit pattern.
* `Cslib.Quantum.patternProb`: the probability of an output pattern.
* `Cslib.Quantum.GateCode.flipCodes`: terminal NOT gates on a list of wires.

## Main results

* `Cslib.Quantum.GateCode.readBit_classicalRun_flipCodes`: distinct terminal NOTs flip exactly
  the selected wires.
* `Cslib.Quantum.onesProb_append_flipCodes_eq_patternProb`: convert a pattern to an all-one event.
* `Cslib.Quantum.hadamardCount_append_flipCodes`: the conversion preserves the denominator.
* `Cslib.Quantum.patternProb_partition`: the next bit partitions a prefix event.
* `Cslib.Quantum.measure_map_readBit_apply`: pattern probabilities are measurement marginals.
* `Cslib.Quantum.patternProb_eq_onesGap`: pattern probabilities use the existing signed gap.
-/

public section

namespace Cslib.Quantum

open Finset

variable {m : ℕ}

/-- The output outcomes agreeing with every specified wire and bit. An out-of-range wire makes
an event impossible. -/
@[expose] def patternAt (m : ℕ) (ps : List (ℕ × Bool)) : Finset (Fin m → Bool) :=
  univ.filter fun y => ∀ p ∈ ps, p.1 < m ∧ readBit y p.1 = p.2

/-- The probability of a specified output pattern in the existing final measurement. -/
@[expose] noncomputable def patternProb (m : ℕ) (gs : List GateCode)
    (ps : List (ℕ × Bool)) (x : List Bool) : ℝ :=
  measureProb (Circuit.run (Circuit.ofCodes m gs) (inputState m x)) (patternAt m ps)

/-- The wires specified by a pattern, in its order. -/
@[expose] def patternWires (ps : List (ℕ × Bool)) : List ℕ := ps.map Prod.fst

/-- The wires that a pattern specifies as zero. -/
@[expose] def patternZeros (ps : List (ℕ × Bool)) : List ℕ :=
  (ps.filter fun p => !p.2).map Prod.fst

@[simp] theorem mem_patternAt {ps : List (ℕ × Bool)} {y : Fin m → Bool} :
    y ∈ patternAt m ps ↔ ∀ p ∈ ps, p.1 < m ∧ readBit y p.1 = p.2 := by
  simp [patternAt]

@[simp] theorem patternAt_nil : patternAt m [] = univ := by
  ext y
  simp

/-- Appending one specified bit intersects the previous event with that bit's event. -/
theorem mem_patternAt_append {ps : List (ℕ × Bool)} {j : ℕ} {b : Bool}
    {y : Fin m → Bool} :
    y ∈ patternAt m (ps ++ [(j, b)]) ↔
      y ∈ patternAt m ps ∧ j < m ∧ readBit y j = b := by
  rw [mem_patternAt, mem_patternAt]
  constructor
  · intro h
    exact ⟨fun p hp => h p (List.mem_append_left _ hp), h (j, b) (by simp)⟩
  · rintro ⟨h, hj, hb⟩ p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h p hp
    · have hp' : p = (j, b) := List.mem_singleton.mp hp
      simpa [hp'] using And.intro hj hb

@[simp] theorem patternProb_nil (m : ℕ) (gs : List GateCode) (x : List Bool) :
    patternProb m gs [] x = 1 := by
  simp [patternProb, measureProb_univ]

/-- Pattern probabilities are nonnegative. -/
theorem patternProb_nonneg (m : ℕ) (gs : List GateCode) (ps : List (ℕ × Bool))
    (x : List Bool) : 0 ≤ patternProb m gs ps x := measureProb_nonneg _ _

namespace GateCode

/-- A NOT gate on each wire of `S`, in order. -/
@[expose] def flipCodes (S : List ℕ) : List GateCode := S.map fun j => (false, j, [])

@[simp] theorem length_flipCodes (S : List ℕ) : (flipCodes S).length = S.length := by
  simp [flipCodes]

/-- Flipping valid wires is a well-formed classical circuit. -/
theorem isClassical_flipCodes {S : List ℕ} (hS : ∀ j ∈ S, j < m) :
    IsClassical m (flipCodes S) := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
  exact ⟨rfl, by simpa [WellFormed] using hS j hj⟩

/-- A list of distinct NOT gates flips exactly the selected bits. -/
theorem readBit_classicalRun_flipCodes {S : List ℕ} (hS : S.Nodup)
    (hvalid : ∀ j ∈ S, j < m) (x : Fin m → Bool) (c : ℕ) :
    readBit (classicalRun (flipCodes S) x) c = (readBit x c ^^ decide (c ∈ S)) := by
  induction S generalizing x with
  | nil => simp [flipCodes]
  | cons a S ih =>
    obtain ⟨ha, hS⟩ := List.nodup_cons.mp hS
    have hma : a < m := hvalid a (by simp)
    have hvalid' : ∀ j ∈ S, j < m := fun j hj => hvalid j (by simp [hj])
    rw [show flipCodes (a :: S) = (false, a, []) :: flipCodes S from rfl,
      classicalRun_cons, ih hS hvalid', readBit_classicalStep]
    by_cases hca : c = a
    · subst c
      simp [ha, hma]
    · simp [hca]

/-- Terminal NOT gates use no Hadamards. -/
@[simp] theorem hadamardCount_flipCodes (S : List ℕ) : hadamardCount (flipCodes S) = 0 := by
  induction S with
  | nil => rfl
  | cons a S ih => simpa [flipCodes] using ih

end GateCode

/-- The zero wires form a sublist of the pattern's wires. -/
theorem patternZeros_sublist (ps : List (ℕ × Bool)) :
    List.Sublist (patternZeros ps) (patternWires ps) :=
  List.filter_sublist.map _

/-- Converting a pattern to all-one form adds at most one gate per specified bit. -/
theorem length_patternZeros_le (ps : List (ℕ × Bool)) : (patternZeros ps).length ≤ ps.length := by
  simpa [patternWires] using (patternZeros_sublist ps).length_le

/-- Zero wires are distinct when the pattern's wires are distinct. -/
theorem nodup_patternZeros {ps : List (ℕ × Bool)} (hps : (patternWires ps).Nodup) :
    (patternZeros ps).Nodup :=
  hps.sublist (patternZeros_sublist ps)

/-- For a pattern on distinct wires, a specified wire is flipped exactly when its bit is zero. -/
theorem mem_patternZeros_iff {ps : List (ℕ × Bool)} (hps : (patternWires ps).Nodup)
    {p : ℕ × Bool} (hp : p ∈ ps) : p.1 ∈ patternZeros ps ↔ p.2 = false := by
  constructor
  · intro h
    obtain ⟨q, hq, hqp⟩ := List.mem_map.mp h
    obtain ⟨hq, hzero⟩ := List.mem_filter.mp hq
    have heq : q = p := List.inj_on_of_nodup_map hps hq hp hqp
    simpa [heq] using hzero
  · intro h
    exact List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, by simp [h]⟩, rfl⟩

/-- Appending a list of NOT gates does not change the Hadamard denominator. -/
theorem hadamardCount_append_flipCodes (gs : List GateCode) (S : List ℕ) :
    hadamardCount (gs ++ GateCode.flipCodes S) = hadamardCount gs := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    obtain ⟨b, t, cs⟩ := g
    cases b <;> simp [ih]

/-- The existing all-one event, expressed through numbered-wire reads. -/
theorem mem_onesAt_iff {S : List ℕ} {y : Fin m → Bool} :
    y ∈ onesAt m S ↔ ∀ j ∈ S, j < m ∧ readBit y j = true := by
  simp only [onesAt, mem_filter, mem_univ, true_and]
  apply forall_congr'
  intro j
  apply forall_congr'
  intro _
  exact ⟨fun ⟨h, hv⟩ => ⟨h, (readBit_of_lt y h).trans hv⟩,
    fun ⟨h, hv⟩ => ⟨h, (readBit_of_lt y h).symm.trans hv⟩⟩

/-- Flipping each desired-zero wire converts a valid pattern with distinct wires to an all-one
event. -/
theorem classicalRun_flipCodes_mem_onesAt_iff {ps : List (ℕ × Bool)}
    (hps : (patternWires ps).Nodup) (hvalid : ∀ p ∈ ps, p.1 < m) (y : Fin m → Bool) :
    GateCode.classicalRun (GateCode.flipCodes (patternZeros ps)) y ∈
        onesAt m (patternWires ps) ↔ y ∈ patternAt m ps := by
  have hzero : ∀ j ∈ patternZeros ps, j < m := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ((patternZeros_sublist ps).subset hj)
    exact hvalid p hp
  rw [mem_onesAt_iff, mem_patternAt]
  change (∀ j ∈ ps.map Prod.fst, _) ↔ _
  simp only [List.forall_mem_map]
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  rw [GateCode.readBit_classicalRun_flipCodes (nodup_patternZeros hps) hzero]
  have hdec : decide (p.1 ∈ patternZeros ps) = !p.2 := by
    simp only [mem_patternZeros_iff hps hp]
    cases p.2 <;> rfl
  rw [hdec]
  cases p.2 <;> cases readBit y p.1 <;> simp

/-- The probability of an arbitrary pattern is the existing all-one probability after terminal
NOTs on its desired-zero wires. -/
theorem onesProb_append_flipCodes_eq_patternProb (gs : List GateCode)
    {ps : List (ℕ × Bool)} (hps : (patternWires ps).Nodup)
    (hvalid : ∀ p ∈ ps, p.1 < m) (x : List Bool) :
    onesProb m (gs ++ GateCode.flipCodes (patternZeros ps)) (patternWires ps) x =
      patternProb m gs ps x := by
  have hzero : ∀ j ∈ patternZeros ps, j < m := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ((patternZeros_sublist ps).subset hj)
    exact hvalid p hp
  rw [onesProb, Circuit.ofCodes_append, Circuit.run, Circuit.eval_append,
    Circuit.measureProb_eval_ofCodes (GateCode.isClassical_flipCodes hzero)]
  change (∑ y, if GateCode.classicalRun (GateCode.flipCodes (patternZeros ps)) y ∈
    onesAt m (patternWires ps) then _ else 0) = _
  simp only [classicalRun_flipCodes_mem_onesAt_iff hps hvalid]
  rw [patternProb, measureProb, ← sum_filter, filter_mem_eq_of_subset (subset_univ _)]
  rfl

/-- A pattern event is a sum over its indicator on all measurement outcomes. -/
theorem measureProb_patternAt_eq_sum (ψ : Qubits m) (ps : List (ℕ × Bool)) :
    measureProb ψ (patternAt m ps) =
      ∑ y, if y ∈ patternAt m ps then ‖ψ.ofLp y‖ ^ 2 else 0 := by
  rw [measureProb, ← sum_filter, filter_mem_eq_of_subset (subset_univ _)]

/-- Splitting a pattern on the next valid wire partitions its probability exactly. This also
holds if that wire was already specified. -/
theorem measureProb_patternAt_partition (ψ : Qubits m) (ps : List (ℕ × Bool))
    {j : ℕ} (hj : j < m) :
    measureProb ψ (patternAt m ps) =
      measureProb ψ (patternAt m (ps ++ [(j, false)])) +
        measureProb ψ (patternAt m (ps ++ [(j, true)])) := by
  rw [measureProb_patternAt_eq_sum, measureProb_patternAt_eq_sum,
    measureProb_patternAt_eq_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro y _
  simp only [mem_patternAt_append]
  by_cases hy : y ∈ patternAt m ps
  · cases readBit y j <;> simp [hy, hj]
  · simp [hy]

/-- Circuit pattern probabilities partition under the next valid output bit. -/
theorem patternProb_partition (gs : List GateCode) (ps : List (ℕ × Bool))
    {j : ℕ} (hj : j < m) (x : List Bool) :
    patternProb m gs ps x = patternProb m gs (ps ++ [(j, false)]) x +
      patternProb m gs (ps ++ [(j, true)]) x :=
  measureProb_patternAt_partition _ _ hj

/-- Prepending a specified bit intersects the corresponding events. -/
theorem mem_patternAt_cons {ps : List (ℕ × Bool)} {j : ℕ} {b : Bool}
    {y : Fin m → Bool} :
    y ∈ patternAt m ((j, b) :: ps) ↔
      (j < m ∧ readBit y j = b) ∧ y ∈ patternAt m ps := by
  simp only [mem_patternAt, List.forall_mem_cons]

/-- A complete pattern on a wire list is exactly a fiber of reading those wires. -/
theorem mem_patternAt_zip_iff {S : List ℕ} {bs : List Bool}
    (hS : ∀ j ∈ S, j < m) (hlen : bs.length = S.length) (y : Fin m → Bool) :
    y ∈ patternAt m (S.zip bs) ↔ S.map (readBit y) = bs := by
  induction S generalizing bs with
  | nil =>
    have : bs = [] := List.eq_nil_of_length_eq_zero hlen
    subst bs
    simp
  | cons j S ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hj : j < m := hS j (by simp)
      have hS' : ∀ k ∈ S, k < m := fun k hk => hS k (by simp [hk])
      have hlen' : bs.length = S.length := by simpa using hlen
      rw [List.zip_cons_cons, mem_patternAt_cons, ih hS' hlen']
      simp [hj]

/-- The marginal of the existing measurement on a list of valid wires agrees with the pattern
probability. -/
theorem measure_map_readBit_apply (gs : List GateCode) (x : List Bool)
    {S : List ℕ} {bs : List Bool} (hS : ∀ j ∈ S, j < m)
    (hlen : bs.length = S.length) :
    ((Circuit.measure (Circuit.ofCodes m gs) (inputState m x)).map
      (fun y => S.map (readBit y))) bs = ENNReal.ofReal (patternProb m gs (S.zip bs) x) := by
  rw [PMF.map_apply, tsum_fintype, patternProb, measureProb_patternAt_eq_sum,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => by split_ifs <;> positivity)]
  apply sum_congr rfl
  intro y _
  simp only [mem_patternAt_zip_iff hS hlen]
  by_cases h : S.map (readBit y) = bs
  · simp [h]
  · simp [h, Ne.symm h]

/-- An arbitrary valid pattern has the existing projected signed-gap representation. Its
terminal NOT gates leave the denominator unchanged. -/
theorem patternProb_eq_onesGap (gs : List GateCode) (hgs : ∀ g ∈ gs, g.WellFormed m)
    {ps : List (ℕ × Bool)} (hps : (patternWires ps).Nodup)
    (hvalid : ∀ p ∈ ps, p.1 < m) (x : List Bool) :
    patternProb m gs ps x =
      (onesGap (patternWires ps) (gs ++ GateCode.flipCodes (patternZeros ps))
        (List.ofFn (inputState m x)) : ℝ) / 2 ^ hadamardCount gs := by
  have hzero : ∀ j ∈ patternZeros ps, j < m := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ((patternZeros_sublist ps).subset hj)
    exact hvalid p hp
  have hwf : ∀ g ∈ gs ++ GateCode.flipCodes (patternZeros ps), g.WellFormed m := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hgs g hg
    · exact (GateCode.isClassical_flipCodes hzero g hg).2
  rw [← onesProb_append_flipCodes_eq_patternProb gs hps hvalid,
    onesProb_eq_onesGap _ hwf, hadamardCount_append_flipCodes]

end Cslib.Quantum
