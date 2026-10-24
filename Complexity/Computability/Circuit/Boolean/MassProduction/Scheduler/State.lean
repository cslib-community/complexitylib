/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.MassProduction.Schedule
public import Complexity.Computability.Circuit.Boolean.Substitution
public import Complexity.Algorithms.Lean.Sort.Bitonic.Basic
public import Complexity.Foundations.Data.BitString.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.PiLex
import Complexity.Algorithms.Lean.Sort.Bitonic.Correctness
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Scheduler states

The scheduler keeps `2 ^ D` records in fixed positions. A record holds the `D`-bit label of its
original request, the bits of that request's target point, and `s` listed points of a line. The
first `a` positions hold accepted requests. `Good targets a x` says that the records are a
permutation of the labelled requests, that every accepted record lists the punctured line through
its target with some nonzero direction, and that accepted lines are pairwise disjoint.

The initial state lists every request in its original position, with no accepted line. When all
records are accepted, sorting by label restores the original order: each label has a fixed rank
(`rank`), so a final wiring reads every request's line from its sorted position (`finalOutput`).

## Main definitions

* `Cslib.Circuits.Boolean.MassProduction.Scheduler.width`,
  `Cslib.Circuits.Boolean.MassProduction.Scheduler.labelBit`,
  `Cslib.Circuits.Boolean.MassProduction.Scheduler.targetBit`,
  `Cslib.Circuits.Boolean.MassProduction.Scheduler.lineBit`,
  `Cslib.Circuits.Boolean.MassProduction.Scheduler.label`,
  `Cslib.Circuits.Boolean.MassProduction.Scheduler.target`,
  `Cslib.Circuits.Boolean.MassProduction.Scheduler.line`,
  `Cslib.Circuits.Boolean.MassProduction.Scheduler.encode`: the record layout, field projections,
  and request label encoding.
* `Cslib.Circuits.Boolean.MassProduction.Scheduler.Good`: the scheduler invariant.
* `Cslib.Circuits.Boolean.MassProduction.Scheduler.initialSubstitution`: the initial records.
* `Cslib.Circuits.Boolean.MassProduction.Scheduler.sortedByLabel`,
  `Cslib.Circuits.Boolean.MassProduction.Scheduler.finalOutput`: sorting records by label and
  reading lines in original order.

## Main results

* `Cslib.Circuits.Boolean.MassProduction.Scheduler.good_initial`: the initial state is good.
* `Cslib.Circuits.Boolean.MassProduction.Scheduler.finalOutput_eq_lineBits`: a fully accepted
  good state yields a valid schedule.

## References

* Adapted from MassProduction/Nonuniform/BufferModel.lean,
  MassProduction/Nonuniform/BufferEndpoints.lean and
  MassProduction/Nonuniform/RecordArray.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction],
  using the sorting network of
  [K. E. Batcher, *Sorting Networks and Their Applications*][Batcher1968].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MassProduction.Scheduler

open Finset BitString LineCode

variable {K : Type*} [Field K] {ℓ b s D : ℕ}

/-! ### Points -/

variable [Fintype K] [DecidableEq K]

/-- The punctured line lists the points `u + scalar c • v`. -/
theorem mem_puncturedLine_iff (scalar : Fin s ≃ {c : K // c ≠ 0}) {u v w : Fin ℓ → K} :
    w ∈ puncturedLine u v ↔ ∃ c, u + (scalar c : K) • v = w := by
  simp only [puncturedLine, mem_image, mem_erase, mem_univ, and_true]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨scalar.symm ⟨c, hc⟩, by rw [Equiv.apply_symm_apply]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨scalar c, (scalar c).2, rfl⟩

omit [Fintype K] [DecidableEq K] in
/-- A line with a nonzero direction lists distinct points. -/
theorem add_smul_injective (scalar : Fin s ≃ {c : K // c ≠ 0}) {u v : Fin ℓ → K} (hv : v ≠ 0) :
    Function.Injective fun c => u + (scalar c : K) • v := by
  intro c c' h
  have h' : ((scalar c : K) - scalar c') • v = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact add_left_cancel h
  rcases smul_eq_zero.mp h' with h'' | h''
  · exact scalar.injective (Subtype.ext (sub_eq_zero.mp h''))
  · exact absurd h'' hv

/-! ### Records -/

/-- A record: `D` label bits, a target point of `L` bits, and `s` listed points. -/
abbrev width (D L s : ℕ) : ℕ := D + (L + s * L)

/-- The position of a label bit in a record. -/
def labelBit {L : ℕ} (j : Fin D) : Fin (width D L s) := Fin.castAdd _ j

/-- The position of a target bit in a record. -/
def targetBit {L : ℕ} (β : Fin L) : Fin (width D L s) := Fin.natAdd D (Fin.castAdd (s * L) β)

/-- The position of a bit of a listed point in a record. -/
def lineBit {L : ℕ} (c : Fin s) (β : Fin L) : Fin (width D L s) :=
  Fin.natAdd D (Fin.natAdd L (finProdFinEquiv (c, β)))

variable {t L : ℕ}

/-- The label bits of record `m`. -/
def label (x : BitString (t * width D L s)) (m : Fin t) : BitString D :=
  fun j => x (finProdFinEquiv (m, labelBit j))

/-- The target bits of record `m`. -/
def target (x : BitString (t * width D L s)) (m : Fin t) : BitString L :=
  fun β => x (finProdFinEquiv (m, targetBit β))

/-- The bits of listed point `c` of record `m`. -/
def line (x : BitString (t * width D L s)) (m : Fin t) (c : Fin s) : BitString L :=
  fun β => x (finProdFinEquiv (m, lineBit c β))

variable (D) in
/-- The label of an original request: its binary numbering. -/
def encode (i : Fin (2 ^ D)) : BitString D := (BitString.equivFin D).symm i

/-- Distinct requests have distinct labels. -/
theorem encode_injective : Function.Injective (encode D) := (BitString.equivFin D).symm.injective

/-- The state invariant after `a` acceptances: the records are a permutation `π` of the labelled
requests, every accepted record lists the punctured line through its target with a nonzero
direction, and accepted lines are pairwise disjoint. -/
def Good (bits : K ≃+ BitString b) (scalar : Fin s ≃ {c : K // c ≠ 0})
    (targets : Fin (2 ^ D) → Fin ℓ → K) (a : ℕ) (x : BitString (2 ^ D * width D (ℓ * b) s)) :
    Prop :=
  ∃ (π : Equiv.Perm (Fin (2 ^ D))) (dirs : Fin (2 ^ D) → Fin ℓ → K),
    (∀ m, label x m = encode D (π m)) ∧
    (∀ m, target x m = pointBits bits (targets (π m))) ∧
    (∀ m, m.val < a → dirs m ≠ 0 ∧
      ∀ c, line x m c = pointBits bits (targets (π m) + (scalar c : K) • dirs m)) ∧
    ∀ m m', m.val < a → m'.val < a → m ≠ m' →
      Disjoint (puncturedLine (targets (π m)) (dirs m)) (puncturedLine (targets (π m')) (dirs m'))

/-! ### The initial state -/

/-- The initial records: each request in its original position, labelled by its position, with
its target bits and an empty line. -/
def initialSubstitution (D L s : ℕ) : Fin (2 ^ D * width D L s) → Fin (2 ^ D * L) ⊕ Bool := fun q =>
  let mf := finProdFinEquiv.symm q
  Fin.addCases (fun j => .inr (encode D mf.1 j))
    (Fin.addCases (fun β => .inl (finProdFinEquiv (mf.1, β))) (fun _ => .inr false)) mf.2

/-- The initial state is good with no accepted requests. -/
theorem good_initial (bits : K ≃+ BitString b) (scalar : Fin s ≃ {c : K // c ≠ 0})
    (targets : Fin (2 ^ D) → Fin ℓ → K) :
    Good bits scalar targets 0
      (substitute (initialSubstitution D (ℓ * b) s) (targetBits bits targets)) := by
  refine ⟨Equiv.refl _, 0, fun m => ?_, fun m => ?_, fun m hm => absurd hm (Nat.not_lt_zero _),
    fun m _ hm => absurd hm (Nat.not_lt_zero _)⟩
  · funext j
    simp [label, labelBit, initialSubstitution, substitute]
  · funext β
    simp [target, targetBit, initialSubstitution, substitute, targetBits]

/-! ### Restoring the original order -/

open Classical in
/-- The sorted position of a label: the number of smaller labels. -/
noncomputable def rank (i : Fin (2 ^ D)) : Fin (2 ^ D) :=
  ⟨#{i' | toLex (encode D i') < toLex (encode D i)}, by
    calc #{i' | toLex (encode D i') < toLex (encode D i)}
        < #(univ : Finset (Fin (2 ^ D))) :=
          card_lt_card ⟨subset_univ _, fun h => by
            have h' := h (mem_univ i)
            simp only [mem_filter, mem_univ, true_and] at h'
            exact lt_irrefl _ h'⟩
      _ = 2 ^ D := by simp⟩

/-- Records sorted by label. -/
noncomputable def sortedByLabel (x : BitString (2 ^ D * width D L s)) :
    Fin (BitonicSort.arity D) → BitString (width D L s) :=
  BitonicSort.sort (fun record => toLex (record ∘ labelBit)) D true
    fun j f => x (finProdFinEquiv (Fin.cast (BitonicSort.arity_eq_two_pow D) j, f))

/-- Every request's listed line, read from its label's sorted position. -/
noncomputable def finalOutput (x : BitString (2 ^ D * width D L s)) :
    BitString (2 ^ D * (s * L)) := fun q =>
  let ip := finProdFinEquiv.symm q
  let cb := finProdFinEquiv.symm ip.2
  sortedByLabel x (Fin.cast (BitonicSort.arity_eq_two_pow D).symm (rank ip.1)) (lineBit cb.1 cb.2)

/-- Sorting by distinct labels places the record of request `i` at its rank. -/
theorem sortedByLabel_rank {x : BitString (2 ^ D * width D L s)} (π : Equiv.Perm (Fin (2 ^ D)))
    (hlabel : ∀ m, label x m = encode D (π m)) (i : Fin (2 ^ D)) :
    sortedByLabel x (Fin.cast (BitonicSort.arity_eq_two_pow D).symm (rank i)) =
      fun f => x (finProdFinEquiv (π.symm i, f)) := by
  have h2 := BitonicSort.arity_eq_two_pow D
  let input : Fin (BitonicSort.arity D) → BitString (width D L s) :=
    fun j f => x (finProdFinEquiv (Fin.cast h2 j, f))
  let key : BitString (width D L s) → Lex (Fin D → Bool) := fun record => toLex (record ∘ labelBit)
  have hkey (j : Fin (BitonicSort.arity D)) :
      key (input j) = toLex (encode D (π (Fin.cast h2 j))) :=
    congrArg toLex (hlabel (Fin.cast h2 j))
  let source := Fin.cast h2.symm (π.symm i)
  have hsource : π (Fin.cast h2 source) = i := by simp [source]
  refine List.Perm.apply_ofFn_eq_of_rank (BitonicSort.sort_perm key D true input).symm key
    (BitonicSort.monotone_sort key D input) source _ (fun j hj => ?_) ?_
  · rw [hkey, hkey, hsource] at hj
    have h' : π (Fin.cast h2 j) = i := encode_injective (toLex_inj.mp hj)
    apply Fin.cast_injective h2
    rw [show Fin.cast h2 source = π.symm i by simp [source], ← h', Equiv.symm_apply_apply]
  · simp only [Fin.val_cast, rank, hkey, hsource]
    exact card_equiv ((finCongr h2).trans π) fun j => by
      simp only [mem_filter, mem_univ, true_and, Equiv.trans_apply, finCongr_apply]
      exact Iff.rfl

/-- When every record is accepted, the final output lists, for every request in its original
position, a punctured line through its target; the lines have nonzero directions and are
pairwise disjoint. -/
theorem finalOutput_eq_lineBits (bits : K ≃+ BitString b) (scalar : Fin s ≃ {c : K // c ≠ 0})
    {targets : Fin (2 ^ D) → Fin ℓ → K} {x : BitString (2 ^ D * width D (ℓ * b) s)}
    (hx : Good bits scalar targets (2 ^ D) x) :
    ∃ directions : Fin (2 ^ D) → Fin ℓ → K, (∀ i, directions i ≠ 0) ∧
      (∀ i j, i ≠ j → Disjoint (puncturedLine (targets i) (directions i))
        (puncturedLine (targets j) (directions j))) ∧
      finalOutput x = lineBits bits (fun c => (scalar c : K)) targets directions := by
  obtain ⟨π, dirs, hlabel, -, hline, hdisj⟩ := hx
  refine ⟨fun i => dirs (π.symm i), fun i => (hline _ (π.symm i).isLt).1, fun i j hij => ?_, ?_⟩
  · have h := hdisj (π.symm i) (π.symm j) (π.symm i).isLt (π.symm j).isLt
      (fun h => hij (π.symm.injective h))
    simpa only [Equiv.apply_symm_apply] using h
  · funext q
    obtain ⟨⟨i, q'⟩, rfl⟩ := finProdFinEquiv.surjective q
    obtain ⟨⟨c, β⟩, rfl⟩ := finProdFinEquiv.surjective q'
    have h := congrFun ((hline (π.symm i) (π.symm i).isLt).2 c) β
    simp only [line, Equiv.apply_symm_apply] at h
    simp only [finalOutput, lineBits, blocksEquiv_symm_apply, Equiv.symm_apply_apply,
      sortedByLabel_rank π hlabel]
    exact h

end Cslib.Circuits.Boolean.MassProduction.Scheduler
