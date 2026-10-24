/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Word
public import Complexity.Computability.Circuit.Iteration
public import Complexity.Foundations.Combinatorics.FunctionalGraph
import Complexity.Tactic.Synthesis
import Mathlib.Tactic.Linarith

/-!
# Moving a residue into a repeated interval

If an orbit repeats with `f^[i] x = f^[j] x` for `i < j`, the state at any time `T ≥ i` is the
state at the unique time in `[i, j)` congruent to `T` modulo `j - i`. A circuit finds that time
without division: it looks up `T % (j - i)` in a table indexed by the period, which depends on the
fixed exponent `T` only through its residues, and then adds the period while the value is below
`i`. At most `K` additions suffice when `i ≤ K` (`liftResidue_reconstructs`).

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.liftResidue`: one bounded correction of a residue.
* `Cslib.Circuits.Boolean.Iteration.repeatWordIndex`: the word computation of the time in the
  repeated interval.

## Main results

* `Cslib.Circuits.Boolean.Iteration.liftResidue_reconstructs`: the corrected residue gives the
  state at time `T`.
* `Cslib.Circuits.Boolean.Iteration.repeatWordIndex_spec`: the same for the word computation.
* `Cslib.Circuits.Boolean.Iteration.synthesis_repeatWordIndex`: its gate count does not depend on
  `T`.

## References

* Adapted from lean/Proofs/Residues.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

/-- One bounded correction of a residue: add the period once if below the interval. -/
def liftResidue (lower period r : ℕ) : ℕ := if r < lower then r + period else r

/-- Repeated correction preserves the residue and never passes the interval. -/
private theorem liftResidue_invariant (lower period r t : ℕ) (hp : 0 < period) (hr : r < period) :
    let v := (liftResidue lower period)^[t] r
    (lower ≤ v ∨ t ≤ v) ∧ v < lower + period ∧ v % period = r := by
  induction t with
  | zero =>
    exact ⟨Or.inr (Nat.zero_le _), by simp only [Function.iterate_zero_apply]; omega,
      Nat.mod_eq_of_lt hr⟩
  | succ t ih =>
    dsimp only at ih ⊢
    rw [Function.iterate_succ_apply', liftResidue]
    split <;> rename_i h
    · refine ⟨?_, by omega, by simpa using ih.2.2⟩
      rcases ih.1 with hlow | ht
      · exact (not_lt_of_ge hlow h).elim
      · exact Or.inr (by omega)
    · exact ⟨Or.inl (by omega), ih.2⟩

/-- Enough corrections place the residue in the interval. -/
private theorem liftResidue_spec (lower period T K : ℕ) (hp : 0 < period) (hK : lower ≤ K) :
    let v := (liftResidue lower period)^[K] (T % period)
    lower ≤ v ∧ v < lower + period ∧ v % period = T % period := by
  have h := liftResidue_invariant lower period (T % period) K hp (Nat.mod_lt _ hp)
  exact ⟨h.1.elim id (hK.trans ·), h.2⟩

/-- The corrected residue lies in the repeated interval and gives the state at time `T`. -/
theorem liftResidue_reconstructs {α : Type*} {f : α → α} {x : α} {i j T K : ℕ}
    (hij : i < j) (heq : f^[i] x = f^[j] x) (hK : i ≤ K) (hT : i ≤ T) :
    let r := (liftResidue i (j - i))^[K] (T % (j - i))
    i ≤ r ∧ r < j ∧ f^[r] x = f^[T] x := by
  obtain ⟨hlo, hhi, hmod⟩ := liftResidue_spec i (j - i) T K (by omega) hK
  exact ⟨hlo, by omega, FunctionalGraph.iterate_eq_iterate_of_mod_eq hij.le heq hlo hT hmod⟩

/-- The word form of `liftResidue`. -/
def liftWord {w : ℕ} (lower period r : BitVec w) : BitVec w :=
  if r.ult lower then r + period else r

/-- The word correction agrees with the natural-number one when the interval fits. -/
private theorem liftWord_toNat {w : ℕ} (lower period r : BitVec w)
    (hfit : lower.toNat + period.toNat ≤ 2 ^ w) :
    (liftWord lower period r).toNat = liftResidue lower.toNat period.toNat r.toNat := by
  unfold liftWord liftResidue
  by_cases hr : r.toNat < lower.toNat
  · simp only [BitVec.ult, hr, decide_true, ↓reduceIte, BitVec.toNat_add]
    exact Nat.mod_eq_of_lt (by omega)
  · simp only [BitVec.ult, hr, decide_false, Bool.false_eq_true, ↓reduceIte]

private theorem liftWord_iterate_toNat {w : ℕ} (lower period r : BitVec w)
    (hfit : lower.toNat + period.toNat ≤ 2 ^ w) (K : ℕ) :
    ((liftWord lower period)^[K] r).toNat =
      (liftResidue lower.toNat period.toNat)^[K] r.toNat := by
  induction K with
  | zero => rfl
  | succ K ih => rw [Function.iterate_succ_apply', liftWord_toNat _ _ _ hfit, ih,
      Function.iterate_succ_apply']

/-- The residues of `T` modulo every period up to `K`, selected by the period. -/
def residueWord {w : ℕ} (T K : ℕ) (period : BitVec w) : BitVec w :=
  word (selectBits period fun j : Fin (K + 1) =>
    fun i : Fin w => (BitVec.ofNat w (T % j.val)).getLsbD i.val)

private theorem residueWord_toNat {w T K : ℕ} (period : BitVec w)
    (hK : K < 2 ^ w) (hp : 0 < period.toNat) (hpK : period.toNat ≤ K) :
    (residueWord T K period).toNat = T % period.toNat := by
  rw [residueWord, selectBits_of_toNat_lt _ _ (by omega), word_getLsbD,
    BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt ((Nat.mod_lt _ hp).trans_le (hpK.trans hK.le))

/-- The time in the repeated interval `[lo, hi)` that is congruent to `T`. -/
def repeatWordIndex {w : ℕ} (T K : ℕ) (lo hi : BitVec w) : BitVec w :=
  (liftWord lo (hi - lo))^[K] (residueWord T K (hi - lo))

/-- The word computation lies in the repeated interval and selects the state at time `T`. -/
theorem repeatWordIndex_spec {α : Type*} {f : α → α} {x : α} {w T K : ℕ}
    (lo hi : BitVec w) (hlt : lo.toNat < hi.toNat) (hhi : hi.toNat ≤ K)
    (hK : K < 2 ^ w) (hT : K ≤ T) (heq : f^[lo.toNat] x = f^[hi.toNat] x) :
    let r := (repeatWordIndex T K lo hi).toNat
    lo.toNat ≤ r ∧ r < hi.toNat ∧ f^[r] x = f^[T] x := by
  have hp : (hi - lo).toNat = hi.toNat - lo.toNat := BitVec.toNat_sub_of_le hlt.le
  have hfit : lo.toNat + (hi - lo).toNat ≤ 2 ^ w := by rw [hp]; have := hi.isLt; omega
  rw [repeatWordIndex, liftWord_iterate_toNat _ _ _ hfit,
    residueWord_toNat _ hK (by rw [hp]; omega) (by rw [hp]; omega), hp]
  exact liftResidue_reconstructs hlt heq (by omega) (by omega)

/-- One word correction: an addition, a comparison and a multiplexer. -/
private theorem synthesis_liftWord {n w : ℕ} (s : Set (BooleanFunction n))
    (lower period r : BitString n → BitVec w)
    (hl : ∀ i : Fin w, (fun x => (lower x).getLsbD i.val) ∈ s)
    (hp : ∀ i : Fin w, (fun x => (period x).getLsbD i.val) ∈ s)
    (hr : ∀ i : Fin w, (fun x => (r x).getLsbD i.val) ∈ s) :
    Synthesis interpretation s (wordWires fun x => liftWord (lower x) (period x) (r x))
      (21 * w + 3) := by
  let build := Synthesis.Builder.start interpretation s
  synthesis_step build using Synthesis.word_add r period
  synthesis_step build using Synthesis.word_ult r lower
  synthesis_step build using Synthesis.word_mux (fun x => r x + period x) r
    (fun x => (r x).ult (lower x))
  exact build.finish (by synthesis_available)
    (by dsimp +zetaDelta [Synthesis.Builder.add, Synthesis.Builder.start]; omega)

/-- Iterated word corrections, sharing all intermediate words. -/
private theorem synthesis_liftWord_iterate {n w : ℕ} (s : Set (BooleanFunction n))
    (lower period init : BitString n → BitVec w)
    (hl : ∀ i : Fin w, (fun x => (lower x).getLsbD i.val) ∈ s)
    (hp : ∀ i : Fin w, (fun x => (period x).getLsbD i.val) ∈ s)
    (hinit : ∀ i : Fin w, (fun x => (init x).getLsbD i.val) ∈ s) (K : ℕ) :
    Synthesis interpretation s
      (wordWires fun x => (liftWord (lower x) (period x))^[K] (init x))
      (K * (21 * w + 3)) := by
  let q := fun t => wordWires fun x => (liftWord (lower x) (period x))^[t] (init x)
  have hs := Synthesis.steps (I := interpretation) (s := s) q
    (21 * w + 3) K (by rintro _ ⟨i, rfl⟩; exact hinit i) fun t _ => ?_
  · exact hs.mono Set.Subset.rfl (Synthesis.subset_stages q le_rfl) le_rfl
  · simpa only [q, Function.iterate_succ_apply'] using
      synthesis_liftWord (s ∪ Synthesis.stages q t) lower period
        (fun x => (liftWord (lower x) (period x))^[t] (init x))
        (fun i => Or.inl (hl i)) (fun i => Or.inl (hp i))
        (fun i => Or.inr (Synthesis.subset_stages q le_rfl ⟨i, rfl⟩))

/-- A residue table costs only its word width and entry count, whatever `T` is. -/
private theorem synthesis_residueWord {n w : ℕ} (s : Set (BooleanFunction n))
    (T K : ℕ) (period : BitString n → BitVec w)
    (hp : ∀ i : Fin w, (fun x => (period x).getLsbD i.val) ∈ s)
    (hconst : ∀ b : Bool, (fun _ : BitString n => b) ∈ s) :
    Synthesis interpretation s (wordWires fun x => residueWord T K (period x))
      (w * ((K + 1) * (2 * w + 3) + 1)) := by
  have h := Synthesis.selectBits (s := s) period
    (fun j : Fin (K + 1) => fun _ => fun i : Fin w =>
      (BitVec.ofNat w (T % j.val)).getLsbD i.val) hp fun _ _ => hconst _
  simpa only [wordWires, residueWord, getLsbD_word] using h

/-- The repeated-interval index circuit has no dependence on the bit length of `T`. -/
theorem synthesis_repeatWordIndex {n w : ℕ} (s : Set (BooleanFunction n))
    (T K : ℕ) (lo hi : BitString n → BitVec w)
    (hlo : ∀ i : Fin w, (fun x => (lo x).getLsbD i.val) ∈ s)
    (hhi : ∀ i : Fin w, (fun x => (hi x).getLsbD i.val) ∈ s)
    (hconst : ∀ b : Bool, (fun _ : BitString n => b) ∈ s) :
    Synthesis interpretation s (wordWires fun x => repeatWordIndex T K (lo x) (hi x))
      (100 * (K + 1) * (w + 1) ^ 2) := by
  let p := fun x => hi x - lo x
  let r := fun x => residueWord T K (p x)
  let build := Synthesis.Builder.start interpretation s
  synthesis_step build using Synthesis.word_sub hi lo
  synthesis_step build using synthesis_residueWord build.wires T K p
  synthesis_step build using synthesis_liftWord_iterate (K := K) build.wires lo p r
  exact build.finish (by synthesis_available) (by
    dsimp +zetaDelta [Synthesis.Builder.add, Synthesis.Builder.start]
    nlinarith [Nat.zero_le (K * w ^ 2), Nat.zero_le (K * w)])

end Cslib.Circuits.Boolean.Iteration
