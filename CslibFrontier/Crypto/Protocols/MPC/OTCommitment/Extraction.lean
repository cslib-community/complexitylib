/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.OTCommitment.Opening
public import CslibFrontier.Foundations.Data.BitString.Threshold
public import CslibFrontier.Probability.StatisticalDistance.Coupling
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Tactic.PMFSwap

/-!
# Extracting the bit committed through ideal OT

The extractor reads the corrupted sender's actual OT inputs at the commit boundary, before the
opening is generated. It takes the strict majority of their pair parities, resolving ties to
false. This is simulator access to ideal-OT inputs, not extraction from a public commitment.

## Main definitions

* `OTCommitment.extract`: the bit fixed at the commit boundary.
* `OTCommitment.realOpening`, `OTCommitment.simulatedOpening`: real and simulated output laws.

## Main results

* `OTCommitment.wrongOpening_bound`: opposite-bit acceptance is at most `2⁻⌈k/2⌉`.
* `OTCommitment.openResult_disagreement_le`: filtering a wrong-bit opening has the same bound.
* `OTCommitment.simulatedOpening_coupled`: a coupling of receiver output and adversary state.

This is a fixed-length, stand-alone corrupted-sender output law, not full ideal commitment,
corrupt-receiver simulation, composition, or malicious MPC completeness. Strategies may be
computationally unbounded. The zero-call bound is one and asserts no useful extraction security.

## References

The underlying commitment construction is [Cramer2000], §7.1, printed p. 21. The extraction and
output-coupling analysis here is original; the source's two-opening bound is a different claim.
-/

public section

namespace Cslib.Crypto.Protocols.MPC.OTCommitment

open Cslib.Probability MeasureTheory
open scoped ENNReal

/-- Strict majority of the submitted OT pair parities; ties resolve to false. Only the simulator
sees these inputs. The sender's other two table entries do not affect honest receiver choices. -/
@[expose] def extract {k : ℕ} (ts : Fin k → Fin 4 → Bool) : Bool :=
  strictMajority k (fun i =>
    ts i (boolPairToFin4 (false, false)) ^^ ts i (boolPairToFin4 (false, true)))

private theorem accepts_choices_eq {k : ℕ} (ts : Fin k → Fin 4 → Bool)
    (b : Bool) (o : Opening k) {c d : Fin k → Bool}
    (hc : Accepts c (fun i => ts i (boolPairToFin4 (false, c i))) b o)
    (hd : Accepts d (fun i => ts i (boolPairToFin4 (false, d i))) b o)
    (h : ∀ i, (ts i (boolPairToFin4 (false, false)) ^^
      ts i (boolPairToFin4 (false, true))) = b → c i = d i) : c = d := by
  funext i
  by_cases he : c i = d i
  · exact he
  · apply h i
    have hc' := (hc i).2
    have hd' := (hd i).2
    have hp := (hc i).1
    cases hcbit : c i <;> cases hdbit : d i <;> simp only [hcbit, hdbit] at he hc' hd'
    all_goals simp_all

/-- A fixed opening to the opposite of the extracted bit is accepted on at most a
`2⁻⌈k/2⌉` fraction of the honest receiver's hidden choices.
Tables need not have consistent parity. -/
theorem wrongOpening_bound {k : ℕ} (ts : Fin k → Fin 4 → Bool) (b : Bool)
    (o : Opening k) (hb : extract ts ≠ b) :
    ((PMF.uniformOfFintype (Fin k → Bool)).map (fun c =>
      @decide (Accepts c (fun i => ts i (boolPairToFin4 (false, c i))) b o)
        (Classical.propDecidable _))) true ≤ (2 : ℝ≥0∞)⁻¹ ^ (k - k / 2) := by
  classical
  let good := {i : Fin k | (ts i (boolPairToFin4 (false, false)) ^^
    ts i (boolPairToFin4 (false, true))) = b}
  let win := fun c => Accepts c (fun i => ts i (boolPairToFin4 (false, c i))) b o
  have hinj : Function.Injective (fun c : {c // win c} => fun i : good => c.val i.val) := by
    intro c d he
    apply Subtype.ext
    exact accepts_choices_eq ts b o c.property d.property (fun i hi =>
      congrFun he ⟨i, hi⟩)
  have hcard : Nat.card {c // win c} ≤ 2 ^ (k / 2) := by
    have hle := Fintype.card_le_of_injective _ hinj
    have hmajor := BitString.card_filter_eq_le_half_of_strictMajorityOn_ne
      Finset.univ (fun i => ts i (boolPairToFin4 (false, false)) ^^
        ts i (boolPairToFin4 (false, true))) b
      (by simpa only [extract, strictMajority_eq_strictMajorityOn] using hb)
    have hg : Fintype.card good ≤ k / 2 := by
      simpa only [good, Fintype.card_subtype, Set.mem_ofPred_eq, Finset.card_univ,
        Fintype.card_fin] using hmajor
    rw [Nat.card_eq_fintype_card]
    exact hle.trans (by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hg)
  rw [Probability.PMF.uniformOfFintype_map_apply]
  simp only [decide_eq_true_eq]
  calc
    _ ≤ (2 ^ (k / 2) : ℝ≥0∞) / Fintype.card (Fin k → Bool) := by
      apply mul_le_mul_of_nonneg_right _ zero_le
      exact_mod_cast hcard
    _ = (2 : ℝ≥0∞)⁻¹ ^ (k - k / 2) := by
      simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
        Nat.cast_ofNat]
      have hk : k = k / 2 + (k - k / 2) := by omega
      conv_lhs => arg 2; rw [hk, pow_add]
      rw [div_eq_mul_inv, ENNReal.mul_inv, ← mul_assoc]
      · rw [ENNReal.mul_inv_cancel (by positivity) (by finiteness)]
        simp [ENNReal.inv_pow]
      all_goals simp

/-- Real corrupted-sender experiment, using the actual OT world. The sender state at the commit
boundary and its arbitrary auxiliary output are retained jointly with the honest receiver's result.
The opening continuation sees only sender state, never receiver choices or answers. -/
@[expose] noncomputable def realOpening {State Output : Type} (A : Sender State) (k : ℕ)
    (initial : PMF State)
    (finish : State → PMF (Option (Bool × Opening k) × Output)) :
    PMF (Option Bool × State × Output) := do
  let st ← initial
  let choices ← PMF.uniformOfFintype (Fin k → Bool)
  let (received, final) ← senderRun A k st choices
  let (submission, out) ← finish final
  pure (openResult choices received submission, final, out)

/-- A simulator for the corrupted-sender output experiment. At the commit boundary it reads the
corrupted sender's ideal-OT inputs and irrevocably fixes `committed`. It privately samples the
honest receiver's choices. After running the sender's opening continuation, it requests release
of the stored bit exactly when the emulated receiver accepted that bit; otherwise it aborts.

The ideal receiver obtains only the stored bit or abort. The sender receives no information
about `committed`, the choices, or the received OT bits. This definition describes one stand-alone
corruption case, not a full ideal commitment functionality or a composable simulator. -/
@[expose] noncomputable def simulatedOpening {State Output : Type} (A : Sender State) (k : ℕ)
    (initial : PMF State)
    (finish : State → PMF (Option (Bool × Opening k) × Output)) :
    PMF (Option Bool × State × Output) := do
  let st ← initial
  let (ts, final) ← senderTables A k st
  let committed := extract ts
  let choices ← PMF.uniformOfFintype (Fin k → Bool)
  let (submission, out) ← finish final
  let result := openResult choices
    (fun i => ts i (boolPairToFin4 (false, choices i))) submission
  pure (if result = some committed then some committed else none, final, out)

/-- For fixed actual OT tables and one opening attempt, filtering an accepted wrong bit
changes the receiver result with probability at most the majority extraction error. -/
theorem openResult_disagreement_le {k : ℕ} (ts : Fin k → Fin 4 → Bool)
    (submission : Option (Bool × Opening k)) :
    (PMF.uniformOfFintype (Fin k → Bool)).toOuterMeasure {c |
      let result := openResult c (fun i => ts i (boolPairToFin4 (false, c i))) submission
      result ≠ (if result = some (extract ts) then some (extract ts) else none)} ≤
        (2 : ℝ≥0∞)⁻¹ ^ (k - k / 2) := by
  classical
  cases submission with
  | none => simp [openResult]
  | some submission =>
      obtain ⟨b, o⟩ := submission
      by_cases hb : extract ts = b
      · simp [openResult, hb]
      · have h := wrongOpening_bound ts b o hb
        rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply] at h
        refine (measure_mono ?_).trans h
        intro c hc
        simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq]
        by_contra hn
        simp [openResult, hn] at hc

/-- The real and simulated laws of receiver output, sender commit-final state, and auxiliary
output admit a coupling with disagreement at most `2⁻⌈k/2⌉`. No finiteness or computational bound
on the sender state is required. This is one stand-alone corrupted-sender output law; it does
not assert full ideal commitment realization or polynomial-time simulation. -/
theorem simulatedOpening_coupled {State Output : Type} (A : Sender State) (k : ℕ)
    (initial : PMF State)
    (finish : State → PMF (Option (Bool × Opening k) × Output)) :
    Probability.PMF.CoupledWithin (realOpening A k initial finish)
      (simulatedOpening A k initial finish) ((2 : ℝ≥0∞)⁻¹ ^ (k - k / 2)) := by
  classical
  let joint := do
    let st ← initial
    let (ts, final) ← senderTables A k st
    let (submission, out) ← finish final
    let choices ← PMF.uniformOfFintype (Fin k → Bool)
    let result := openResult choices
      (fun i => ts i (boolPairToFin4 (false, choices i))) submission
    pure ((result, final, out),
      (if result = some (extract ts) then some (extract ts) else none, final, out))
  refine ⟨joint, ?_, ?_, ?_⟩
  · simp only [joint, realOpening, Probability.PMF.monad_bind_eq_bind,
      Probability.PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map,
      senderRun_eq, PMF.bind_map]
    pmf_swap
    rfl
  · simp only [joint, simulatedOpening, Probability.PMF.monad_bind_eq_bind,
      Probability.PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map]
    pmf_swap
  · simp only [joint, Probability.PMF.monad_bind_eq_bind,
      Probability.PMF.monad_pure_eq_pure]
    apply Probability.PMF.toOuterMeasure_bind_le
    intro st
    apply Probability.PMF.toOuterMeasure_bind_le
    rintro ⟨ts, final⟩
    apply Probability.PMF.toOuterMeasure_bind_le
    rintro ⟨submission, out⟩
    change ((PMF.uniformOfFintype (Fin k → Bool)).map _).toOuterMeasure _ ≤ _
    rw [PMF.toOuterMeasure_map_apply]
    simpa only [Set.preimage_ofPred_eq, ne_eq, Prod.mk.injEq, and_true, eq_self] using
      openResult_disagreement_le ts submission

end Cslib.Crypto.Protocols.MPC.OTCommitment
