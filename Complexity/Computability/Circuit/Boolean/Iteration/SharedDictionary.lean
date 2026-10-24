/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration
public import Complexity.Computability.Circuit.Boolean.BatchOr
import Mathlib.Tactic.Linarith

/-!
# Finishing trajectories with a shared checkpoint dictionary

Several fixed-power computations can share their checkpoint table. One batched lookup answers,
for every state of every orbit prefix, whether it is a checkpoint and which state the table stores
with it (`synthesis_lookupOr`); the lookup sorts all queries together with the table once, using
`batchOrCircuit`. Each trajectory then finishes on its own: the last flagged prefix time selects
a payload, which is advanced by the remaining steps (`finishHit`, `synthesis_finishHit`), and a
trajectory without a flagged time must repeat early, where the fixed-power circuit without
checkpoints is correct (`exists_repeat_power`).

All gates of the native De Morgan basis, including constants, are charged; wiring and fanout
are free.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.lookupOr`: the OR of the values stored under a key.
* `Cslib.Circuits.Boolean.Iteration.hitRecord`,
  `Cslib.Circuits.Boolean.Iteration.hitIndex`,
  `Cslib.Circuits.Boolean.Iteration.hitPayload`: a flagged checkpoint-hit record and its time and
  payload projections.
* `Cslib.Circuits.Boolean.Iteration.finishHit`: the state reached from the last flagged hit.

## Main results

* `Cslib.Circuits.Boolean.Iteration.synthesis_lookupOr`: one shared lookup for many queries.
* `Cslib.Circuits.Boolean.Iteration.finishHit_correct`,
  `Cslib.Circuits.Boolean.Iteration.synthesis_finishHit`: finishing one trajectory.
* `Cslib.Circuits.Boolean.Iteration.exists_repeat_power`: a fixed power on orbits that repeat
  early, with no checkpoints.

## References

* Adapted from lean/Proofs/{BatchLookup,BatchFinish}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
* The lookup is `batchOrCircuit`, after
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

variable {n w a M : ℕ}

/-! ### Shared lookup -/

section Lookup

variable {k v : ℕ}

/-- The bitwise OR of the values stored under `key`. With distinct keys this is the value stored
under `key`, and all-false if `key` is absent (`lookupOr_of_eq`, `lookupOr_of_forall_ne`). -/
def lookupOr (keys : Fin M → BitString k) (values : Fin M → BitString v) (key : BitString k) :
    BitString v :=
  fun bit => decide (∃ j, keys j = key ∧ values j bit = true)

/-- With injective keys, `lookupOr` returns the value at the matching entry. -/
theorem lookupOr_of_eq {keys : Fin M → BitString k} (values : Fin M → BitString v)
    (hkeys : Function.Injective keys) {j : Fin M} {key : BitString k} (h : keys j = key) :
    lookupOr keys values key = values j := by
  funext bit
  apply Bool.eq_iff_iff.mpr
  simp only [lookupOr, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, hv⟩
    rwa [hkeys (hi.trans h.symm)] at hv
  · exact fun hv => ⟨j, h, hv⟩

/-- When `key` is absent from `keys`, `lookupOr` returns the all-false bit string. -/
theorem lookupOr_of_forall_ne {keys : Fin M → BitString k} (values : Fin M → BitString v)
    {key : BitString k} (h : ∀ j, keys j ≠ key) : lookupOr keys values key = fun _ => false := by
  funext bit
  simp only [lookupOr, decide_eq_false_iff_not, not_exists, not_and]
  exact fun j hj => absurd hj (h j)

/-- **Shared lookup.** Answering `Q` available queries against one hardwired table of `M` keys
costs one `batchOrCircuit`: at most `48 * (Q + M + 1) * (⌈log₂ (Q + M)⌉ + 1) ^ 2 * (k + v + 1)`
gates, constants included. -/
theorem synthesis_lookupOr {Q : ℕ} (s : Set (BooleanFunction a)) (keys : Fin M → BitString k)
    (values : Fin M → BitString v) (queries : BitString a → Fin Q → BitString k)
    (hq : ∀ q bit, (fun x => queries x q bit) ∈ s) :
    Synthesis interpretation s (⋃ q, wires fun x => lookupOr keys values (queries x q))
      (48 * (Q + M + 1) * (Nat.clog 2 (Q + M) + 1) ^ 2 * (k + v + 1)) := by
  let c := batchOrCircuit (input := Q * k) (fun j i => Sum.inr (keys j i))
    (fun j bit => Sum.inr (values j bit)) (fun q i => Sum.inl (finProdFinEquiv (q, i)))
  have h := Synthesis.circuit (I := interpretation) (s := s) c
    (fun i x => queries x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)
    fun i => hq _ _
  refine h.mono Set.Subset.rfl ?_ (size_batchOrCircuit_le _ _ _)
  intro g hg
  obtain ⟨q, bit, rfl⟩ := Set.mem_iUnion.mp hg
  refine ⟨finProdFinEquiv (q, bit), funext fun x => Bool.eq_iff_iff.mpr ?_⟩
  let y : BitString (Q * k) := fun i => queries x (finProdFinEquiv.symm i).1
    (finProdFinEquiv.symm i).2
  have hkey (j : Fin M) : substitute (fun i => Sum.inr (keys j i)) y = keys j :=
    funext fun _ => substitute_inr rfl
  have hval (j : Fin M) : substitute (fun bit => Sum.inr (values j bit)) y bit = values j bit :=
    substitute_inr rfl
  have hquery : substitute (fun i => Sum.inl (finProdFinEquiv (q, i))) y = queries x q :=
    funext fun i => (substitute_inl rfl).trans (by simp only [y, Equiv.symm_apply_apply])
  rw [eval_batchOrCircuit_iff]
  change (∃ j, substitute _ y = substitute _ y ∧ substitute _ y bit = true) ↔ _
  simp only [hkey, hval, hquery, lookupOr, decide_eq_true_eq]

end Lookup

/-! ### Finishing one trajectory -/

/-- A hit at prefix time `index` with stored state `payload`: a set flag, then `index` in `w`
bits, then the payload. -/
def hitRecord (index : ℕ) (payload : BitString n) : BitString (w + n + 1) :=
  Fin.cons true (Fin.append (fun bit : Fin w => (BitVec.ofNat w index).getLsbD bit.val) payload)

/-- The time field of a hit record. -/
def hitIndex (record : BitString (w + n + 1)) : BitVec w :=
  word fun bit => record (Fin.castAdd n bit).succ

/-- The payload field of a hit record. -/
def hitPayload (record : BitString (w + n + 1)) : BitString n :=
  fun bit => record (Fin.natAdd w bit).succ

/-- Bit zero of `hitRecord` is the set hit flag `true`. -/
@[simp] theorem hitRecord_zero (index : ℕ) (payload : BitString n) :
    hitRecord (w := w) index payload 0 = true := rfl

/-- Reading `hitIndex` from `hitRecord index payload` recovers `BitVec.ofNat w index`. -/
@[simp] theorem hitIndex_hitRecord (index : ℕ) (payload : BitString n) :
    hitIndex (hitRecord (w := w) index payload) = BitVec.ofNat w index := by
  simpa only [hitIndex, hitRecord, Fin.cons_succ, Fin.append_left] using
    word_getLsbD (BitVec.ofNat w index)

/-- Reading `hitPayload` from `hitRecord index payload` recovers `payload`. -/
@[simp] theorem hitPayload_hitRecord (index : ℕ) (payload : BitString n) :
    hitPayload (hitRecord (w := w) index payload) = payload := by
  funext bit
  simp only [hitPayload, hitRecord, Fin.cons_succ, Fin.append_right]

/-- The state `K - j` steps after the payload at the last flagged prefix time `j`, or `fallback`
if no time is flagged. -/
def finishHit (f : BitString n → BitString n) (K : ℕ) (flags : Fin (K + 1) → Bool)
    (payloads : Fin (K + 1) → BitString n) (fallback : BitString n) : BitString n :=
  let chosen := chooseRecord flags (fun j => hitRecord (w := w) j.val (payloads j))
    (fun _ => false) (K + 1)
  if chosen 0 then hitValue f K (hitIndex chosen) (hitPayload chosen) else fallback

/-- If every flagged prefix time `j` carries `f^[T - K] (f^[j] x)`, and the fallback is correct
when no time is flagged, the finished state is `f^[T] x`. -/
theorem finishHit_correct (f : BitString n → BitString n) (T K : ℕ) (x : BitString n)
    (flags : Fin (K + 1) → Bool) (payloads : Fin (K + 1) → BitString n) (fallback : BitString n)
    (hK : K < 2 ^ w) (hT : K ≤ T)
    (hyes : ∀ j, flags j = true → payloads j = f^[T - K] (f^[j.val] x))
    (hno : (∀ j, flags j = false) → fallback = f^[T] x) :
    finishHit (w := w) f K flags payloads fallback = f^[T] x := by
  unfold finishHit
  by_cases hh : ∃ j, flags j = true
  · obtain ⟨j, -, hj, he⟩ := chooseRecord_spec flags
      (fun j => hitRecord (w := w) j.val (payloads j)) (fun _ => false) (K + 1)
      (by obtain ⟨j, hj⟩ := hh; exact ⟨j, j.isLt, hj⟩)
    simp only [he, hitRecord_zero, ite_true, hitIndex_hitRecord, hitPayload_hitRecord,
      hyes j hj]
    exact hitValue_spec f T K j.val x (Nat.le_of_lt_succ j.isLt) hK hT
  · have hf : ∀ j, flags j = false := fun j => Bool.eq_false_iff.mpr fun hj => hh ⟨j, hj⟩
    simp only [chooseRecord_of_forall_eq_false _ _ _ hf, Bool.false_eq_true, ite_false]
    exact hno hf

/-- Finishing a trajectory: selecting the last hit, advancing its payload and choosing the
fallback. -/
theorem synthesis_finishHit (c : Circuit signature n n) (s : Set (BooleanFunction a)) (K : ℕ)
    (flags : BitString a → Fin (K + 1) → Bool) (payloads : BitString a → Fin (K + 1) → BitString n)
    (fallback : BitString a → BitString n) (hf : ∀ j, (fun x => flags x j) ∈ s)
    (hp : ∀ j bit, (fun x => payloads x j bit) ∈ s)
    (hc : ∀ b : Bool, (fun _ : BitString a => b) ∈ s)
    {C : ℕ} (hfall : Synthesis interpretation s (wires fallback) C) :
    Synthesis interpretation s
      (wires fun x => finishHit (w := w) (c.eval interpretation) K (flags x) (payloads x)
        (fallback x))
      ((K + 1) * (4 * (w + n + 1)) + K * c.size + 200 * (K + 1) * (n + w + 1) ^ 2 + C +
        4 * n) := by
  let chosen := fun x => chooseRecord (flags x)
    (fun j => hitRecord (w := w) j.val (payloads x j)) (fun _ => false) (K + 1)
  have hsel := synthesis_chooseRecord s flags (fun x j => hitRecord (w := w) j.val (payloads x j))
    (fun _ _ => false) hf (fun j bit => ?_) fun _ => hc false
  · let src := s ∪ wires chosen
    have hi : ∀ bit : Fin w, (fun x => (hitIndex (chosen x)).getLsbD bit.val) ∈ src := by
      intro bit
      simp only [hitIndex, getLsbD_word]
      exact Or.inr ⟨_, rfl⟩
    have hpay : wires (fun x => hitPayload (chosen x)) ⊆ src := by
      rintro _ ⟨bit, rfl⟩
      exact Or.inr ⟨_, rfl⟩
    have hh := synthesis_hitValue src c K (fun x => hitIndex (chosen x))
      (fun x => hitPayload (chosen x)) hi hpay fun b => Or.inl (hc b)
    have hout := synthesis_ite hh (hfall.mono Set.subset_union_left Set.Subset.rfl le_rfl)
      (Synthesis.of_mem (s := src) (Or.inr ⟨0, rfl⟩))
    exact (hsel.trans hout).mono Set.Subset.rfl Set.Subset.rfl (by omega)
  · induction bit using Fin.cases with
    | zero => exact hc true
    | succ bit =>
      induction bit using Fin.addCases with
      | left bit => simpa only [hitRecord, Fin.cons_succ, Fin.append_left] using hc _
      | right bit => simpa only [hitRecord, Fin.cons_succ, Fin.append_right] using hp j bit

/-- **Fixed powers on early repeats.** The fixed-power circuit without checkpoints computes
`f^[T]` on every state whose orbit repeats among its first `L` states, for `2 L ≤ T`. -/
theorem exists_repeat_power (c : Circuit signature n n) (T L : ℕ) (hL : 0 < L)
    (hLN : L ≤ 2 ^ n) (hT : 2 * L ≤ T) :
    ∃ out : Circuit signature n n,
      (∀ x, FunctionalGraph.Repeats (c.eval interpretation) x L →
        out.eval interpretation x = (c.eval interpretation)^[T] x) ∧
      out.size ≤ 40000 * powerBudget n c.size 0 L := by
  let d := Nat.clog 2 (2 * L + 1)
  have hcap : 0 + (2 * L + 1) ≤ BitonicSort.arity d := by
    simpa only [Nat.zero_add, BitonicSort.arity_eq_two_pow] using
      Nat.le_pow_clog (by decide : 1 < 2) (2 * L + 1)
  have hd : d ≤ n + 2 := by
    apply Nat.clog_le_of_le_pow
    simp only [Nat.pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega
  have hpow : 2 ^ d ≤ 2 * (0 + 2 * L + 1) := by
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (show 1 < 2 * L + 1 by omega)
    have hdpos : 0 < d := Nat.clog_pos (by decide) (by omega)
    rw [show 2 ^ d = 2 ^ (d - 1) * 2 by rw [← Nat.pow_succ, show (d - 1).succ = d by omega]]
    change 2 ^ (d - 1) < 2 * L + 1 at hp
    omega
  have hfit : 2 * L < 2 ^ (n + 2) := by
    simp only [Nat.pow_succ]
    omega
  obtain ⟨out, hout, hs⟩ := exists_fixedOutput (w := n + 2) c T (2 * L) d (Fin.elim0 :
    Fin 0 → BitString n)
  refine ⟨out, fun x hx => ?_, ?_⟩
  · rw [hout]
    apply reconstruct_spec _ T (2 * L) _ x _ _ hfit hT
    apply Record.detect_sorted_witness _ T (2 * L) d _ x hcap hfit
    obtain ⟨i, j, hij, hj, he⟩ := hx
    exact Or.inr ⟨i, j, hij, by omega, he⟩
  · refine hs.trans ((construction_cost n c.size 0 L d hL hd hpow).trans ?_)
    simp only [powerBudget, Nat.zero_div, le_refl]

end Cslib.Circuits.Boolean.Iteration
