/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Reader.Invariant
public import Complexity.Computability.TreeEval.Reader.Cert.Machine

/-!
# The space of the Tree Evaluation read machine

On the encoding of an instance of value length `ℓ` and height `H`, the space budget of every state
that `Cslib.TreeEval.Reader.machine` reaches is `O((ℓ + H + 1) · log (ℓ + 2))`: residues
below the prime `p ≤ 4ℓ + 2` have `O(log (ℓ + 2))` bits. The registers and the sums hold `ℓ`
of them, the stack holds at most `H` frames with a residue each, and the counters have
`O(ℓ + log (H + 2))` bits.

## Main definitions

* `Cslib.TreeEval.Reader.spaceBound`: the bound `(ℓ + H + 1) · (|ℓ| + 1)`, with `|ℓ|` the length of
  `ℓ` in binary.

## Main results

* `Cslib.TreeEval.Reader.stateBudget_le`: the budget of every state reached is `O(spaceBound ℓ H)`.

## References

* [J. Cook and I. Mertz, *Tree Evaluation is in Space O(log n · log log n)*][CookMertz2024]
* [O. Goldreich, *On the Cook–Mertz Tree Evaluation procedure*][Goldreich2024TreeEval],
  Algorithm 1, which the machine runs.
-/

@[expose] public section

namespace Cslib.TreeEval

namespace Reader

open Iter Turing MultiTapeTM

/-- **The space bound** `(ℓ + H + 1) · (|ℓ| + 1)`. -/
def spaceBound (ℓ H : ℕ) : ℕ := (ℓ + H + 1) * ((encNat ℓ).length + 1)

/-- A residue below the prime has at most three bits more than `ℓ`. -/
private theorem length_lt_primeFor {ℓ v : ℕ} (hv : v ≤ primeFor ℓ) : (encNat v).length ≤
    (encNat ℓ).length + 3 :=
  by
  refine (length_encNat_mono (hv.trans (primeFor_le ℓ))).trans ?_
  rw [length_encNat_eq_size, length_encNat_eq_size]
  refine Nat.size_le.mpr ?_
  have := Nat.lt_size_self ℓ
  rw [pow_add]
  omega

private theorem length_encFrame_le {fr : Frame} {P : ℕ} (h : (encNat fr.round).length ≤ P) :
    (encFrame fr).length ≤ 2 * P + 25 := by
  rw [encFrame_apply, length_encPair]
  have := length_encFinEnum_lt (Frame.equiv fr).2
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    at this
  simp only [Frame.equiv, Equiv.coe_fn_mk] at this ⊢
  omega

private theorem length_encList_frames_le {st : List Frame} {P : ℕ}
    (h : ∀ fr ∈ st, (encNat fr.round).length ≤ P) :
    (encList encFrame st).length ≤ st.length * (4 * P + 51) :=
  (length_encList_le encFrame st fun fr hfr => length_encFrame_le (h fr hfr)).trans_eq
    (by ring)

private theorem length_encMode_lt (m : Mode) : (encMode m).length < 7 := by
  have := length_encFinEnum_lt m
  have hc : Nat.card Mode = 7 := by
    rw [Nat.card_congr Mode.equiv]; simp
  rw [hc] at this
  exact this

private theorem length_encTag_lt (t : Fin 7) : (encFinEnum (Fin 7) t).length < 7 := by
  simpa using length_encFinEnum_lt t

/-- The bounds on the components of a state that satisfies the invariant. -/
structure Bounds (ℓ H : ℕ) (s : State) : Prop where
  ell : s.ell ≤ ℓ
  height : s.height ≤ H
  p : (encNat s.p).length ≤ (encNat ℓ).length + 3
  regs : ∀ r, (s.regs.get r).length ≤ ℓ ∧
    (encList encNat (s.regs.get r)).length ≤ ℓ * (2 * ((encNat ℓ).length + 3) + 1)
  stack : s.stack.length ≤ H
  rounds : ∀ fr ∈ s.stack, (encNat fr.round).length ≤ (encNat ℓ).length + 3
  n₁ : (encNat s.ctl.toTuple.2.1).length ≤ (encNat ℓ).length + H + 3 * ℓ + 4
  n₂ : (encNat s.ctl.toTuple.2.2.1).length ≤ (encNat ℓ).length + 3
  acc : s.ctl.toTuple.2.2.2.length ≤ ℓ ∧
    (encList encNat s.ctl.toTuple.2.2.2).length ≤ ℓ * (2 * ((encNat ℓ).length + 3) + 1)

private theorem bounds_regs_wf {ℓ p : ℕ} {R : Regs} (hR : R.WF p ℓ) (hp : p ≤ primeFor ℓ)
    (r : Fin 3) :
    (R.get r).length ≤ ℓ ∧
      (encList encNat (R.get r)).length ≤ ℓ * (2 * ((encNat ℓ).length + 3) + 1) := by
  obtain ⟨hlen, hlt⟩ := hR r
  refine ⟨hlen.le, ?_⟩
  have := length_encList_le encNat (R.get r) (b := (encNat ℓ).length + 3)
    fun v hv => length_lt_primeFor ((hlt v hv).le.trans hp)
  rwa [hlen] at this

theorem bounds_of_inv {ℓ H : ℕ} {s : State} (hs : Inv ℓ H s) : Bounds ℓ H s := by
  obtain ⟨e, h, p, R, st, m, c⟩ := s
  have hL := length_encNat_le_self ℓ
  have hH := length_encNat_le_self H
  have hempty (r : Fin 3) : (Regs.get (([], [], []) : Regs) r).length ≤ ℓ ∧
      (encList encNat (Regs.get (([], [], []) : Regs) r)).length ≤
        ℓ * (2 * ((encNat ℓ).length + 3) + 1) := by
    fin_cases r <;> simp [Regs.get]
  cases c with
  | hdrLength n =>
    obtain ⟨heq, hn⟩ := hs
    simp only [State.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := heq
    have := length_encNat_mono hn
    exact ⟨Nat.zero_le _, Nat.zero_le _, by simp, hempty, by simp, by simp,
      by simp only [Ctl.toTuple]; omega, by simp [Ctl.toTuple], by simp [Ctl.toTuple]⟩
  | hdrHeight n =>
    obtain ⟨heq, hn⟩ := hs
    simp only [State.mk.injEq] at heq
    obtain ⟨he, rfl, rfl, rfl, rfl, rfl, -⟩ := heq
    subst e
    have := length_encNat_mono hn
    exact ⟨le_rfl, Nat.zero_le _, by simp, hempty, by simp, by simp,
      by simp only [Ctl.toTuple]; omega, by simp [Ctl.toTuple], by simp [Ctl.toTuple]⟩
  | prime q d =>
    obtain ⟨heq, hq, hqp, hd, hdq⟩ := hs
    simp only [State.mk.injEq] at heq
    obtain ⟨he, hh, rfl, rfl, rfl, rfl, -⟩ := heq
    subst e h
    have h₁ := length_lt_primeFor hqp
    have h₂ := length_lt_primeFor (hdq.trans hqp)
    exact ⟨le_rfl, le_rfl, by simp, hempty, by simp, by simp,
      by simp only [Ctl.toTuple]; omega, by simpa [Ctl.toTuple] using h₂, by simp [Ctl.toTuple]⟩
  | run =>
    dsimp only [Inv, RunInv] at hs
    obtain ⟨rfl, rfl, hp2, hpp, hR, hst, hrd, -⟩ := hs
    exact ⟨le_rfl, le_rfl, length_lt_primeFor hpp, bounds_regs_wf hR hpp, hst,
      fun fr hfr => length_lt_primeFor ((hrd fr hfr).le.trans hpp),
      by simp [Ctl.toTuple], by simp [Ctl.toTuple], by simp [Ctl.toTuple]⟩
  | leaf i =>
    dsimp only [Inv, RunInv] at hs
    obtain ⟨rfl, rfl, hp2, hpp, hR, hst, hrd, hi⟩ := hs
    have := length_encNat_mono hi
    exact ⟨le_rfl, le_rfl, length_lt_primeFor hpp, bounds_regs_wf hR hpp, hst,
      fun fr hfr => length_lt_primeFor ((hrd fr hfr).le.trans hpp),
      by simp only [Ctl.toTuple]; omega, by simp [Ctl.toTuple], by simp [Ctl.toTuple]⟩
  | scan k acc =>
    dsimp only [Inv, RunInv] at hs
    obtain ⟨rfl, rfl, hp2, hpp, hR, hst, hrd, hk, hacc, hacc'⟩ := hs
    have h₁ := (length_encNat_mono hk).trans (length_tableLength_le e)
    have h₂ := length_encList_le encNat acc (b := (encNat e).length + 3)
      fun v hv => length_lt_primeFor ((hacc' v hv).le.trans hpp)
    rw [hacc] at h₂
    exact ⟨le_rfl, le_rfl, length_lt_primeFor hpp, bounds_regs_wf hR hpp, hst,
      fun fr hfr => length_lt_primeFor ((hrd fr hfr).le.trans hpp),
      by simp only [Ctl.toTuple]; omega, by simp [Ctl.toTuple], ⟨by simp [Ctl.toTuple, hacc], h₂⟩⟩
  | done =>
    dsimp only [Inv, RunInv] at hs
    obtain ⟨rfl, rfl, hp2, hpp, hR, hst, hrd, -⟩ := hs
    exact ⟨le_rfl, le_rfl, length_lt_primeFor hpp, bounds_regs_wf hR hpp, hst,
      fun fr hfr => length_lt_primeFor ((hrd fr hfr).le.trans hpp),
      by simp [Ctl.toTuple], by simp [Ctl.toTuple], by simp [Ctl.toTuple]⟩

/-- **The budget of a state** within the space bound. -/
theorem stateBudget_le {ℓ H : ℕ} {s : State} (hb : Bounds ℓ H s) :
    stateBudget s ≤ 2 ^ 12 * spaceBound ℓ H := by
  obtain ⟨e, h, p, R, st, m, c⟩ := s
  obtain ⟨he, hh, hp, hR, hst, hrd, hn₁, hn₂, hacc⟩ := hb
  simp only at he hh hp hR hst hrd hn₁ hn₂ hacc
  set L := (encNat ℓ).length with hL
  have hHl := length_encNat_le_self H
  have hel := length_encNat_mono he
  have hhl := (length_encNat_mono hh).trans hHl
  obtain ⟨hR0, hR0'⟩ := hR 0
  obtain ⟨hR1, hR1'⟩ := hR 1
  obtain ⟨hR2, hR2'⟩ := hR 2
  simp only [Regs.get] at hR0 hR0' hR1 hR1' hR2 hR2'
  have hstk := length_encList_frames_le hrd
  have htop : (encNat (st.headD dfr).round).length ≤ L + 3 := by
    rcases st with _ | ⟨fr, st⟩
    · simp
    · exact hrd fr (List.mem_cons_self ..)
  have hm := length_encMode_lt m
  have ht := length_encTag_lt c.toTuple.1
  obtain ⟨hacc₁, hacc₂⟩ := hacc
  have hstk' : st.length * (4 * (L + 3) + 51) ≤ H * (4 * (L + 3) + 51) :=
    Nat.mul_le_mul_right _ hst
  have hX : regLen (State.toTuple ⟨e, h, p, R, st, m, c⟩) + e + 1 ≤ 5 * ℓ + 1 := by
    simp only [regLen, State.toTuple, Tuple.regs, Tuple.acc]; omega
  have hY : (encNat p).length + (encNat (st.headD dfr).round).length + (encNat e).length + 4 ≤
      3 * L + 10 := by omega
  have hXY := Nat.mul_le_mul hX hY
  simp only [stateBudget, stepBudget, encStepInT, encTuple, encRegs, encCtlTuple, length_encPair,
    State.toTuple, Tuple.ell, Tuple.height, Tuple.p, Tuple.stack, spaceBound, encBool_apply,
    List.length_singleton] at hXY ⊢
  nlinarith

end Reader

end Cslib.TreeEval
