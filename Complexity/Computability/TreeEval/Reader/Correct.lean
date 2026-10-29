/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Reader.Arith
import Complexity.Foundations.Data.Nat.Div

/-!
# Correctness of the Tree Evaluation read machine

Run on the encoding of an instance, `Cslib.TreeEval.Reader.machine` halts with the value of the
tree as its output: a call on a subtree performs the procedure `Cslib.TreeEval.proc` on it and
returns, by induction on the subtree, with the rounds of a gate, the reading of a leaf and the pass
over the table of a gate as loops of their own.

## Main results

* `Cslib.TreeEval.Reader.exists_runFrom_call`: a call on a subtree performs the procedure
  and returns.
* `Cslib.TreeEval.Reader.exists_run_eq`: the machine halts with the value of the tree.
-/

@[expose] public section

namespace Cslib.TreeEval

namespace Reader

open Iter Turing BitString

variable {ℓ H : ℕ} (T : Tree ℓ H)

/-- The input at an offset into the body, in the form produced by `simp`. -/
@[simp] theorem getElem?_encode_body (k : ℕ) :
    T.encode[ℓ + (H + (2 + k))]? = T.body[k]? := by
  rw [Tree.encode, show ℓ + (H + (2 + k)) = (Tree.header ℓ H).length + k by simp; omega,
    List.getElem?_append_right (by omega)]
  simp

/-- A configuration of the machine on `T`, running with the prime `p`. -/
abbrev cfg (p : ℕ) (R : Regs) (st : List Frame) (mode : Mode) (ctl : Ctl) (out : List Bool) :
    ReadMachine.Cfg State :=
  ⟨⟨ℓ, H, p, R, st, mode, ctl⟩, out⟩

variable {T}

/-- One step of the leaf loop. -/
private theorem next_leaf {p : ℕ} (R : Regs) (st : List Frame) (neg : Bool) (t : Fin 3) {i : ℕ}
    (hi : i < ℓ) (out : List Bool) :
    machine.next T.encode (cfg (ℓ := ℓ) (H := H) p R st (.call neg t) (.leaf i) out) =
      cfg (ℓ := ℓ) (H := H) p (R.set t (modifyAt (R.get t) i (addMod p
          (if T.body.getD (pathOffset ℓ H (path st) + i) false then sgnVal p neg else 0))))
        st (.call neg t) (.leaf (i + 1)) out := by
  simp [ReadMachine.next, machine, step, addr, ReadMachine.readBit, offset, hi, Nat.add_assoc,
    List.getD_eq_getElem?_getD]

private theorem cast_ite_sgnVal {p : ℕ} [Fact p.Prime] (b neg : Bool) :
    (((if b then sgnVal p neg else 0 : ℕ)) : ZMod p) = sgn neg * bitVal (ZMod p) b := by
  cases b <;> simp [BitString.bitVal]

/-- **The leaf loop**: after `i ≤ ℓ` steps, bits `0, …, i - 1` of the leaf have been added. -/
private theorem runFrom_leaf_loop {p : ℕ} [Fact p.Prime] {st : List Frame} {v : Fin ℓ → Bool}
    (hv : T.nodeAt (path st) = .leaf v) (R : Regs) (hR : R.WF p ℓ) (neg : Bool) (t : Fin 3)
    (out : List Bool) : ∀ i ≤ ℓ, ∃ R', machine.runFrom T.encode
      (cfg (ℓ := ℓ) (H := H) p R st (.call neg t) (.leaf 0) out) i =
        cfg (ℓ := ℓ) (H := H) p R' st (.call neg t) (.leaf i) out ∧ R'.WF p ℓ ∧
      R'.toState p ℓ = Function.update (R.toState p ℓ) t fun j =>
        R.toState p ℓ t j + if (j : ℕ) < i then sgn neg * bitVal (ZMod p) (v j) else 0 := by
  have hp := (Fact.out : p.Prime).pos
  intro i hi
  induction i with
  | zero => exact ⟨R, rfl, hR, by simp⟩
  | succ i ih =>
    obtain ⟨R', h', hR', hS'⟩ := ih (by omega)
    have hbit : T.body.getD (pathOffset ℓ H (path st) + i) false = v ⟨i, by omega⟩ := by
      rw [List.getD_eq_getElem?_getD, Tree.getElem_body_leaf T hv ⟨i, by omega⟩]
      rfl
    refine ⟨_, by rw [ReadMachine.runFrom_add, h', ReadMachine.runFrom_one, next_leaf _ _ _ _
      (by omega), hbit], hR'.set_modifyAt hp _ _ _, ?_⟩
    rw [toState_set_modifyAt R' t ⟨i, by omega⟩ (hR' t).1, hS']
    funext r j
    by_cases hr : r = t
    · subst hr
      by_cases hj : j = ⟨i, by omega⟩
      · subst hj
        have : ((R'.get r).getD i 0 : ZMod p) = R'.toState p ℓ r ⟨i, by omega⟩ := rfl
        simp only [Function.update_self, cast_addMod, cast_ite_sgnVal, this, hS']
        simp [add_comm]
      · have hji : (j : ℕ) ≠ i := fun e => hj (Fin.ext e)
        simp only [Function.update_self, Function.update_of_ne hj]
        simp [show (j : ℕ) < i + 1 ↔ (j : ℕ) < i by omega]
    · simp [hr]

/-- **The leaf phase**: a call on the leaf at the current path adds `±` its value to the target
register and returns, in `ℓ + 2` steps. -/
private theorem runFrom_leaf {p : ℕ} [Fact p.Prime] {st : List Frame} {v : Fin ℓ → Bool}
    (hv : T.nodeAt (path st) = .leaf v) (R : Regs) (hR : R.WF p ℓ) (neg : Bool) (t : Fin 3)
    (out : List Bool) : ∃ R', machine.runFrom T.encode
      (cfg (ℓ := ℓ) (H := H) p R st (.call neg t) .run out) (ℓ + 2) =
        cfg (ℓ := ℓ) (H := H) p R' st .ret .run out ∧ R'.WF p ℓ ∧
      R'.toState p ℓ = Function.update (R.toState p ℓ) t
        (R.toState p ℓ t + (sgn neg : ZMod p) • (embed v : Fin ℓ → ZMod p)) := by
  have hlen : st.length = H := by simpa using Tree.length_of_nodeAt_leaf hv
  obtain ⟨R', h', hR', hS'⟩ := runFrom_leaf_loop hv R hR neg t out ℓ le_rfl
  refine ⟨R', ?_, hR', ?_⟩
  · rw [show ℓ + 2 = 1 + (ℓ + 1) by omega, ReadMachine.runFrom_add, ReadMachine.runFrom_one]
    have h0 : machine.next T.encode (cfg (ℓ := ℓ) (H := H) p R st (.call neg t) .run out) =
        cfg (ℓ := ℓ) (H := H) p R st (.call neg t) (.leaf 0) out := by
      simp [ReadMachine.next, machine, step, runStep, hlen]
    rw [h0, ReadMachine.runFrom_add, h', ReadMachine.runFrom_one]
    simp [ReadMachine.next, machine, step]
  · rw [hS']
    congr 1
    funext j
    simp [embed]

/-- One step of the pass over a table. -/
private theorem next_scan {p : ℕ} (R : Regs) (fr : Frame) (st : List Frame) {k : ℕ}
    (hk : k < tableLength ℓ) (acc : List ℕ) (out : List Bool) :
    machine.next T.encode (cfg (ℓ := ℓ) (H := H) p R (fr :: st) .ret (.scan k acc) out) =
      cfg (ℓ := ℓ) (H := H) p R (fr :: st) .ret (.scan (k + 1)
        (if T.body.getD (pathOffset ℓ H (path st) + k) false then
          modifyAt acc (k % ℓ) (addMod p (weight p ℓ (k / ℓ) (R.get (fr.target + 1))
            (R.get (fr.target + 2)))) else acc)) out := by
  cases hb : T.body.getD (pathOffset ℓ H (path st) + k) false <;>
    simp_all [ReadMachine.next, machine, step, addr, ReadMachine.readBit, offset, Nat.add_assoc,
      List.getD_eq_getElem?_getD]

/-- **The pass over a table**: after `k` bits, the sums for every output bit `i` cover the
positions `q < k` of the table for `i` that are set, weighted by the masked registers. -/
private theorem runFrom_scan_loop {p : ℕ} [Fact p.Prime] {fr : Frame} {st : List Frame}
    {f : Gate ℓ} (hf : T.nodeAt (path st) = .gate f)
    (R : Regs) (out : List Bool) :
    ∀ k ≤ tableLength ℓ, ∃ acc, machine.runFrom T.encode
      (cfg (ℓ := ℓ) (H := H) p R (fr :: st) .ret (.scan 0 (List.replicate ℓ 0)) out) k =
        cfg (ℓ := ℓ) (H := H) p R (fr :: st) .ret (.scan k acc) out ∧ acc.length = ℓ ∧
      (∀ a ∈ acc, a < p) ∧ ∀ i : Fin ℓ, (acc.getD i 0 : ZMod p) =
        ∑ q ∈ Finset.range k, if q % ℓ = i then bitVal (ZMod p) (tableBit f q) *
          ((weight p ℓ (q / ℓ) (R.get (fr.target + 1)) (R.get (fr.target + 2)) : ℕ) : ZMod p)
        else 0 := by
  have hp := (Fact.out : p.Prime).pos
  intro k hk
  induction k with
  | zero =>
    refine ⟨List.replicate ℓ 0, rfl, by simp, fun a ha => ?_, fun i => ?_⟩
    · rw [(List.mem_replicate.mp ha).2]; exact hp
    · simp [List.getD_eq_getElem?_getD]
  | succ k ih =>
    obtain ⟨acc, h', hlen, hlt, hsum⟩ := ih (by omega)
    have hℓ : 0 < ℓ := by
      rcases Nat.eq_zero_or_pos ℓ with h0 | h0
      · simp [tableLength, h0] at hk
      · exact h0
    have hbit : T.body.getD (pathOffset ℓ H (path st) + k) false = tableBit f k := by
      rw [List.getD_eq_getElem?_getD, Tree.getElem_body_gate T hf (by omega)]
      rfl
    refine ⟨_, by rw [ReadMachine.runFrom_add, h', ReadMachine.runFrom_one, next_scan _ _ _
      (by omega), hbit], ?_, ?_, fun i => ?_⟩
    · split_ifs <;> simp [modifyAt, hlen]
    · split_ifs
      exacts [(modifyAt_addMod_wf hp hlt _ _).2, hlt]
    · rw [Finset.sum_range_succ, ← hsum i]
      by_cases hb : tableBit f k
      · by_cases hi : k % ℓ = i
        · simp [hb, hi, modifyAt, List.getD_eq_getElem?_getD, hlen,
            show (i : ℕ) < ℓ from i.isLt, BitString.bitVal, add_comm]
        · simp [hb, hi, modifyAt, List.getD_eq_getElem?_getD]
      · simp [hb, BitString.bitVal]

/-- The bit of a table at position `k * ℓ + i`. -/
theorem tableBit_mul_add (f : Gate ℓ) (k : ℕ) (i : Fin ℓ) :
    tableBit f (k * ℓ + i) = f (lowBits ℓ k) (highBits ℓ k) i := by
  have hmod : (k * ℓ + i) % ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
  simp only [tableBit, Nat.mul_add_div_fin, hmod, i.isLt, dite_true]

/-- **The update of a round**: from phase `1`, the pass over the table of the gate subtracts `±`
the multilinear extensions of its output bits at the masked registers, in `4^ℓ * ℓ + 2` steps,
and calls the left child for subtraction. -/
private theorem runFrom_update {p : ℕ} [Fact p.Prime] {fr : Frame} {st : List Frame}
    {f : Gate ℓ} (hf : T.nodeAt (path st) = .gate f)
    (hph : fr.phase = 1) (R : Regs) (hR : R.WF p ℓ) (out : List Bool) :
    ∃ R', machine.runFrom T.encode
      (cfg (ℓ := ℓ) (H := H) p R (fr :: st) .ret .run out) (tableLength ℓ + 2) =
        cfg (ℓ := ℓ) (H := H) p R' ({ fr with phase := 2 } :: st) (.call true (fr.target + 1))
          .run out ∧ R'.WF p ℓ ∧
      R'.toState p ℓ = gateUpdate f (sgn fr.neg) fr.target (R.toState p ℓ) := by
  have hp := (Fact.out : p.Prime).pos
  obtain ⟨acc, h', hlen, -, hsum⟩ :=
    runFrom_scan_loop (p := p) (fr := fr) hf R out (tableLength ℓ) le_rfl
  refine ⟨subtractSums p (sgnVal p fr.neg) fr.target acc R, ?_, hR.subtractSums hp _ _ _, ?_⟩
  · rw [show tableLength ℓ + 2 = 1 + (tableLength ℓ + 1) by omega, ReadMachine.runFrom_add,
      ReadMachine.runFrom_one]
    have h0 : machine.next T.encode (cfg (ℓ := ℓ) (H := H) p R (fr :: st) .ret .run out) =
        cfg (ℓ := ℓ) (H := H) p R (fr :: st) .ret (.scan 0 (List.replicate ℓ 0)) out := by
      obtain ⟨j, ph, neg, t⟩ := fr
      simp only at hph
      subst hph
      simp [ReadMachine.next, machine, step, runStep]
    rw [h0, ReadMachine.runFrom_add, h', ReadMachine.runFrom_one]
    simp [ReadMachine.next, machine, step]
  · rw [toState_subtractSums _ _ _ _ (hR _).1, gateUpdate, cast_sgnVal]
    congr 1
    funext i
    congr 2
    rw [hsum i, tableLength, Nat.sum_range_mul_ite_mod _ i.isLt, eval_gatePoly_eq_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [tableBit_mul_add, cast_weight, Nat.mul_add_div_fin]
    rfl

private theorem next_push {p : ℕ} (R : Regs) {st : List Frame} (hst : st.length ≠ H) (neg : Bool)
    (t : Fin 3) (out : List Bool) :
    machine.next T.encode (cfg (ℓ := ℓ) (H := H) p R st (.call neg t) .run out) =
      cfg (ℓ := ℓ) (H := H) p (R.scale p (t + 1) (unitVal 0)) (⟨0, 0, neg, t⟩ :: st)
        (.call false (t + 1)) .run out := by
  simp [ReadMachine.next, machine, step, runStep, hst]

private theorem next_phase0 {p : ℕ} (R : Regs) (j : ℕ) (neg : Bool) (t : Fin 3) (st : List Frame)
    (out : List Bool) :
    machine.next T.encode (cfg (ℓ := ℓ) (H := H) p R (⟨j, 0, neg, t⟩ :: st) .ret .run out) =
      cfg (ℓ := ℓ) (H := H) p (R.scale p (t + 2) (unitVal j)) (⟨j, 1, neg, t⟩ :: st)
        (.call false (t + 2)) .run out := by
  simp [ReadMachine.next, machine, step, runStep]

private theorem next_phase2 {p : ℕ} (R : Regs) (j : ℕ) (neg : Bool) (t : Fin 3) (st : List Frame)
    (out : List Bool) :
    machine.next T.encode (cfg (ℓ := ℓ) (H := H) p R (⟨j, 2, neg, t⟩ :: st) .ret .run out) =
      cfg (ℓ := ℓ) (H := H) p (R.scale p (t + 1) (unitInv p j)) (⟨j, 3, neg, t⟩ :: st)
        (.call true (t + 2)) .run out := by
  simp [ReadMachine.next, machine, step, runStep]

private theorem next_phase3 {p : ℕ} (R : Regs) (j : ℕ) (neg : Bool) (t : Fin 3) (st : List Frame)
    (out : List Bool) :
    machine.next T.encode (cfg (ℓ := ℓ) (H := H) p R (⟨j, 3, neg, t⟩ :: st) .ret .run out) =
      if j + 1 < p - 1 then
        cfg (ℓ := ℓ) (H := H) p (((R.scale p (t + 2) (unitInv p j))).scale p (t + 1)
          (unitVal (j + 1))) (⟨j + 1, 0, neg, t⟩ :: st) (.call false (t + 1)) .run out
      else cfg (ℓ := ℓ) (H := H) p (R.scale p (t + 2) (unitInv p j)) st .ret .run out := by
  by_cases h : j + 1 < p - 1 <;> simp [ReadMachine.next, machine, step, runStep, h]

/-- The hypothesis that calls on the subtree at a path perform `pl`. -/
def CallSpec (T : Tree ℓ H) (p : ℕ) [Fact p.Prime] (P : List Bool)
    (pl : ZMod p → Fin 3 → TreeEval.State (ZMod p) ℓ → TreeEval.State (ZMod p) ℓ) : Prop :=
  ∀ st' neg t R out, R.WF p ℓ → path st' = P → ∃ n R', machine.runFrom T.encode
    (cfg (ℓ := ℓ) (H := H) p R st' (.call neg t) .run out) n =
      cfg (ℓ := ℓ) (H := H) p R' st' .ret .run out ∧ R'.WF p ℓ ∧
    R'.toState p ℓ = pl (sgn neg) t (R.toState p ℓ)

/-- **One round** of the machine at a gate performs `gateRound` and starts the next round or
returns. -/
private theorem exists_runFrom_round {p : ℕ} [Fact p.Prime] {st : List Frame}
    {f : Gate ℓ} (hf : T.nodeAt (path st) = .gate f)
    {pl pr : ZMod p → Fin 3 → TreeEval.State (ZMod p) ℓ → TreeEval.State (ZMod p) ℓ}
    (hl : CallSpec T p (path st ++ [false]) pl) (hr : CallSpec T p (path st ++ [true]) pr)
    {j : ℕ} (hj : j < p - 1) (neg : Bool) (t : Fin 3) (R : Regs) (hR : R.WF p ℓ)
    (out : List Bool) :
    ∃ n R', machine.runFrom T.encode (cfg (ℓ := ℓ) (H := H) p (R.scale p (t + 1) (unitVal j))
        (⟨j, 0, neg, t⟩ :: st) (.call false (t + 1)) .run out) n =
      (if j + 1 < p - 1 then
        cfg (ℓ := ℓ) (H := H) p (R'.scale p (t + 1) (unitVal (j + 1))) (⟨j + 1, 0, neg, t⟩ :: st)
          (.call false (t + 1)) .run out
      else cfg (ℓ := ℓ) (H := H) p R' st .ret .run out) ∧ R'.WF p ℓ ∧
      R'.toState p ℓ = gateRound pl pr f (sgn neg) t (Iter.zmodUnit p j) (R.toState p ℓ) := by
  have hp := (Fact.out : p.Prime).pos
  have dl (ph : Fin 4) (h : ph.val % 2 = 0) :
      path (⟨j, ph, neg, t⟩ :: st) = path st ++ [false] := by
    simp [Frame.dir, h]
  have dr (ph : Fin 4) (h : ph.val % 2 = 1) :
      path (⟨j, ph, neg, t⟩ :: st) = path st ++ [true] := by
    simp [Frame.dir, h]
  obtain ⟨n₁, R₁, h₁, hR₁, hS₁⟩ := hl (⟨j, 0, neg, t⟩ :: st) false (t + 1)
    (R.scale p (t + 1) (unitVal j)) out (hR.scale hp _ _) (dl 0 rfl)
  obtain ⟨n₂, R₂, h₂, hR₂, hS₂⟩ := hr (⟨j, 1, neg, t⟩ :: st) false (t + 2)
    (R₁.scale p (t + 2) (unitVal j)) out (hR₁.scale hp _ _) (dr 1 rfl)
  obtain ⟨R₃, h₃, hR₃, hS₃⟩ := runFrom_update (fr := ⟨j, 1, neg, t⟩) hf rfl R₂ hR₂ out
  obtain ⟨n₄, R₄, h₄, hR₄, hS₄⟩ := hl (⟨j, 2, neg, t⟩ :: st) true (t + 1) R₃ out hR₃ (dl 2 rfl)
  obtain ⟨n₅, R₅, h₅, hR₅, hS₅⟩ := hr (⟨j, 3, neg, t⟩ :: st) true (t + 2)
    (R₄.scale p (t + 1) (unitInv p j)) out (hR₄.scale hp _ _) (dr 3 rfl)
  generalize tableLength ℓ + 2 = G at h₃
  refine ⟨n₁ + (1 + (n₂ + (G + (n₄ + (1 + (n₅ + 1)))))),
    R₅.scale p (t + 2) (unitInv p j), ?_, hR₅.scale hp _ _, ?_⟩
  · simp only [ReadMachine.runFrom_add, ReadMachine.runFrom_one]
    rw [h₁, next_phase0, h₂, h₃, h₄, next_phase2, h₅, next_phase3]
  · rw [toState_scale, hS₅, toState_scale, hS₄, hS₃, hS₂, toState_scale, hS₁, toState_scale,
      cast_unitVal hj, cast_unitInv_eq hj]
    simp only [gateRound, gateUpdate, sgn_false, sgn_true]

/-- The rounds `j, …, j + k` of a gate, the last ones before `p - 1`, perform the corresponding
`gateRound`s and return. -/
private theorem exists_runFrom_rounds {p : ℕ} [Fact p.Prime] {st : List Frame}
    {f : Gate ℓ} (hf : T.nodeAt (path st) = .gate f)
    {pl pr : ZMod p → Fin 3 → TreeEval.State (ZMod p) ℓ → TreeEval.State (ZMod p) ℓ}
    (hl : CallSpec T p (path st ++ [false]) pl) (hr : CallSpec T p (path st ++ [true]) pr)
    (neg : Bool) (t : Fin 3) (out : List Bool) (k : ℕ) :
    ∀ j (R : Regs), R.WF p ℓ → j + k + 1 = p - 1 → ∃ n R', machine.runFrom T.encode
      (cfg (ℓ := ℓ) (H := H) p (R.scale p (t + 1) (unitVal j)) (⟨j, 0, neg, t⟩ :: st)
        (.call false (t + 1)) .run out) n = cfg (ℓ := ℓ) (H := H) p R' st .ret .run out ∧
      R'.WF p ℓ ∧ R'.toState p ℓ = ((List.range' j (k + 1)).map (Iter.zmodUnit p)).foldl
        (fun S u => gateRound pl pr f (sgn neg) t u S) (R.toState p ℓ) := by
  induction k with
  | zero =>
    intro j R hR hj
    obtain ⟨n, R', h, hR', hS'⟩ := exists_runFrom_round hf hl hr (j := j) (by omega) neg t R hR out
    refine ⟨n, R', ?_, hR', by simpa using hS'⟩
    simpa only [show ¬j + 1 < p - 1 by omega, ↓reduceIte] using h
  | succ k ih =>
    intro j R hR hj
    obtain ⟨n, R', h, hR', hS'⟩ := exists_runFrom_round hf hl hr (j := j) (by omega) neg t R hR out
    simp only [show j + 1 < p - 1 by omega, ↓reduceIte] at h
    obtain ⟨n', R'', h', hR'', hS''⟩ := ih (j + 1) R' hR' (by omega)
    refine ⟨n + n', R'', by rw [ReadMachine.runFrom_add, h, h'], hR'', ?_⟩
    rw [hS'', hS']
    simp only [List.range'_succ, List.map_cons, List.foldl_cons]

/-- **A call on a subtree** at the path of the stack performs the procedure on it and returns,
for every initial content of the registers. -/
theorem exists_runFrom_call {p : ℕ} [Fact p.Prime] {d : ℕ} (U : Tree ℓ d) :
    ∀ st : List Frame, (∀ Q, T.nodeAt (path st ++ Q) = U.nodeAt Q) →
      CallSpec T p (path st) (proc ((List.range (p - 1)).map (Iter.zmodUnit p)) U) := by
  have hp2 := (Fact.out : p.Prime).two_le
  induction U with
  | leaf v =>
    intro st hst st' neg t R out hR hpath
    have hv : T.nodeAt (path st') = .leaf v := by rw [hpath]; simpa using hst []
    obtain ⟨R', h, hR', hS'⟩ := runFrom_leaf hv R hR neg t out
    exact ⟨ℓ + 2, R', h, hR', by rw [hS']; rfl⟩
  | @node d f l r ihl ihr =>
    intro st hst st' neg t R out hR hpath
    have hg : T.nodeAt (path st') = .gate f := by rw [hpath]; simpa using hst []
    have hlen : st'.length ≠ H := by
      have := Tree.length_lt_of_nodeAt_gate hg
      rw [length_path] at this
      exact this.ne
    have hl : CallSpec T p (path st' ++ [false])
        (proc ((List.range (p - 1)).map (Iter.zmodUnit p)) l) := fun st'' neg t R out hR h =>
      ihl st'' (fun Q => by rw [h, hpath, List.append_assoc]; simpa using hst (false :: Q))
        st'' neg t R out hR rfl
    have hr : CallSpec T p (path st' ++ [true])
        (proc ((List.range (p - 1)).map (Iter.zmodUnit p)) r) := fun st'' neg t R out hR h =>
      ihr st'' (fun Q => by rw [h, hpath, List.append_assoc]; simpa using hst (true :: Q))
        st'' neg t R out hR rfl
    obtain ⟨n, R', h, hR', hS'⟩ :=
      exists_runFrom_rounds hg hl hr neg t out (p - 2) 0 R hR (by omega)
    refine ⟨1 + n, R', by rw [ReadMachine.runFrom_add, ReadMachine.runFrom_one, next_push _ hlen,
      h], hR', ?_⟩
    rw [hS', proc, List.range_eq_range', show p - 1 = p - 2 + 1 by omega]

/-! ### The header, the prime and the output -/

theorem getElem?_encode_lt_ell {n : ℕ} (hn : n < ℓ) : T.encode[n]? = some true := by
  rw [Tree.encode, List.getElem?_append_left (by simp; omega)]
  simp [Tree.header, List.getElem?_append_left, hn]

theorem getElem?_encode_ell : T.encode[ℓ]? = some false := by
  rw [Tree.encode, List.getElem?_append_left (by simp; omega)]
  simp [Tree.header]

theorem getElem?_encode_height {n : ℕ} (hn : n < H) : T.encode[ℓ + 1 + n]? = some true := by
  rw [Tree.encode, List.getElem?_append_left (by simp; omega)]
  simp only [Tree.header, List.append_assoc, List.cons_append]
  rw [List.getElem?_append_right (by simp; omega)]
  simp [show ℓ + 1 + n - ℓ = n + 1 by omega, List.getElem?_append_left, hn]

theorem getElem?_encode_height_end : T.encode[ℓ + 1 + H]? = some false := by
  rw [Tree.encode, List.getElem?_append_left (by simp; omega)]
  simp only [Tree.header, List.append_assoc, List.cons_append]
  rw [List.getElem?_append_right (by simp; omega)]
  simp [show ℓ + 1 + H - ℓ = H + 1 by omega]

/-- The state while searching the prime. -/
private abbrev primeCfg (ℓ H q d : ℕ) : ReadMachine.Cfg State :=
  ⟨⟨ℓ, H, 0, ([], [], []), [], .ret, .prime q d⟩, []⟩

/-- **The header**: after `ℓ + H + 2` steps the machine has read `ℓ` and `H` and starts the search
for the prime at `2ℓ + 2`. -/
private theorem run_header : machine.run T.encode (ℓ + 1 + (H + 1)) = primeCfg ℓ H
    (2 * ℓ + 2) 2 := by
  have h₁ : ∀ n ≤ ℓ, machine.run T.encode n =
      ⟨⟨0, 0, 0, ([], [], []), [], .ret, .hdrLength n⟩, []⟩ := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [ReadMachine.run_add, ih (by omega), ReadMachine.runFrom_one]
      simp [ReadMachine.next, machine, step, addr, ReadMachine.readBit, List.getD_eq_getElem?_getD,
        getElem?_encode_lt_ell (T := T) (show n < ℓ by omega)]
  have h₂ : ∀ n ≤ H, machine.run T.encode (ℓ + 1 + n) =
      ⟨⟨ℓ, 0, 0, ([], [], []), [], .ret, .hdrHeight n⟩, []⟩ := by
    intro n hn
    induction n with
    | zero =>
      rw [Nat.add_zero, ReadMachine.run_add, h₁ ℓ le_rfl, ReadMachine.runFrom_one]
      simp [ReadMachine.next, machine, step, addr, ReadMachine.readBit, List.getD_eq_getElem?_getD,
        getElem?_encode_ell (T := T)]
    | succ n ih =>
      rw [← Nat.add_assoc, ReadMachine.run_add, ih (by omega), ReadMachine.runFrom_one]
      simp [ReadMachine.next, machine, step, addr, ReadMachine.readBit, List.getD_eq_getElem?_getD,
        getElem?_encode_height (T := T) (show n < H by omega)]
  rw [← Nat.add_assoc, ReadMachine.run_add, h₂ H le_rfl, ReadMachine.runFrom_one]
  simp [ReadMachine.next, machine, step, addr, ReadMachine.readBit, List.getD_eq_getElem?_getD,
    getElem?_encode_height_end (T := T)]

/-- The registers at the start: three registers of `ℓ` zeros. -/
private abbrev zeroRegs (ℓ : ℕ) : Regs :=
    (List.replicate ℓ 0, List.replicate ℓ 0, List.replicate ℓ 0)

/-- **Testing a candidate**: from divisor `d`, with no divisor in `[2, d)`, the machine finds that
`q` is prime and starts the procedure with it, or that it is not and moves to `q + 1`. -/
private theorem exists_runFrom_test {q : ℕ} :
    ∀ k d, d + k = q → 2 ≤ d → (∀ e, 2 ≤ e → e < d → q % e ≠ 0) →
      ∃ n, machine.runFrom T.encode (primeCfg ℓ H q d) n =
        if q.Prime then cfg (ℓ := ℓ) (H := H) q (zeroRegs ℓ) [] (.call false 2) .run []
        else primeCfg ℓ H (q + 1) 2 := by
  intro k
  induction k with
  | zero =>
    intro d hd hd2 hdiv
    have hprime : q.Prime := Nat.prime_def_lt'.mpr ⟨by omega, fun m hm hlt hdvd =>
      hdiv m hm (by omega) (Nat.mod_eq_zero_of_dvd hdvd)⟩
    obtain rfl : d = q := by omega
    refine ⟨1, ?_⟩
    rw [ReadMachine.runFrom_one]
    simp [ReadMachine.next, machine, step, hprime]
  | succ k ih =>
    intro d hd hd2 hdiv
    by_cases hmod : q % d = 0
    · have hnot : ¬q.Prime := fun hp =>
        (Nat.prime_def_lt'.mp hp).2 d hd2 (by omega) (Nat.dvd_of_mod_eq_zero hmod)
      refine ⟨1, ?_⟩
      rw [ReadMachine.runFrom_one]
      simp [ReadMachine.next, machine, step, show d < q by omega, hmod, hnot]
    · obtain ⟨n, hn⟩ := ih (d + 1) (by omega) (by omega) fun e he hlt =>
        if h : e = d then h ▸ hmod else hdiv e he (by omega)
      refine ⟨1 + n, ?_⟩
      rw [ReadMachine.runFrom_add, ReadMachine.runFrom_one, ← hn]
      simp [ReadMachine.next, machine, step, show d < q by omega, hmod]

/-- The least prime `p ≥ 2ℓ + 2`. -/
def primeFor (ℓ : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (2 * ℓ + 2))

theorem primeFor_prime (ℓ : ℕ) : (primeFor ℓ).Prime :=
  (Nat.find_spec (Nat.exists_infinite_primes (2 * ℓ + 2))).2

theorem le_primeFor (ℓ : ℕ) : 2 * ℓ + 2 ≤ primeFor ℓ :=
  (Nat.find_spec (Nat.exists_infinite_primes (2 * ℓ + 2))).1

/-- **The search for the prime** finds `primeFor ℓ` and starts the procedure with it. -/
private theorem exists_runFrom_search :
    ∀ k q, q + k = primeFor ℓ → 2 * ℓ + 2 ≤ q → ∃ n, machine.runFrom T.encode
      (primeCfg ℓ H q 2) n =
        cfg (ℓ := ℓ) (H := H) (primeFor ℓ) (zeroRegs ℓ) [] (.call false 2) .run [] := by
  intro k
  induction k with
  | zero =>
    intro q hq _
    obtain rfl : q = primeFor ℓ := by omega
    obtain ⟨n, hn⟩ := exists_runFrom_test (T := T) (q := primeFor ℓ) (primeFor ℓ - 2) 2
      (by have := le_primeFor ℓ; omega) le_rfl (fun e he hlt => absurd hlt (by omega))
    simp only [primeFor_prime ℓ, ↓reduceIte] at hn
    exact ⟨n, hn⟩
  | succ k ih =>
    intro q hq hq2
    have hnot : ¬q.Prime := fun hp => by
      have := Nat.find_min' (Nat.exists_infinite_primes (2 * ℓ + 2)) ⟨hq2, hp⟩
      rw [← primeFor] at this
      omega
    obtain ⟨n, hn⟩ := exists_runFrom_test (T := T) (q := q) (q - 2) 2 (by omega) le_rfl
      (fun e he hlt => absurd hlt (by omega))
    simp only [hnot, ↓reduceIte] at hn
    obtain ⟨n', hn'⟩ := ih (q + 1) (by omega) (by omega)
    exact ⟨n + n', by rw [ReadMachine.runFrom_add, hn, hn']⟩

private theorem toState_zeroRegs (p : ℕ) : (zeroRegs ℓ).toState p ℓ = 0 := by
  funext r i
  fin_cases r <;> simp [Regs.toState, Regs.get, List.getD_eq_getElem?_getD]

/-- Registers holding the bits of a value, read in `ZMod p`, hold `0` and `1`. -/
private theorem map_get_eq_ofFn {p : ℕ} [Fact p.Prime] {R : Regs} (hR : R.WF p ℓ) {v : Fin ℓ → Bool}
    (h : R.toState p ℓ 2 = embed v) : (R.get 2).map (· == 1) = List.ofFn v := by
  have hp := (Fact.out : p.Prime).one_lt
  obtain ⟨hlen, hlt⟩ := hR 2
  refine List.ext_getElem (by simp [hlen]) fun i h₁ h₂ => ?_
  have hi : i < ℓ := by simpa using h₂
  have hv := congrFun h ⟨i, hi⟩
  simp only [Regs.toState, embed, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
    (show i < (R.get 2).length by omega), Option.getD_some] at hv
  have hval := congrArg ZMod.val hv
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hlt _ (List.getElem_mem _))] at hval
  simp only [List.getElem_map, List.getElem_ofFn]
  cases hb : v ⟨i, hi⟩ <;> simp [hb, BitString.bitVal, ZMod.val_one, ZMod.val_zero] at hval ⊢ <;>
    omega

/-- **The read machine evaluates the tree.** On the encoding of an instance it halts, with the
value of the tree as its output. -/
theorem exists_run_eq (T : Tree ℓ H) :
    ∃ n s, machine.run T.encode n = ⟨s, List.ofFn T.eval⟩ ∧ machine.halt s = true := by
  have : Fact (primeFor ℓ).Prime := ⟨primeFor_prime ℓ⟩
  have hK : 2 * ℓ < Fintype.card (ZMod (primeFor ℓ)) - 1 := by
    rw [ZMod.card]; have := le_primeFor ℓ; omega
  obtain ⟨n₁, h₁⟩ := exists_runFrom_search (T := T) (primeFor ℓ - (2 * ℓ + 2)) (2 * ℓ + 2)
    (by have := le_primeFor ℓ; omega) le_rfl
  obtain ⟨n₂, R, h₂, hR, hS⟩ := exists_runFrom_call (T := T) (p := primeFor ℓ) T []
    (fun Q => by simp [path]) [] false 2 (zeroRegs ℓ) []
    (fun r => by fin_cases r <;> simp [Regs.get, (Fact.out : (primeFor ℓ).Prime).pos]) rfl
  rw [toState_zeroRegs, proc_eq Iter.nodup_zmodUnits Iter.mem_zmodUnits hK] at hS
  refine ⟨ℓ + 1 + (H + 1) + n₁ + n₂ + 1, ⟨ℓ, H, primeFor ℓ, R, [], .ret, .done⟩, ?_, rfl⟩
  rw [ReadMachine.run_add, ReadMachine.run_add, ReadMachine.run_add, run_header, h₁, h₂,
    ReadMachine.runFrom_one]
  simp only [ReadMachine.next, machine, step, runStep]
  simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
  rw [map_get_eq_ofFn (v := T.eval) hR (by rw [hS]; simp)]

end Reader

end Cslib.TreeEval
