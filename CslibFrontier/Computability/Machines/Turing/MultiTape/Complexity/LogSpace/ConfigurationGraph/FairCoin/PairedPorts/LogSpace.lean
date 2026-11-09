/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.FairCoin.PairedPorts
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.SmallSpace
import CslibFrontier.Foundations.Data.List.OfFnGetD
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import Mathlib.Data.Nat.Size

/-!
# Logarithmic-space certificates for clocked paired-port configuration graphs

This module proves that all instance-dependent components of the clocked paired-port reduction for
fair-coin logspace machines (`Turing.MultiTapePTM`) are computable in deterministic logarithmic
space (`Turing.MultiTapeTM.ComputableInLogSpace`).

Each port/reward certificate first checks in logarithmic space that the binary lengths of the
numeric arguments lie within the polynomial clocked-box bit budget `O(log |w|)` (returning the
exact out-of-range fallback `false`, `0`, or `none` otherwise), queries the `O(1)` required input
bits via `computableInLogSpace_bitsGetElem?`, and evaluates the linear-space register arithmetic
from `FairCoin.PairedPorts` on the resulting `O(log L)`-bit summary via
`comp_logSpace_of_length_log`.

## Main results

* `Turing.MultiTapeTM.comp_logSpace_of_length_log`: composition of a logarithmic-output-length
  `ComputableInLogSpace` producer with a linear-space `ComputableInSpace` consumer.
* `Turing.MultiTapeTM.computableInLogSpace_bitsLength`,
  `Turing.MultiTapeTM.computableInLogSpace_natBitLength`,
  `Turing.MultiTapeTM.computableInLogSpace_bitsGetElem?`: general logarithmic-space word and
  bit-length queries.
* `Turing.MultiTapeNTM.ConfigurationGraph.computableInLogSpace_clockedVertexBound`,
  `Turing.MultiTapeNTM.ConfigurationGraph.computableInLogSpace_startID`,
  `Turing.MultiTapeNTM.ConfigurationGraph.computableInLogSpace_clockedAccept`: logarithmic-space
  certificates for dimension, start ID, and terminal reward.
* `Turing.MultiTapePTM.ConfigurationGraph.computableInLogSpace_clockedOutCount`,
  `Turing.MultiTapePTM.ConfigurationGraph.computableInLogSpace_clockedOutPort`,
  `Turing.MultiTapePTM.ConfigurationGraph.computableInLogSpace_clockedInPort`: logarithmic-space
  certificates for clocked port multiplicities and port lookups.
-/

public section

namespace Turing.MultiTapeTM

open CounterProgram CounterProgram.Instr CounterProgram.Expr ComputableInSpace

/-! ### Composing logspace functions of logarithmic output length with linear-space functions -/

/-- Compose a `ComputableInLogSpace` producer whose encoded output has logarithmic length with a
`ComputableInSpace` consumer running in space linear in its input length. -/
theorem comp_logSpace_of_length_log {α β γ : Type}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {f : α → β} {g : β → γ}
    (hf : ComputableInLogSpace f encIn encMid)
    (hlen : ∃ C, ∀ a, (encMid (f a)).length ≤ C * (Nat.log2 (encIn a).length + 1))
    (hg : ComputableInSpace g encMid encOut fun b => (encMid b).length) :
    ComputableInLogSpace (fun a => g (f a)) encIn encOut := by
  obtain ⟨C, hC⟩ := hlen
  obtain ⟨tf, cf, hf⟩ := hf
  obtain ⟨tg, cg, hg, -⟩ := hg
  obtain ⟨c, h⟩ := hf.comp_space hg
  refine ⟨_, c * (cf + cg * (C + 1) + 2 + (C + 1) + 1),
    h.mono (fun _ => le_rfl) fun a => ?_⟩
  dsimp only
  let L := Nat.log2 (encIn a).length + 1
  have hL : 1 ≤ L := Nat.le_add_left _ _
  have hCa : (encMid (f a)).length ≤ C * L := hC a
  have hm_len : (encMid (f a)).length + 1 ≤ (C + 1) * L :=
    calc (encMid (f a)).length + 1
        ≤ C * L + L := Nat.add_le_add hCa hL
      _ = (C + 1) * L := by ring
  have hm_bits : (encNat ((encMid (f a)).length + 1)).length ≤ (C + 1) * L :=
    (length_encNat_le_of_lt_two_pow Nat.lt_two_pow_self).trans hm_len
  have hn_bits : (encNat ((encIn a).length + 1)).length ≤ 2 * L := by
    have := length_encNat_le_log2_add_two
      (j := (encIn a).length + 1) (N := (encIn a).length) le_rfl
    dsimp only [L]
    omega
  have hsg : cg * ((encMid (f a)).length + 1) ≤ cg * (C + 1) * L :=
    calc cg * ((encMid (f a)).length + 1)
        ≤ cg * ((C + 1) * L) := Nat.mul_le_mul_left cg hm_len
      _ = cg * (C + 1) * L := by ring
  rw [Nat.mul_assoc]
  refine Nat.mul_le_mul_left c ?_
  calc cf * L + cg * ((encMid (f a)).length + 1) +
          (encNat ((encIn a).length + 1)).length +
          (encNat ((encMid (f a)).length + 1)).length + 1
      ≤ cf * L + cg * (C + 1) * L + 2 * L + (C + 1) * L + L :=
        Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add (Nat.add_le_add le_rfl hsg) hn_bits)
            hm_bits)
          hL
    _ = (cf + cg * (C + 1) + 2 + (C + 1) + 1) * L := by ring

/-- A linear-space `ComputableInSpace` function preserves logarithmic encoded-output length. -/
theorem length_log_of_inSpace {α β γ : Type}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {f : α → β} {g : β → γ}
    (hlen : ∃ C, ∀ a, (encMid (f a)).length ≤ C * (Nat.log2 (encIn a).length + 1))
    (hg : ComputableInSpace g encMid encOut fun b => (encMid b).length) :
    ∃ C', ∀ a, (encOut (g (f a))).length ≤ C' * (Nat.log2 (encIn a).length + 1) := by
  obtain ⟨C, hC⟩ := hlen
  obtain ⟨_, cg, -, hglen⟩ := hg
  refine ⟨cg * (C + 1), fun a => ?_⟩
  let L := Nat.log2 (encIn a).length + 1
  have hL : 1 ≤ L := Nat.le_add_left _ _
  have hm : (encMid (f a)).length + 1 ≤ (C + 1) * L :=
    calc (encMid (f a)).length + 1
        ≤ C * L + L := Nat.add_le_add (hC a) hL
      _ = (C + 1) * L := by ring
  calc (encOut (g (f a))).length
      ≤ cg * ((encMid (f a)).length + 1) := hglen (f a)
    _ ≤ cg * ((C + 1) * L) := Nat.mul_le_mul_left cg hm
    _ = cg * (C + 1) * L := by ring

/-! ### Binary word length and binary-indexed bit lookup in logarithmic space -/

/-- Length of a bit word in binary, computed in logarithmic space. -/
theorem computableInLogSpace_bitsLength :
    ComputableInLogSpace List.length encBits encNat :=
  ComputableInLogSpace.unaryToBinary
    ((ComputableInLogSpace.bitsMap fun _ => true).congr fun w => by
      rw [encUnary_apply, encBits_apply, List.map_const'])

/-- Number of binary digits of a natural number, computed in logarithmic space. -/
theorem computableInLogSpace_natBitLength :
    ComputableInLogSpace (fun m : ℕ => (encNat m).length) encNat encNat :=
  computableInLogSpace_bitsLength.comp
    (ComputableInLogSpace.of_eq (f := fun m : ℕ => encNat m)
      (encIn := encNat) (encMid := encBits) fun _ => rfl)

section BitsGetElem

private def bitsGetElemProgram : CounterProgram where
  code :=
    [read (mul (const 2) (reg 0)) 1 2 2,
     assign 0 (add (reg 0) (const 1)) 0,
     assign 2 (const 1) 3,
     read (add (add (mul (const 2) (reg 0)) (const 1)) (reg 1)) 4 6 9,
     lt (reg 0) (reg 2) 13 5,
     assign 3 (add (reg 3) (reg 2)) 7,
     lt (reg 0) (reg 2) 13 7,
     assign 2 (mul (const 2) (reg 2)) 8,
     assign 1 (add (reg 1) (const 1)) 3,
     lt (reg 3) (reg 0) 10 13,
     read (add (mul (const 2) (reg 3)) (const 1)) 11 12 13,
     halt [true, true],
     halt [true, false],
     halt []]
  registers := 4

private theorem bounded4_regs {B a₀ a₁ a₂ a₃ : ℕ}
    (h₀ : a₀ ≤ B) (h₁ : a₁ ≤ B) (h₂ : a₂ ≤ B) (h₃ : a₃ ≤ B) :
    ∀ r ∈ [a₀, a₁, a₂, a₃], r ≤ B := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

private def valBits : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * valBits bs

private theorem valBits_lt_two_pow : ∀ bs : List Bool, valBits bs < 2 ^ bs.length
  | [] => by simp [valBits]
  | b :: bs => by
    have ih := valBits_lt_two_pow bs
    simp only [valBits, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

private theorem valBits_bits (n : ℕ) : valBits n.bits = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · rfl
      · rw [Nat.bit0_bits m hm.ne', valBits, ih m (by omega)]
        simp
    · rw [Nat.bit1_bits m, valBits, ih m (by omega)]
      simp [Nat.add_comm]

private theorem valBits_take_succ :
    ∀ (bs : List Bool) (j : ℕ) (hj : j < bs.length),
      valBits (bs.take (j + 1)) = valBits (bs.take j) + (if bs[j] then 2 ^ j else 0)
  | [], _, hj => absurd hj (by simp)
  | b :: bs, 0, _ => by
    simp only [List.take_succ_cons, List.take_zero, valBits, List.getElem_cons_zero, pow_zero]
    cases b <;> simp
  | b :: bs, j + 1, hj => by
    have hj' : j < bs.length := Nat.lt_of_succ_lt_succ hj
    simp only [List.take_succ_cons, valBits, List.getElem_cons_succ, valBits_take_succ bs j hj',
      pow_succ]
    (cases bs[j] <;> simp); omega

private theorem bitsGetElem_run (w : List Bool) (i : ℕ) {B : ℕ}
    (hB : 2 * w.length + 1 + i.bits.length + 1 ≤ B) :
    ∃ s, bitsGetElemProgram.Reaches (frame w ++ i.bits) (bitsGetElemProgram.Running B)
      bitsGetElemProgram.init s ∧
      bitsGetElemProgram.instr s.1 = .halt (encOption encBool w[i]?) ∧
      ∀ r ∈ s.2, r ≤ B := by
  have scan : ∀ j ≤ w.length,
      bitsGetElemProgram.Reaches (frame w ++ i.bits) (bitsGetElemProgram.Running B)
        (0, [j, 0, 0, 0]) (2, [w.length, 0, 0, 0]) := by
    intro j hj
    induction h : w.length - j generalizing j with
    | zero =>
      obtain rfl : j = w.length := by omega
      refine CounterProgram.Reaches.read (by rfl)
        (bounded4_regs (by omega) (by omega) (by omega) (by omega)) ?_
      simpa [getElem?_frame_append_length, readLabel] using
        CounterProgram.Reaches.refl (2, [w.length, 0, 0, 0])
    | succ _ ih =>
      refine CounterProgram.Reaches.read (by rfl)
        (bounded4_regs (by omega) (by omega) (by omega) (by omega)) ?_
      simp only [eval_mul, eval_const, eval_reg, List.getD_cons_zero,
        (getElem?_frame_append w i.bits (show j < w.length by omega)).1, readLabel]
      refine CounterProgram.Reaches.assign (by rfl)
        (bounded4_regs (by omega) (by omega) (by omega) (by omega)) ?_
      simpa using ih (j + 1) (by omega) (by omega)
  have setPow : bitsGetElemProgram.Reaches (frame w ++ i.bits) (bitsGetElemProgram.Running B)
      (2, [w.length, 0, 0, 0]) (3, [w.length, 0, 2 ^ 0, valBits (i.bits.take 0)]) := by
    refine CounterProgram.Reaches.assign (by rfl)
      (bounded4_regs (by omega) (by omega) (by omega) (by omega)) ?_
    simpa [valBits] using CounterProgram.Reaches.refl (3, [w.length, 0, 1, 0])
  have loop : ∀ j ≤ i.bits.length, 2 ^ j ≤ 2 * w.length + 1 →
      valBits (i.bits.take j) ≤ 2 * w.length →
      ∃ s, bitsGetElemProgram.Reaches (frame w ++ i.bits) (bitsGetElemProgram.Running B)
        (3, [w.length, j, 2 ^ j, valBits (i.bits.take j)]) s ∧
        bitsGetElemProgram.instr s.1 = .halt (encOption encBool w[i]?) ∧
        ∀ r ∈ s.2, r ≤ B := by
    intro j hj
    induction h : i.bits.length - j generalizing j with
    | zero =>
      intro hpow hrem
      obtain rfl : j = i.bits.length := by omega
      have hval_eq : valBits (i.bits.take i.bits.length) = i := by
        rw [List.take_length, valBits_bits]
      rw [hval_eq] at hrem ⊢
      have hb := bounded4_regs (B := B) (a₀ := w.length) (a₁ := i.bits.length)
        (a₂ := 2 ^ i.bits.length) (a₃ := i) (by omega) (by omega) (by omega) (by omega)
      have h3 : bitsGetElemProgram.Reaches (frame w ++ i.bits) (bitsGetElemProgram.Running B)
          (3, [w.length, i.bits.length, 2 ^ i.bits.length, i])
          (9, [w.length, i.bits.length, 2 ^ i.bits.length, i]) := by
        refine CounterProgram.Reaches.read (by rfl) hb ?_
        simpa [getElem?_frame_append_boundary, readLabel] using
          CounterProgram.Reaches.refl (9, [w.length, i.bits.length, 2 ^ i.bits.length, i])
      by_cases hiw : i < w.length
      · have h9 : bitsGetElemProgram.Reaches (frame w ++ i.bits) (bitsGetElemProgram.Running B)
            (9, [w.length, i.bits.length, 2 ^ i.bits.length, i])
            (10, [w.length, i.bits.length, 2 ^ i.bits.length, i]) := by
          refine CounterProgram.Reaches.lt (by rfl) hb ?_
          simpa [hiw] using CounterProgram.Reaches.refl _
        cases hbit : w[i]
        · refine ⟨(12, [w.length, i.bits.length, 2 ^ i.bits.length, i]),
            (h3.trans h9).trans ?_, ?_, hb⟩
          · refine CounterProgram.Reaches.read (by rfl) hb ?_
            simpa [(getElem?_frame_append w i.bits hiw).2, hbit, readLabel] using
              CounterProgram.Reaches.refl _
          · simp [List.getElem?_eq_getElem hiw, hbit, bitsGetElemProgram, instr]
        · refine ⟨(11, [w.length, i.bits.length, 2 ^ i.bits.length, i]),
            (h3.trans h9).trans ?_, ?_, hb⟩
          · refine CounterProgram.Reaches.read (by rfl) hb ?_
            simpa [(getElem?_frame_append w i.bits hiw).2, hbit, readLabel] using
              CounterProgram.Reaches.refl _
          · simp [List.getElem?_eq_getElem hiw, hbit, bitsGetElemProgram, instr]
      · refine ⟨(13, [w.length, i.bits.length, 2 ^ i.bits.length, i]), h3.trans ?_, ?_, hb⟩
        · refine CounterProgram.Reaches.lt (by rfl) hb ?_
          simpa [hiw] using CounterProgram.Reaches.refl _
        · simp [List.getElem?_eq_none (by omega : w.length ≤ i), bitsGetElemProgram, instr]
    | succ _ ih =>
      intro hpow hrem
      have hj_lt : j < i.bits.length := by omega
      have hb := bounded4_regs (B := B) (a₀ := w.length) (a₁ := j) (a₂ := 2 ^ j)
        (a₃ := valBits (i.bits.take j)) (by omega) (by omega) (by omega) (by omega)
      by_cases hgt : w.length < 2 ^ j
      · have hj_sz : j < i.size := Nat.size_eq_bits_len i ▸ hj_lt
        have hi_ge : 2 ^ j ≤ i := Nat.lt_size.mp hj_sz
        have hnone : w[i]? = none := List.getElem?_eq_none (by omega)
        refine ⟨(13, [w.length, j, 2 ^ j, valBits (i.bits.take j)]), ?_, ?_, hb⟩
        · refine CounterProgram.Reaches.read (by rfl) hb ?_
          simp only [eval_add, eval_mul, eval_const, eval_reg, List.getD_cons_zero,
            List.getD_cons_succ, getElem?_frame_append_boundary, List.getElem?_eq_getElem hj_lt]
          cases i.bits[j]
          · dsimp only [readLabel]
            refine CounterProgram.Reaches.lt (by rfl) hb ?_
            simpa [hgt] using CounterProgram.Reaches.refl _
          · dsimp only [readLabel]
            refine CounterProgram.Reaches.lt (by rfl) hb ?_
            simpa [hgt] using CounterProgram.Reaches.refl _
        · simp [hnone, bitsGetElemProgram, instr]
      · have hpow_le_w : 2 ^ j ≤ w.length := by omega
        have hnext_pow : 2 ^ (j + 1) ≤ 2 * w.length + 1 := by
          rw [pow_succ]
          omega
        have hnext_rem : valBits (i.bits.take (j + 1)) ≤ 2 * w.length := by
          have hv := valBits_lt_two_pow (i.bits.take (j + 1))
          have htl : (i.bits.take (j + 1)).length = j + 1 :=
            List.length_take_of_le (by omega)
          rw [htl, pow_succ] at hv
          omega
        obtain ⟨s, hs, hout, hsB⟩ := ih (j + 1) (by omega) (by omega) hnext_pow hnext_rem
        refine ⟨s, ?_, hout, hsB⟩
        have hb7 := bounded4_regs (B := B) (a₀ := w.length) (a₁ := j) (a₂ := 2 ^ j)
          (a₃ := valBits (i.bits.take (j + 1))) (by omega) (by omega) (by omega) (by omega)
        have hb8 := bounded4_regs (B := B) (a₀ := w.length) (a₁ := j) (a₂ := 2 ^ (j + 1))
          (a₃ := valBits (i.bits.take (j + 1))) (by omega) (by omega) (by omega) (by omega)
        have htail7 : bitsGetElemProgram.Reaches (frame w ++ i.bits)
            (bitsGetElemProgram.Running B) (7, [w.length, j, 2 ^ j, valBits (i.bits.take (j + 1))])
            s := by
          refine CounterProgram.Reaches.assign (by rfl) hb7 ?_
          have hmul : 2 * 2 ^ j = 2 ^ (j + 1) := by rw [pow_succ]; ring
          simp only [eval_mul, eval_const, eval_reg, List.getD_cons_succ, List.getD_cons_zero,
            List.set_cons_succ, List.set_cons_zero, hmul]
          refine CounterProgram.Reaches.assign (by rfl) hb8 ?_
          simpa using hs
        refine CounterProgram.Reaches.read (by rfl) hb ?_
        simp only [eval_add, eval_mul, eval_const, eval_reg, List.getD_cons_zero,
          List.getD_cons_succ, getElem?_frame_append_boundary, List.getElem?_eq_getElem hj_lt]
        have hstep_val := (valBits_take_succ i.bits j hj_lt).symm
        cases htb : i.bits[j]
        · simp only [htb, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hstep_val
          dsimp only [readLabel]
          refine CounterProgram.Reaches.lt (by rfl) hb ?_
          simp only [eval_reg, List.getD_cons_zero, List.getD_cons_succ, hgt, ↓reduceIte]
          rwa [hstep_val]
        · simp only [htb, ↓reduceIte] at hstep_val
          dsimp only [readLabel]
          refine CounterProgram.Reaches.lt (by rfl) hb ?_
          simp only [eval_reg, List.getD_cons_zero, List.getD_cons_succ, hgt, ↓reduceIte]
          refine CounterProgram.Reaches.assign (by rfl) hb ?_
          simpa only [eval_add, eval_reg, List.getD_cons_succ, List.getD_cons_zero,
            List.set_cons_succ, List.set_cons_zero, hstep_val] using htail7
  obtain ⟨s, hs, hout, hsB⟩ := loop 0 (Nat.zero_le _) (by simp) (by simp [valBits])
  dsimp only [CounterProgram.init, bitsGetElemProgram, List.replicate]
  exact ⟨s, ((scan 0 (Nat.zero_le _)).trans setPow).trans hs, hout, hsB⟩

/-- Looking up an optional bit of `w` at a binary index `i` is computable in logarithmic space. -/
theorem computableInLogSpace_bitsGetElem? :
    ComputableInLogSpace (fun (w, i) => w[i]?) (encPair encBits encNat) (encOption encBool) := by
  refine bitsGetElemProgram.computableInLogSpace_of_reaches 1 fun ⟨w, i⟩ => ?_
  rw [pow_one, encPair_apply, encBits_apply, encNat_apply]
  refine bitsGetElem_run w i ?_
  rw [List.length_append, length_frame]

end BitsGetElem

end Turing.MultiTapeTM

namespace Turing.MultiTapeNTM.ConfigurationGraph

open MultiTapeTM ComputableInSpace

/-- When `u` is at least `clockedVertexBound D d n`, `clockedAccept` returns `false`. -/
theorem clockedAccept_eq_false_of_ge_bound {k : ℕ} {State : Type} [Fintype State]
    {D d n u : ℕ} (hu : clockedVertexBound (k := k) D d n ≤ u) :
    clockedAccept (k := k) (State := State) (radix D n) n (2 * (2 * (n + 1)) ^ d) u = false := by
  have hB : 1 ≤ radix D n := Nat.one_le_pow D (n + 2) (by omega)
  have hN : 0 < vertexBound (k := k) (radix D n) := Nat.pow_pos hB
  have hu' : (2 * (2 * (n + 1)) ^ d + 1) * vertexBound (k := k) (radix D n) ≤ u := hu
  have hdiv : 2 * (2 * (n + 1)) ^ d + 1 ≤ u / vertexBound (k := k) (radix D n) :=
    (Nat.le_div_iff_mul_le hN).mpr hu'
  have hne : u / vertexBound (k := k) (radix D n) ≠ 2 * (2 * (n + 1)) ^ d :=
    Nat.ne_of_gt hdiv
  dsimp only [clockedAccept]
  exact ite_eq_right hne

/-- Any clocked identifier below `clockedVertexBound D d n` has binary length bounded linearly in
the binary length of `n`. -/
theorem length_encNat_lt_of_lt_clockedVertexBound {k : ℕ} {D d n u : ℕ}
    (hu : u < clockedVertexBound (k := k) D d n) :
    (encNat u).length <
      (D * Fintype.card (Register k) + d + 2) * ((encNat n).length + 1) + 1 := by
  let E := D * Fintype.card (Register k) + d + 2
  have hn_lt : n < 2 ^ (encNat n).length := by
    simpa [encNat_apply, Nat.size_eq_bits_len] using Nat.lt_size_self n
  have htwo_n : 2 * (n + 1) ≤ 2 ^ ((encNat n).length + 1) := by
    rw [pow_succ']
    omega
  have hbox := clockedVertexBound_add_one_le_pow (k := k) D d n
  have hu_pow : u < 2 ^ (E * ((encNat n).length + 1)) := by
    calc
      u < clockedVertexBound (k := k) D d n := hu
      _ < (2 * (n + 1)) ^ E := Nat.lt_of_succ_le hbox
      _ ≤ (2 ^ ((encNat n).length + 1)) ^ E := Nat.pow_le_pow_left htwo_n E
      _ = 2 ^ (E * ((encNat n).length + 1)) := by rw [← pow_mul, Nat.mul_comm]
  exact Nat.lt_succ_of_le (length_encNat_le_of_lt_two_pow hu_pow)

/-- Computing the clocked compact dimension `clockedVertexBound D d w.length` from `w` in
logarithmic space. -/
theorem computableInLogSpace_clockedVertexBound {k : ℕ} (D d : ℕ) :
    ComputableInLogSpace
      (fun w : List Bool => clockedVertexBound (k := k) D d w.length)
      encBits encNat :=
  (comp_logSpace_of_length_log
    computableInLogSpace_bitsLength
    ⟨1, fun w => by simpa using length_encNat_le_log2 (le_rfl : w.length ≤ w.length)⟩
    (clockedVertexBound_budget (k := k) D d
      (of_inO (ComputableInO.of_eq fun _ => rfl)) (.refl _))).congr_fun fun _ => rfl

/-- Computing the clock-zero compact start identifier `startID ntm (radix D w.length)` from `w` in
logarithmic space. -/
theorem computableInLogSpace_startID {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (D : ℕ) :
    ComputableInLogSpace
      (fun w : List Bool => startID ntm (radix D w.length))
      encBits encNat := by
  have hn : ComputableInSpace (fun n : ℕ => n) encNat encNat fun n => (encNat n).length :=
    of_inO (ComputableInO.of_eq fun _ => rfl)
  have hB : ComputableInSpace (fun n : ℕ => radix D n) encNat encNat fun n => (encNat n).length :=
    budget_natPow (budget_natAdd hn (budget_const 2 (.refl _))) (.refl _) D
  exact (comp_logSpace_of_length_log
    computableInLogSpace_bitsLength
    ⟨1, fun w => by simpa using length_encNat_le_log2 (le_rfl : w.length ≤ w.length)⟩
    (startID_budget ntm hB (.refl _))).congr_fun fun _ => rfl

/-- Computing the terminal accepting-ID indicator `clockedAccept` on `(w, u)` in logarithmic
space. -/
theorem computableInLogSpace_clockedAccept {k : ℕ} {State : Type} [Fintype State] (D d : ℕ) :
    ComputableInLogSpace
      (fun (w, u) => clockedAccept (k := k) (State := State)
        (radix D w.length) w.length (2 * (2 * (w.length + 1)) ^ d) u)
      (encPair encBits encNat) encBool := by
  let E := D * Fintype.card (Register k) + d + 2
  let encWU := encPair encBits encNat
  let guard (x : List Bool × ℕ) : Bool :=
    decide ((encNat x.2).length < E * ((encNat x.1.length).length + 1) + 1)
  have hln : ComputableInLogSpace (fun x : List Bool × ℕ => (encNat x.1.length).length)
      encWU encNat :=
    computableInLogSpace_natBitLength.comp
      (computableInLogSpace_bitsLength.comp (ComputableInLogSpace.fst encBits encNat))
  have hlu : ComputableInLogSpace (fun x : List Bool × ℕ => (encNat x.2).length)
      encWU encNat :=
    computableInLogSpace_natBitLength.comp (ComputableInLogSpace.snd encBits encNat)
  have hpair_len : ∃ C, ∀ x : List Bool × ℕ,
      (encPair encNat encNat ((encNat x.1.length).length, (encNat x.2).length)).length ≤
        C * (Nat.log2 (encWU x).length + 1) := by
    refine ⟨4, fun x => ?_⟩
    have hw_le : x.1.length ≤ (encWU x).length := by
      simp only [encWU, length_encPair, encBits_apply]
      omega
    have hln_le : (encNat x.1.length).length ≤ (encWU x).length :=
      (length_encNat_le_of_lt_two_pow Nat.lt_two_pow_self).trans hw_le
    have hlu_le : (encNat x.2).length ≤ (encWU x).length :=
      length_le_encPair_right encBits encNat x
    have h1 := length_encNat_le_log2 hln_le
    have h2 := length_encNat_le_log2 hlu_le
    rw [length_encPair]
    dsimp only
    omega
  have hguard_space : ComputableInSpace
      (fun p : ℕ × ℕ => decide (p.2 < E * (p.1 + 1) + 1))
      (encPair encNat encNat) encBool fun p => (encPair encNat encNat p).length :=
    budget_natLt (snd encNat encNat)
      (budget_natSucc (budget_natMul (budget_const E (.refl _))
        (budget_natSucc (fst encNat encNat))))
  have hguard : ComputableInLogSpace guard encWU encBool :=
    (comp_logSpace_of_length_log (ComputableInLogSpace.pair hln hlu) hpair_len
      hguard_space).congr_fun fun _ => rfl
  let encSub := (Function.Embedding.subtype (fun x => guard x = true)).trans encWU
  have hnu_log : ComputableInLogSpace
      (fun s : {x : List Bool × ℕ // guard x = true} => (s.val.1.length, s.val.2))
      encSub (encPair encNat encNat) :=
    (ComputableInLogSpace.pair
      (computableInLogSpace_bitsLength.comp (ComputableInLogSpace.fst encBits encNat))
      (ComputableInLogSpace.snd encBits encNat)).restrict _
  have hnu_len : ∃ C, ∀ s : {x : List Bool × ℕ // guard x = true},
      (encPair encNat encNat (s.val.1.length, s.val.2)).length ≤
        C * (Nat.log2 (encSub s).length + 1) := by
    refine ⟨2 * E + 4, fun s => ?_⟩
    let L := Nat.log2 (encSub s).length + 1
    have hL : 1 ≤ L := Nat.le_add_left _ _
    have hw_le : s.val.1.length ≤ (encSub s).length := by
      change s.val.1.length ≤ (encWU s.val).length
      simp only [encWU, length_encPair, encBits_apply]
      omega
    have hln_le : (encNat s.val.1.length).length ≤ L :=
      length_encNat_le_log2 hw_le
    have hlu_lt : (encNat s.val.2).length ≤ E * (L + 1) := by
      have hlt : (encNat s.val.2).length < E * ((encNat s.val.1.length).length + 1) + 1 :=
        of_decide_eq_true s.property
      exact (Nat.le_of_lt_succ hlt).trans (Nat.mul_le_mul_left E (Nat.add_le_add_right hln_le 1))
    calc (encPair encNat encNat (s.val.1.length, s.val.2)).length
        = 2 * (encNat s.val.1.length).length + 1 + (encNat s.val.2).length :=
          length_encPair (s.val.1.length, s.val.2)
      _ ≤ 2 * L + L + E * (L + L) :=
          Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 2 hln_le) hL)
            (hlu_lt.trans (Nat.mul_le_mul_left E (Nat.add_le_add_left hL L)))
      _ ≤ (2 * E + 4) * L := by
          calc 2 * L + L + E * (L + L) = (2 * E + 3) * L := by ring
            _ ≤ (2 * E + 4) * L := Nat.mul_le_mul_right L (by omega)
  have hacc_space : ComputableInSpace
      (fun p : ℕ × ℕ => clockedAccept (k := k) (State := State)
        (radix D p.1) p.1 (2 * (2 * (p.1 + 1)) ^ d) p.2)
      (encPair encNat encNat) encBool fun p => (encPair encNat encNat p).length := by
    have hn := fst encNat encNat
    have hu := snd encNat encNat
    have htwo : ComputableInSpace (fun _ : ℕ × ℕ => 2) (encPair encNat encNat) encNat
        fun p => (encPair encNat encNat p).length := budget_const 2 (.refl _)
    have hB := budget_natPow (budget_natAdd hn htwo) (.refl _) D
    have hT := budget_natMul htwo
      (budget_natPow (budget_natMul htwo (budget_natSucc hn)) (.refl _) d)
    exact clockedAccept_budget (k := k) (State := State) hB hn hT hu (.refl _)
  let f (x : List Bool × ℕ) : Bool :=
    clockedAccept (k := k) (State := State)
      (radix D x.1.length) x.1.length (2 * (2 * (x.1.length + 1)) ^ d) x.2
  have htrue : ComputableInLogSpace (f ∘ Subtype.val) encSub encBool :=
    (comp_logSpace_of_length_log hnu_log hnu_len hacc_space).congr_fun fun _ => rfl
  have hfalse : ComputableInLogSpace
      ((fun _ : List Bool × ℕ => false) ∘ Subtype.val)
      ((Function.Embedding.subtype (fun x => guard x = false)).trans encWU) encBool :=
    (ComputableInLogSpace.const false).restrict _
  refine (ComputableInLogSpace.ite_subtype hguard htrue hfalse).congr_fun fun ⟨w, u⟩ => ?_
  by_cases hg : guard (w, u) = true
  · simp [hg, f]
  · have hg' : guard (w, u) = false := Bool.eq_false_iff.mpr hg
    have hnot : ¬ (encNat u).length < E * ((encNat w.length).length + 1) + 1 :=
      of_decide_eq_false hg'
    have hge : clockedVertexBound (k := k) D d w.length ≤ u := by
      by_contra hlt
      exact hnot (length_encNat_lt_of_lt_clockedVertexBound (Nat.lt_of_not_ge hlt))
    simp [hg', clockedAccept_eq_false_of_ge_bound hge]

end Turing.MultiTapeNTM.ConfigurationGraph

namespace Turing.MultiTapePTM.ConfigurationGraph

open MultiTapeNTM.ConfigurationGraph MultiTapeTM ComputableInSpace

section PortLogSpace

variable {k : ℕ} {State : Type} [Fintype State]

private abbrev Triple := List Bool × ℕ × ℕ

private abbrev encTriple : Triple ↪ List Bool :=
  encPair encBits (encPair encNat encNat)

private abbrev NAP := ℕ × ℕ × ℕ

private abbrev encNAP : NAP ↪ List Bool :=
  encPair encNat (encPair encNat encNat)

private def napLen (z : NAP) : ℕ := z.1

private def napId (z : NAP) : ℕ := (Prod.snd z).1

private def napPort (z : NAP) : ℕ := (Prod.snd z).2

private theorem pair_length_log {α β γ : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {f : α → β} {g : α → γ}
    (hf : ∃ C, ∀ a, (encB (f a)).length ≤ C * (Nat.log2 (encA a).length + 1))
    (hg : ∃ C, ∀ a, (encC (g a)).length ≤ C * (Nat.log2 (encA a).length + 1)) :
    ∃ C, ∀ a, (encPair encB encC (f a, g a)).length ≤ C * (Nat.log2 (encA a).length + 1) := by
  obtain ⟨Cf, hCf⟩ := hf
  obtain ⟨Cg, hCg⟩ := hg
  refine ⟨2 * Cf + Cg + 1, fun a => ?_⟩
  let L := Nat.log2 (encA a).length + 1
  have hL : 1 ≤ L := Nat.le_add_left _ _
  calc (encPair encB encC (f a, g a)).length
      = 2 * (encB (f a)).length + 1 + (encC (g a)).length :=
        length_encPair (f a, g a)
    _ ≤ 2 * (Cf * L) + L + Cg * L :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 2 (hCf a)) hL) (hCg a)
    _ = (2 * Cf + Cg + 1) * L := by ring

private theorem length_encOption_bool_le (o : Option Bool) :
    (encOption encBool o).length ≤ 2 := by
  cases o <;> simp

private theorem optionBool_length_log {α : Type} {encA : α ↪ List Bool} {f : α → Option Bool}
    (_ : ComputableInLogSpace f encA (encOption encBool)) :
    ∃ C, ∀ a, (encOption encBool (f a)).length ≤ C * (Nat.log2 (encA a).length + 1) :=
  ⟨2, fun a => (length_encOption_bool_le (f a)).trans
    (Nat.le_mul_of_pos_right 2 (Nat.succ_pos _))⟩

private theorem length_encList_optionBool_le :
    ∀ l : List (Option Bool), (encList (encOption encBool) l).length ≤ 5 * l.length
  | [] => by simp
  | o :: os => by
    have ho := length_encOption_bool_le o
    have ih := length_encList_optionBool_le os
    rw [encList_cons, List.length_append, length_frame, List.length_cons]
    omega

private theorem optionBoolList_length_log {α : Type} {encA : α ↪ List Bool}
    {g : α → List (Option Bool)} (m : ℕ)
    (_ : ComputableInLogSpace g encA (encList (encOption encBool)))
    (hm : ∀ a, (g a).length = m) :
    ∃ C, ∀ a, (encList (encOption encBool) (g a)).length ≤
      C * (Nat.log2 (encA a).length + 1) :=
  ⟨5 * m, fun a => by
    have h1 := length_encList_optionBool_le (g a)
    rw [hm a] at h1
    exact h1.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))⟩

private def portGuard (k D d P : ℕ) : Triple → Bool
  | (w, a, p) =>
    let E := D * Fintype.card (Register k) + d + 2
    decide ((encNat a).length < E * ((encNat w.length).length + 1) + 1 ∧
      (encNat p).length < Nat.size P + 1)

private theorem length_encNat_lt_of_lt_port {P p : ℕ} (hp : p < P) :
    (encNat p).length < Nat.size P + 1 := by
  have hp_pow : p < 2 ^ Nat.size P := lt_trans hp (Nat.lt_size_self P)
  exact Nat.lt_succ_of_le (length_encNat_le_of_lt_two_pow hp_pow)

private theorem computableInLogSpace_portGuard (k D d P : ℕ) :
    ComputableInLogSpace (portGuard k D d P) encTriple encBool := by
  let E := D * Fintype.card (Register k) + d + 2
  have hw := ComputableInLogSpace.fst encBits (encPair encNat encNat)
  have hap := ComputableInLogSpace.snd encBits (encPair encNat encNat)
  have hln := computableInLogSpace_natBitLength.comp (computableInLogSpace_bitsLength.comp hw)
  have hla := computableInLogSpace_natBitLength.comp
    ((ComputableInLogSpace.fst encNat encNat).comp hap)
  have hlp := computableInLogSpace_natBitLength.comp
    ((ComputableInLogSpace.snd encNat encNat).comp hap)
  have hln_len : ∃ C, ∀ x : Triple,
      (encNat (encNat x.1.length).length).length ≤ C * (Nat.log2 (encTriple x).length + 1) := by
    refine ⟨1, fun ⟨w, a, p⟩ => ?_⟩
    have hw_le : w.length ≤ (encTriple (w, a, p)).length := by
      simp only [encTriple, length_encPair, encBits_apply]
      omega
    have hln_le : (encNat w.length).length ≤ (encTriple (w, a, p)).length :=
      (length_encNat_le_of_lt_two_pow Nat.lt_two_pow_self).trans hw_le
    simpa using length_encNat_le_log2 hln_le
  have hla_len : ∃ C, ∀ x : Triple,
      (encNat (encNat (Prod.fst x.2)).length).length ≤
        C * (Nat.log2 (encTriple x).length + 1) := by
    refine ⟨1, fun ⟨w, a, p⟩ => ?_⟩
    have hla_le : (encNat a).length ≤ (encTriple (w, a, p)).length := by
      simp only [encTriple, length_encPair]
      omega
    simpa using length_encNat_le_log2 hla_le
  have hlp_len : ∃ C, ∀ x : Triple,
      (encNat (encNat (Prod.snd x.2)).length).length ≤
        C * (Nat.log2 (encTriple x).length + 1) := by
    refine ⟨1, fun ⟨w, a, p⟩ => ?_⟩
    have hlp_le : (encNat p).length ≤ (encTriple (w, a, p)).length := by
      simp only [encTriple, length_encPair]
      omega
    simpa using length_encNat_le_log2 hlp_le
  have hlengths := ComputableInLogSpace.pair hln (ComputableInLogSpace.pair hla hlp)
  have hlen_bound := pair_length_log hln_len (pair_length_log hla_len hlp_len)
  have hln_s : ComputableInSpace napLen encNAP encNat fun z => (encNAP z).length :=
    (fst encNat (encPair encNat encNat)).of_enc_eq fun _ => rfl
  have hrest_s : ComputableInSpace Prod.snd encNAP (encPair encNat encNat)
      fun z => (encNAP z).length :=
    snd encNat (encPair encNat encNat)
  have hla_s : ComputableInSpace napId encNAP encNat fun z => (encNAP z).length :=
    (budget_comp_linear (fst encNat encNat) hrest_s).of_enc_eq fun _ => rfl
  have hlp_s : ComputableInSpace napPort encNAP encNat fun z => (encNAP z).length :=
    (budget_comp_linear (snd encNat encNat) hrest_s).of_enc_eq fun _ => rfl
  have htest : ComputableInSpace
      (fun z : NAP => decide (napId z < E * (napLen z + 1) + 1 ∧ napPort z < Nat.size P + 1))
      encNAP encBool fun z => (encNAP z).length := by
    refine (and_inSpace
      (budget_natLt hla_s
        (budget_natSucc (budget_natMul (budget_const E (.refl _)) (budget_natSucc hln_s))))
      (budget_natLt hlp_s (budget_const (Nat.size P + 1) (.refl _)))).of_enc_eq fun z => ?_
    simp
  exact (comp_logSpace_of_length_log hlengths hlen_bound htest).congr_fun fun ⟨w, a, p⟩ => rfl

private abbrev GuardedSub (k D d P : ℕ) :=
  {x : Triple // portGuard k D d P x = true}

private abbrev encGuardedSub (k D d P : ℕ) : GuardedSub k D d P ↪ List Bool :=
  (Function.Embedding.subtype (fun x => portGuard k D d P x = true)).trans encTriple

private def wordSub {k D d P : ℕ} (s : GuardedSub k D d P) : List Bool := s.val.1

private def lenSub {k D d P : ℕ} (s : GuardedSub k D d P) : ℕ := s.val.1.length

private def idSub {k D d P : ℕ} (s : GuardedSub k D d P) : ℕ := (Prod.snd s.val).1

private def portSub {k D d P : ℕ} (s : GuardedSub k D d P) : ℕ := (Prod.snd s.val).2

private def napOfSub {k D d P : ℕ} (s : GuardedSub k D d P) : NAP :=
  (lenSub s, idSub s, portSub s)

private theorem computableInLogSpace_wordSub (k D d P : ℕ) :
    ComputableInLogSpace (wordSub (k := k) (D := D) (d := d) (P := P))
      (encGuardedSub k D d P) encBits :=
  (ComputableInLogSpace.fst encBits (encPair encNat encNat)).restrict _

private theorem computableInLogSpace_lenSub (k D d P : ℕ) :
    ComputableInLogSpace (lenSub (k := k) (D := D) (d := d) (P := P))
      (encGuardedSub k D d P) encNat :=
  computableInLogSpace_bitsLength.comp (computableInLogSpace_wordSub k D d P)

private theorem length_lenSub_log (k D d P : ℕ) :
    ∃ C, ∀ s : GuardedSub k D d P,
      (encNat (lenSub s)).length ≤ C * (Nat.log2 (encGuardedSub k D d P s).length + 1) := by
  refine ⟨1, fun ⟨⟨w, a, p⟩, _⟩ => ?_⟩
  have hw_le : w.length ≤ (encTriple (w, a, p)).length := by
    simp only [encTriple, length_encPair, encBits_apply]
    omega
  simpa [lenSub] using length_encNat_le_log2 hw_le

private theorem computableInLogSpace_napOfSub (k D d P : ℕ) :
    ComputableInLogSpace (napOfSub (k := k) (D := D) (d := d) (P := P))
      (encGuardedSub k D d P) encNAP := by
  have hw := ComputableInLogSpace.fst encBits (encPair encNat encNat)
  have hap := ComputableInLogSpace.snd encBits (encPair encNat encNat)
  exact ((ComputableInLogSpace.pair (computableInLogSpace_bitsLength.comp hw) hap).restrict
    _).congr_fun fun ⟨⟨w, a, p⟩, _⟩ => rfl

private theorem length_napOfSub_log (k D d P : ℕ) :
    ∃ C, ∀ s : GuardedSub k D d P,
      (encNAP (napOfSub s)).length ≤ C * (Nat.log2 (encGuardedSub k D d P s).length + 1) := by
  let E := D * Fintype.card (Register k) + d + 2
  have hid_len : ∃ C, ∀ s : GuardedSub k D d P,
      (encNat (idSub s)).length ≤ C * (Nat.log2 (encGuardedSub k D d P s).length + 1) := by
    refine ⟨2 * E, fun ⟨⟨w, a, p⟩, hs⟩ => ?_⟩
    let L := Nat.log2 (encTriple (w, a, p)).length + 1
    have hL : 1 ≤ L := Nat.le_add_left _ _
    have hw_le : w.length ≤ (encTriple (w, a, p)).length := by
      simp only [encTriple, length_encPair, encBits_apply]
      omega
    have hln : (encNat w.length).length ≤ L := length_encNat_le_log2 hw_le
    obtain ⟨hla_lt, -⟩ := of_decide_eq_true hs
    have hla_le : (encNat a).length ≤ E * (L + 1) :=
      (Nat.le_of_lt_succ hla_lt).trans (Nat.mul_le_mul_left E (Nat.add_le_add_right hln 1))
    calc (encNat a).length
        ≤ E * (L + L) := hla_le.trans (Nat.mul_le_mul_left E (Nat.add_le_add_left hL L))
      _ = 2 * E * L := by ring
  have hport_len : ∃ C, ∀ s : GuardedSub k D d P,
      (encNat (portSub s)).length ≤ C * (Nat.log2 (encGuardedSub k D d P s).length + 1) := by
    refine ⟨Nat.size P, fun ⟨⟨w, a, p⟩, hs⟩ => ?_⟩
    obtain ⟨-, hlp_lt⟩ := of_decide_eq_true hs
    exact (Nat.le_of_lt_succ hlp_lt).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  exact pair_length_log (length_lenSub_log k D d P) (pair_length_log hid_len hport_len)

/-- Query `w[idx (f s)]?` in logarithmic space when `idx` is computed in linear space from an
`O(log L)`-bit summary `f s`. -/
private theorem computableInLogSpace_queryAt {k D d P : ℕ} {β : Type} {encB : β ↪ List Bool}
    {f : GuardedSub k D d P → β} {idx : β → ℕ}
    (hf : ComputableInLogSpace f (encGuardedSub k D d P) encB)
    (hlen : ∃ C, ∀ s, (encB (f s)).length ≤ C * (Nat.log2 (encGuardedSub k D d P s).length + 1))
    (hidx : ComputableInSpace idx encB encNat fun b => (encB b).length) :
    ComputableInLogSpace (fun s => (wordSub s)[idx (f s)]?)
      (encGuardedSub k D d P) (encOption encBool) := by
  have hidx_log := comp_logSpace_of_length_log hf hlen hidx
  exact computableInLogSpace_bitsGetElem?.comp
    (ComputableInLogSpace.pair (computableInLogSpace_wordSub k D d P) hidx_log)

private theorem computableInLogSpace_recipeSymbols (D : ℕ) {k' d P : ℕ}
    {vFun : GuardedSub k' D d P → ℕ}
    (hv_log : ComputableInLogSpace vFun (encGuardedSub k' D d P) encNat)
    (hv_len : ∃ C, ∀ s, (encNat (vFun s)).length ≤
      C * (Nat.log2 (encGuardedSub k' D d P s).length + 1)) :
    ∀ recs : List (PredRecipe k' State),
      ComputableInLogSpace
        (fun s : GuardedSub k' D d P =>
          recs.map fun rec =>
            (wordSub s)[queryIndex (k := k') (radix D (lenSub s))
              (evalPredRecipe rec (radix D (lenSub s)) (vFun s))]?)
        (encGuardedSub k' D d P) (encList (encOption encBool))
  | [] => ComputableInLogSpace.const []
  | rec :: recs => by
    have hnv_log := ComputableInLogSpace.pair (computableInLogSpace_lenSub k' D d P) hv_log
    have hnv_len := pair_length_log (length_lenSub_log k' D d P) hv_len
    have hidx_space : ComputableInSpace
        (fun p : ℕ × ℕ => queryIndex (k := k') (radix D p.1) (evalPredRecipe rec (radix D p.1) p.2))
        (encPair encNat encNat) encNat fun p => (encPair encNat encNat p).length := by
      have hn := fst encNat encNat
      have hv := snd encNat encNat
      have hB := budget_natPow (budget_natAdd hn (budget_const 2 (.refl _))) (.refl _) D
      exact queryIndex_budget (k := k') hB (evalPredRecipe_budget rec hB hv (.refl _))
    have hhead := computableInLogSpace_queryAt hnv_log hnv_len hidx_space
    have htail := computableInLogSpace_recipeSymbols D hv_log hv_len recs
    exact ComputableInLogSpace.listCons hhead htail

private theorem budget_listGetDOptionBool {α : Type} {enc : α ↪ List Bool} {S : α → ℕ} :
    ∀ (idx : ℕ) {l : α → List (Option Bool)},
      ComputableInSpace l enc (encList (encOption encBool)) S →
      ComputableInSpace (fun x => (l x).getD idx none) enc (encOption encBool) S
  | 0, l, hl => (budget_headD none hl).of_enc_eq fun x => by cases l x <;> rfl
  | idx + 1, l, hl =>
    (budget_listGetDOptionBool idx (budget_tail hl)).of_enc_eq fun x => by cases l x <;> rfl

private theorem ge_bound_or_port_ge_of_portGuard_false {k' D d P : ℕ} {w : List Bool} {a p : ℕ}
    (h : portGuard k' D d P (w, a, p) = false) :
    clockedVertexBound (k := k') D d w.length ≤ a ∨ P ≤ p := by
  have hnot := of_decide_eq_false h
  by_cases ha : a < clockedVertexBound (k := k') D d w.length
  · refine Or.inr ?_
    by_contra hp
    exact hnot ⟨length_encNat_lt_of_lt_clockedVertexBound ha,
      length_encNat_lt_of_lt_port (Nat.lt_of_not_ge hp)⟩
  · exact Or.inl (Nat.le_of_not_lt ha)

private theorem nap_fields_inSpace {α : Type} {enc : α ↪ List Bool} {S : α → ℕ} {f : α → NAP}
    (hf : ComputableInSpace f enc encNAP S) :
    ComputableInSpace (fun x => napLen (f x)) enc encNat S ∧
    ComputableInSpace (fun x => napId (f x)) enc encNat S ∧
    ComputableInSpace (fun x => napPort (f x)) enc encNat S := by
  have hrest := budget_comp_linear (snd encNat (encPair encNat encNat)) hf
  exact ⟨(budget_comp_linear (fst encNat (encPair encNat encNat)) hf).of_enc_eq fun _ => rfl,
    (budget_comp_linear (fst encNat encNat) hrest).of_enc_eq fun _ => rfl,
    (budget_comp_linear (snd encNat encNat) hrest).of_enc_eq fun _ => rfl⟩

/-- Outgoing port multiplicity `clockedOutCount machine D d w a p` is computable in deterministic
logarithmic space. -/
theorem computableInLogSpace_clockedOutCount (machine : MultiTapePTM k Bool State) (D d : ℕ) :
    ComputableInLogSpace
      (fun (w, a, p) => clockedOutCount machine D d w a p)
      (encPair encBits (encPair encNat encNat)) encNat := by
  have hguard := computableInLogSpace_portGuard k D d 2
  have hnap_log := computableInLogSpace_napOfSub k D d 2
  have hnap_len := length_napOfSub_log k D d 2
  have hidxOut_space : ComputableInSpace
      (fun z : NAP =>
        queryIndex (k := k) (radix D (napLen z))
          (napId z % vertexBound (k := k) (radix D (napLen z))))
      encNAP encNat fun z => (encNAP z).length := by
    obtain ⟨hn, ha, -⟩ := nap_fields_inSpace (of_inO (ComputableInO.of_eq fun _ => rfl))
    have hB := budget_natPow (budget_natAdd hn (budget_const 2 (.refl _))) (.refl _) D
    have hN := vertexBound_budget (k := k) hB (.refl _)
    exact queryIndex_budget (k := k) hB (budget_natMod ha hN)
  have hsymOut_log := computableInLogSpace_queryAt hnap_log hnap_len hidxOut_space
  have hpack_log := ComputableInLogSpace.pair hnap_log hsymOut_log
  have hpack_len := pair_length_log hnap_len (optionBool_length_log hsymOut_log)
  let encPack := encPair encNAP (encOption encBool)
  have hcnt_space : ComputableInSpace
      (fun z : NAP × Option Bool =>
        clockedOutCountWithSymbol machine D d (napLen z.1) (napId z.1) (napPort z.1) z.2)
      encPack encNat fun z => (encPack z).length := by
    obtain ⟨hn, ha, hp⟩ := nap_fields_inSpace (fst encNAP (encOption encBool))
    have hsym := snd encNAP (encOption encBool)
    exact clockedOutCountWithSymbol_budget machine D d hn ha hp hsym (.refl _)
  let f : Triple → ℕ := fun (w, a, p) => clockedOutCount machine D d w a p
  have htrue : ComputableInLogSpace (f ∘ Subtype.val) (encGuardedSub k D d 2) encNat :=
    (comp_logSpace_of_length_log hpack_log hpack_len hcnt_space).congr_fun fun ⟨⟨w, a, p⟩, _⟩ => rfl
  have hfalse : ComputableInLogSpace
      ((fun _ : Triple => 0) ∘ Subtype.val)
      ((Function.Embedding.subtype (fun x => portGuard k D d 2 x = false)).trans encTriple)
      encNat :=
    (ComputableInLogSpace.const 0).restrict _
  refine (ComputableInLogSpace.ite_subtype hguard htrue hfalse).congr_fun fun ⟨w, a, p⟩ => ?_
  by_cases hg : portGuard k D d 2 (w, a, p) = true
  · simp [hg, f]
  · have hg' : portGuard k D d 2 (w, a, p) = false := Bool.eq_false_iff.mpr hg
    rcases ge_bound_or_port_ge_of_portGuard_false hg' with ha | hp
    · simp [hg', clockedOutCount_eq_zero_of_ge_bound machine ha p]
    · simp [hg', clockedOutCount_eq_zero_of_port_ge machine a hp]

/-- Outgoing paired-port lookup `clockedOutPort machine D d w a p` is computable in deterministic
logarithmic space. -/
theorem computableInLogSpace_clockedOutPort (machine : MultiTapePTM k Bool State) (D d : ℕ) :
    ComputableInLogSpace
      (fun (w, a, p) => clockedOutPort machine D d w a p)
      (encPair encBits (encPair encNat encNat)) (encOption (encPair encNat encNat)) := by
  have hguard := computableInLogSpace_portGuard k D d 2
  have hnap_log := computableInLogSpace_napOfSub k D d 2
  have hnap_len := length_napOfSub_log k D d 2
  have hidxOut_space : ComputableInSpace
      (fun z : NAP =>
        queryIndex (k := k) (radix D (napLen z))
          (napId z % vertexBound (k := k) (radix D (napLen z))))
      encNAP encNat fun z => (encNAP z).length := by
    obtain ⟨hn, ha, -⟩ := nap_fields_inSpace (of_inO (ComputableInO.of_eq fun _ => rfl))
    have hB := budget_natPow (budget_natAdd hn (budget_const 2 (.refl _))) (.refl _) D
    have hN := vertexBound_budget (k := k) hB (.refl _)
    exact queryIndex_budget (k := k) hB (budget_natMod ha hN)
  have hsymOut_log := computableInLogSpace_queryAt hnap_log hnap_len hidxOut_space
  have hpack1_log := ComputableInLogSpace.pair hnap_log hsymOut_log
  have hpack1_len := pair_length_log hnap_len (optionBool_length_log hsymOut_log)
  let encPack1 := encPair encNAP (encOption encBool)
  have hvVal_space : ComputableInSpace
      (fun z : NAP × Option Bool =>
        ((coinOutTargetsWithSymbol machine (radix D (napLen z.1)) (napLen z.1)
          (napId z.1 % vertexBound (k := k) (radix D (napLen z.1))) z.2)[napPort z.1]?).getD 0)
      encPack1 encNat fun z => (encPack1 z).length := by
    obtain ⟨hn, ha, hp⟩ := nap_fields_inSpace (fst encNAP (encOption encBool))
    have hsym := snd encNAP (encOption encBool)
    have hB := budget_natPow (budget_natAdd hn (budget_const 2 (.refl _))) (.refl _) D
    have hN := vertexBound_budget (k := k) hB (.refl _)
    have houtList := coinOutTargetsWithSymbol_budget machine hB hn (budget_natMod ha hN) hsym
      (.refl _)
    exact getElem?_getD_zero_budget 2 (fun _ => length_coinOutTargetsWithSymbol_le ..) houtList hp
      (.refl _)
  have hvVal_log := comp_logSpace_of_length_log hpack1_log hpack1_len hvVal_space
  have hvVal_len := length_log_of_inSpace hpack1_len hvVal_space
  have hinSyms_log := computableInLogSpace_recipeSymbols D hvVal_log hvVal_len
    (predRecipes machine)
  have hpack2_log := ComputableInLogSpace.pair hpack1_log hinSyms_log
  have hpack2_len := pair_length_log hpack1_len
    (optionBoolList_length_log (inPortBound machine) hinSyms_log fun _ => List.length_map _)
  have hp1 := fst encPack1 (encList (encOption encBool))
  obtain ⟨hn, ha, hp⟩ := nap_fields_inSpace
    (budget_comp_linear (fst encNAP (encOption encBool)) hp1)
  have hsymOut := budget_comp_linear (snd encNAP (encOption encBool)) hp1
  have hinSyms := snd encPack1 (encList (encOption encBool))
  have hout_space := clockedOutPortWithSymbols_budget machine D d _
    hn ha hp hsymOut (fun i => budget_listGetDOptionBool i.val hinSyms) (.refl _)
  let f : Triple → Option (ℕ × ℕ) := fun (w, a, p) => clockedOutPort machine D d w a p
  have htrue : ComputableInLogSpace (f ∘ Subtype.val) (encGuardedSub k D d 2)
      (encOption (encPair encNat encNat)) := by
    refine (comp_logSpace_of_length_log hpack2_log hpack2_len hout_space).congr_fun
      fun ⟨⟨w, a, p⟩, _⟩ => ?_
    dsimp only [Function.comp_apply, f, napOfSub, napLen, napId, napPort, wordSub, lenSub, idSub,
      portSub]
    dsimp only [clockedOutPortWithSymbols, clockedOutPort, coinInSources]
    split_ifs with hcond
    · cases hget : (coinOutTargetsWithSymbol machine (radix D w.length) w.length
          (a % vertexBound (k := k) (radix D w.length))
          w[queryIndex (k := k) (radix D w.length)
            (a % vertexBound (k := k) (radix D w.length))]?)[p]? with
      | none => rfl
      | some v =>
        have hlen_map :
            (List.map
              (fun rec =>
                w[queryIndex (k := k) (radix D w.length)
                  (evalPredRecipe rec (radix D w.length) v)]?)
              (predRecipes machine)).length = inPortBound machine := List.length_map _
        dsimp only [Option.getD]
        rw [List.ofFn_getD_eq_of_length none hlen_map]
    · rfl
  have hfalse : ComputableInLogSpace
      ((fun _ : Triple => (none : Option (ℕ × ℕ))) ∘ Subtype.val)
      ((Function.Embedding.subtype (fun x => portGuard k D d 2 x = false)).trans encTriple)
      (encOption (encPair encNat encNat)) :=
    (ComputableInLogSpace.const none).restrict _
  refine (ComputableInLogSpace.ite_subtype hguard htrue hfalse).congr_fun fun ⟨w, a, p⟩ => ?_
  by_cases hg : portGuard k D d 2 (w, a, p) = true
  · simp [hg, f]
  · have hg' : portGuard k D d 2 (w, a, p) = false := Bool.eq_false_iff.mpr hg
    rcases ge_bound_or_port_ge_of_portGuard_false hg' with ha | hp
    · simp [hg', clockedOutPort_eq_none_of_ge_bound machine ha p]
    · simp [hg', clockedOutPort_eq_none_of_port_ge machine a hp]

/-- Incoming paired-port lookup `clockedInPort machine D d w b q` is computable in deterministic
logarithmic space. -/
theorem computableInLogSpace_clockedInPort (machine : MultiTapePTM k Bool State) (D d : ℕ) :
    ComputableInLogSpace
      (fun (w, b, q) => clockedInPort machine D d w b q)
      (encPair encBits (encPair encNat encNat)) (encOption (encPair encNat encNat)) := by
  let P := inPortBound machine
  have hguard := computableInLogSpace_portGuard k D d P
  have hnap_log := computableInLogSpace_napOfSub k D d P
  have hnap_len := length_napOfSub_log k D d P
  have hv_space : ComputableInSpace
      (fun z : NAP => napId z % vertexBound (k := k) (radix D (napLen z)))
      encNAP encNat fun z => (encNAP z).length := by
    obtain ⟨hn, hb, -⟩ := nap_fields_inSpace (of_inO (ComputableInO.of_eq fun _ => rfl))
    have hB := budget_natPow (budget_natAdd hn (budget_const 2 (.refl _))) (.refl _) D
    exact budget_natMod hb (vertexBound_budget (k := k) hB (.refl _))
  have hv_log := comp_logSpace_of_length_log hnap_log hnap_len hv_space
  have hv_len := length_log_of_inSpace hnap_len hv_space
  have hinSyms_log := computableInLogSpace_recipeSymbols D hv_log hv_len (predRecipes machine)
  have hpack1_log := ComputableInLogSpace.pair hnap_log hinSyms_log
  have hpack1_len := pair_length_log hnap_len
    (optionBoolList_length_log P hinSyms_log fun _ => List.length_map _)
  let encPack1 := encPair encNAP (encList (encOption encBool))
  have hidxPred_space : ComputableInSpace
      (fun z : NAP × List (Option Bool) =>
        queryIndex (k := k) (radix D (napLen z.1))
          (((coinInSourcesWithSymbols machine (radix D (napLen z.1)) (napLen z.1)
            (napId z.1 % vertexBound (k := k) (radix D (napLen z.1)))
            (List.ofFn fun i : Fin P => z.2.getD i.val none))[napPort z.1]?).getD 0))
      encPack1 encNat fun z => (encPack1 z).length := by
    obtain ⟨hn, hb, hq⟩ := nap_fields_inSpace (fst encNAP (encList (encOption encBool)))
    have hinSyms := snd encNAP (encList (encOption encBool))
    have hB := budget_natPow (budget_natAdd hn (budget_const 2 (.refl _))) (.refl _) D
    have hN := vertexBound_budget (k := k) hB (.refl _)
    have hinList := coinInSourcesWithSymbols_ofFn_budget machine
      (fun i z => z.2.getD i.val none)
      hB hn (budget_natMod hb hN)
      (fun i => budget_listGetDOptionBool i.val hinSyms) (.refl _)
    have huVal := getElem?_getD_zero_budget P (fun _ => length_coinInSourcesWithSymbols_le ..)
      hinList hq (.refl _)
    exact queryIndex_budget (k := k) hB huVal
  have hsymPred_log := computableInLogSpace_queryAt hpack1_log hpack1_len hidxPred_space
  have hpack2_log := ComputableInLogSpace.pair hpack1_log hsymPred_log
  have hpack2_len := pair_length_log hpack1_len (optionBool_length_log hsymPred_log)
  have hp1 := fst encPack1 (encOption encBool)
  obtain ⟨hn, hb, hq⟩ := nap_fields_inSpace
    (budget_comp_linear (fst encNAP (encList (encOption encBool))) hp1)
  have hinSyms := budget_comp_linear (snd encNAP (encList (encOption encBool))) hp1
  have hsymPred := snd encPack1 (encOption encBool)
  have hin_space := clockedInPortWithSymbols_budget machine D d _
    hn hb hq (fun i => budget_listGetDOptionBool i.val hinSyms) hsymPred (.refl _)
  let f : Triple → Option (ℕ × ℕ) := fun (w, b, q) => clockedInPort machine D d w b q
  have htrue : ComputableInLogSpace (f ∘ Subtype.val) (encGuardedSub k D d P)
      (encOption (encPair encNat encNat)) := by
    refine (comp_logSpace_of_length_log hpack2_log hpack2_len hin_space).congr_fun
      fun ⟨⟨w, b, q⟩, _⟩ => ?_
    dsimp only [Function.comp_apply, f, napOfSub, napLen, napId, napPort, wordSub, lenSub, idSub,
      portSub]
    dsimp only [clockedInPortWithSymbols, clockedInPort, coinInSources]
    split_ifs with hcond
    · have hlen_map :
          (List.map
            (fun rec =>
              w[queryIndex (k := k) (radix D w.length)
                (evalPredRecipe rec (radix D w.length)
                  (b % vertexBound (k := k) (radix D w.length)))]?)
            (predRecipes machine)).length = P := List.length_map _
      rw [List.ofFn_getD_eq_of_length none hlen_map]
      cases hget : (coinInSourcesWithSymbols machine (radix D w.length) w.length
          (b % vertexBound (k := k) (radix D w.length))
          ((predRecipes machine).map fun rec =>
            w[queryIndex (k := k) (radix D w.length)
              (evalPredRecipe rec (radix D w.length)
                (b % vertexBound (k := k) (radix D w.length)))]?))[q]? with
      | none => rfl
      | some u => simp
    · rfl
  have hfalse : ComputableInLogSpace
      ((fun _ : Triple => (none : Option (ℕ × ℕ))) ∘ Subtype.val)
      ((Function.Embedding.subtype (fun x => portGuard k D d P x = false)).trans encTriple)
      (encOption (encPair encNat encNat)) :=
    (ComputableInLogSpace.const none).restrict _
  refine (ComputableInLogSpace.ite_subtype hguard htrue hfalse).congr_fun fun ⟨w, b, q⟩ => ?_
  by_cases hg : portGuard k D d P (w, b, q) = true
  · simp [hg, f]
  · have hg' : portGuard k D d P (w, b, q) = false := Bool.eq_false_iff.mpr hg
    rcases ge_bound_or_port_ge_of_portGuard_false hg' with hb | hq
    · simp [hg', clockedInPort_eq_none_of_ge_bound machine hb q]
    · simp [hg', clockedInPort_eq_none_of_port_ge machine b hq]

end PortLogSpace

end Turing.MultiTapePTM.ConfigurationGraph
