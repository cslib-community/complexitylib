/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CountingLeaf.Raw
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds

/-!
# Counting leaves with a separately charged long context

The context is copied and projected only a fixed number of times. Counter normalization, path
decoding and the padding checks operate on the remaining short fields. Their polynomial cost is
therefore separate from the context length and from the supplied predicate's own time and space.
The certificate constructs the actual `runRaw` function; it assumes only a certificate for the
primitive predicate, not for the complete counting-leaf answer.
-/

public section

namespace Cslib.CountingLeaf

open Turing.MultiTapeTM

/-- Length of the local counter, path, selector and index fields, excluding the context. -/
@[expose] def RawInput.localSize (q : RawInput) : ℕ :=
  q.count.length + q.width.length + q.path.length + 1 + q.bit.length

private def localQuery (q : RawInput) : RawInput := { q with context := [] }

private theorem localQuery_inO : ComputableInO localQuery encRawInput encRawInput
    (fun q => (encRawInput q).length) (fun q => (encRawInput q).length) := by
  have h := encRawInput_mk_inO (ComputableInO.const ([] : List Bool))
    encRawInput_count_inO encRawInput_width_inO encRawInput_path_inO
    encRawInput_carry_inO encRawInput_bit_inO
  exact h.mono 6 (fun _ => by omega) (fun _ => by omega)

/-- Raw leaf evaluation pays linearly for the context and polynomially only for local fields,
in addition to the supplied predicate's input-indexed time and workspace bounds. The degree and
all realizing-machine constants are uniform over the context and every raw field. -/
theorem computableInO_runRaw (predicate : List Bool × ℕ → Bool)
    {T S : List Bool × ℕ → ℕ}
    (hp : ComputableInO predicate (encPair encBits encNat) encBool T S) :
    ∃ d, ComputableInO (runRaw predicate) encRawInput encBool
      (fun q => q.context.length + (q.localSize + 1) ^ d +
        T (q.context, BitString.binaryValue q.path))
      (fun q => q.context.length + (q.localSize + 1) ^ d +
        S (q.context, BitString.binaryValue q.path)) := by
  obtain ⟨dg, eg, hg⟩ :=
    (computableInPolyTime_runRaw (fun _ => true) (ComputableInPolyTime.const true)).exists_degree
  obtain ⟨dp, ep, hpath⟩ := ComputableInPolyTime.bitsBinaryValue.exists_degree
  have hguard := hg.inO.comp localQuery_inO
  have hindex := hpath.inO.comp encRawInput_path_inO
  have hpair := encRawInput_context_inO.prod hindex
  have hpred := hp.comp hpair
  have h := hguard.ite hpred (ComputableInO.const false)
  have heq : (fun q => if runRaw (fun _ => true) (localQuery q) then
      predicate (q.context, BitString.binaryValue q.path) else false) = runRaw predicate := by
    funext q
    by_cases hv : ofBits q.bit < ofBits q.width ∧ ofBits q.bit = 0 ∧ q.carry = false ∧
        BitString.binaryValue q.path < ofBits q.count <;>
      simp [runRaw, run, RawInput.normalize, localQuery, hv]
  change ComputableInO (fun q => if runRaw (fun _ => true) (localQuery q) then
    predicate (q.context, BitString.binaryValue q.path) else false) _ _ _ _ at h
  rw [heq] at h
  let d := dg + dp + 1
  have hcost (q : RawInput) (x : ℕ) :
      3 * (encRawInput q).length + ((encRawInput (localQuery q)).length + 1) ^ dg +
        (q.path.length + 1) ^ dp + x ≤
          (8 ^ dg + 40) * (q.context.length + (q.localSize + 1) ^ d + x + 1) := by
    have hlen : (encRawInput q).length ≤ 2 * q.context.length + 8 * (q.localSize + 1) := by
      simp only [length_encRawInput, RawInput.localSize]
      omega
    have hlocal : (encRawInput (localQuery q)).length + 1 ≤ 8 * (q.localSize + 1) := by
      simp only [length_encRawInput, localQuery, List.length_nil, RawInput.localSize]
      omega
    have hbase : 1 ≤ q.localSize + 1 := by omega
    have hsmall : q.localSize + 1 ≤ (q.localSize + 1) ^ d := by
      simpa only [pow_one] using Nat.pow_le_pow_right hbase (show 1 ≤ d by dsimp [d]; omega)
    have hguard : ((encRawInput (localQuery q)).length + 1) ^ dg ≤
        8 ^ dg * (q.localSize + 1) ^ d := by
      calc _ ≤ (8 * (q.localSize + 1)) ^ dg := Nat.pow_le_pow_left hlocal dg
        _ = 8 ^ dg * (q.localSize + 1) ^ dg := mul_pow _ _ _
        _ ≤ _ := Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right hbase (by dsimp [d]; omega))
    have hpath : (q.path.length + 1) ^ dp ≤ (q.localSize + 1) ^ d := by
      exact (Nat.pow_le_pow_left (by dsimp [RawInput.localSize]; omega) dp).trans
        (Nat.pow_le_pow_right hbase (by dsimp [d]; omega))
    have hlen' : (encRawInput q).length ≤
        2 * q.context.length + 8 * (q.localSize + 1) ^ d :=
      hlen.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 8 hsmall) _)
    calc
      _ ≤ 3 * (2 * q.context.length + 8 * (q.localSize + 1) ^ d) +
          8 ^ dg * (q.localSize + 1) ^ d + (q.localSize + 1) ^ d + x := by omega
      _ = 6 * q.context.length + (8 ^ dg + 25) * (q.localSize + 1) ^ d + 1 * x := by ring
      _ ≤ (8 ^ dg + 40) * q.context.length + (8 ^ dg + 40) * (q.localSize + 1) ^ d +
          (8 ^ dg + 40) * x + (8 ^ dg + 40) := by
        have hc := Nat.mul_le_mul_right q.context.length
          ((by decide : 6 ≤ 40).trans (Nat.le_add_left 40 (8 ^ dg)))
        have hl := Nat.mul_le_mul_right ((q.localSize + 1) ^ d)
          (show 8 ^ dg + 25 ≤ 8 ^ dg + 40 by omega)
        have hx := Nat.mul_le_mul_right x
          ((by decide : 1 ≤ 40).trans (Nat.le_add_left 40 (8 ^ dg)))
        exact (Nat.add_le_add (Nat.add_le_add hc hl) hx).trans (Nat.le_add_right _ _)
      _ = _ := by ring
  refine ⟨d, h.mono (8 ^ dg + 40) (fun q => ?_) (fun q => ?_)⟩
  · have hb := hcost q (T (q.context, BitString.binaryValue q.path))
    dsimp only [Function.comp_apply, encBits_apply]
    split_ifs <;> omega
  · have hb := hcost q (S (q.context, BitString.binaryValue q.path))
    dsimp only [Function.comp_apply, encBits_apply]
    split_ifs <;> omega

end Cslib.CountingLeaf
