/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BQP.TensorContraction
public import Complexity.Computability.Circuit.Quantum.Output
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Data.List.GetD

/-!
# Integer masses of quantum output prefixes

An arbitrary output pattern is reduced to the existing projected-gap simulator by appending a
NOT gate for each desired zero. This changes neither the Hadamard count nor the power-of-two
probability denominator. Zipping a wire list with a prefix gives the integer masses used by the
rank decoder. Their root is `2 ^ h`, and each nonterminal mass is the sum of its two children.

The resource theorem charges at most one extra gate per measured wire. A wire list of length at
most the original gate count therefore preserves the contraction exponent up to a constant.
-/

public section

namespace Cslib.Complexity.QuantumContraction

open Quantum Turing.MultiTapeTM Cslib.GenericRAM ComputableInPolyTime

/-- The integer numerator of a pattern, computed by the projected-gap simulator after flipping
its desired-zero wires. Correctness requires distinct, valid pattern wires. -/
@[expose] def patternGap (gs : List GateCode) (X : List Bool) (ps : List (ℕ × Bool)) : ℕ :=
  gapValue (patternWires ps) (gs ++ GateCode.flipCodes (patternZeros ps)) X

/-- The mass of a prefix on the given wire list. Extra prefix bits are ignored by `zip`; the
rank decoder only requests prefixes at most as long as the wire list. -/
@[expose] def prefixGap (gs : List GateCode) (X : List Bool) (S : List ℕ)
    (pre : List Bool) : ℕ := patternGap gs X (S.zip pre)

private theorem wellFormed_append_pattern {gs : List GateCode} {X : List Bool}
    (hgs : ∀ g ∈ gs, g.WellFormed X.length) {ps : List (ℕ × Bool)}
    (hvalid : ∀ p ∈ ps, p.1 < X.length) :
    ∀ g ∈ gs ++ GateCode.flipCodes (patternZeros ps), g.WellFormed X.length := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hgs g hg
  · refine (GateCode.isClassical_flipCodes (S := patternZeros ps) ?_ g hg).2
    intro j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ((patternZeros_sublist ps).subset hj)
    exact hvalid p hp

/-- The simulator's pattern numerator has the original circuit's Hadamard denominator. -/
theorem patternProb_eq_patternGap {gs : List GateCode} {X : List Bool}
    (hgs : ∀ g ∈ gs, g.WellFormed X.length) {ps : List (ℕ × Bool)}
    (hps : (patternWires ps).Nodup) (hvalid : ∀ p ∈ ps, p.1 < X.length) :
    patternProb X.length gs ps X = (patternGap gs X ps : ℝ) / 2 ^ hadamardCount gs := by
  rw [← onesProb_append_flipCodes_eq_patternProb gs hps hvalid X,
    onesProb_eq_gapValue (wellFormed_append_pattern hgs hvalid) _ le_rfl,
    hadamardCount_append_flipCodes]
  simp [patternGap]

private theorem patternWires_zip_sublist (S : List ℕ) (pre : List Bool) :
    (patternWires (S.zip pre)).Sublist S := by
  induction S generalizing pre with
  | nil => simp [patternWires]
  | cons j S ih =>
    cases pre with
    | nil => simp [patternWires]
    | cons b pre => simpa [patternWires] using (ih pre).cons_cons j

private theorem valid_zip {S : List ℕ} {m : ℕ} (hS : ∀ j ∈ S, j < m) (pre : List Bool) :
    ∀ p ∈ S.zip pre, p.1 < m := by
  intro p hp
  exact hS p.1 (List.of_mem_zip hp).1

/-- Prefix probabilities are represented exactly by the integer query. -/
theorem patternProb_eq_prefixGap {gs : List GateCode} {X : List Bool}
    (hgs : ∀ g ∈ gs, g.WellFormed X.length) {S : List ℕ} (hS : S.Nodup)
    (hvalid : ∀ j ∈ S, j < X.length) (pre : List Bool) :
    patternProb X.length gs (S.zip pre) X =
      (prefixGap gs X S pre : ℝ) / 2 ^ hadamardCount gs :=
  patternProb_eq_patternGap hgs (hS.sublist (patternWires_zip_sublist S pre))
    (valid_zip hvalid pre)

/-- The empty output prefix has exactly `2 ^ h` ranks. -/
theorem prefixGap_nil {gs : List GateCode} {X : List Bool}
    (hgs : ∀ g ∈ gs, g.WellFormed X.length) (S : List ℕ) :
    prefixGap gs X S [] = 2 ^ hadamardCount gs := by
  have h := patternProb_eq_patternGap hgs (ps := []) (by simp [patternWires]) (by simp)
  simp only [patternProb_nil] at h
  have hpow : (2 : ℝ) ^ hadamardCount gs ≠ 0 := by positivity
  have heq := (eq_div_iff hpow).mp h
  have heq' : (patternGap gs X [] : ℝ) = 2 ^ hadamardCount gs := by simpa using heq.symm
  simpa [prefixGap] using (show patternGap gs X [] = 2 ^ hadamardCount gs by
    exact_mod_cast heq')

private theorem zip_append_bit (S : List ℕ) (pre : List Bool) (b : Bool)
    (hlen : pre.length < S.length) :
    S.zip (pre ++ [b]) = S.zip pre ++ [(S.getD pre.length 0, b)] := by
  induction pre generalizing S with
  | nil =>
    cases S with
    | nil => simp at hlen
    | cons j S => simp
  | cons c pre ih =>
    cases S with
    | nil => simp at hlen
    | cons j S =>
      have hlen' : pre.length < S.length := by simpa using hlen
      simpa using congrArg (List.cons (j, c)) (ih S hlen')

/-- Every prefix below the requested depth splits into its two nonnegative integer masses. -/
theorem prefixGap_add {gs : List GateCode} {X : List Bool}
    (hgs : ∀ g ∈ gs, g.WellFormed X.length) {S : List ℕ} (hS : S.Nodup)
    (hvalid : ∀ j ∈ S, j < X.length) (pre : List Bool) (hlen : pre.length < S.length) :
    prefixGap gs X S pre = prefixGap gs X S (pre ++ [false]) +
      prefixGap gs X S (pre ++ [true]) := by
  have hj : S.getD pre.length 0 < X.length := by
    rw [List.getD_eq_getElem _ _ hlen]
    exact hvalid _ (List.getElem_mem hlen)
  have h := patternProb_partition gs (S.zip pre) hj X
  rw [← zip_append_bit S pre false hlen, ← zip_append_bit S pre true hlen,
    patternProb_eq_prefixGap hgs hS hvalid,
    patternProb_eq_prefixGap hgs hS hvalid,
    patternProb_eq_prefixGap hgs hS hvalid, ← add_div] at h
  have hpow : (2 : ℝ) ^ hadamardCount gs ≠ 0 := by positivity
  exact_mod_cast (div_left_inj' hpow).mp h

/-! ### Native query resources -/

section Resources

variable {α : Type} {enc : α ↪ List Bool}

private theorem poly_patternWires {ps : α → List (ℕ × Bool)}
    (hps : ComputableInPolyTime ps enc (encList (encPair encUnary encBool))) :
    ComputableInPolyTime (fun a => patternWires (ps a)) enc (encList encUnary) := by
  unfold patternWires
  fun_prop

private theorem poly_patternZeros {ps : α → List (ℕ × Bool)}
    (hps : ComputableInPolyTime ps enc (encList (encPair encUnary encBool))) :
    ComputableInPolyTime (fun a => patternZeros (ps a)) enc (encList encUnary) := by
  unfold patternZeros
  fun_prop

private theorem poly_flipCodes {S : α → List ℕ}
    (hS : ComputableInPolyTime S enc (encList encUnary)) :
    ComputableInPolyTime (fun a => GateCode.flipCodes (S a)) enc (encList encGateCode) := by
  unfold GateCode.flipCodes
  fun_prop

/-- A prefix query on at most `L` wires adds at most `L` NOT gates, so its contraction exponent
is bounded using the original gate count. No bound on the supplied prefix length is required. -/
private theorem prefix_exponent_le (A : ℕ) (gs : List GateCode) (S : List ℕ)
    (pre : List Bool) (hS : S.length ≤ gs.length) :
    A * ((gs ++ GateCode.flipCodes (patternZeros (S.zip pre))).length + 1) /
        Nat.sqrt (Nat.log 2 ((gs ++ GateCode.flipCodes (patternZeros (S.zip pre))).length + 2)) ≤
      2 * A * (gs.length + 1) / Nat.sqrt (Nat.log 2 (gs.length + 2)) := by
  have hz := length_patternZeros_le (S.zip pre)
  have hzip : (S.zip pre).length ≤ S.length := by simp only [List.length_zip]; omega
  have hlen : (gs ++ GateCode.flipCodes (patternZeros (S.zip pre))).length =
      gs.length + (patternZeros (S.zip pre)).length := by simp
  rw [hlen]
  refine Nat.div_le_div ?_ (Nat.sqrt_le_sqrt (Nat.log_mono_right (by omega))) ?_
  · have hnum : gs.length + (patternZeros (S.zip pre)).length + 1 ≤ 2 * (gs.length + 1) :=
      by omega
    exact (Nat.mul_le_mul_left A hnum).trans_eq (by ring)
  · exact Nat.sqrt_eq_zero.not.mpr (Nat.log_pos (by norm_num) (by omega)).ne'

/-- **One exact prefix query with the original circuit exponent.** The wire list, circuit and
explicit register are computed in polynomial time. The list contains at most one entry per gate
and all its wires are valid. Prefixes may have arbitrary length: zipping them with the wire list
keeps the appended circuit small even on states outside the decoder's reachable set. -/
theorem exists_expTimePolySpace_prefixGap {gs : α → List GateCode} {X : α → List Bool}
    {S : α → List ℕ} {pre : α → List Bool}
    (hgs : ComputableInPolyTime gs enc (encList encGateCode))
    (hX : ComputableInPolyTime X enc encBits)
    (hS : ComputableInPolyTime S enc (encList encUnary))
    (hpre : ComputableInPolyTime pre enc encBits)
    (hwf : ∀ a, ∀ g ∈ gs a, g.WellFormed (X a).length)
    (hvalid : ∀ a, ∀ j ∈ S a, j < (X a).length)
    (hsize : ∀ a, (S a).length ≤ (gs a).length) :
    ∃ (A : ℕ) (c : NativeCertificate (fun a => prefixGap (gs a) (X a) (S a) (pre a))
        enc encNat),
      c.ExpTimePolySpace fun a =>
        A * ((gs a).length + 1) / Nat.sqrt (Nat.log 2 ((gs a).length + 2)) := by
  have hps : ComputableInPolyTime (fun a => (S a).zip (pre a)) enc
      (encList (encPair encUnary encBool)) :=
    (zip encUnary encBool).comp (hS.prod (bitsToList.comp hpre))
  have hcodes := listAppend' hgs (poly_flipCodes (poly_patternZeros hps))
  obtain ⟨A, c, hc⟩ := exists_expTimePolySpace_gapValue (poly_patternWires hps) hcodes hX
    (fun a => wellFormed_append_pattern (hwf a) (valid_zip (hvalid a) (pre a)))
  refine ⟨2 * A, c, hc.mono fun a => ?_⟩
  exact prefix_exponent_le A (gs a) (S a) (pre a) (hsize a)

end Resources

end Cslib.Complexity.QuantumContraction
