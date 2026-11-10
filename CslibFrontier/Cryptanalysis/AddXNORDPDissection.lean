/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORBalanceCompatibility
public import CslibFrontier.Cryptanalysis.AddXNORSourceResources
import all CslibFrontier.Cryptanalysis.AddXNORJoinedDissection
import all CslibFrontier.Cryptanalysis.AddXNORSourceCounterBalance
import CslibFrontier.Cryptanalysis.AddXNORSourceQuarter
import all CslibFrontier.Computability.GenericRAM.Native.Combinators

/-!
# The DP balance prepass before the complete source dissection search

Run the actual original-input DP balance prepass, retain its scalar result, then
execute the approved complete sorted-list dissection search and witness readback.
The slow count-only balance-output branch is bypassed. Per-class search/orientation
is unchanged, so its established resource envelope remains available.

## Main results

* `original_correct`: actual original-input witness soundness and exhaustive misses.
* `sourceCertificate_bounds`: whole-run resources in the actual returned balance.
* `source_parameter_bounds`: the fixed polynomial depends only on original source widths.

`BalanceCompatibility` identifies the returned DP scalar with the actual search
envelope. On typed inputs the full pipeline realizes the source Theorem 7 bounds,
with the computed capped depth; on admitted depths this is the paper's parameter.
No expectation of class size is substituted for the maximum smaller-class size.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.DPDissection
open Turing.MultiTapeTM Cslib.GenericRAM

/-- Scalar DP balance followed by the actual generated class search and decoded witness. -/
def run (input : Source.Input) : ℕ × Option (List Bool) :=
  (SourceCounterBalance.run input, JoinedDissection.solve (Source.prepare input))

/-- Frame the binary balance before the optional framed bit-string witness, using the
existing witness encoding and explicit option tag. -/
abbrev outputEncoding : (ℕ × Option (List Bool)) ↪ List Bool := encPair encNat (encOption encBits)

private noncomputable def searchCertificate : NativeCertificate
    (fun input => JoinedDissection.solve (Source.prepare input)) Source.encoding
    (encOption encBits) := JoinedDissection.solveCertificate.comp Source.prepareCertificate

/-- One actual source machine runs the faster DP scalar prepass before full-state retention,
then preserves the approved search/control/readback path. Both phases and frames are charged. -/
noncomputable def sourceCertificate : NativeCertificate run Source.encoding outputEncoding :=
  SourceCounterBalance.runCertificate.prod searchCertificate

private theorem source_time (input : Source.Input) : sourceCertificate.time input =
    SourceCounterBalance.runCertificate.time input+searchCertificate.time input := rfl

private theorem source_space (input : Source.Input) : sourceCertificate.space input =
    SourceCounterBalance.runCertificate.space input+searchCertificate.space input := rfl

/-- Replacing the balance-output branch does not assume a witness or a completed traversal. -/
theorem original_correct {m : ℕ} (p : ℕ) (s : BitVec m) (tail : List (BitVec m)) :
    let (_, result) := run (Source.ofWords p s tail)
    (result = none ↔ ¬ Solvable tail s 0) ∧
      ∀ ops, result = some ops → ops.length = tail.length ∧ eval (ops.zip tail) s = 0 :=
  JoinedDissection.original_correct p s tail

private theorem search_time_le (input : Source.Input) :
    searchCertificate.time input ≤
      JoinedDissection.sourceCertificate.time input := by
  dsimp only [searchCertificate, JoinedDissection.sourceCertificate, NativeCertificate.congr]
  rw [NativeCertificate.comp_time, NativeCertificate.comp_time, NativeCertificate.prod_time]
  omega

private theorem search_space_le (input : Source.Input) :
    searchCertificate.space input ≤
      JoinedDissection.sourceCertificate.space input := by
  dsimp only [searchCertificate, JoinedDissection.sourceCertificate, NativeCertificate.congr]
  rw [NativeCertificate.comp_space, NativeCertificate.comp_space, NativeCertificate.prod_space]
  omega

/-- Reuse the approved search envelope while replacing only the scalar prepass branch. -/
private theorem envelope_bounds : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ m p (s : BitVec m) (tail : List (BitVec m)),
      let original := Source.ofWords p s tail
      let I := (Source.encoding original).length
      sourceCertificate.time original ≤ 2^(tail.length/2)*P I ∧
        sourceCertificate.space original ≤
          (2^(tail.length/4)+ClassBalance.balance (Source.prepare original))*P I := by
  obtain ⟨A, hpA, mA, fast⟩ := SourceCounterBalance.source_certificate
  obtain ⟨B, hpB, mB, old⟩ := SourceResources.sourceCertificate_bounds
  let P := fun I => A (I+1)+B I
  have hp : Cslib.PolynomiallyBounded P := by dsimp only [P]; fun_prop
  have mp : Monotone P := fun _ _ h => Nat.add_le_add (mA (Nat.add_le_add_right h 1)) (mB h)
  refine ⟨P, hp, mp, fun m p s tail => ?_⟩
  dsimp only
  rw [source_time, source_space]
  have f := fast m p s tail
  have slow := old m p s tail
  dsimp only at slow
  -- Abstract the source value before resource arithmetic to avoid unfolding large certificates.
  generalize Source.ofWords p s tail = input at f slow ⊢
  let I := (Source.encoding input).length
  have timePart := search_time_le input
  have spacePart := search_space_le input
  have powers := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    (show tail.length/4 ≤ tail.length/2 by omega)
  have scaledT := Nat.mul_le_mul_right (A (I+1)) powers
  have scaledS := Nat.mul_le_mul_right (A (I+1))
    (Nat.le_add_right (2^(tail.length/4)) (ClassBalance.balance (Source.prepare input)))
  constructor
  · exact (Nat.add_le_add (f.1.trans scaledT) (timePart.trans slow.1)).trans_eq
      (by dsimp only [P]; ring)
  · exact (Nat.add_le_add (f.2.trans scaledS) (spacePart.trans slow.2)).trans_eq
      (by dsimp only [P]; ring)

/-- The returned scalar is exactly the balance controlling the actual per-class search. -/
theorem original_balance {m : ℕ} (p : ℕ) (s : BitVec m) (tail : List (BitVec m)) :
    (run (Source.ofWords p s tail)).1 =
      ClassBalance.balance (Source.prepare (Source.ofWords p s tail)) :=
  BalanceCompatibility.original_balance p s tail

/-- The returned scalar is the maximum smaller-class population of the actual original half
chains, at the computed depth. This identifies the source parameter, not a supplied class size. -/
theorem original_classBalance {m : ℕ} (p : ℕ) (s : BitVec m) (tail : List (BitVec m)) :
    let d := min p (min m (tail.length/4))
    let left := SourceCounterCounts.forwardOperands tail
    let right := SourceCounterCounts.backwardOperands tail
    (run (Source.ofWords p s tail)).1 = classBalance d
      (fun i : Fin left.length => left[i.val]) (fun i : Fin right.length => right[i.val]) s 0 :=
  SourceCounterBalance.run_eq_classBalance p s tail

/-- On admitted low-bit depths the computed cap is inert, so the returned scalar is the
paper's requested `μ_p`, including every fourth-quarter residue and indexed multiplicity. -/
theorem original_classBalance_admitted {m p : ℕ} (hp : p ≤ m)
    (s : BitVec m) (tail : List (BitVec m)) (hk : p ≤ tail.length / 4) :
    let left := SourceCounterCounts.forwardOperands tail
    let right := SourceCounterCounts.backwardOperands tail
    (run (Source.ofWords p s tail)).1 = classBalance p
      (fun i : Fin left.length => left[i.val]) (fun i : Fin right.length => right[i.val]) s 0 := by
  have depth : min p (min m (tail.length/4)) = p := Nat.min_eq_left (le_min hp hk)
  simpa only [depth] using original_classBalance p s tail

/-- Whole-run source bit time and every-prefix peak workspace use the actual DP balance
returned by this same execution. Preparation, prepass, class retention/probing/reuse, original
witness decoding and their simultaneous internal tapes are all charged. -/
theorem sourceCertificate_bounds : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ m p (s : BitVec m) (tail : List (BitVec m)),
      let original := Source.ofWords p s tail
      let I := (Source.encoding original).length
      sourceCertificate.time original ≤ 2^(tail.length/2)*P I ∧
        sourceCertificate.space original ≤ (2^(tail.length/4)+(run original).1)*P I := by
  obtain ⟨P, hp, mp, bound⟩ := envelope_bounds
  refine ⟨P, hp, mp, fun m p s tail => ?_⟩
  simpa only [original_balance] using bound m p s tail

/-- Original source-parameter form of Theorem 7 for the actual uniform multitape execution.
The requested low-bit depth fits the physical words; the machine additionally caps it at the
quarter size. The fixed polynomial is only in original word width and operand count.
For admitted `p ≤ tail.length/4`, the returned balance is exactly `μ_p` by
`original_classBalance`. No runtime or execution conclusion is an endpoint premise. -/
theorem source_parameter_bounds : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ m p (s : BitVec m) (tail : List (BitVec m)), p ≤ m →
      sourceCertificate.time (Source.ofWords p s tail) ≤ 2^(tail.length/2)*P (m+tail.length+1) ∧
        sourceCertificate.space (Source.ofWords p s tail) ≤
          (2^(tail.length/4)+(run (Source.ofWords p s tail)).1)*P (m+tail.length+1) := by
  obtain ⟨A, hpA, mA, bound⟩ := sourceCertificate_bounds
  let R := fun b => 10*(b+1)^2
  have hp : Cslib.PolynomiallyBounded (fun b => A (R b)) := by dsimp only [R]; fun_prop
  have mr : Monotone R := fun _ _ h => Nat.mul_le_mul_left 10
    (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 2)
  refine ⟨fun b => A (R b), hp, mA.comp mr, fun m p s tail hm => ?_⟩
  have input := SourceQuarter.original_input_length hm s tail
  have scalar : (Source.encoding (Source.ofWords p s tail)).length ≤ R (m+tail.length+1) := by
    dsimp only [R]
    nlinarith only [input, Nat.zero_le (m*tail.length), Nat.zero_le (m^2),
      Nat.zero_le (tail.length^2), Nat.zero_le m, Nat.zero_le tail.length]
  have h := bound m p s tail
  exact ⟨h.1.trans (Nat.mul_le_mul_left _ (mA scalar)),
    h.2.trans (Nat.mul_le_mul_left _ (mA scalar))⟩

end Cslib.Cryptanalysis.AddXNOR.DPDissection
