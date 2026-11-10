/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORClassDepth
public import CslibFrontier.Cryptanalysis.AddXNORDPDissection
import CslibFrontier.Cryptanalysis.AddXNORSourceQuarter
import all CslibFrontier.Cryptanalysis.AddXNORSource

/-!
# The deterministic source range without a word-width restriction

[WangLvShenZhang2027], Theorem 7 (PDF p. 22), permits every `p ≤ floor(q/4)`.
The actual machine caps at the physical width; the additional labels are empty,
so the returned balance is still exactly the requested parameter. The depth
header is charged using the source's quarter bound, not an extra `p ≤ m` premise.
The per-class uniform expectation continues to require `p ≤ m`.

## Main results

* `original_classBalance_quarter`: the actual scalar equals the requested balance.
* `source_quarter_depth_bounds`: whole-run original-width bounds throughout the source range.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.DPDissection
open Turing.MultiTapeTM

/-- In the source range, capping the machine depth at the physical width adds only empty
labels. No restriction relating the requested depth to word width is needed. -/
theorem original_classBalance_quarter {m : ℕ} (p : ℕ) (s : BitVec m)
    (tail : List (BitVec m)) (hk : p ≤ tail.length / 4) :
    let left := SourceCounterCounts.forwardOperands tail
    let right := SourceCounterCounts.backwardOperands tail
    (run (Source.ofWords p s tail)).1 = classBalance p
      (fun i : Fin left.length => left[i.val]) (fun i : Fin right.length => right[i.val]) s 0 := by
  have cap : min p (min m (tail.length/4)) = min p m := by omega
  simpa only [cap, classBalance_min_width] using original_classBalance p s tail

/-- Actual source Theorem 7 time and every-prefix space for all requested `p ≤ floor(q/4)`,
including depths above the physical word width. The balance is the actual returned `μ_p`,
by `original_classBalance_quarter`; all input headers and intermediate tapes are charged. -/
theorem source_quarter_depth_bounds : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ m p (s : BitVec m) (tail : List (BitVec m)), p ≤ tail.length/4 →
      sourceCertificate.time (Source.ofWords p s tail) ≤ 2^(tail.length/2)*P (m+tail.length+1) ∧
        sourceCertificate.space (Source.ofWords p s tail) ≤
          (2^(tail.length/4)+(run (Source.ofWords p s tail)).1)*P (m+tail.length+1) := by
  obtain ⟨A, hpA, mA, bound⟩ := sourceCertificate_bounds
  let R := fun b => 12*(b+1)^2
  have hp : Cslib.PolynomiallyBounded (fun b => A (R b)) := by dsimp only [R]; fun_prop
  have mr : Monotone R := fun _ _ h => Nat.mul_le_mul_left 12
    (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 2)
  refine ⟨fun b => A (R b), hp, mA.comp mr, fun m p s tail hk => ?_⟩
  have base := SourceQuarter.original_input_length (p := 0) (Nat.zero_le m) s tail
  have wire : (Source.encoding (Source.ofWords p s tail)).length =
      2*p+(Source.encoding (Source.ofWords 0 s tail)).length := by
    simp only [Source.encoding, Source.ofWords, length_encPair, encUnary_apply,
      List.length_replicate]
    omega
  have scalar : (Source.encoding (Source.ofWords p s tail)).length ≤ R (m+tail.length+1) := by
    rw [wire]
    dsimp only [R]
    have depth : p ≤ tail.length := hk.trans (Nat.div_le_self _ _)
    nlinarith only [base, depth, Nat.zero_le (m*tail.length), Nat.zero_le (m^2),
      Nat.zero_le (tail.length^2), Nat.zero_le m, Nat.zero_le tail.length]
  have h := bound m p s tail
  exact ⟨h.1.trans (Nat.mul_le_mul_left _ (mA scalar)),
    h.2.trans (Nat.mul_le_mul_left _ (mA scalar))⟩

end Cslib.Cryptanalysis.AddXNOR.DPDissection
