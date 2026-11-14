/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.SMN
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Encoded size of the s-m-n construction

The existing description transformation `Turing.MultiTapeTM.Universal.hardwire d p` builds the
prefix `p` into the description `d`. This module accounts for the size of the description it
constructs. The exact decomposition follows its writing, copying, rewinding and redirected
transition tables; the arithmetic endpoint is quadratic in the framed encoding of `(d, p)`.

These are rigorous lengths in `Turing.MultiTapeTM.Universal.eDesc`. That encoding uses unary state
and symbol numbers, so the bounds are model-dependent code lengths, not implementation byte counts
or tight estimates for another compiler. The transformation itself is offline: its polynomial-time
uniformity is `Turing.MultiTapeTM.Universal.computableInPolyTime_hardwire`, while the compiler's
runtime is not charged to a hardwired program unless another construction executes the compiler.

## Main definitions

This module adds no representation: it measures the existing
`Turing.MultiTapeTM.Universal.hardwire` construction with
`Turing.MultiTapeTM.Universal.descLen`, which is exactly the length of `eDesc`.

## Main results

* `Turing.MultiTapeTM.Universal.Hardwire.descLen_hardwire_eq`: the exact structural decomposition
  of a generated description's encoded length.
* `Turing.MultiTapeTM.Universal.Hardwire.descLen_hardwire_le`: a concrete quadratic upper bound in
  the encoded input length.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Lemma 6.1][Sipser2013]
-/

public section

namespace Turing.MultiTapeTM.Universal

namespace Hardwire

open Redirect

/-- There are three writing transitions for the marker and for each prefix bit. -/
theorem length_writeEntries (p : List Bool) (k : ℕ) :
    (writeEntries p k).length = 3 * (p.length + 1) := by
  simp [writeEntries, bitSyms, List.length_flatMap, List.sum_replicate, Nat.mul_comm]
  omega

/-- The input-copying table has transitions for the two bits and the final blank. -/
theorem length_copyEntries (k : ℕ) : (copyEntries k).length = 3 := rfl

/-- The rewinding table has transitions for a blank, the two bits and the marker. -/
theorem length_rewindEntries (q : ℕ) (r : Option ℕ) (rest : List (Option ℕ)) (next : ℕ) :
    (rewindEntries q r rest next).length = 4 := by
  simp [rewindEntries, bitSyms]

private theorem length_vlift_le (i : Option ℕ) : (vlift i).length ≤ 2 := by
  rcases i with _ | i
  · rfl
  · simp only [vlift]
    split <;> simp

private theorem length_redirect_le (table : List (Key × Act)) :
    (redirect (fun q => 2 * q + 1) none [] 0 id table).length ≤ 2 * table.length := by
  induction table with
  | nil => rfl
  | cons e table ih =>
    rw [redirect, List.flatMap_cons, List.length_append, List.length_map, ← redirect]
    have := length_vlift_le e.1.input
    simp only [List.length_cons]
    omega

/-- The exact encoded length of a hardwired description, split into the preparation tables and
the redirected source table. Each table is measured by its actual framed encoding. -/
theorem descLen_hardwire_eq (d : Desc) (p : List Bool) :
    descLen (hardwire d p) = 2 * (d.tapes + 1) + 2 +
      (encList (encPair eKey eAct) (writeEntries p d.tapes)).length +
      (encList (encPair eKey eAct) (copyEntries d.tapes)).length +
      (encList (encPair eKey eAct)
        (rewindEntries 2 none (List.replicate d.tapes none) (2 * d.q₀ + 1))).length +
      (encList (encPair eKey eAct)
        (redirect (fun q => 2 * q + 1) none [] 0 id d.table)).length := by
  simp only [descLen, hardwire, eDesc_apply, length_encPair, encUnary_apply,
    List.length_replicate, encList_append, List.length_append]
  omega

private theorem length_redirectEntry_le (e : Key × Act) (s : Option ℕ)
    (hs : s ∈ vlift e.1.input) :
    (encPair eKey eAct (redirectEntry (fun q => 2 * q + 1) none [] 0 id e s)).length ≤
      50 * ((encPair eKey eAct e).length + 1) := by
  rcases e with ⟨⟨q, i, work⟩, ⟨move, actions, output, next⟩⟩
  rcases i with _ | i
  · have hs' : s = some marker ∨ s = none := by simpa [vlift] using hs
    rcases hs' with rfl | rfl <;> rcases output with _ | output <;>
      rcases next with _ | next <;> rcases move with _ | _ | _ <;>
      simp_all [redirectEntry, eKey_apply, eAct_apply, eTA, length_encList,
        encUnary_apply, encSign, encOption, vmove, marker] <;> omega
  · by_cases hi : i = marker
    · simp [vlift, hi] at hs
    · have : s = some i := by simpa [vlift, hi] using hs
      subst s
      rcases output with _ | output <;> rcases next with _ | next <;>
        rcases move with _ | _ | _ <;>
        simp_all [redirectEntry, eKey_apply, eAct_apply, eTA, length_encList,
          encUnary_apply, encSign, encOption, vmove, marker] <;> omega

private theorem length_encList_redirect_le (d : Desc) :
    (encList (encPair eKey eAct)
      (redirect (fun q => 2 * q + 1) none [] 0 id d.table)).length ≤
        (2 * d.table.length) * (2 * (50 * (descLen d + 1)) + 1) := by
  refine (length_encList_le (encPair eKey eAct) _ (b := 50 * (descLen d + 1)) ?_).trans ?_
  · intro e' he'
    simp only [redirect, List.mem_flatMap, List.mem_map] at he'
    obtain ⟨e, he, s, hs, rfl⟩ := he'
    have hentry := length_le_encList_of_mem (encPair eKey eAct) he
    have htable : (encList (encPair eKey eAct) d.table).length ≤ descLen d := by
      simp only [descLen, eDesc_apply, length_encPair]
      omega
    exact (length_redirectEntry_le e s hs).trans
      (Nat.mul_le_mul_left 50 (Nat.add_le_add_right (hentry.trans htable) 1))
  · exact Nat.mul_le_mul_right _ (length_redirect_le d.table)

private theorem length_prepEntry_le {d : Desc} {p : List Bool} {e : Key × Act}
    (he : e ∈ prep d p) :
    (encPair eKey eAct e).length ≤ 100 * (descLen d + p.length + 1) := by
  have htapes := tapes_le d
  have hq₀ := q₀_le d
  simp only [prep, writeEntries, copyEntries, rewindEntries, bitSyms, List.mem_append,
    List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ((⟨r, hr, rfl⟩ | ⟨⟨b, i⟩, hbi, r, hr, rfl⟩) | (rfl | rfl | rfl)) |
    (⟨s, hs, rfl⟩ | rfl)
  · rcases hr with rfl | rfl | rfl <;>
      simp [eKey_apply, eAct_apply, eTA, length_encList, encUnary_apply, encSign,
        encOption, marker] <;> omega
  · rw [List.mem_zipIdx_iff_getElem?] at hbi
    have hi : i < p.length := by
      simpa only [List.length_reverse] using (List.getElem?_eq_some_iff.mp hbi).1
    have hbit : eBit b ≤ 1 := by cases b <;> decide
    rcases hr with rfl | rfl | rfl <;>
      simp [eKey_apply, eAct_apply, eTA, length_encList, encUnary_apply, encSign,
        encOption] <;> omega
  · simp [eKey_apply, eAct_apply, eTA, length_encList, encUnary_apply, encSign,
      encOption]
    omega
  · simp [eKey_apply, eAct_apply, eTA, length_encList, encUnary_apply, encSign,
      encOption]
    omega
  · simp [eKey_apply, eAct_apply, eTA, length_encList, encUnary_apply, encSign,
      encOption]
    omega
  · rcases hs with rfl | rfl | rfl <;>
      simp [eKey_apply, eAct_apply, eTA, length_encList, encUnary_apply, encSign,
        encOption]
    all_goals omega
  · simp [eKey_apply, eAct_apply, eTA, length_encList, encUnary_apply, encSign,
      encOption, marker]
    omega

private theorem length_prep (d : Desc) (p : List Bool) :
    (prep d p).length = 3 * p.length + 10 := by
  simp only [prep, List.length_append, length_writeEntries, length_copyEntries,
    length_rewindEntries]
  omega

private theorem length_encList_prep_le (d : Desc) (p : List Bool) :
    (encList (encPair eKey eAct) (prep d p)).length ≤
      (3 * p.length + 10) * (2 * (100 * (descLen d + p.length + 1)) + 1) := by
  rw [← length_prep]
  exact length_encList_le (encPair eKey eAct) _ fun _ he => length_prepEntry_le he

/-- The encoded hardwired description has quadratic size in the encoded source description and
the prefix. The constant `2500` is a proved coarse upper bound, not a tightness claim. Both sides
use the library's unary `eDesc` coding, not an implementation-size estimate. -/
theorem descLen_hardwire_le (d : Desc) (p : List Bool) :
    descLen (hardwire d p) ≤
      2500 * ((encPair eDesc encBits (d, p)).length) ^ 2 := by
  have hprep := length_encList_prep_le d p
  have hredirect := length_encList_redirect_le d
  have htapes := tapes_le d
  have htable := table_le d
  have hinput : descLen d + p.length + 1 ≤ (encPair eDesc encBits (d, p)).length := by
    change (eDesc d).length + p.length + 1 ≤ _
    simp only [length_encPair, encBits_apply]
    omega
  rw [descLen_hardwire_eq]
  simp only [prep, encList_append, List.length_append] at hprep
  nlinarith [sq_nonneg (descLen d + p.length + 1),
    sq_nonneg ((encPair eDesc encBits (d, p)).length)]

end Hardwire

end Turing.MultiTapeTM.Universal
