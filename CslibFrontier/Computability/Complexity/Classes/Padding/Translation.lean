/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Time
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Transducer
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.NatPolynomial
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OPrimitives

/-!
# Translation of deterministic time collapses

If `DTIME f₁ ⊆ DTIME f₂`, then `DTIME (f₁ ∘ G) ⊆ DTIME (f₂ ∘ G)` for every padding function `G`
with `n < G n` computable in polynomial time in binary. A word `x` of length `m` is padded to
length exactly `G m` by prefixing `G m - m - 1` ones and a zero. The padded problem accepts `y`
when, after removing the leading ones and one zero, the remainder `x` satisfies `G |x| ≤ |y|` and
lies in the original problem. The guard costs `O(|y|)` and the writer `O(G m)`, so the transfer
loses only constant factors.

This is the translation (padding) argument of [Fortnow and Santhanam, §3.3,
Lemma 5][FortnowSanthanam2006] for a general padding function, with all native costs proved. The
only hypotheses on the bounds are that `f₁` is monotone and `n ≤ f₁ n`, `n ≤ f₂ n`.

## Main results

* `Cslib.Complexity.DTIME_comp_subset_of_subset`: a deterministic time collapse transfers along
  a polynomial-time padding function.

## References

* [L. Fortnow and R. Santhanam, §3.3, Lemma 5][FortnowSanthanam2006]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- The word `x` padded to length `L`: `L - |x| - 1` ones, a zero, then `x`. -/
private def pad (L : ℕ) (x : List Bool) : List Bool :=
  List.replicate (L - x.length - 1) true ++ false :: x

/-- Removes the leading ones and one zero. -/
private def unpad (y : List Bool) : List Bool :=
  (y.dropWhile (· = true)).tail

private theorem unpad_replicate_append (k : ℕ) (x : List Bool) :
    unpad (List.replicate k true ++ false :: x) = x := by
  induction k with
  | zero => rfl
  | succ k ih => simp [unpad, List.replicate_succ]

private theorem unpad_pad (L : ℕ) (x : List Bool) : unpad (pad L x) = x :=
  unpad_replicate_append _ x

private theorem length_pad {L : ℕ} {x : List Bool} (h : x.length < L) :
    (pad L x).length = L := by
  simp only [pad, List.length_append, List.length_replicate, List.length_cons]
  omega

private theorem length_unpad_le (y : List Bool) : (unpad y).length ≤ y.length := by
  simp only [unpad, List.length_tail]
  have := (List.dropWhile_suffix (· = true) (l := y)).length_le
  omega

/-- The transducer removing the leading ones and one zero. Its state records whether the zero was
removed. -/
private def unpadT : Transducer Bool Bool where
  q₀ := false
  step q b := if q then (true, [b]) else (!b, [])
  final _ := []
  length_step_le q b := by cases q <;> cases b <;> simp
  length_final_le _ := by simp

private theorem run_unpadT_true (y : List Bool) : unpadT.run true y = y := by
  induction y with
  | nil => rfl
  | cons b y ih =>
    rw [Transducer.run_cons]
    change [b] ++ unpadT.run true y = _
    rw [ih]
    rfl

private theorem run_unpadT (y : List Bool) : unpadT.run false y = unpad y := by
  induction y with
  | nil => rfl
  | cons b y ih =>
    rw [Transducer.run_cons]
    cases b
    · change [] ++ unpadT.run true y = _
      rw [run_unpadT_true]
      rfl
    · change [] ++ unpadT.run false y = _
      rw [ih]
      simp [unpad]

private theorem computableInO_unpad :
    ComputableInO unpad encBits encBits (fun y => y.length) fun y => y.length := by
  refine .of_tidy (ComputableTidilyInO.of_bounds
    (unpadT.computableTidilyInTimeAndSpace fun y => (run_unpadT y).symm) 12
    (fun y => ?_) (fun _ => Nat.zero_le _) fun y => ?_)
  · simp only [encBits_apply]
    omega
  · have := length_unpad_le y
    simp only [encBits_apply]
    omega

variable {G : ℕ → ℕ}

/-- The padding writer, within time `O(G |x|)`. -/
private theorem computableInO_pad (hG : ComputableInPolyTime G encNat encNat)
    (hlt : ∀ n, n < G n) :
    ComputableInO (fun x => pad (G x.length) x) encBits encBits (fun x => G x.length)
      fun x => G x.length := by
  have hgap : ComputableInPolyTime (fun n => G n - n - 1) encNat encNat :=
    .binary_sub' (.binary_sub' hG .id') (.const 1)
  have hu := ComputableInO.natToUnary.comp (hgap.nat_inO.comp ComputableInO.lengthNat)
  have hcons : ComputableInO (fun x : List Bool => false :: x) encBits encBits
      (fun x => x.length + x.length) fun x => x.length + x.length :=
    (ComputableInO.const (encMid := encBits) [false]).append
      (ComputableInO.of_eq (f := fun x : List Bool => x) (encMid := encBits) fun _ => rfl)
      fun _ => rfl
  have h := hu.append hcons (g := fun x => pad (G x.length) x) (encOut := encBits) fun _ => rfl
  refine h.mono 4 (fun x => ?_) fun x => ?_
  all_goals
    have := hlt x.length
    simp only [Function.comp_apply]
    omega

/-- **Translation of deterministic time collapses.** If `DTIME f₁ ⊆ DTIME f₂`, then the collapse
transfers along every padding function `G` computable in polynomial time in binary with
`n < G n`: `DTIME (f₁ ∘ G) ⊆ DTIME (f₂ ∘ G)`. Pad an input of length `m` to length `G m`. -/
theorem DTIME_comp_subset_of_subset {f₁ f₂ : ℕ → ℕ} (hf₁ : Monotone f₁) (hf₁n : ∀ n, n ≤ f₁ n)
    (hf₂n : ∀ n, n ≤ f₂ n) (hG : ComputableInPolyTime G encNat encNat) (hlt : ∀ n, n < G n)
    (h : DTIME encBits f₁ ⊆ DTIME encBits f₂) :
    DTIME encBits (f₁ ∘ G) ⊆ DTIME encBits (f₂ ∘ G) := by
  intro A hA
  classical
  let guard (y : List Bool) := decide (G (unpad y).length ≤ y.length)
  let B : Set (List Bool) :=
    {y | (if guard y then indicator A (unpad y) else false) = true}
  have hle : ComputableInPolyTime (fun p : ℕ × ℕ => decide (G p.1 ≤ p.2))
      (encPair encNat encNat) encBool :=
    (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.binary_le).comp
      ((hG.comp (.fst encNat encNat)).prod (.snd encNat encNat))
  have hguard : ComputableInO guard encBits encBool (fun y => y.length) fun y => y.length := by
    have hlens := (ComputableInO.lengthNat.comp computableInO_unpad).prod ComputableInO.lengthNat
    refine (hle.natPair_inO.comp hlens).mono 5 (fun y => ?_) fun y => ?_
    all_goals
      have := length_unpad_le y
      simp only [Function.comp_apply]
      omega
  have hdec := hguard.ite ((computableInO_indicator_of_mem_DTIME hA).comp computableInO_unpad)
    (ComputableInO.const (encMid := encBool) false)
  have hB : B ∈ DTIME encBits f₁ := by
    refine setOf_mem_DTIME_of_computableInO
      (hdec.mono (T' := fun y => f₁ y.length) (S' := fun y => f₁ y.length) 4
        (fun y => ?_) fun y => ?_) fun _ => le_rfl
    all_goals
      have hy := hf₁n y.length
      have hu := length_unpad_le y
      simp only [Function.comp_apply, encBits_apply]
      split_ifs with hg
      · have := hf₁ (of_decide_eq_true hg)
        omega
      · omega
  have hpre : A = (fun x => pad (G x.length) x) ⁻¹' B := by
    ext x
    have hg : guard (pad (G x.length) x) = true := by
      simp only [guard, unpad_pad, length_pad (hlt x.length), le_refl, decide_true]
    simp only [Set.mem_preimage, B, Set.mem_ofPred_eq, hg, ↓reduceIte, unpad_pad]
    simp [indicator]
  rw [hpre]
  refine preimage_mem_DTIME (C := 2) (h hB) (computableInO_pad hG hlt) fun x => ?_
  simp only [encBits_apply, length_pad (hlt x.length), Function.comp_apply]
  have := hf₂n (G x.length)
  omega

end Cslib.Complexity
