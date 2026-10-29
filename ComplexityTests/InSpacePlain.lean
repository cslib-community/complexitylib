/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Bit
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain

/-!
# Plain bounded-space combinators and arithmetic

Client checks for the plain `Turing.MultiTapeTM.ComputableInSpace` and
`Turing.MultiTapeTM.ComputableInPolySpace` libraries without tidy bridges: binary division,
multiplication, bit extraction, bounded list folds, and exponentially long iterations in
polynomial space.
-/

namespace ComplexityTests.InSpacePlain

open Cslib Turing.MultiTapeTM

/-- Modular list scan: fold `acc ↦ (acc + x) % (m + 1)` across a list of binary naturals, staying
within linear space in `(m, xs)`. -/
def modSum (p : ℕ × List ℕ) : ℕ :=
  p.2.foldl (fun acc x => (acc + x) % (p.1 + 1)) 0

theorem modSum_inSpace :
    ComputableInSpace modSum (encPair encNat (encList encNat)) encNat
      fun p => (encPair encNat (encList encNat) p).length := by
  have hm := ComputableInSpace.fst encNat (encList encNat)
  have hxs := ComputableInSpace.snd encNat (encList encNat)
  have hstep : ComputableInSpace
      (fun q : (ℕ × ℕ) × ℕ => (q.1.2 + q.2) % (q.1.1 + 1))
      (encPair (encPair encNat encNat) encNat) encNat
      fun q => (encPair (encPair encNat encNat) encNat q).length + 1 := by
    have hin : (fun q => (encPair (encPair encNat encNat) encNat q).length) ≼
        fun q => (encPair (encPair encNat encNat) encNat q).length + 1 :=
      .of_le fun _ => by omega
    have hma := (ComputableInSpace.fst (encPair encNat encNat) encNat).weaken hin
    have hx := (ComputableInSpace.snd (encPair encNat encNat) encNat).weaken hin
    exact ComputableInSpace.budget_natMod
      (ComputableInSpace.budget_natAdd (ComputableInSpace.snd' hma) hx)
      (ComputableInSpace.budget_natAdd (ComputableInSpace.fst' hma)
        (ComputableInSpace.budget_const 1 hin))
  have hlen (p : ℕ × List ℕ) (i : ℕ) :
      (encNat ((p.2.take i).foldl (fun acc x => (acc + x) % (p.1 + 1)) 0)).length ≤
        (encNat p.1).length := by
    cases hp : p.2.take i using List.reverseRecOn with
    | nil => exact length_encNat_mono (Nat.zero_le _)
    | append_singleton ys y =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact length_encNat_mono (Nat.lt_succ_iff.mp (Nat.mod_lt _ (Nat.succ_pos _)))
  refine ((ComputableInSpace.foldlWith (encP := encNat) (encA := encNat) (encL := encList encNat)
    (par := Prod.fst) (list := Prod.snd) (init := fun _ => 0)
    (step := fun m acc x => (acc + x) % (m + 1)) hm hxs (ComputableInSpace.const 0) hstep
    (Q := fun p => 4 * (encPair encNat (encList encNat) p).length + 4)
    (B := fun p => (encNat p.1).length)
    (fun p i hi => by
      have h₁ := hlen p i
      have h₂ := length_le_encList_of_mem encNat (List.getElem_mem hi)
      simp only [length_encPair] at h₁ h₂ ⊢
      omega)
    (fun p i _ => hlen p i)).weaken ?_).of_enc_eq fun _ => rfl
  exact .of_le_linear 9 4 fun p => by simp only [length_encPair]; omega

example : modSum (6, [3, 5, 6, 2]) = 2 := rfl
example : modSum (0, [3, 5]) = 0 := rfl

/-- Extract the `j`-th bit of `a * b` in linear space in the encoded triple. -/
def mulBit (t : (ℕ × ℕ) × ℕ) : Bool :=
  (t.1.1 * t.1.2).testBit t.2

theorem mulBit_inSpace :
    ComputableInSpace mulBit (encPair (encPair encNat encNat) encNat) encBool
      fun t => (encPair (encPair encNat encNat) encNat t).length + 1 := by
  have hin : (fun t => (encPair (encPair encNat encNat) encNat t).length) ≼
      fun t => (encPair (encPair encNat encNat) encNat t).length + 1 :=
    .of_le fun _ => by omega
  have hab := (ComputableInSpace.fst (encPair encNat encNat) encNat).weaken hin
  have hj := (ComputableInSpace.snd (encPair encNat encNat) encNat).weaken hin
  have hprod := ComputableInSpace.budget_natMul
    (ComputableInSpace.fst' hab) (ComputableInSpace.snd' hab)
  obtain ⟨c, hc⟩ := hprod.length_le
  exact (ComputableInSpace.natTestBit.comp (hprod.prod hj)).weaken
    ⟨64 * c + 64, fun t => by
      have hlen := hc t
      simp only [length_encPair] at hlen ⊢
      nlinarith⟩

example : mulBit ((6, 7), 1) = true := rfl
example : mulBit ((6, 7), 2) = false := rfl

/-- Counting in binary via `iterate` runs for exponentially many steps in the binary input length
while staying in `ComputableInPolySpace`. -/
def countUp (n : ℕ) : ℕ :=
  (· + 1)^[n] 0

theorem countUp_polySpace : ComputableInPolySpace countUp encNat encNat := by
  have hstep : ComputableInPolySpace (· + 1) encNat encNat :=
    ComputableInPolySpace.of_inSpace
      (PolyBounded.of_forall_le 1 1 fun n => by simp only [pow_one]; omega)
      ComputableInSpace.natSucc
  refine (ComputableInPolySpace.iterate ComputableInPolyTime.id'
    (ComputableInPolySpace.of_polyTime (ComputableInPolyTime.const 0)) hstep
    (B := fun n => (encNat n).length)
    (PolyBounded.of_forall_le 1 1 fun n => by simp only [pow_one]; omega) ?_).congr
    fun _ => rfl
  intro n k hk
  rw [ComputableInO.iterate_succ_eq, zero_add]
  exact length_encNat_mono hk

example (n : ℕ) : countUp n = n := by
  simp [countUp, ComputableInO.iterate_succ_eq]

end ComplexityTests.InSpacePlain
