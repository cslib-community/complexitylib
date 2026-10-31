/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Constructible
public import Complexity.Computability.Complexity.Classes.Hierarchy
public import Complexity.Computability.Complexity.Classes.Hierarchy.ShortDesc
public import Complexity.Computability.Complexity.Classes.Time
public import Complexity.Computability.Machines.Turing.MultiTape.Run
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-!
# The time hierarchy theorem

The deterministic time class `Cslib.Complexity.DTIME enc t` of
`Complexity.Computability.Complexity.Classes.Time` consists of the problems that some machine with
a binary alphabet and finitely many states decides within time `c₁ * t n + c₂`, for constants `c₁`
and `c₂`, on instances whose encoding under `enc` has length `n`. A bound `t` is
*time-constructible* (`Cslib.Complexity.TimeConstructible`) when such a machine computes `t n` in
binary from any word of length `n` within time `O(t n)`; so are `2 ^ n` and `(n + 1) ^ k` for
`k ≥ 2`. These definitions and their generic API are in
`Complexity.Computability.Complexity.Classes.Constructible`.

## The time hierarchy theorem

The clocked diagonal `Cslib.Complexity.clockedDiagonal J` of
`Complexity.Computability.Complexity.Classes.Hierarchy` runs the machine described at the start of
its input `x` on `x` for `J x.length` steps with the universal function, and negates the verdict;
the diagonal function `Cslib.Complexity.diagonal` has the clock `2 ^ n`.
`Cslib.Complexity.timeDiagonal J` applies it only when the framed description is short,
`2 ^ |unframe x| ≤ |x|` (`Cslib.Complexity.Diagonal.shortDesc`, in
`Complexity.Computability.Complexity.Classes.Hierarchy.ShortDesc`), and answers `false` otherwise.
Decoding a description of `L` bits takes time polynomial in `L`, of a degree fixed by the decoder,
hence `O(2 ^ L)`, which is `O(n)` on short descriptions; padded descriptions are short.

The resource estimate used here bounds `J` simulated steps by `O(B ^ 5 * J ^ 3)`,
where `B` bounds the encoded description, input and clock length. This weakens the sharper
`O((B + 1) ^ 4 * J ^ 2)` bound (`Turing.MultiTapeTM.Universal.universal_bounds_le`), so the problem
decided by
`timeDiagonal J` is in `DTIME ((n + 1) ^ 5 * (J n + 1) ^ 3)` for a time-constructible clock `J`
(`Cslib.Complexity.setOf_timeDiagonal_mem_DTIME`). It is not in `DTIME f` when every `c * f n + c`
is eventually below `J n`, by the diagonal argument
(`Cslib.Complexity.setOf_timeDiagonal_notMem_DTIME`). In fact each constant need only be beaten
at arbitrarily large lengths (`Cslib.Complexity.setOf_timeDiagonal_notMem_DTIME_of_frequently_le`);
this also yields noninclusion when the bounds are incomparable at other lengths.
Hence `DTIME f ⊂ DTIME g`
[Arora and Barak, Theorem 3.1][AroraBarak09], [Sipser, Theorem 9.10][Sipser2013]:

* when such a time-constructible clock `J` has `(n + 1) ^ 5 * (J n + 1) ^ 3 ≤ g n` eventually
  (`Cslib.Complexity.DTIME_ssubset_DTIME_of_clock`);
* when `f` is time-constructible, `n ≤ f n` and `(n + 1) ^ 8 * (f n + 1) ^ 3 ≤ g n` eventually,
  with the clock `(n + 1) * f n` (`Cslib.Complexity.DTIME_ssubset_DTIME`). As `n ≤ f n`, the gap
  `(f n + 1) ^ 11 ≤ g n` suffices.

The polynomial gap is the overhead of the native universal machine, which is polynomial in the
description and in the clock. The textbook gap `f n * log (f n) = o(g n)` needs a simulation with
logarithmic overhead and is not claimed here. `Hierarchy.LogClock` reduces the clock inflation
to `f n * (Nat.size (f n) + 1)`. `Hierarchy.Polynomial` uses native padding to prove strictness
between every pair of distinct positive integer polynomial degrees, despite this
interpreter overhead.

## Main definitions

* `Cslib.Complexity.timeDiagonal`: the clocked diagonal on short descriptions.

## Main results

* `Cslib.Complexity.computableInO_timeDiagonal`: the clocked diagonal is computable within the
  time of the universal machine.
* `Cslib.Complexity.setOf_timeDiagonal_mem_DTIME`,
  `Cslib.Complexity.setOf_timeDiagonal_notMem_DTIME`: the clocked diagonal is decidable within
  the time of the universal machine, and not within time `O(f)` for clocks beyond every `O(f)`.
* `Cslib.Complexity.setOf_timeDiagonal_notMem_DTIME_of_frequently_le`,
  `Cslib.Complexity.DTIME_not_subset_DTIME_of_clock`: the clock need only dominate each constant
  at arbitrarily large favorable lengths.
* `Cslib.Complexity.DTIME_ssubset_DTIME_of_clock`: the time hierarchy theorem, for a clock.
* `Cslib.Complexity.DTIME_ssubset_DTIME`: the time hierarchy theorem, for a time-constructible
  bound.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Filter

/-! ### The clocked diagonal -/

namespace Diagonal

/-- The space of the universal run grows with the number of steps. -/
private theorem runBound_le_succ (D N J : ℕ) : runBound D N J ≤ runBound D N (J + 1) := by
  simp only [runBound, ctxBound, cfgBound, tapeBound]
  gcongr <;> omega

/-- The numeric core of the resources of the clocked diagonal: for an input of length `n`, a
decoding time `A` linear in `n`, a decoded description of encoded length `D`, encoded symbols of
length `N`, a clock `J` of `L` binary digits and a result of encoded length `E`, everything is
within `K * (n + 1) ^ 5 * (J + 1) ^ 3` steps and cells. -/
private theorem clockedBounds_aux (cA cD cO C₂ : ℕ) : ∃ K, ∀ {n A D N J L I E : ℕ},
    A ≤ cA * (n + 1) → D ≤ cD * (n + A + 1) → N ≤ 3 * n → (L + 1) ^ 2 ≤ C₂ * (J + 1) →
    I = 2 * D + 1 + (2 * N + 1 + L) →
    E ≤ cO * (n + A + (n + J) + (runBound D N J + I) + 1) →
    n + A + (n + J) + ((J + 1) * (stepBound D N J + runBound D N J + (L + 1) ^ 2) +
        (I + 1) ^ 2) + (E + 1) ^ 2 ≤ K * ((n + 1) ^ 5 * (J + 1) ^ 3) ∧
      n + A + (n + J) + (runBound D N J + I) + E ≤ K * ((n + 1) ^ 5 * (J + 1) ^ 3) := by
  set P := cD * (cA + 1) + 3 with hP
  set R := 5 * P + C₂ with hR
  set Q := cA + 4 + 200 * P ^ 2 + R with hQ
  refine ⟨cA + 3 + 100000 * P ^ 5 + C₂ + R ^ 2 + (cO * Q + 1) ^ 2 + 200 * P ^ 2 + R + cO * Q,
    fun {n A D N J L I E} hA hD hN hL hI hE => ?_⟩
  have hPn : P * (n + 1) = cD * (cA + 1) * (n + 1) + 3 * (n + 1) := by rw [hP]; ring
  have hD' : D ≤ cD * (cA + 1) * (n + 1) :=
    hD.trans ((Nat.mul_le_mul_left cD (show n + A + 1 ≤ (cA + 1) * (n + 1) by
      have : (cA + 1) * (n + 1) = cA * (n + 1) + (n + 1) := by ring
      omega)).trans (le_of_eq (by ring)))
  obtain ⟨hU₁, hU₂⟩ := Turing.MultiTapeTM.Universal.universal_bounds_le
    (D := D) (N := N) (J := J + 1)
    (B := P * (n + 1) - 1) (L := 0) (by omega) (by omega) (Nat.zero_le _) (by omega)
  have hPX1 : 1 ≤ P * (n + 1) := by omega
  rw [Nat.sub_add_cancel hPX1] at hU₁ hU₂
  simp only [zero_add, one_pow] at hU₁
  have hstep := stepBound_mono (le_refl D) (le_refl N) (Nat.le_add_right J 1)
  have hrun := runBound_le_succ D N J
  have hD'' : D ≤ P * (n + 1) := by omega
  have hN' : N ≤ P * (n + 1) := by omega
  -- the monomials
  have hX1 : 1 ≤ n + 1 := by omega
  have hY1 : 1 ≤ J + 1 := by omega
  set W := (n + 1) ^ 5 * (J + 1) ^ 3 with hW
  set Z := (n + 1) ^ 2 * (J + 1) with hZ
  have hZ1 : 1 ≤ Z := Nat.mul_pos (Nat.pow_pos hX1) hY1
  have hXY : (n + 1) * (J + 1) ≤ W := Nat.mul_le_mul (Nat.le_self_pow (by norm_num) (n + 1))
    (Nat.le_self_pow (by norm_num) (J + 1))
  have hXYZ : (n + 1) * (J + 1) ≤ Z :=
    Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) (n + 1))
  have hZW : Z ≤ W := Nat.mul_le_mul (Nat.pow_le_pow_right hX1 (by omega))
    (Nat.le_self_pow (by norm_num) (J + 1))
  have hX2Y2 : (n + 1) ^ 2 * (J + 1) ^ 2 ≤ W := Nat.mul_le_mul (Nat.pow_le_pow_right hX1 (by omega))
    (Nat.pow_le_pow_right hY1 (by omega))
  have hX4Y2 : (n + 1) ^ 4 * (J + 1) ^ 2 ≤ W := Nat.mul_le_mul (Nat.pow_le_pow_right hX1 (by omega))
    (Nat.pow_le_pow_right hY1 (by omega))
  have hY2 : (J + 1) ^ 2 ≤ W := by
    have := Nat.mul_le_mul (Nat.one_le_pow 5 (n + 1) hX1)
      (Nat.pow_le_pow_right hY1 (show 2 ≤ 3 by omega))
    rwa [one_mul] at this
  -- the pieces
  have hU' : 100000 * (P * (n + 1)) ^ 4 * (J + 1) ^ 2 ≤ 100000 * P ^ 5 * W := by
    have hmono := Nat.mul_le_mul
      (Nat.pow_le_pow_right hPX1 (show 4 ≤ 5 by omega))
      (Nat.pow_le_pow_right hY1 (show 2 ≤ 3 by omega))
    have hscaled := Nat.mul_le_mul_left 100000 hmono
    simpa only [hW, mul_pow, Nat.mul_assoc] using hscaled
  have hrunZ : runBound D N J ≤ 200 * P ^ 2 * Z := by
    have : 200 * (P * (n + 1)) ^ 2 * (J + 1) = 200 * P ^ 2 * Z := by
      simp only [hZ, mul_pow, Nat.mul_assoc]
    omega
  have hLY : L ≤ C₂ * (J + 1) := (Nat.le_succ L).trans ((Nat.le_self_pow two_ne_zero _).trans hL)
  have hI1 : I + 1 ≤ R * ((n + 1) * (J + 1)) := by
    have h₁ : 5 * P * (n + 1) ≤ 5 * P * ((n + 1) * (J + 1)) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hY1)
    have h₂ : C₂ * (J + 1) ≤ C₂ * ((n + 1) * (J + 1)) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hX1)
    have e₁ : R * ((n + 1) * (J + 1)) =
        5 * P * ((n + 1) * (J + 1)) + C₂ * ((n + 1) * (J + 1)) := by
      rw [hR]; ring
    have e₂ : 5 * P * (n + 1) = 5 * (P * (n + 1)) := by ring
    omega
  have hpre : n + A + (n + J) ≤ (cA + 3) * ((n + 1) * (J + 1)) := by
    have h₁ : (cA + 2) * (n + 1) ≤ (cA + 2) * ((n + 1) * (J + 1)) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hY1)
    have h₂ : (J + 1) ≤ (n + 1) * (J + 1) := Nat.le_mul_of_pos_left _ hX1
    have e₁ : (cA + 3) * ((n + 1) * (J + 1)) =
        (cA + 2) * ((n + 1) * (J + 1)) + (n + 1) * (J + 1) := by ring
    have e₂ : (cA + 2) * (n + 1) = cA * (n + 1) + 2 * (n + 1) := by ring
    omega
  have hsum : n + A + (n + J) + (runBound D N J + I) + 1 ≤ Q * Z := by
    have h₁ := Nat.mul_le_mul_left (cA + 3) hXYZ
    have h₂ := Nat.mul_le_mul_left R hXYZ
    have e : Q * Z = (cA + 3) * Z + 200 * P ^ 2 * Z + R * Z + Z := by rw [hQ]; ring
    omega
  have hEZ : E ≤ cO * Q * Z :=
    hE.trans ((Nat.mul_le_mul_left cO hsum).trans (le_of_eq (by ring)))
  have hE1 : E + 1 ≤ (cO * Q + 1) * Z := by
    have e : (cO * Q + 1) * Z = cO * Q * Z + Z := by ring
    omega
  have hT₁ : (J + 1) * (stepBound D N J + runBound D N J + (L + 1) ^ 2) ≤
      100000 * P ^ 5 * W + C₂ * W := by
    have h₁ : (J + 1) * (stepBound D N J + runBound D N J) ≤
        (J + 1 + 1) * (stepBound D N (J + 1) + runBound D N (J + 1) + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h₂ : (J + 1) * (L + 1) ^ 2 ≤ C₂ * W := by
      calc (J + 1) * (L + 1) ^ 2 ≤ (J + 1) * (C₂ * (J + 1)) := Nat.mul_le_mul_left _ hL
        _ = C₂ * (J + 1) ^ 2 := by ring
        _ ≤ C₂ * W := Nat.mul_le_mul_left _ hY2
    rw [Nat.mul_add]
    omega
  have hI2 : (I + 1) ^ 2 ≤ R ^ 2 * W := by
    calc (I + 1) ^ 2 ≤ (R * ((n + 1) * (J + 1))) ^ 2 := Nat.pow_le_pow_left hI1 2
      _ = R ^ 2 * ((n + 1) ^ 2 * (J + 1) ^ 2) := by simp only [mul_pow]
      _ ≤ R ^ 2 * W := Nat.mul_le_mul_left _ hX2Y2
  have hE2 : (E + 1) ^ 2 ≤ (cO * Q + 1) ^ 2 * W := by
    calc (E + 1) ^ 2 ≤ ((cO * Q + 1) * Z) ^ 2 := Nat.pow_le_pow_left hE1 2
      _ = (cO * Q + 1) ^ 2 * ((n + 1) ^ 4 * (J + 1) ^ 2) := by
        simp only [hZ, mul_pow, ← pow_mul]
      _ ≤ (cO * Q + 1) ^ 2 * W := Nat.mul_le_mul_left _ hX4Y2
  have hpreW : n + A + (n + J) ≤ (cA + 3) * W := hpre.trans (Nat.mul_le_mul_left _ hXY)
  have hrunW : runBound D N J ≤ 200 * P ^ 2 * W := hrunZ.trans (Nat.mul_le_mul_left _ hZW)
  have hIW : I ≤ R * W := (Nat.le_succ I).trans (hI1.trans (Nat.mul_le_mul_left R hXY))
  have hEW : E ≤ cO * Q * W := hEZ.trans (Nat.mul_le_mul_left _ hZW)
  have e : (cA + 3 + 100000 * P ^ 5 + C₂ + R ^ 2 + (cO * Q + 1) ^ 2 + 200 * P ^ 2 + R + cO * Q) *
      W = (cA + 3) * W + 100000 * P ^ 5 * W + C₂ * W + R ^ 2 * W + (cO * Q + 1) ^ 2 * W +
        200 * P ^ 2 * W + R * W + cO * Q * W := by ring
  rw [e]
  constructor
  · clear * - hpreW hT₁ hI2 hE2
    omega
  · clear * - hpreW hrunW hIW hEW
    omega

end Diagonal

/-- **The clocked diagonal on short descriptions.** The clocked diagonal
`Cslib.Complexity.clockedDiagonal J` when the description framed at the start of `x` is short
(`Cslib.Complexity.Diagonal.shortDesc`), and `false` otherwise. -/
def timeDiagonal (J : ℕ → ℕ) (x : List Bool) : Bool :=
  if Diagonal.shortDesc x then clockedDiagonal J x else false

open Diagonal in
/-- **The clocked diagonal is computable within the time of the universal machine**: within time
and space `O((n + 1) ^ 5 * (J n + 1) ^ 3)` on inputs of length `n`, for a time-constructible clock
`J`, charging the shortness test, decoding, the symbols, the clock, the universal run and the
test. -/
theorem computableInO_timeDiagonal {J : ℕ → ℕ} (hJ : TimeConstructible J) :
    ComputableInO (timeDiagonal J) encBits encBool
      (fun x => (x.length + 1) ^ 5 * (J x.length + 1) ^ 3)
      fun x => (x.length + 1) ^ 5 * (J x.length + 1) ^ 3 := by
  have this : ComputableTidilyInO (timeDiagonal J) encBits encBool
      (fun x => (x.length + 1) ^ 5 * (J x.length + 1) ^ 3) fun x => (x.length + 1) ^ 5 *
      (J x.length + 1) ^ 3 := by
    obtain ⟨dd, ed, hdec⟩ := exists_computableInDegree_decodeDesc
    have hu : ComputableTidilyInO unframe encBits encBits (fun x => x.length) fun x => x.length :=
      ComputableTidilyInO.of_linear (.of_unframe fun _ => rfl)
    have hdesc := hdec.inO.tidy.comp hu
    have hsym := Universal.computableTidilyInDegree_map_eBit.inO_one
    have hclock := hJ.computableInO.tidy
    have hU := computableTidilyInO_universal.comp (hdesc.prod (hsym.prod hclock))
    have h := computableInO_shortDesc.tidy.ite (computableInO_verdict.tidy.comp hU)
      (ComputableTidilyInO.const (encMid := encBool) false)
    obtain ⟨cD, hcD⟩ := hdesc.length_le
    obtain ⟨cO, hcO⟩ := hU.length_le
    obtain ⟨cA, hcA⟩ := PolynomiallyBounded.exists_le_mul_two_pow (p := fun u => (u + 1) ^ dd)
      (by fun_prop)
    obtain ⟨C₂, hC₂⟩ := exists_pow_length_encNat_le 2
    obtain ⟨K, hK⟩ := clockedBounds_aux cA cD cO C₂
    have hbounds (x : List Bool) (hs : shortDesc x = true) := by
      have hA : ((unframe x).length + 1) ^ dd ≤ cA * (x.length + 1) :=
        (hcA _).trans (Nat.mul_le_mul_left _ ((of_decide_eq_true hs).trans (Nat.le_succ _)))
      have hN : (encList encUnary (x.map eBit)).length ≤ 3 * x.length :=
        (length_encList_le encUnary _ (b := 1) fun s hs => by
          obtain ⟨b, -, rfl⟩ := List.mem_map.mp hs
          cases b
          · exact Nat.zero_le _
          · exact le_rfl).trans (by rw [List.length_map]; omega)
      have hD := hcD x
      have hE := hcO x
      dsimp only [Function.comp_apply, encBits_apply] at hD hE
      exact hK (D := descLen (decodeDesc (unframe x))) hA hD hN (hC₂ _)
        (by rw [length_encPair, length_encPair]) hE
    have hW (x : List Bool) : x.length + 1 ≤ (x.length + 1) ^ 5 * (J x.length + 1) ^ 3 :=
      (Nat.le_self_pow (by norm_num) _).trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)))
    have hW2 (x : List Bool) : (x.length + 1) ^ 2 ≤ (x.length + 1) ^ 5 * (J x.length + 1) ^ 3 :=
      (Nat.pow_le_pow_right (by omega) (by omega)).trans
        (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)))
    refine h.mono (K + 2) (fun x => ?_) fun x => ?_
    · have e : (K + 2) * ((x.length + 1) ^ 5 * (J x.length + 1) ^ 3 + 1) =
          K * ((x.length + 1) ^ 5 * (J x.length + 1) ^ 3) +
            2 * ((x.length + 1) ^ 5 * (J x.length + 1) ^ 3) + K + 2 := by ring
      have := hW x
      have := hW2 x
      dsimp only [Function.comp_apply, encBits_apply]
      split_ifs with hs
      · have := (hbounds x hs).1
        omega
      · omega
    · have e : (K + 2) * ((x.length + 1) ^ 5 * (J x.length + 1) ^ 3 + 1) =
          K * ((x.length + 1) ^ 5 * (J x.length + 1) ^ 3) +
            2 * ((x.length + 1) ^ 5 * (J x.length + 1) ^ 3) + K + 2 := by ring
      have := hW x
      dsimp only [Function.comp_apply, encBits_apply]
      split_ifs with hs
      · have := (hbounds x hs).2
        omega
      · omega
  simpa only [computableInO_iff_computableTidilyInO] using this

/-- **Diagonalization at arbitrarily large favorable lengths.** The clock need only dominate
each linear bound infinitely often. A description can be padded to every sufficiently large
length, so the diagonal argument does not require eventual domination or monotonicity. -/
theorem setOf_timeDiagonal_notMem_DTIME_of_frequently_le {f J : ℕ → ℕ}
    (hJ : ∀ c, ∃ᶠ n in atTop, c * f n + c ≤ J n) :
    {x | timeDiagonal J x = true} ∉ DTIME encBits f := by
  rintro ⟨c₁, c₂, s, hA⟩
  obtain ⟨g, ⟨k, State, hfinite, tm, htm⟩, hg⟩ := decidableInTimeAndSpace_iff.mp hA
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  let code := eDesc (desc eS eBit tm)
  obtain ⟨n, hn, htime⟩ := frequently_atTop.mp (hJ (max c₁ c₂))
    (2 * code.length + 1 + 2 ^ code.length)
  have hbase : 2 * code.length + 1 ≤ n := (Nat.le_add_right _ _).trans hn
  have hcode : 2 ^ code.length ≤ n := (Nat.le_add_left _ _).trans hn
  let pad := List.replicate (n - (2 * code.length + 1)) false
  have hlen : (frame code ++ pad).length = n := by
    simp only [List.length_append, length_frame, pad, List.length_replicate]
    omega
  have hshort : Diagonal.shortDesc (frame (eDesc (desc eS eBit tm)) ++ pad) = true := by
    rw [Diagonal.shortDesc, unframe_frame_append, hlen]
    exact decide_eq_true hcode
  have htime : c₁ * f (frame (eDesc (desc eS eBit tm)) ++ pad).length + c₂ ≤
      J (frame (eDesc (desc eS eBit tm)) ++ pad).length := by
    rw [hlen]
    exact (Nat.add_le_add (Nat.mul_le_mul_right _ (le_max_left _ _))
      (le_max_right _ _)).trans htime
  obtain ⟨hhalt, hout⟩ := (htm _).runFrom_of_le htime
  have hd := clockedDiagonal_desc eS tm pad J hhalt hout
  have hgx := hg (frame (eDesc (desc eS eBit tm)) ++ pad)
  simp only [Set.mem_ofPred_eq, timeDiagonal, hshort, ↓reduceIte, hd] at hgx
  revert hgx
  cases g (frame (eDesc (desc eS eBit tm)) ++ pad) <;> decide

/-- **The diagonal argument for time.** Eventual domination of every linear time bound is a
sufficient special case of diagonalization at arbitrarily large favorable lengths. -/
theorem setOf_timeDiagonal_notMem_DTIME {f J : ℕ → ℕ}
    (hJ : ∀ c, ∀ᶠ n in atTop, c * f n + c ≤ J n) :
    {x | timeDiagonal J x = true} ∉ DTIME encBits f :=
  setOf_timeDiagonal_notMem_DTIME_of_frequently_le fun c => (hJ c).frequently

/-- The problem of the clocked diagonal is decidable within time
`O((n + 1) ^ 5 * (J n + 1) ^ 3)`. -/
theorem setOf_timeDiagonal_mem_DTIME {J : ℕ → ℕ} (hJ : TimeConstructible J) :
    {x | timeDiagonal J x = true} ∈ DTIME encBits fun n => (n + 1) ^ 5 * (J n + 1) ^ 3 :=
  setOf_mem_DTIME_of_computableInO (computableInO_timeDiagonal hJ)
    (t := fun n => (n + 1) ^ 5 * (J n + 1) ^ 3) fun _ => le_rfl

/-! ### The time hierarchy theorem -/

/-- **Time-class noninclusion from a clock.** Infinitely many favorable lengths for each constant
suffice to separate the upper class from `DTIME f`. Unlike strict inclusion, this statement needs
no comparison between `f` and `g` at the other lengths. -/
theorem DTIME_not_subset_DTIME_of_clock {f g J : ℕ → ℕ} (hJ : TimeConstructible J)
    (hfJ : ∀ c, ∃ᶠ n in atTop, c * f n + c ≤ J n)
    (hg : ∀ᶠ n in atTop, (n + 1) ^ 5 * (J n + 1) ^ 3 ≤ g n) :
    ¬DTIME encBits g ⊆ DTIME encBits f := fun h =>
  setOf_timeDiagonal_notMem_DTIME_of_frequently_le hfJ
    (h (DTIME_mono_of_eventually_le hg (setOf_timeDiagonal_mem_DTIME hJ)))

/-- **A hierarchy for irregular bounds.** The clock must dominate the lower bound only
infinitely often for each constant. Eventual `f ≤ g` supplies the inclusion separately. -/
theorem DTIME_ssubset_DTIME_of_frequently_clock {f g J : ℕ → ℕ} (hJ : TimeConstructible J)
    (hfJ : ∀ c, ∃ᶠ n in atTop, c * f n + c ≤ J n)
    (hfg : ∀ᶠ n in atTop, f n ≤ g n)
    (hg : ∀ᶠ n in atTop, (n + 1) ^ 5 * (J n + 1) ^ 3 ≤ g n) :
    DTIME encBits f ⊂ DTIME encBits g :=
  ⟨DTIME_mono_of_eventually_le hfg, DTIME_not_subset_DTIME_of_clock hJ hfJ hg⟩

/-- **The time hierarchy theorem, for a clock.** If a time-constructible clock `J` eventually
exceeds every `c * f n + c`, then `DTIME f` is strictly contained in every `DTIME g` with
`(n + 1) ^ 5 * (J n + 1) ^ 3 ≤ g n` eventually [Arora and Barak, Theorem 3.1][AroraBarak09]. -/
theorem DTIME_ssubset_DTIME_of_clock {f g J : ℕ → ℕ} (hJ : TimeConstructible J)
    (hfJ : ∀ c, ∀ᶠ n in atTop, c * f n + c ≤ J n)
    (hg : ∀ᶠ n in atTop, (n + 1) ^ 5 * (J n + 1) ^ 3 ≤ g n) :
    DTIME encBits f ⊂ DTIME encBits g := by
  have hsub : DTIME encBits f ⊆ DTIME encBits g := DTIME_mono_of_eventually_le <| by
    filter_upwards [hfJ 1, hg] with n h₁ h₂
    have : J n ≤ (n + 1) ^ 5 * (J n + 1) ^ 3 :=
      (Nat.le_succ _).trans ((Nat.le_self_pow (by norm_num) _).trans
        (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))))
    omega
  exact (Set.ssubset_iff_of_subset hsub).mpr ⟨_,
    DTIME_mono_of_eventually_le hg (setOf_timeDiagonal_mem_DTIME hJ),
    setOf_timeDiagonal_notMem_DTIME hfJ⟩

/-- **The time hierarchy theorem.** If `f` is time-constructible and `n ≤ f n`, then `DTIME f` is
strictly contained in every `DTIME g` with `(n + 1) ^ 8 * (f n + 1) ^ 3 ≤ g n` eventually
[Arora and Barak, Theorem 3.1][AroraBarak09], [Sipser, Theorem 9.10][Sipser2013]. The gap is the
polynomial overhead of the native universal machine, not the textbook `f n * log (f n)`. -/
theorem DTIME_ssubset_DTIME {f g : ℕ → ℕ} (hf : TimeConstructible f) (hn : ∀ n, n ≤ f n)
    (hg : ∀ᶠ n in atTop, (n + 1) ^ 8 * (f n + 1) ^ 3 ≤ g n) :
    DTIME encBits f ⊂ DTIME encBits g := by
  refine DTIME_ssubset_DTIME_of_clock (hf.succ_mul hn) (fun c => ?_) (hg.mono fun n h => ?_)
  · filter_upwards [eventually_ge_atTop c] with n hc
    have := hn n
    have : c * f n ≤ n * f n := Nat.mul_le_mul_right _ hc
    rw [Nat.succ_mul]
    omega
  · refine le_trans ?_ h
    calc (n + 1) ^ 5 * ((n + 1) * f n + 1) ^ 3 ≤ (n + 1) ^ 5 * ((n + 1) * (f n + 1)) ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by rw [Nat.mul_succ]; omega) 3)
      _ = (n + 1) ^ 8 * (f n + 1) ^ 3 := by ring

end Cslib.Complexity
