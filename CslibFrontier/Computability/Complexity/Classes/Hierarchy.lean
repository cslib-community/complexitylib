/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.ResourceBound
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Bit
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Run
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

/-!
# A decidable problem outside P

The clocked diagonal `Cslib.Complexity.clockedDiagonal J` reads a description of a machine framed
at the start of its input `x` (`Turing.MultiTapeTM.Universal.decodeDesc`), runs the described
machine on the whole of `x`, symbol by symbol under the fixed coding `false ↦ 0`, `true ↦ 1`, for
`J x.length` steps with the universal function, and negates the verdict: it returns `false`
exactly when the described machine has halted with output `[true]` by then. The diagonal function
`Cslib.Complexity.diagonal` is the clocked diagonal with clock `2 ^ n`; other clocks give the time
hierarchy theorem in `CslibFrontier.Computability.Complexity.Classes.Hierarchy.Time`.

The diagonal is itself computed, by one fixed machine, within time `O(2 ^ (4 * n))` and space
`O(2 ^ (2 * n))` on inputs of length `n` (`Cslib.Complexity.computableInO_diagonal`). The
bound charges decoding, converting the input to symbols through the universal input-coding API,
writing the clock `2 ^ n` in binary, the universal run and the final test. The universal run
dominates, within time polynomial in `n` times
`2 ^ (3 * n)` and space polynomial in `n` times `2 ^ n`, and one more factor `2 ^ n` absorbs the
polynomials. The exponents are deliberately loose.

No machine computing a Boolean function in polynomial time decides the diagonal problem, by the
diagonal argument of the time hierarchy theorem [Arora and Barak, Theorem 3.1][AroraBarak09]. Its
description, padded to a length where the machine halts within the exponential clock, is an input
on which the diagonal returns the negation of the machine's answer
(`Cslib.Complexity.diagonal_notMem_P`). The argument uses only that the machine halts with its
answer within a polynomial time bound, so it applies to plain, not necessarily tidy, machines as
well (`Cslib.Complexity.not_computableInTimeAndSpace_diagonal`). Together, the problem decided by
an explicit exponential-time computation is not in `P`. No time-bounded classes are defined here.

## Main definitions

* `Cslib.Complexity.clockedDiagonal`: the diagonal with a clock.
* `Cslib.Complexity.diagonal`: the diagonal function, with clock `2 ^ n`.

## Main results

* `Cslib.Complexity.computableInO_diagonal`: the diagonal in exponential time and space.
* `Cslib.Complexity.diagonal_notMem_P`: the diagonal problem is not in `P`.
* `Cslib.Complexity.not_computableInTimeAndSpace_diagonal`: no plain machine computes the
  diagonal within a polynomial time bound.
* `Cslib.Complexity.clockedDiagonal_desc`, `Cslib.Complexity.diagonal_desc`,
  `Cslib.Complexity.not_forall_halted_diagonal`: the reusable diagonal core: the negated answer on
  a padded description, and the diagonal argument itself.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]

The padded diagonal argument follows the original Complexitylib's `Classes/Hierarchy` and
`UTM/Diagonal` (Samuel Schlesinger), here on the native universal interpreter of Christian
Reitwiessner.
-/

@[expose] public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

namespace Diagonal

/-- The output test of the diagonal on a result of the universal function: `false` exactly when
the simulated machine has halted with output `[true]`, under the coding
`Turing.MultiTapeTM.Universal.eBit`. -/
def verdict (r : List ℕ × Bool) : Bool := !(r.2 && decide (r.1 = [eBit true]))

end Diagonal

/-- **The diagonal with clock `J`.** Run the machine described at the start of `x` on `x`, under the
coding `Turing.MultiTapeTM.Universal.eBit` of bits by `0` and `1`, for `J x.length` steps, and
return `false` exactly when it has halted with output `[true]`. -/
def clockedDiagonal (J : ℕ → ℕ) (x : List Bool) : Bool :=
  Diagonal.verdict (universal (decodeDesc (unframe x), x.map eBit, J x.length))

/-- **The diagonal function**, the clocked diagonal with clock `2 ^ n`: run the machine described
at the start of `x` on `x` for `2 ^ x.length` steps, and return `false` exactly when it has halted
with output `[true]`. -/
def diagonal : List Bool → Bool := clockedDiagonal (2 ^ ·)

/-- The diagonal is the clocked diagonal with clock `2 ^ n`. -/
theorem clockedDiagonal_two_pow : clockedDiagonal (2 ^ ·) = diagonal := rfl

/-- On its padded description, the clocked diagonal negates the answer of a machine that halts
within the clock. -/
theorem clockedDiagonal_desc {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) (pad : List Bool) (J : ℕ → ℕ) {b : Bool}
    (hhalt : (tm.runFrom (tm.initCfg (frame (eDesc (desc eS eBit tm)) ++ pad))
      (J (frame (eDesc (desc eS eBit tm)) ++ pad).length)).Halted)
    (hout : (tm.runFrom (tm.initCfg (frame (eDesc (desc eS eBit tm)) ++ pad))
      (J (frame (eDesc (desc eS eBit tm)) ++ pad).length)).output = [b]) :
    clockedDiagonal J (frame (eDesc (desc eS eBit tm)) ++ pad) = !b := by
  rw [clockedDiagonal, decodeDesc_unframe_frame_append, universal_desc, hout]
  simp only [List.map_cons, List.map_nil, Cfg.Halted] at hhalt ⊢
  rw [hhalt]
  cases b <;> simp [Diagonal.verdict, eBit]

/-- On its padded description, the diagonal negates the answer of a machine that halts within the
exponential clock. -/
theorem diagonal_desc {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) (pad : List Bool) {b : Bool}
    (hhalt : (tm.runFrom (tm.initCfg (frame (eDesc (desc eS eBit tm)) ++ pad))
      (2 ^ (frame (eDesc (desc eS eBit tm)) ++ pad).length)).Halted)
    (hout : (tm.runFrom (tm.initCfg (frame (eDesc (desc eS eBit tm)) ++ pad))
      (2 ^ (frame (eDesc (desc eS eBit tm)) ++ pad).length)).output = [b]) :
    diagonal (frame (eDesc (desc eS eBit tm)) ++ pad) = !b :=
  clockedDiagonal_desc eS tm pad (2 ^ ·) hhalt hout

/-- **The diagonal argument.** No finite binary machine halts within a polynomially bounded time
`t x` with output `[diagonal x]` on every input `x`: on its own description, padded beyond the
polynomial, it would answer the negation of its answer. -/
theorem not_forall_halted_diagonal {k : ℕ} {State : Type} [Finite State]
    (tm : MultiTapeTM k Bool State) {t : List Bool → ℕ} (ht : PolyBounded List.length t)
    (h : ∀ x, (tm.runFrom (tm.initCfg x) (t x)).Halted ∧
      (tm.runFrom (tm.initCfg x) (t x)).output = [diagonal x]) : False := by
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  -- a padding beyond which the machine halts within the exponential clock
  obtain ⟨c, d, hle⟩ := ht.exists_le
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (PolynomiallyBounded.eventually_lt_two_pow (f := fun n => c * (n + 1) ^ d) (by fun_prop))
  set x := frame (eDesc (desc eS eBit tm)) ++ List.replicate N false with hx
  have hlen : N ≤ x.length := by simp [x]
  have htime : t x ≤ 2 ^ x.length := (hle x).trans (hN _ hlen).le
  obtain ⟨hhalt, hout⟩ := h x
  have heq := MultiTapeTM.runFrom_eq_of_halt tm _ htime hhalt
  have hdiag := diagonal_desc eS tm _ ((congrArg Cfg.Halted heq).mpr hhalt)
    ((congrArg Cfg.output heq).trans hout)
  revert hdiag
  cases diagonal x <;> decide

/-- **The diagonal problem is not in `P`**, by the diagonal argument of the time hierarchy
theorem [Arora and Barak, Theorem 3.1][AroraBarak09]. -/
theorem diagonal_notMem_P : {x | diagonal x = true} ∉ P encBits := by
  rintro ⟨f, ⟨t, s, ht, -, k, State, hfinite, tm, htm⟩, hf⟩
  have hfx (x : List Bool) : f x = diagonal x := by
    cases h : diagonal x
    · cases hfx : f x
      · rfl
      · exact absurd ((hf x).mpr hfx) (by simp [h])
    · exact (hf x).mp h
  exact not_forall_halted_diagonal tm (.of_polynomiallyBounded _ ht) fun x => by
    obtain ⟨hhalt, hout⟩ := (htm x).runFrom_of_le le_rfl
    exact ⟨hhalt, hout.trans (by rw [encBool_apply, hfx])⟩

/-- **No plain machine computes the diagonal in polynomial time**: the separation does not depend
on tidy normal forms. -/
theorem not_computableInTimeAndSpace_diagonal {t s : List Bool → ℕ}
    (ht : PolyBounded List.length t) : ¬ComputableInTimeAndSpace diagonal encBits encBool t s := by
  rintro ⟨k, State, hfinite, tm, htm⟩
  exact not_forall_halted_diagonal tm ht fun x => (htm x).runFrom_of_le le_rfl

namespace Diagonal

/-! ### The resources of the diagonal -/

/-- The test is within time quadratic and space linear in the encoded result. -/
theorem computableInO_verdict :
    ComputableInO verdict eOut encBool (fun r => ((eOut r).length + 1) ^ 2)
      fun r => (eOut r).length := by
  have heq := (ComputableInO.eq (encList encUnary)).comp
    ((ComputableInO.fst (encList encUnary) encBool).prod
      (ComputableInO.const (encMid := encList encUnary) [eBit true]))
  have hfin := (ComputableInDegree.of_finite (encIn := encPair encBool encBool)
    (encMid := encBool) fun q : Bool × Bool => !(q.1 && q.2)).inO_one
  refine (hfin.comp ((ComputableInO.snd (encList encUnary) encBool).prod heq)).mono 64
    (fun r => ?_) fun r => ?_
  all_goals
    have h₁ := length_le_encPair_left (encList encUnary) encBool r
    have h₂ : (encList encUnary [eBit true]).length = 3 := rfl
    simp only [Function.comp_apply, length_encPair, encBool_apply, List.length_singleton,
      h₂] at h₁ ⊢
  · nlinarith
  · omega

/-- The numeric core of the resources of the diagonal: for an input of length `n`, a decoded
description of encoded length `D`, encoded symbols of length `N`, a clock `J ≥ 1`, an encoded
universal input of length `I` and a result of encoded length `E`, everything is within
`K * M ^ 5 * J ^ 3` steps and `K * M ^ 5 * J` cells. -/
private theorem bounds_aux {n A D N J L I E cD cO M K : ℕ} (hJ : 1 ≤ J)
    (hD : D ≤ cD * (A + 1)) (hN : N ≤ 3 * n) (hL : L = n + 1) (hI : I = 2 * D + 1 + (2 * N + 1 + L))
    (hM : M = cD * (A + 1) + A + 4 * n + 2) (hK : K = 65 + 100 * (cO + 1) ^ 2)
    (hE : E ≤ cO * (A + (n + n) + (I + 1) ^ 2 * (J + 1) + 1)) :
    A + (n + n) + (I + 1) ^ 4 * (J + 1) ^ 2 + (E + 1) ^ 2 ≤ K * (M ^ 5 * J ^ 3) ∧
      A + (n + n) + (I + 1) ^ 2 * (J + 1) + E ≤ K * (M ^ 5 * J) := by
  have hM1 : 1 ≤ M := by omega
  have hIM : I + 1 ≤ 2 * M := by omega
  have hM2 : M ≤ M ^ 2 := Nat.le_self_pow two_ne_zero _
  have hMM2 : M ≤ M ^ 2 * J := hM2.trans (Nat.le_mul_of_pos_right _ hJ)
  have hM25 : M ^ 2 ≤ M ^ 5 := Nat.pow_le_pow_right hM1 (by omega)
  -- the space of the universal run, and the encoded result
  have hS : A + (n + n) + (I + 1) ^ 2 * (J + 1) ≤ 9 * (M ^ 2 * J) := by
    have h : (I + 1) ^ 2 * (J + 1) ≤ 8 * (M ^ 2 * J) :=
      calc _ ≤ (2 * M) ^ 2 * (2 * J) := Nat.mul_le_mul (Nat.pow_le_pow_left hIM 2) (by omega)
        _ = 8 * (M ^ 2 * J) := by ring
    omega
  have hE' : E + 1 ≤ 10 * (cO + 1) * (M ^ 2 * J) := by
    have h₁ : E ≤ cO * (9 * (M ^ 2 * J) + 1) := hE.trans (Nat.mul_le_mul_left _ (by omega))
    have h₂ : 1 ≤ M ^ 2 * J := le_trans hM1 hMM2
    nlinarith
  constructor
  · have hO2 : (E + 1) ^ 2 ≤ 100 * (cO + 1) ^ 2 * (M ^ 5 * J ^ 3) := by
      calc (E + 1) ^ 2 ≤ (10 * (cO + 1) * (M ^ 2 * J)) ^ 2 := Nat.pow_le_pow_left hE' 2
        _ = 100 * (cO + 1) ^ 2 * (M ^ 4 * J ^ 2) := by ring
        _ ≤ 100 * (cO + 1) ^ 2 * (M ^ 5 * J ^ 3) := by gcongr <;> omega
    have hU : (I + 1) ^ 4 * (J + 1) ^ 2 ≤ 64 * (M ^ 5 * J ^ 3) :=
      calc _ ≤ (2 * M) ^ 4 * (2 * J) ^ 2 :=
            Nat.mul_le_mul (Nat.pow_le_pow_left hIM 4) (Nat.pow_le_pow_left (by omega) 2)
        _ = 64 * (M ^ 4 * J ^ 2) := by ring
        _ ≤ 64 * (M ^ 5 * J ^ 3) := by gcongr <;> omega
    have hA : A + (n + n) ≤ M ^ 5 * J ^ 3 := by
      have h₁ : A + (n + n) ≤ M := by omega
      have h₂ : M ≤ M ^ 5 * J ^ 3 :=
        (hM2.trans hM25).trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos hJ))
      omega
    rw [hK]
    generalize M ^ 5 * J ^ 3 = X at hA hU hO2 ⊢
    linarith
  · have hY : 10 * (cO + 1) * (M ^ 2 * J) ≤ 100 * (cO + 1) ^ 2 * (M ^ 5 * J) :=
      calc _ ≤ 10 * (10 * (cO + 1) ^ 2) * (M ^ 5 * J) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ (by nlinarith))
              (Nat.mul_le_mul_right _ hM25)
        _ = 100 * (cO + 1) ^ 2 * (M ^ 5 * J) := by ring
    have hM2J : M ^ 2 * J ≤ M ^ 5 * J := Nat.mul_le_mul_right _ hM25
    rw [hK]
    generalize M ^ 2 * J = Z at hS hE' hM2J hY ⊢
    generalize M ^ 5 * J = W at hM2J hY ⊢
    linarith

end Diagonal

open Diagonal in
/-- **The diagonal is decidable in exponential time**, within time `O(2 ^ (4 * n))` and space
`O(2 ^ (2 * n))` on inputs of length `n`, charging decoding, the symbols, the clock, the universal
run and the test. -/
theorem computableInO_diagonal :
    ComputableInO diagonal encBits encBool (fun x => 2 ^ (4 * x.length))
      fun x => 2 ^ (2 * x.length) := by
  obtain ⟨dd, ed, hdec⟩ := exists_computableInDegree_decodeDesc
  have hu := Internal.DecoderWords.unframe_degree
  have hdesc := (hdec.comp hu).inO
  have hsym := Universal.computableInO_map_eBit
  have hclock := (ComputableInDegree.two_pow_length encBits).inO_one
  have hpre := hdesc.prod (hsym.prod hclock)
  have hU := computableInO_universal.comp hpre
  have h := computableInO_verdict.comp hU
  -- the sizes of the decoded description and of the result
  obtain ⟨cD, hcD⟩ := hdesc.length_le
  obtain ⟨cO, hcO⟩ := hU.length_le
  -- one power of two absorbs every polynomial factor
  obtain ⟨C, hC⟩ := PolynomiallyBounded.exists_le_mul_two_pow
    (p := fun n => (cD * ((n + 1) ^ max 1 (1 * dd) + 1) + (n + 1) ^ max 1 (1 * dd) + 4 * n + 2) ^
      5)
    (by fun_prop)
  set K := 65 + 100 * (cO + 1) ^ 2 with hK
  have hbounds (x : List Bool) := by
    have hL : (encNat (2 ^ x.length)).length = x.length + 1 := by
      rw [encNat_two_pow, List.length_append, List.length_replicate, List.length_singleton]
    have hN : (encList encUnary (x.map eBit)).length ≤ 3 * x.length :=
      (length_encList_le encUnary _ (b := 1) fun s hs => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.mp hs
        cases b
        · exact Nat.zero_le _
        · exact le_rfl).trans (by rw [List.length_map]; omega)
    have hE := hcO x
    simp only [Function.comp_apply, encBits, Function.Embedding.refl_apply] at hE
    exact bounds_aux
      (I := (eIn (decodeDesc (unframe x), x.map eBit, 2 ^ x.length)).length) Nat.one_le_two_pow
      (hcD x) hN hL (by rw [length_encPair, length_encPair]; rfl) rfl hK hE
  refine h.mono (K * C) (fun x => ?_) fun x => ?_
  · obtain ⟨h₁, -⟩ := hbounds x
    simp only [Function.comp_apply, encBits, Function.Embedding.refl_apply] at h₁ ⊢
    have hJ4 : 2 ^ (4 * x.length) = 2 ^ x.length * (2 ^ x.length) ^ 3 := by
      ring
    have := hC x.length
    calc _ ≤ K * (_ ^ 5 * (2 ^ x.length) ^ 3) := h₁
      _ ≤ K * (C * 2 ^ x.length * (2 ^ x.length) ^ 3) := by gcongr
      _ ≤ K * C * (2 ^ (4 * x.length) + 1) := by rw [hJ4]; nlinarith
  · obtain ⟨-, h₂⟩ := hbounds x
    simp only [Function.comp_apply, encBits, Function.Embedding.refl_apply] at h₂ ⊢
    have hJ2 : 2 ^ (2 * x.length) = 2 ^ x.length * 2 ^ x.length := by rw [two_mul, pow_add]
    have := hC x.length
    calc _ ≤ K * (_ ^ 5 * 2 ^ x.length) := h₂
      _ ≤ K * (C * 2 ^ x.length * 2 ^ x.length) := by gcongr
      _ ≤ K * C * (2 ^ (2 * x.length) + 1) := by rw [hJ2]; nlinarith

end Cslib.Complexity
