/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Turing
public import Complexity.Computability.WordRAM.OfTuring

/-!
# Polynomial time on the word RAM and on multi-tape Turing machines

A function with binary output is computable in polynomial time by a multi-tape Turing machine
(`Turing.MultiTapeTM.ComputableInPolyTime`) exactly when one fixed word-RAM program computes it
on the bits of its input within polynomially many instructions, at every word size above a
polynomial threshold. The two directions are the simulation of Turing machines by the word RAM
(`Cslib.WordRAM.OfTuring`) and the simulation of the word RAM by Turing machines
(`Cslib.WordRAM.Program.ComputesInTime.turingComputableInPolyTime_of_width`) [Cook and
Reckhow][CookReckhow1973].

## Conventions

* **Input.** The instance `a` is given to the program as its bits, the word list
  `(encIn a).map Bool.toNat`, placed as in `State.init`.
* **Output.** The program returns `f a` as one word; the machine writes it in binary (`encNat`).
* **Word size.** Since one word holds the output, whose bit length is bounded only by the running
  time, the threshold `W |encIn a|` is polynomial rather than logarithmic. When the values of `f`
  are polynomial in `|encIn a|`, so that the output has logarithmically many bits, a logarithmic
  threshold suffices and the word-RAM side is `Cslib.WordRAM.UniformComputableInPolyTime`; that
  value bound is also necessary for it. For decision problems, see
  `Cslib.WordRAM.mem_P_iff_uniformPolynomialTime`.
* **Basis.** Any basis containing `Basis.additive` whose checked operations are polynomial-time,
  such as `Basis.additive`, `Basis.arithmetic` and `Basis.standard`.

## Main results

* `Cslib.WordRAM.computableInPolyTime_map_toNat`: the bits of an instance, as words, are
  computable in polynomial time.
* `Cslib.WordRAM.turingComputableInPolyTime_iff_exists_computesInTime`: Turing-machine polynomial
  time is uniform polynomial word-RAM time at polynomial word sizes.
* `Cslib.WordRAM.turingComputableInPolyTime_iff_uniformComputableInPolyTime`: for functions with
  polynomially bounded values, Turing-machine polynomial time is
  `Cslib.WordRAM.UniformComputableInPolyTime` on the bits, at logarithmic word sizes.
* `Cslib.WordRAM.UniformComputableInPolyTime.polyBounded`: such word-RAM functions have
  polynomially bounded values.

## References

* [S. A. Cook and R. A. Reckhow, *Time bounded random access machines*][CookReckhow1973]
-/

@[expose] public section

namespace Cslib.WordRAM

open Turing.MultiTapeTM

variable {B : Basis} {α : Type} {encIn : α ↪ List Bool}

/-- The bits of an instance, as words framed as a list of binary naturals, are computable in
polynomial time from the instance. -/
theorem computableInPolyTime_map_toNat (encIn : α ↪ List Bool) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun a => (encIn a).map Bool.toNat) encIn
      (encList encNat) :=
  (Turing.MultiTapeTM.ComputableInPolyTime.map
    (Turing.MultiTapeTM.ComputableInPolyTime.of_finite Bool.toNat)).comp
    ((bits_encList_polyTime encBool).1.comp
      (Turing.MultiTapeTM.ComputableInPolyTime.of_eq fun _ => rfl))

/-- **Turing-machine polynomial time is word-RAM polynomial time.** Over any basis `B` containing
`Basis.additive` whose checked operations are polynomial-time, a function `f` with binary output is
computable in polynomial time by a multi-tape Turing machine exactly when one fixed word-RAM program
over `B` computes it on the bits `(encIn a).map Bool.toNat` of its input, within `T |encIn a|`
instructions at every word size of at least `W |encIn a|`, for polynomially bounded `T` and `W`. -/
theorem turingComputableInPolyTime_iff_exists_computesInTime (φ : Basis.additive.Hom B)
    (hop : ∀ op : B.Op, Turing.MultiTapeTM.ComputableInPolyTime (B.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat)) {f : α → ℕ} :
    Turing.MultiTapeTM.ComputableInPolyTime f encIn encNat ↔
      ∃ (r : ℕ) (p : Program B r) (T W : ℕ → ℕ), PolynomiallyBounded T ∧
        PolynomiallyBounded W ∧ p.ComputesInTime (fun _ a => (encIn a).map Bool.toNat)
          (fun a _ => T (encIn a).length) (fun a w => W (encIn a).length ≤ w) f := by
  constructor
  · intro h
    obtain ⟨r, p, T, W, hT, hW, hp⟩ := h.exists_wordRAM_nat
    exact ⟨r, p.mapOp φ, T, W, hT, hW, hp.mapOp φ⟩
  · rintro ⟨r, p, T, W, hT, hW, hp⟩
    -- Simulate at a computable width above `W |encIn a|` and the input length.
    obtain ⟨width, hwidth, hge⟩ := exists_unary_majorant (encIn := encIn)
      (u := fun a => W (encIn a).length + (encIn a).length + 1)
      (((PolyBounded.of_polynomiallyBounded _ hW).add PolyBounded.self).add (.const 1))
    refine hp.turingComputableInPolyTime_of_width hop hwidth
      (fun a => by have := hge a; omega) (fun a => ⟨?_, fun v hv => ?_⟩)
      (computableInPolyTime_map_toNat encIn)
      ((PolyBounded.of_polynomiallyBounded _ hT).comp PolyBounded.self)
    · have := hge a
      rw [List.length_map]
      exact Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
    · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hv
      have := hge a
      exact (Bool.toNat_le b).trans_lt
        (Nat.one_lt_two_pow_iff.2 (by omega))

/-! ## Logarithmic word sizes -/

section LogWidth

open OfTuring

/-- The bits of an instance fit every word size above a positive logarithmic threshold. -/
private theorem inputFits_map_toNat {k : ℕ} (hk : 0 < k) {w : ℕ} (a : α)
    (hw : logWidth k (encIn a).length ≤ w) : InputFits w ((encIn a).map Bool.toNat) := by
  have hlog : Nat.log 2 (encIn a).length + 1 ≤ w := (Nat.le_mul_of_pos_left _ hk).trans hw
  refine ⟨?_, fun v hv => ?_⟩
  · rw [List.length_map]
    exact (Nat.lt_pow_succ_log_self (by norm_num) _).trans_le
      (Nat.pow_le_pow_right (by norm_num) hlog)
  · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hv
    exact (Bool.toNat_le b).trans_lt (Nat.one_lt_two_pow_iff.2 (by omega))

/-- **A uniform polynomial-time word-RAM function has polynomially bounded values.** At the
smallest admitted word size, `logWidth k |encIn a|`, the output `f a` is one word, so
`f a < 2 ^ logWidth k |encIn a| ≤ 2 ^ k (|encIn a| + 1) ^ k`. -/
theorem UniformComputableInPolyTime.polyBounded {f : α → ℕ}
    (h : UniformComputableInPolyTime B f (fun _ a => (encIn a).map Bool.toNat)
      (fun a => (encIn a).length)) :
    PolyBounded (fun a => (encIn a).length) f := by
  obtain ⟨T, -, k, hk, r, p, hp⟩ := h
  refine ⟨fun n => 2 ^ k * (n + 1) ^ k, .of_forall_le (2 ^ k) k fun _ => le_rfl, fun a => ?_⟩
  have hi := inputFits_map_toNat (encIn := encIn) hk a le_rfl
  obtain ⟨n, hex, -⟩ := hp a _ le_rfl hi
  exact (hex.fits_init hi).le.trans (two_pow_logWidth_le k _)

/-- **Turing-machine polynomial time is uniform polynomial word-RAM time at logarithmic word
sizes, for functions with polynomially bounded values.** Over any basis `B` containing
`Basis.additive` whose checked operations are polynomial-time, let `f a` be polynomially bounded
in `|encIn a|`. Then `f` is computable in polynomial time by a multi-tape Turing machine exactly
when one fixed word-RAM program over `B` computes it on the bits `(encIn a).map Bool.toNat`,
within polynomially many instructions in `|encIn a|`, at every word size above a logarithmic
threshold (`Cslib.WordRAM.UniformComputableInPolyTime`). The value bound is necessary for the
word-RAM side (`Cslib.WordRAM.UniformComputableInPolyTime.polyBounded`); without it, see
`Cslib.WordRAM.turingComputableInPolyTime_iff_exists_computesInTime`. -/
theorem turingComputableInPolyTime_iff_uniformComputableInPolyTime (φ : Basis.additive.Hom B)
    (hop : ∀ op : B.Op, Turing.MultiTapeTM.ComputableInPolyTime (B.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat)) {f : α → ℕ}
    (hf : PolyBounded (fun a => (encIn a).length) f) :
    Turing.MultiTapeTM.ComputableInPolyTime f encIn encNat ↔
      UniformComputableInPolyTime B f (fun _ a => (encIn a).map Bool.toNat)
        (fun a => (encIn a).length) := by
  refine ⟨fun h => ?_, fun h =>
    h.turingComputableInPolyTime hop PolyBounded.self (computableInPolyTime_map_toNat encIn)⟩
  obtain ⟨t, s, ht, -, K, Q, hfin, tm, htm⟩ := h
  have := Fintype.ofFinite Q
  -- The simulator's words stay below `D (n + 1) ^ e`, and the values below `D' (n + 1) ^ e'`.
  have hS : PolynomiallyBounded fun n => simBound K (Fintype.card Q) n (t n) := by
    unfold simBound
    fun_prop
  obtain ⟨D, e, hD⟩ := polynomiallyBounded_iff_le.1 hS
  obtain ⟨bound, hbound, hfb⟩ := hf
  obtain ⟨D', e', hD'⟩ := polynomiallyBounded_iff_le.1 hbound
  refine ⟨fun n => simTime K (Fintype.card Q) (t n), ?_, D + e + D' + e' + 1, by omega, regs K,
    _, Program.ComputesInTime.mapOp (p := simProgram tm.tr tm.q₀ (Fintype.equivFin Q)) φ
      fun a w hw _ => ?_⟩
  · unfold simTime
    exact (PolynomiallyBounded.const _).add (ht.mul (.const _))
  · obtain ⟨hhalt, hout⟩ := (htm a).runFrom_of_le le_rfl
    have hb : simBound K (Fintype.card Q) (encIn a).length (t (encIn a).length) < 2 ^ w :=
      calc _ ≤ D * ((encIn a).length + 1) ^ e := hD _
        _ < 2 ^ logWidth (D + e) (encIn a).length := lt_two_pow_logWidth _ _ _
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num)
          ((logWidth_mono (by omega) le_rfl).trans hw)
    -- The output has at most `logWidth (D' + e') |encIn a|` bits, fewer than `w`.
    have hsize : (f a).size ≤ logWidth (D' + e') (encIn a).length :=
      Nat.size_le.2 (((hfb a).trans (hD' _)).trans_lt (lt_two_pow_logWidth _ _ _))
    have hlt : logWidth (D' + e') (encIn a).length < w :=
      lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (by omega) (by omega)) hw
    obtain ⟨n, hn, hex⟩ := executes_simProgram (fun _ _ _ => rfl) (Fintype.equivFin Q) hhalt hb
      (by rw [hout, encNat_apply, Nat.size_eq_bits_len]; omega)
    rw [hout, encNat_apply, Cslib.BitString.lsbValue_bits] at hex
    exact ⟨n, hex, hn⟩

end LogWidth

end Cslib.WordRAM
