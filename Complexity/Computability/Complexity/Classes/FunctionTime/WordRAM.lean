/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Turing.Overhead
public import Complexity.Computability.Complexity.Classes.FunctionTime
public import Complexity.Computability.Complexity.Classes.Time

/-!
# Word-RAM time bounds give deterministic time bounds

A fixed `Basis.additive` program that computes `f` within `T n` instructions on the bits of an
input of length `n`, at every word size of at least the logarithmic threshold `logWidth k n`, gives
`f ∈ FTIME encIn encNat (t + (n + T + 1) ^ 4 · (k (size n + 1) + 1) ^ 3)`, provided the time bound
`T n` itself is computable from the input in time `O(t n)`. For `T n ≥ n` this is
`O(t n + T(n) ^ 4 log³ n)`. The decision version gives the same bound in `DTIME`.

The simulating machine runs at the word size `k (size n + 1) = Θ(k log n)`, and its overhead is the
explicit polynomial of `Program.ComputesInTime.computableInO_of_width_additive`. The clock
hypothesis on `T` is needed because the machine computes its own step budget. The exponent `4`
comes from the association-list memory of the simulator, whose scans are cubic in the encoded
state; it is not a property of the word-RAM model.

The input convention is that of `Complexity.Computability.WordRAM.Invariance`: the words are the
bits of `encIn a`, and the size is `|encIn a|`. Together with the converse simulations of
`Complexity.Computability.WordRAM.OfTuring`, this transfers word-RAM running times to the time
classes beyond `P`.

## Main results

* `Cslib.WordRAM.Program.ComputesInTime.computableInO_bits`: the simulation as a
  `ComputableInO` bound depending only on the input length.
* `Cslib.WordRAM.Program.ComputesInTime.mem_FTIME`: word-RAM time gives function time.
* `Cslib.WordRAM.Program.DecidesInTime.mem_DTIME`: word-RAM decision time gives `DTIME`.

## References

* [S. A. Cook and R. A. Reckhow, *Time bounded random access machines*][CookReckhow1973]
-/

@[expose] public section

namespace Cslib.WordRAM

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity

variable {α : Type} {encIn : α ↪ List Bool} {r k : ℕ}

/-- **The simulation of the bit-list convention at logarithmic word size**, with time
`O(t n + (n + T n + 1) ^ 4 · (k (size n + 1) + 1) ^ 3)` and a space bound depending only on the
input length `n`. -/
theorem Program.ComputesInTime.computableInO_bits (hk : 1 ≤ k) {p : Program .additive r}
    {T t : ℕ → ℕ} {f : α → ℕ}
    (h : p.ComputesInTime (fun _ a => (encIn a).map Bool.toNat) (fun a _ => T (encIn a).length)
      (fun a w => logWidth k (encIn a).length ≤ w) f)
    (hT : (fun a => T (encIn a).length) ∈ FTIME encIn encNat t) :
    ∃ S : ℕ → ℕ, Turing.MultiTapeTM.ComputableInO f encIn encNat
      (fun a => t (encIn a).length + ((encIn a).length + T (encIn a).length + 1) ^ 4 *
        (k * (Nat.size (encIn a).length + 1) + 1) ^ 3)
      (fun a => S (encIn a).length) := by
  obtain ⟨c₁, c₂, s, hTs⟩ := hT
  have hwidth := ((logWidthBound_degree k).of_encIn_eq (encIn' := encIn) (fun a => encIn a)
    fun _ => rfl).inO
  have hencode := (bitsToNats_degree.of_encIn_eq (encIn' := encIn) (fun a => encIn a)
    fun _ => rfl).inO
  have hO := h.computableInO_of_width_additive
    (width := fun a => k * (Nat.size (encIn a).length + 1)) hwidth
    (fun a => logWidth_le_mul_size_succ k _) (fun a => inputFits_map_toNat hk _) hencode
    (NativeCertificate.ofTimeAndSpace hTs).computes (fun _ => le_rfl)
  refine ⟨fun n => n + 2 * (n + 1) ^ 2 + (s n + (c₁ * t n + c₂)) +
    ((n + T n + 1) * (k * (Nat.size n + 1) + 1)) ^ 3, hO.mono (c₁ + c₂ + 5) (fun a => ?_)
      (fun a => ?_)⟩
  · simp only [List.length_map, NativeCertificate.ofTimeAndSpace]
    obtain ⟨X, hX⟩ : ∃ X, X = ((encIn a).length + T (encIn a).length + 1) ^ 4 *
        (k * (Nat.size (encIn a).length + 1) + 1) ^ 3 := ⟨_, rfl⟩
    rw [← hX]
    have hw1 : 1 ≤ (k * (Nat.size (encIn a).length + 1) + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    have hcube : (T (encIn a).length + 1) * (((encIn a).length + T (encIn a).length + 1) *
        (k * (Nat.size (encIn a).length + 1) + 1)) ^ 3 ≤ X := by
      rw [hX, Nat.mul_pow, ← Nat.mul_assoc]
      refine Nat.mul_le_mul_right _ ?_
      calc (T (encIn a).length + 1) * ((encIn a).length + T (encIn a).length + 1) ^ 3
          ≤ ((encIn a).length + T (encIn a).length + 1) *
              ((encIn a).length + T (encIn a).length + 1) ^ 3 :=
            Nat.mul_le_mul_right _ (by omega)
        _ = ((encIn a).length + T (encIn a).length + 1) ^ 4 := by ring
    have hsq : ((encIn a).length + 1) ^ 2 ≤ X := by
      rw [hX]
      calc ((encIn a).length + 1) ^ 2 ≤ ((encIn a).length + T (encIn a).length + 1) ^ 4 :=
            (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
        _ ≤ _ := Nat.le_mul_of_pos_right _ hw1
    have hn : (encIn a).length ≤ ((encIn a).length + 1) ^ 2 := by nlinarith
    have h0 := Nat.zero_le (c₁ * X)
    have h1 := Nat.zero_le (c₂ * t (encIn a).length)
    have h2 := Nat.zero_le (c₂ * X)
    nlinarith
  · simp only [List.length_map, NativeCertificate.ofTimeAndSpace]
    refine le_trans ?_ (Nat.le_mul_of_pos_left _ (by omega))
    omega

/-- **Word-RAM time gives function time.** A `Basis.additive` program computing `f` within
`T n` instructions on the bits of an input of length `n`, at every word size of at least
`logWidth k n`, computes a function in `FTIME encIn encNat` with bound
`t n + (n + T n + 1) ^ 4 · (k (size n + 1) + 1) ^ 3`, when `T n` is computable from the input in
time `O(t n)`. -/
theorem Program.ComputesInTime.mem_FTIME (hk : 1 ≤ k) {p : Program .additive r}
    {T t : ℕ → ℕ} {f : α → ℕ}
    (h : p.ComputesInTime (fun _ a => (encIn a).map Bool.toNat) (fun a _ => T (encIn a).length)
      (fun a w => logWidth k (encIn a).length ≤ w) f)
    (hT : (fun a => T (encIn a).length) ∈ FTIME encIn encNat t) :
    f ∈ FTIME encIn encNat
      (fun n => t n + (n + T n + 1) ^ 4 * (k * (Nat.size n + 1) + 1) ^ 3) := by
  obtain ⟨S, c, hc, -⟩ := h.computableInO_bits hk hT
  exact ⟨c, c, fun n => c * (S n + 1), hc.mono (fun a => by rw [Nat.mul_add, Nat.mul_one])
    (fun _ => le_rfl)⟩

/-- **Word-RAM decision time gives deterministic time.** A `Basis.additive` program deciding `A`
within `T n` instructions on the bits of an input of length `n`, at every word size of at least
`logWidth k n`, puts `A` in `DTIME encIn` with bound
`t n + (n + T n + 1) ^ 4 · (k (size n + 1) + 1) ^ 3`, when `T n` is computable from the input in
time `O(t n)`. -/
theorem Program.DecidesInTime.mem_DTIME (hk : 1 ≤ k) {p : Program .additive r}
    {T t : ℕ → ℕ} {A : Set α}
    (h : p.DecidesInTime (fun _ a => (encIn a).map Bool.toNat) A (fun a _ => T (encIn a).length)
      (fun a w => logWidth k (encIn a).length ≤ w))
    (hT : (fun a => T (encIn a).length) ∈ FTIME encIn encNat t) :
    A ∈ DTIME encIn (fun n => t n + (n + T n + 1) ^ 4 * (k * (Nat.size n + 1) + 1) ^ 3) := by
  classical
  obtain ⟨S, hO⟩ := h.computesInTime.computableInO_bits hk hT
  have hone : Turing.MultiTapeTM.ComputableInO (fun v : ℕ => decide (v = 1)) encNat encBool
      (fun v => (encNat v).length) (fun v => (encNat v).length) :=
    ((ComputableInDegree.of_linear ComputableInLinearTimeAndSpace.natEq).comp
      ((ComputableInDegree.of_eq (f := fun v : ℕ => v) (encIn := encNat) (encMid := encNat)
        fun _ => rfl).prod (ComputableInDegree.const 1))).mono (d' := 1) (e' := 1) |>.inO_one
  have h := setOf_mem_DTIME_of_computableInO (hone.comp_linear hO)
    (t := fun n => t n + (n + T n + 1) ^ 4 * (k * (Nat.size n + 1) + 1) ^ 3) fun _ => le_rfl
  convert h using 1
  ext a
  by_cases ha : a ∈ A <;> simp [ha]

end Cslib.WordRAM
