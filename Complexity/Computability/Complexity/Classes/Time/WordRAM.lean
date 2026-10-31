/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Constructible
public import Complexity.Computability.Complexity.Classes.FunctionTime.WordRAM
public import Complexity.Computability.WordRAM.MapOp
public import Complexity.Computability.WordRAM.OfTuring
import Complexity.Computability.Complexity.Classes.Constructible.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Deterministic time on the word RAM

`Cslib.WordRAM.RAMTIME B enc T` is the class of problems decided by one fixed word-RAM program over
the basis `B` within `c * T n + c` instructions, for a constant `c`, on instances whose encoding
under `enc` has length `n`, at every word size of at least the logarithmic threshold
`logWidth k n`, for a constant `k > 0`. The conventions are those of
`Cslib.WordRAM.UniformPolynomialTime` in `Complexity.Computability.Complexity.Classes.P.WordRAM`:
the input words are the bits `(enc a).map Bool.toNat`, and the size is `|enc a|`. The program may
read the word size; the time bound does not depend on it.

The two simulations between the word RAM and multi-tape Turing machines relate `RAMTIME` to
`Cslib.Complexity.DTIME`:

* **RAM ⇒ TM.** For a time-constructible `T`, a program over `Basis.additive` in time `O(T)` is
  simulated by a machine in time `O((n + T n + 1) ^ 4 * (log n + 1) ^ 3)`
  (`Cslib.WordRAM.RAMTIME_additive_subset_DTIME`). This is the explicit overhead of
  `Cslib.WordRAM.Program.DecidesInTime.mem_DTIME`, run on the clock `(c + 1) * (T n + 1)`, with
  the constants `c` and `k` absorbed into the `DTIME` constant.
* **TM ⇒ RAM.** For a polynomially bounded `g`, a machine in time `O(g)` is simulated by a program
  over `Basis.additive` in time `O(g)` (`Cslib.WordRAM.DTIME_subset_RAMTIME_additive`), the
  simulation of `Cslib.WordRAM.OfTuring.executes_simProgram`. The polynomial bound is needed for
  logarithmic words to hold the addresses of the simulated tapes.

## Main definitions

* `Cslib.WordRAM.RAMTIME`: deterministic time on the word RAM.

## Main results

* `Cslib.WordRAM.RAMTIME_mono`, `Cslib.WordRAM.RAMTIME_subset_of_hom`: monotonicity in the time
  bound and in the basis.
* `Cslib.WordRAM.RAMTIME_additive_subset_DTIME`: word-RAM time in deterministic time.
* `Cslib.WordRAM.DTIME_subset_RAMTIME_additive`: deterministic time in word-RAM time.

## References

* [S. A. Cook and R. A. Reckhow, *Time bounded random access machines*][CookReckhow1973]
-/

@[expose] public section

namespace Cslib.WordRAM

open Turing.MultiTapeTM Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool}

/-- **Deterministic time on the word RAM.** The problems decided by one fixed program over the
basis `B` within `c * T n + c` instructions, for a constant `c`, on the bits of an instance whose
encoding under `enc` has length `n`, at every word size of at least `logWidth k n`, for a constant
`k > 0`. -/
def RAMTIME (B : Basis) (enc : α ↪ List Bool) (T : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ c, UniformDecidableInTimeLogWord B A (fun _ a => (enc a).map Bool.toNat)
    (fun a => (enc a).length) fun a _ => c * T (enc a).length + c}

/-- `RAMTIME` is monotone in the time bound. -/
theorem RAMTIME_mono {B : Basis} {T₁ T₂ : ℕ → ℕ} (h : ∀ n, T₁ n ≤ T₂ n) :
    RAMTIME B enc T₁ ⊆ RAMTIME B enc T₂ := by
  rintro A ⟨c, k, hk, hd⟩
  exact ⟨c, k, hk, hd.mono (fun a _ => Nat.add_le_add_right (Nat.mul_le_mul_left _ (h _)) _)
    fun _ _ hw => hw⟩

/-- `RAMTIME` grows with the basis. -/
theorem RAMTIME_subset_of_hom {B B' : Basis} (φ : B.Hom B') {T : ℕ → ℕ} :
    RAMTIME B enc T ⊆ RAMTIME B' enc T := by
  rintro A ⟨c, k, hk, hd⟩
  exact ⟨c, k, hk, hd.mapOp φ⟩

/-! ## Word-RAM time in deterministic time -/

/-- A time-constructible bound is computed from any encoded instance within its own time. -/
private theorem TimeConstructible.mem_FTIME {T : ℕ → ℕ} (hT : TimeConstructible T) :
    (fun a => T (enc a).length) ∈ FTIME enc encNat T := by
  obtain ⟨c, s, K, Q, hQ, tm, htm⟩ := hT
  exact ⟨c, c, s, K, Q, hQ, tm, fun a => htm (enc a)⟩

/-- **Word-RAM time in deterministic time.** For a time-constructible `T`, a problem decided by a
fixed program over `Basis.additive` in time `O(T n)` at logarithmic word sizes is in
`DTIME ((n + T n + 1) ^ 4 * (Nat.size n + 1) ^ 3)`. For `n ≤ T n` this is
`O(T(n) ^ 4 log³ n)`. -/
theorem RAMTIME_additive_subset_DTIME {T : ℕ → ℕ} (hT : TimeConstructible T) :
    RAMTIME .additive enc T ⊆
      DTIME enc fun n => (n + T n + 1) ^ 4 * (Nat.size n + 1) ^ 3 := by
  rintro A ⟨c, k, hk, r, p, hp⟩
  -- Run the simulation on the clock `(c + 1) * (T n + 1)`, which dominates `c * T n + c`.
  have hg : Turing.MultiTapeTM.ComputableInPolyTime (fun m : ℕ => (c + 1) * (m + 1)) encNat
      encNat :=
    ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const (c + 1))
      (ComputableInPolyTime.binary_add.comp
        (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const 1)))
  have hclock : TimeConstructible fun n => (c + 1) * (T n + 1) :=
    hT.comp_of_computableInPolyTime hg fun n => by nlinarith
  have hp' := hp.mono (time' := fun a _ => (c + 1) * (T (enc a).length + 1))
    (fun a _ => by nlinarith) fun _ _ hw => hw
  have hA := Program.DecidesInTime.mem_DTIME (T := fun n => (c + 1) * (T n + 1)) hk hp'
    (TimeConstructible.mem_FTIME hclock)
  refine DTIME_mono_of_le_mul_add (C := (c + 1) + (c + 2) ^ 4 * (k + 1) ^ 3) (fun n => ?_) hA
  have hz : 1 ≤ (Nat.size n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h₁ : (c + 1) * (T n + 1) ≤ (c + 1) * ((n + T n + 1) ^ 4 * (Nat.size n + 1) ^ 3) := by
    refine Nat.mul_le_mul_left _ ?_
    calc T n + 1 ≤ n + T n + 1 := by omega
      _ ≤ (n + T n + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
      _ ≤ _ := Nat.le_mul_of_pos_right _ hz
  have h₂ : (n + (c + 1) * (T n + 1) + 1) ^ 4 * (k * (Nat.size n + 1) + 1) ^ 3 ≤
      (c + 2) ^ 4 * (k + 1) ^ 3 * ((n + T n + 1) ^ 4 * (Nat.size n + 1) ^ 3) := by
    calc _ ≤ ((c + 2) * (n + T n + 1)) ^ 4 * ((k + 1) * (Nat.size n + 1)) ^ 3 := by
          gcongr
          · nlinarith
          · nlinarith
      _ = _ := by ring
  calc (c + 1) * (T n + 1) + (n + (c + 1) * (T n + 1) + 1) ^ 4 * (k * (Nat.size n + 1) + 1) ^ 3
      ≤ (c + 1) * ((n + T n + 1) ^ 4 * (Nat.size n + 1) ^ 3) +
          (c + 2) ^ 4 * (k + 1) ^ 3 * ((n + T n + 1) ^ 4 * (Nat.size n + 1) ^ 3) :=
        Nat.add_le_add h₁ h₂
    _ = ((c + 1) + (c + 2) ^ 4 * (k + 1) ^ 3) * ((n + T n + 1) ^ 4 * (Nat.size n + 1) ^ 3) := by
        ring
    _ ≤ _ := Nat.le_add_right _ _

/-! ## Deterministic time in word-RAM time -/

section OfTuring

open OfTuring

/-- **Deterministic time in word-RAM time.** For a polynomially bounded `g`, a problem in
`DTIME g` is decided by one fixed program over `Basis.additive` within `O(g n)` instructions at
every word size above a logarithmic threshold: the simulator of a machine deciding it
(`Cslib.WordRAM.OfTuring.simProgram`), run on the bits of the instance. -/
theorem DTIME_subset_RAMTIME_additive {g : ℕ → ℕ} (hg : PolynomiallyBounded g) :
    DTIME enc g ⊆ RAMTIME .additive enc g := by
  rintro A ⟨c₁, c₂, s, hA⟩
  obtain ⟨f, ⟨K, Q, hfin, tm, htm⟩, hfA⟩ := decidableInTimeAndSpace_iff.mp hA
  have := Fintype.ofFinite Q
  -- The words of the simulator stay below `D (n + 1) ^ e`.
  have hS : PolynomiallyBounded fun n => simBound K (Fintype.card Q) n (c₁ * g n + c₂) := by
    unfold simBound
    fun_prop
  obtain ⟨D, e, hD⟩ := polynomiallyBounded_iff_le.1 hS
  refine ⟨(c₁ + c₂) * (stepCost K (Fintype.card Q) + 2) + 2 * K + 13, D + e + 2, by omega,
    regs K, simProgram tm.tr tm.q₀ (Fintype.equivFin Q), fun a w hw _ => ?_⟩
  obtain ⟨hhalt, hout⟩ := (htm a).runFrom_of_le le_rfl
  have hb : simBound K (Fintype.card Q) (enc a).length (c₁ * g (enc a).length + c₂) < 2 ^ w :=
    calc _ ≤ D * ((enc a).length + 1) ^ e := hD _
      _ < 2 ^ logWidth (D + e) (enc a).length := lt_two_pow_logWidth _ _ _
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num)
        ((logWidth_mono (by omega) le_rfl).trans hw)
  have hw2 : 2 ≤ w := le_trans (by unfold logWidth; nlinarith) hw
  obtain ⟨n, hn, hex⟩ := executes_simProgram (fun _ _ _ => rfl) (Fintype.equivFin Q) hhalt hb
    (by rw [hout]; simp only [encBool_apply, List.length_singleton]; omega)
  rw [hout, encBool_apply, Cslib.BitString.lsbValue_singleton] at hex
  refine ⟨(f a).toNat, n, hex, hn.trans ?_, Bool.toNat_le _, ?_⟩
  · unfold simTime
    dsimp only
    nlinarith [Nat.zero_le (c₂ * (stepCost K (Fintype.card Q) + 2) * g (enc a).length),
      Nat.zero_le (c₁ * (stepCost K (Fintype.card Q) + 2)),
      Nat.zero_le ((2 * K + 13) * g (enc a).length)]
  · rw [hfA a]
    cases f a <;> simp

end OfTuring

end Cslib.WordRAM
