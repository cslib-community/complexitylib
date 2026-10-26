/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.ACC0.Basic
public import Complexity.Computability.Circuit.Boolean.ACC0.Simulation
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Complexity.Classes.PH.Kannan
import Complexity.Computability.Circuit.Boolean.Smolensky.Majority
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# ACC⁰ and lower bounds against modular-counting circuits

**ACC⁰** (`Cslib.Circuits.Boolean.ACC0`) is the union of the modular constant-depth circuit classes
`AC0Mod q` over all fixed moduli `q ≥ 2` [Barrington1989], [Vollmer, Chapter 4][Vollmer1999],
[Arora and Barak, Section 14.2][AroraBarak09]. The development is split into two submodules, both
re-exported here:

* `Complexity.Computability.Circuit.Boolean.ACC0.Basic`: the definition of `ACC0`, the degenerate
  moduli `q = 0, 1`, divisibility monotonicity `AC0Mod q ⊆ AC0Mod q'` for `q ∣ q'`, Boolean closure,
  `ACC0 ⊆ TC0`, and the strict inclusions `AC0 ⊂ ACC0` and `AC0Mod p ⊂ ACC0` (`p` an odd prime)
  obtained from Håstad's and Razborov–Smolensky's lower bounds for parity.
* `Complexity.Computability.Circuit.Boolean.ACC0.Simulation`: logarithmic-depth simulation of
  `MOD_q` gates by unbounded fan-in circuits, giving `ACMod q i ⊆ AC (i + 1)` and
  `ACC0 ⊆ AC 1 ⊆ NC 2 ⊆ PPoly`, and the polynomial-size simulation of unbounded-depth `MOD_q`
  circuits (`SIZEMod q`) by fan-in-two De Morgan circuits (`SIZEMod_subset_SIZE`).

This module adds the resulting separations:

* **`P ⊄ AC⁰` and `P ⊄ AC⁰[p]`**: parity lies in `P` (`parity_mem_P`), so it witnesses languages in
  `P` outside `AC0` (`exists_mem_P_notMem_AC0`) [Hastad1986] and outside `AC0Mod p` for every odd
  prime `p` (`exists_mem_P_notMem_AC0Mod`) [Razborov1987], [Smolensky1987].
* **Fixed-exponent `MOD_q` circuit lower bounds in `Σ₂`**: for every modulus `q` (prime or
  composite) and every exponent `k`, combining `SIZEMod_subset_SIZE` with Kannan's theorem gives a
  language in `Σ₂` with no `MOD_q` circuits of size `O(n ^ k)` of any depth
  (`Kannan.language_notMem_SIZEMod`, `exists_mem_SigmaP_two_notMem_SIZEMod`) [Kannan1982].

## Main results

* `Cslib.Circuits.Boolean.parity_mem_P`: parity is in `P`.
* `Cslib.Circuits.Boolean.exists_mem_P_notMem_AC0`,
  `Cslib.Circuits.Boolean.exists_mem_P_notMem_AC0Mod`: `P ⊄ AC⁰` and `P ⊄ AC⁰[p]` for odd primes
  `p`.
* `Cslib.Circuits.Boolean.Kannan.language_notMem_SIZEMod`,
  `Cslib.Circuits.Boolean.exists_mem_SigmaP_two_notMem_SIZEMod`: fixed-exponent `MOD_q` circuit
  lower bounds in `Σ₂` for every modulus `q`.

## References

* [D. A. M. Barrington, *Bounded-width polynomial-size branching programs recognize exactly those
  languages in NC¹*][Barrington1989]
* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [J. Håstad, *Almost optimal lower bounds for small depth circuits*][Hastad1986]
* [A. A. Razborov, *Lower bounds on the size of bounded depth circuits over a complete basis with
  logical addition*][Razborov1987]
* [R. Smolensky, *Algebraic methods in the theory of lower bounds for Boolean circuit
  complexity*][Smolensky1987]
* [R. Kannan, *Circuit-size lower bounds and non-reducibility to sparse sets*][Kannan1982]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Set Finset BitString Unbounded Cslib.Complexity Turing.MultiTapeTM

/-- **Parity is in `P`** (`Language.ofSlices parity ∈ P encBits`). -/
theorem parity_mem_P : (Language.ofSlices parity : Set (List Bool)) ∈ P encBits := by
  refine ⟨fun w => w.foldl bne false, ?_, fun w => ?_⟩
  · exact ComputableInPolyTime.bitsFoldlWithInput bne
      ComputableInPolyTime.id' (ComputableInPolyTime.const false)
  · change w ∈ (Language.ofSlices parity : Language Bool) ↔ w.foldl bne false = true
    rw [Language.mem_ofSlices, foldl_bne_eq_parity]

/-- **Unconditional separation `P ⊄ AC⁰`**: parity is in `P` and not in `AC⁰` [Hastad1986]. -/
theorem exists_mem_P_notMem_AC0 :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ P encBits ∧ L ∉ AC0 :=
  ⟨Language.ofSlices parity, parity_mem_P, parity_notMem_AC0⟩

/-- **Unconditional separation `P ⊄ AC⁰[p]`** for every odd prime `p`: parity is in `P` and not in
`AC⁰[p]` [Razborov1987], [Smolensky1987]. -/
theorem exists_mem_P_notMem_AC0Mod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ P encBits ∧ L ∉ AC0Mod p :=
  ⟨Language.ofSlices parity, parity_mem_P, Smolensky.parity_notMem_AC0Mod hp2⟩

/-- **Kannan's language escapes `SIZEMod q`**: for every `q, k, c : ℕ`,
`Kannan.language (8 * (k + 1))` has no circuits over the `AC⁰[q]` basis of size
`c * (n + 1) ^ k` [Kannan1982]. -/
theorem Kannan.language_notMem_SIZEMod (q k c : ℕ) :
    Kannan.language (8 * (k + 1)) ∉ SIZEMod q fun n => c * (n + 1) ^ k :=
  fun hc => Kannan.language_notMem_SIZE (8 * (k + 1))
    ((2100 * (max q 1) ^ 3) ^ 2 * (c + 1) ^ 8) (SIZEMod_subset_SIZE q c k hc)

/-- **Unconditional fixed-exponent `MOD_q` circuit lower bound in `Σ₂`** (for every modulus `q`,
prime or composite): for every `q, k : ℕ`, some language in `Σ₂` has no circuits over the `AC⁰[q]`
basis of size `O(n ^ k)` (even of unbounded depth), by combining `SIZEMod_subset_SIZE` with
Kannan's theorem [Kannan1982]. -/
theorem exists_mem_SigmaP_two_notMem_SIZEMod (q k : ℕ) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ SigmaP 2 encBits ∧
      ∀ c, L ∉ SIZEMod q fun n => c * (n + 1) ^ k := by
  obtain ⟨L, hL₂, hLnot⟩ := exists_mem_SigmaP_two_notMem_SIZE (8 * (k + 1))
  refine ⟨L, hL₂, fun c hc => ?_⟩
  exact hLnot ((2100 * (max q 1) ^ 3) ^ 2 * (c + 1) ^ 8) (SIZEMod_subset_SIZE q c k hc)

end Cslib.Circuits.Boolean
