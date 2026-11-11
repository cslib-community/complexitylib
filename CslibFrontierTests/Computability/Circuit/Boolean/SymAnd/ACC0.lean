/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Boolean.SymAnd.ACC0
public import CslibFrontier.Computability.Circuit.Boolean.SymAnd.Restrict
public import CslibFrontier.Computability.Circuit.Pi
public import CslibFrontier.Foundations.BooleanAnalysis.LowDegree.Choose
public import CslibFrontier.Foundations.BooleanAnalysis.LowDegree.OrTest
public import CslibFrontier.Foundations.Data.Nat.Choose.PrimePowerDvd

/-!
# Tests for ACC⁰ → `SYM ∘ AND`

Concrete instances of the ingredients of `CslibFrontier.Computability.Circuit.Boolean.SymAnd.ACC0`:

* the prime-power digit tests of `Nat.pow_dvd_iff_forall_dvd_choose` and
  `Nat.mod_ne_zero_iff_exists_not_dvd_choose`, on a residue with a witness and one without;
* the binomial count of `BitString.sum_powersetCard_monomial`;
* the seeded OR test over `𝔽₂` with a seed that is bad for its argument set;
* the restriction `SymAnd.restrict`, which drops the AND gates reading a fixed slot;
* non-vacuity of `Circuit.exists_symAnd_eval_eq`: a one-gate `MOD_3` circuit and a one-gate
  `MOD_6` circuit (a composite modulus) are `SYM ∘ AND` circuits within the stated fan-in bounds
  that take both values;
* the explicit circuit `Circuit.toSymAnd` of the one-gate `MOD_6` circuit, evaluated on inputs;
* the language corollaries for `MOD_6`, for `ACC0`, and for `AC0Mod 0` (where `MOD_0` is `OR`).
-/

@[expose] public section

namespace CslibFrontierTests.Computability.Circuit.Boolean.SymAnd.ACC0

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean Finset

/-! ### Prime-power digits -/

/-- `8 ∣ 24`: the digits `C(24, 1)`, `C(24, 2)`, `C(24, 4)` are even. -/
example : 2 ^ 3 ∣ 24 :=
  (Nat.pow_dvd_iff_forall_dvd_choose Nat.prime_two 3 24).2 (by decide)

/-- `4 ∤ 6`: the digit `C(6, 2) = 15` is odd. -/
example : ¬ 2 ^ 2 ∣ 6 := fun h =>
  absurd ((Nat.pow_dvd_iff_forall_dvd_choose Nat.prime_two 2 6).1 h 1 (by decide)) (by decide)

/-- `7 % 6 ≠ 0` is witnessed by the prime `2` and the digit `C(7, 1) = 7`, which is odd. -/
example : 7 % 6 ≠ 0 :=
  (Nat.mod_ne_zero_iff_exists_not_dvd_choose (by decide) 7).2
    ⟨2, 0, Nat.prime_two, by decide, by decide⟩

/-- `12 % 6 = 0`, so no prime power of `6` has a nonzero digit test on `12`. -/
example : ¬ ∃ p i, p.Prime ∧ p ^ (i + 1) ∣ 6 ∧ ¬ p ∣ (12 : ℕ).choose (p ^ i) := fun h =>
  (Nat.mod_ne_zero_iff_exists_not_dvd_choose (by decide) 12).2 h (by decide)

/-! ### Binomial counts and the seeded OR test -/

/-- The two-element monomials on four bits, three of them true, sum to `C(3, 2) = 3`. -/
example : ∑ S ∈ (univ : Finset (Fin 4)).powersetCard 2,
    monomial ℤ S ![true, false, true, true] = 3 := by
  rw [sum_powersetCard_monomial]
  decide

/-- Over `𝔽₂` with its one-element basis and both arguments true, the seed vectors `1` and `1`
sum to `0`: the seed is bad, and the OR test reads even although some argument is true. -/
example : orTest (Module.Basis.singleton (Fin 1) (ZMod 2)) (fun _ : Fin 2 => (1 : ZMod 2))
    univ (fun _ => true) % 2 = 0 := by
  by_contra h
  have := (orTest_emod_two_ne_zero_iff _ _ _ _).1 h
  exact this (by decide)

/-- With only the first argument true the same test reads odd. -/
example : orTest (Module.Basis.singleton (Fin 1) (ZMod 2)) (fun _ : Fin 2 => (1 : ZMod 2))
    univ ![true, false] % 2 ≠ 0 :=
  (orTest_emod_two_ne_zero_iff _ _ _ _).2 (by decide)

/-! ### Restriction -/

/-- "At least one of `x₀ ∧ x₁`, `x₂`" on three slots. -/
def orAnd : SymAnd (Fin 3) := ⟨{{0, 1}, {2}}, fun c => decide (1 ≤ c)⟩

/-- Slots `0` and `1` read inputs `1` and `0`; slot `2` is fixed to `false`. -/
def ρ : Fin 3 → Option (Fin 2) := ![some 1, some 0, none]

example : (orAnd.restrict ρ).size = 1 := by decide
example : (orAnd.restrict ρ).fanIn = 2 := by decide
example : (orAnd.restrict ρ).eval ![true, true] = true := by
  rw [SymAnd.eval_restrict]; decide
example : (orAnd.restrict ρ).eval ![true, false] = false := by
  rw [SymAnd.eval_restrict]; decide

/-! ### ACC⁰ circuits as `SYM ∘ AND` circuits -/

/-- One `MOD_q` gate on two inputs. -/
def modTwo : Circuit Unbounded.extSignature 2 1 :=
  Circuit.oneGate (σ := Unbounded.extSignature) (.gate 2) id

example (q : ℕ) (x : Fin 2 → Bool) :
    modTwo.eval (Unbounded.extInterpretation (modGate q)) x 0 = modGate q 2 x := rfl

/-- **Non-vacuity, prime modulus.** One `MOD_3` gate is a `SYM ∘ AND` circuit within the stated
bounds, and that circuit takes both values. -/
theorem mod3_nonvacuous : ∃ C' : SymAnd (Fin 2),
    C'.eval = (fun x => modGate 3 2 x) ∧
      C'.fanIn ≤ (2 * (3 * ((3 + 1) ^ 2 + Nat.log 2 (2 + 1) + 2))) ^ 5 ^ (1 * (3 + 2)) ∧
      C'.eval ![true, false] = true ∧ C'.eval ![false, false] = false := by
  obtain ⟨C', hC', hf, -⟩ := modTwo.exists_symAnd_eval_eq (m := 3) (by decide)
  have hd : modTwo.depth = 1 := Circuit.depth_oneGate _ _
  have hs : modTwo.size = 1 := Circuit.size_oneGate _ _
  rw [hd, hs] at hf
  refine ⟨C', hC', hf, ?_, ?_⟩ <;> rw [hC'] <;> decide

/-- **Non-vacuity, composite modulus.** One `MOD_6` gate is a `SYM ∘ AND` circuit within the stated
fan-in bound that takes both values; the composite modulus is handled through its prime-power
digits. -/
theorem mod6_nonvacuous : ∃ C' : SymAnd (Fin 2),
    C'.eval = (fun x => modGate 6 2 x) ∧
      C'.fanIn ≤ (2 * (3 * ((6 + 1) ^ 2 + Nat.log 2 (2 + 1) + 2))) ^ 5 ^ (1 * (6 + 2)) ∧
      C'.eval ![true, true] = true ∧ C'.eval ![false, false] = false := by
  obtain ⟨C', hC', hf, -⟩ := modTwo.exists_symAnd_eval_eq (m := 6) (by decide)
  have hd : modTwo.depth = 1 := Circuit.depth_oneGate _ _
  have hs : modTwo.size = 1 := Circuit.size_oneGate _ _
  rw [hd, hs] at hf
  exact ⟨C', hC', hf, by rw [hC']; decide, by rw [hC']; decide⟩

/-! ### The explicit circuit -/

/-- The explicit circuit of one `MOD_6` gate reads `true` on `(true, false)`. -/
example : (modTwo.toSymAnd 6).eval ![true, false] = true := by
  rw [Circuit.eval_toSymAnd _ (by decide)]
  decide

/-- The explicit circuit of one `MOD_6` gate reads `false` on `(false, false)`. -/
example : (modTwo.toSymAnd 6).eval ![false, false] = false := by
  rw [Circuit.eval_toSymAnd _ (by decide)]
  decide

/-- The `MOD_6` language has quasi-polynomial `SYM ∘ AND` circuits. -/
example : ∃ c, ∀ n, ∃ C' : SymAnd (Fin n), C'.eval = (Language.ofSlices (modGate 6)).slice n ∧
    C'.fanIn ≤ (c * (Nat.log 2 n + 1)) ^ c ∧ C'.size ≤ 2 ^ (c * (Nat.log 2 n + 1)) ^ c :=
  exists_symAnd_of_mem_AC0Mod (modGate_mem_AC0Mod 6)

/-- The language corollary needs no positivity: `AC0Mod 0`, where `MOD_0` is `OR`, is covered. -/
example : ∃ c, ∀ n, ∃ C' : SymAnd (Fin n), C'.eval = (Language.ofSlices (modGate 0)).slice n ∧
    C'.fanIn ≤ (c * (Nat.log 2 n + 1)) ^ c ∧ C'.size ≤ 2 ^ (c * (Nat.log 2 n + 1)) ^ c :=
  exists_symAnd_of_mem_AC0Mod (modGate_mem_AC0Mod 0)

/-- Every `ACC0` language, here `MOD_6`, has quasi-polynomial `SYM ∘ AND` circuits. -/
example : ∃ c, ∀ n, ∃ C' : SymAnd (Fin n), C'.eval = (Language.ofSlices (modGate 6)).slice n ∧
    C'.fanIn ≤ (c * (Nat.log 2 n + 1)) ^ c ∧ C'.size ≤ 2 ^ (c * (Nat.log 2 n + 1)) ^ c :=
  exists_symAnd_of_mem_ACC0 (modGate_mem_ACC0 6)

end CslibFrontierTests.Computability.Circuit.Boolean.SymAnd.ACC0
