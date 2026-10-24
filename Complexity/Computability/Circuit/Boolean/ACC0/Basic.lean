/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.ModGates
public import Complexity.Computability.Circuit.Boolean.ModMajority
public import Mathlib.Data.Nat.Prime.Defs
import Complexity.Computability.Circuit.Boolean.Smolensky.Majority

/-!
# Definition, divisibility monotonicity, and Boolean closure of `ACC⁰`

**ACC⁰** (`Cslib.Circuits.Boolean.ACC0`) is the union of the modular constant-depth circuit classes
`AC0Mod q` over all fixed moduli `q ≥ 2` [Barrington1989], [Vollmer, Chapter 4][Vollmer1999],
[Arora and Barak, Section 14.2][AroraBarak09]: the languages over `Bool` decided at every input
length by polynomial-size, constant-depth nonuniform circuits over negations, unbounded fan-in
conjunctions and disjunctions, and unbounded fan-in `MOD_q` gates (`modGate q`). Since `modGate 0`
is disjunction and `modGate 1` is the constant `false`, the union over all `q : ℕ` gives the same
class (`ACC0_eq_iUnion_AC0Mod`).

Repeating each input wire of a `MOD_q` gate `k ≥ 1` times multiplies the Hamming weight by `k`, and
`(w * k) % (q * k) = (w % q) * k`, so a single `MOD_{q * k}` gate simulates a `MOD_q` gate
(`AC0Mod_subset_AC0Mod_mul_right`, `AC0Mod_subset_AC0Mod_of_dvd`). Two circuits with moduli `q₁`
and `q₂` therefore embed into the common modulus `q₁ * q₂`, making `ACC0` closed under complement,
intersection, and union (`ACC0.compl`, `ACC0.inf`, `ACC0.sup`). By Håstad's and
Razborov–Smolensky's lower bounds for parity, `AC0 ⊂ AC0Mod 2 ⊆ ACC0` (`AC0_ssubset_AC0Mod_two`,
`AC0_ssubset_ACC0`) and `AC0Mod p ⊂ ACC0` for every odd prime `p` (`AC0Mod_ssubset_ACC0`).

## Main definitions

* `Cslib.Circuits.Boolean.ACC0`: the class ACC⁰ = `⋃ q ≥ 2, AC0Mod q`.
* `Cslib.Circuits.Boolean.modZeroCircuit`, `Cslib.Circuits.Boolean.modOneCircuit`,
  `Cslib.Circuits.Boolean.modMulCircuit`: gate simulations for `q = 0`, `q = 1`, and `q ∣ q * k`.

## Main results

* `Cslib.Circuits.Boolean.AC0Mod_zero`, `Cslib.Circuits.Boolean.AC0Mod_one`:
  `AC⁰[0] = AC⁰[1] = AC⁰`.
* `Cslib.Circuits.Boolean.AC0Mod_subset_AC0Mod_of_dvd`: `AC⁰[q] ⊆ AC⁰[q']` when `q ∣ q'` and
  `0 < q'`.
* `Cslib.Circuits.Boolean.ACC0_eq_iUnion_AC0Mod`: `ACC⁰ = ⋃ q, AC⁰[q]`.
* `Cslib.Circuits.Boolean.ACC0.compl`, `Cslib.Circuits.Boolean.ACC0.inf`,
  `Cslib.Circuits.Boolean.ACC0.sup`: Boolean closure of `ACC⁰`.
* `Cslib.Circuits.Boolean.ACC0_subset_TC0`: `ACC⁰ ⊆ TC⁰`.
* `Cslib.Circuits.Boolean.AC0_ssubset_ACC0`, `Cslib.Circuits.Boolean.AC0Mod_ssubset_ACC0`:
  strictness of `AC⁰ ⊂ ACC⁰` and `AC⁰[p] ⊂ ACC⁰` for odd prime `p`.

## References

* [D. A. M. Barrington, *Bounded-width polynomial-size branching programs recognize exactly those
  languages in NC¹*][Barrington1989]
* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Set Finset BitString Unbounded

/-! ### Degenerate moduli `q = 0, 1` and divisibility monotonicity for `AC0Mod` -/

/-- For `q = 0`, `modGate 0 m` tests whether the Hamming weight is nonzero, which is the
unbounded disjunction `.or m`. -/
theorem modGate_zero (m : ℕ) (x : Fin m → Bool) :
    modGate 0 m x = Unbounded.interpretation (.or m) x := by
  simp [modGate, Nat.mod_zero, card_eq_zero, filter_eq_empty_iff]

/-- For `q = 1`, `modGate 1 m` is the constant `false`. -/
@[simp] theorem modGate_one (m : ℕ) (x : Fin m → Bool) :
    modGate 1 m x = false := by
  simp [modGate, Nat.mod_one]

/-- For `q = 2`, `modGate 2 m` is the `m`-bit parity function `parity m`. -/
theorem modGate_two_eq_parity (m : ℕ) : modGate 2 m = parity m := by
  funext x
  simp only [modGate, parity, parityOn, ne_eq, Nat.mod_two_ne_zero]

/-- A circuit over the `AC⁰` basis simulating an operation of `AC⁰[0]`. -/
def modZeroCircuit : (op : ExtOp) → Circuit Unbounded.signature (extSignature.Arity op) 1
  | .ac op => Circuit.oneGate (σ := Unbounded.signature) op id
  | .gate m => Circuit.oneGate (σ := Unbounded.signature) (.or m) id

/-- `modZeroCircuit op` computes the `AC⁰[0]` operation `op` over the `AC⁰` basis. -/
theorem computes_modZeroCircuit (op : ExtOp) :
    (modZeroCircuit op).Computes Unbounded.interpretation
      (single (extInterpretation (modGate 0) op)) := by
  intro x
  funext o
  rw [Subsingleton.elim o 0]
  cases op with
  | ac op => rfl
  | gate m =>
    simp only [modZeroCircuit, Circuit.eval_oneGate, id_eq, single, extInterpretation_gate,
      modGate_zero]

/-- **`AC⁰[0] = AC⁰`**: modulo `0`, a `MOD_0` gate is an unbounded `OR` gate. -/
@[simp] theorem AC0Mod_zero : AC0Mod 0 = AC0 := by
  refine (ConstDepth.subset_of_simulation (b := 1) (c := 1) fun op =>
    ⟨modZeroCircuit op, computes_modZeroCircuit op, ?_, ?_⟩).antisymm (AC0_subset_AC0Mod 0)
  · cases op <;> simp [modZeroCircuit]
  · cases op <;> simp [modZeroCircuit]

/-- A circuit over the `AC⁰` basis simulating an operation of `AC⁰[1]`. -/
def modOneCircuit : (op : ExtOp) → Circuit Unbounded.signature (extSignature.Arity op) 1
  | .ac op => Circuit.oneGate (σ := Unbounded.signature) op id
  | .gate _ => constCircuit (Signature.Hom.id _) false

/-- `modOneCircuit op` computes the `AC⁰[1]` operation `op` over the `AC⁰` basis. -/
theorem computes_modOneCircuit (op : ExtOp) :
    (modOneCircuit op).Computes Unbounded.interpretation
      (single (extInterpretation (modGate 1) op)) := by
  intro x
  funext o
  rw [Subsingleton.elim o 0]
  cases op with
  | ac op => rfl
  | gate m => simp [modOneCircuit, single]

/-- **`AC⁰[1] = AC⁰`**: modulo `1`, a `MOD_1` gate is the constant `false`. -/
@[simp] theorem AC0Mod_one : AC0Mod 1 = AC0 := by
  refine (ConstDepth.subset_of_simulation (b := 1) (c := 1) fun op =>
    ⟨modOneCircuit op, computes_modOneCircuit op, ?_, ?_⟩).antisymm (AC0_subset_AC0Mod 1)
  · cases op <;> simp [modOneCircuit]
  · cases op with
    | ac op => simp [modOneCircuit]
    | gate m => exact depth_constCircuit_le false

/-- Repeating each of the `m` coordinates of `x` `k` times via `finProdFinEquiv` multiplies the
Hamming weight by `k`. -/
theorem weight_comp_finProdFinEquiv_fst {m k : ℕ} (x : Fin m → Bool) :
    BitString.weight (fun j : Fin (m * k) => x (finProdFinEquiv.symm j).1) =
      BitString.weight x * k := by
  rw [BitString.weight_eq_sum_toNat, BitString.weight_eq_sum_toNat]
  rw [Equiv.sum_comp finProdFinEquiv.symm (fun p : Fin m × Fin k => (x p.1).toNat),
    Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- A `MOD_q` gate on `m` inputs is computed by a single `MOD_{q * k}` gate on `m * k` inputs
when `0 < k`, by repeating each input wire `k` times. -/
theorem modGate_mul_right (q m : ℕ) {k : ℕ} (hk : 0 < k) (x : Fin m → Bool) :
    modGate (q * k) (m * k) (fun j => x (finProdFinEquiv.symm j).1) = modGate q m x := by
  simp only [modGate_eq_modCount, modCount, weight_comp_finProdFinEquiv_fst,
    Nat.mul_mod_mul_right, ne_eq, mul_eq_zero, hk.ne', or_false]

/-- A circuit over the `AC⁰[q * k]` basis simulating a single operation of `AC⁰[q]`. -/
def modMulCircuit (k : ℕ) : (op : ExtOp) → Circuit extSignature (extSignature.Arity op) 1
  | .ac op => Circuit.oneGate (σ := extSignature) (.ac op) id
  | .gate m => Circuit.oneGate (σ := extSignature) (.gate (m * k))
      fun j => (finProdFinEquiv.symm j).1

/-- `modMulCircuit k op` computes the `AC⁰[q]` operation `op` over the `AC⁰[q * k]` basis when
`0 < k`. -/
theorem computes_modMulCircuit (q : ℕ) {k : ℕ} (hk : 0 < k) (op : ExtOp) :
    (modMulCircuit k op).Computes (extInterpretation (modGate (q * k)))
      (single (extInterpretation (modGate q) op)) := by
  intro x
  funext o
  rw [Subsingleton.elim o 0]
  cases op with
  | ac op => rfl
  | gate m =>
    simp only [modMulCircuit, Circuit.eval_oneGate, single, extInterpretation_gate]
    exact modGate_mul_right q m hk x

/-- **`AC⁰[q] ⊆ AC⁰[q * k]`** for every `k > 0`: a `MOD_{q * k}` gate simulates a `MOD_q` gate by
repeating each wire `k` times. -/
theorem AC0Mod_subset_AC0Mod_mul_right (q : ℕ) {k : ℕ} (hk : 0 < k) :
    AC0Mod q ⊆ AC0Mod (q * k) := by
  refine ConstDepth.subset_of_simulation (b := 1) (c := 1) fun op =>
    ⟨modMulCircuit k op, computes_modMulCircuit q hk op, ?_, ?_⟩
  · cases op <;> simp [modMulCircuit]
  · cases op <;> simp [modMulCircuit]

/-- **`AC⁰[q] ⊆ AC⁰[k * q]`** for every `k > 0`. -/
theorem AC0Mod_subset_AC0Mod_mul_left {k : ℕ} (hk : 0 < k) (q : ℕ) :
    AC0Mod q ⊆ AC0Mod (k * q) := by
  rw [mul_comm]
  exact AC0Mod_subset_AC0Mod_mul_right q hk

/-- **Divisibility monotonicity**: if `q ∣ q'` and `0 < q'`, then `AC⁰[q] ⊆ AC⁰[q']`. -/
theorem AC0Mod_subset_AC0Mod_of_dvd {q q' : ℕ} (hq' : 0 < q') (h : q ∣ q') :
    AC0Mod q ⊆ AC0Mod q' := by
  obtain ⟨k, rfl⟩ := h
  have hk : 0 < k := Nat.pos_of_mul_pos_left hq'
  exact AC0Mod_subset_AC0Mod_mul_right q hk

/-! ### Definition of `ACC⁰` and closure properties -/

/-- **ACC⁰**: the class of languages over `Bool` decided at every input length by constant-depth,
polynomial-size circuits over negation, unbounded fan-in conjunction and disjunction, and
unbounded fan-in `MOD_q` gates for some fixed modulus `q ≥ 2` [Barrington1989],
[Vollmer, Chapter 4][Vollmer1999]. -/
def ACC0 : Set (Language Bool) :=
  ⋃ q ≥ 2, AC0Mod q

/-- Membership in `ACC⁰`: a language belongs to `ACC0` iff it belongs to `AC0Mod q` for some
modulus `q ≥ 2`. -/
theorem mem_ACC0_iff {L : Language Bool} :
    L ∈ ACC0 ↔ ∃ q ≥ 2, L ∈ AC0Mod q := by
  simp [ACC0]

/-- **AC⁰ ⊆ ACC⁰**: every `AC⁰` language belongs to `AC⁰[2] ⊆ ACC⁰`. -/
theorem AC0_subset_ACC0 : AC0 ⊆ ACC0 :=
  fun _ hL => mem_ACC0_iff.2 ⟨2, le_rfl, AC0_subset_AC0Mod 2 hL⟩

/-- **AC⁰[q] ⊆ ACC⁰** for every modulus `q : ℕ` (including `q = 0, 1`). -/
theorem AC0Mod_subset_ACC0 (q : ℕ) : AC0Mod q ⊆ ACC0 := by
  rcases q with _ | _ | q
  · rw [AC0Mod_zero]
    exact AC0_subset_ACC0
  · rw [AC0Mod_one]
    exact AC0_subset_ACC0
  · exact fun _ hL => mem_ACC0_iff.2 ⟨q + 2, by omega, hL⟩

/-- **`ACC⁰` is the union of `AC⁰[q]` over all `q : ℕ`.** -/
theorem ACC0_eq_iUnion_AC0Mod : ACC0 = ⋃ q, AC0Mod q := by
  refine Subset.antisymm (iUnion₂_subset fun q _ => subset_iUnion AC0Mod q) ?_
  exact iUnion_subset AC0Mod_subset_ACC0

/-- Membership in `ACC⁰` is equivalent to membership in `AC⁰[q]` for some `q : ℕ`. -/
theorem mem_ACC0_iff_exists_AC0Mod {L : Language Bool} :
    L ∈ ACC0 ↔ ∃ q, L ∈ AC0Mod q := by
  rw [ACC0_eq_iUnion_AC0Mod, Set.mem_iUnion]

/-- The modular counting language `Language.ofSlices (modGate q)` is in `AC⁰[q]`. -/
theorem modGate_mem_AC0Mod (q : ℕ) : Language.ofSlices (modGate q) ∈ AC0Mod q := by
  refine ConstDepth.mem_iff.2 ⟨1, fun _ => 1, by fun_prop, fun n =>
    ⟨Circuit.oneGate (σ := extSignature) (.gate n) id, fun x => ?_,
      (Circuit.depth_oneGate _ _).le, le_rfl⟩⟩
  funext j
  rw [Language.slice_ofSlices]
  rfl

/-- The modular counting language `Language.ofSlices (modGate q)` is in `ACC⁰`. -/
theorem modGate_mem_ACC0 (q : ℕ) : Language.ofSlices (modGate q) ∈ ACC0 :=
  AC0Mod_subset_ACC0 q (modGate_mem_AC0Mod q)

/-- **Parity is in `AC⁰[2]`.** -/
theorem parity_mem_AC0Mod_two : Language.ofSlices parity ∈ AC0Mod 2 := by
  have h : Language.ofSlices parity = Language.ofSlices (modGate 2) := by
    congr 1
    funext n
    exact (modGate_two_eq_parity n).symm
  rw [h]
  exact modGate_mem_AC0Mod 2

/-- **Parity is in `ACC⁰`.** -/
theorem parity_mem_ACC0 : Language.ofSlices parity ∈ ACC0 :=
  AC0Mod_subset_ACC0 2 parity_mem_AC0Mod_two

/-- **`AC⁰` is strictly contained in `AC⁰[2]`.** -/
theorem AC0_ssubset_AC0Mod_two : AC0 ⊂ AC0Mod 2 :=
  (Set.ssubset_iff_of_subset (AC0_subset_AC0Mod 2)).2
    ⟨_, parity_mem_AC0Mod_two, parity_notMem_AC0⟩

/-- **`AC⁰` is strictly contained in `ACC⁰`.** -/
theorem AC0_ssubset_ACC0 : AC0 ⊂ ACC0 :=
  (Set.ssubset_iff_of_subset AC0_subset_ACC0).2
    ⟨_, parity_mem_ACC0, parity_notMem_AC0⟩

/-- **`AC⁰[p]` is strictly contained in `ACC⁰`** for every odd prime `p`, witnessed by parity
[Razborov1987], [Smolensky1987]. -/
theorem AC0Mod_ssubset_ACC0 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : AC0Mod p ⊂ ACC0 :=
  (Set.ssubset_iff_of_subset (AC0Mod_subset_ACC0 p)).2
    ⟨_, parity_mem_ACC0, Smolensky.parity_notMem_AC0Mod hp2⟩

namespace AC0Mod

variable {q : ℕ} {L M : Language Bool}

/-- The empty language is in `AC⁰[q]`. -/
theorem bot_mem (q : ℕ) : (⊥ : Language Bool) ∈ AC0Mod q :=
  ConstDepth.bot_mem Unbounded.toExt

/-- The full language is in `AC⁰[q]`. -/
theorem top_mem (q : ℕ) : (⊤ : Language Bool) ∈ AC0Mod q :=
  ConstDepth.top_mem Unbounded.toExt

/-- `AC⁰[q]` is closed under complement. -/
theorem compl (hL : L ∈ AC0Mod q) : Lᶜ ∈ AC0Mod q :=
  ConstDepth.compl Unbounded.toExt hL

/-- `AC⁰[q]` is closed under intersection. -/
theorem inf (hL : L ∈ AC0Mod q) (hM : M ∈ AC0Mod q) : L ⊓ M ∈ AC0Mod q :=
  ConstDepth.inf Unbounded.toExt hL hM

/-- `AC⁰[q]` is closed under union. -/
theorem sup (hL : L ∈ AC0Mod q) (hM : M ∈ AC0Mod q) : L ⊔ M ∈ AC0Mod q :=
  ConstDepth.sup Unbounded.toExt hL hM

end AC0Mod

namespace ACC0

variable {L M : Language Bool}

/-- The empty language is in `ACC⁰`. -/
theorem bot_mem : (⊥ : Language Bool) ∈ ACC0 :=
  AC0_subset_ACC0 (ConstDepth.bot_mem (Signature.Hom.id _))

/-- The full language is in `ACC⁰`. -/
theorem top_mem : (⊤ : Language Bool) ∈ ACC0 :=
  AC0_subset_ACC0 (ConstDepth.top_mem (Signature.Hom.id _))

/-- **`ACC⁰` is closed under complement.** -/
theorem compl (hL : L ∈ ACC0) : Lᶜ ∈ ACC0 := by
  obtain ⟨q, hq, hLq⟩ := mem_ACC0_iff.1 hL
  exact mem_ACC0_iff.2 ⟨q, hq, AC0Mod.compl hLq⟩

/-- **`ACC⁰` is closed under intersection**: circuits with moduli `q₁` and `q₂` embed into
`AC⁰[q₁ * q₂]`. -/
theorem inf (hL : L ∈ ACC0) (hM : M ∈ ACC0) : L ⊓ M ∈ ACC0 := by
  obtain ⟨q₁, hq₁, hL₁⟩ := mem_ACC0_iff.1 hL
  obtain ⟨q₂, hq₂, hM₂⟩ := mem_ACC0_iff.1 hM
  refine mem_ACC0_iff.2 ⟨q₁ * q₂, by nlinarith, ?_⟩
  exact AC0Mod.inf
    (AC0Mod_subset_AC0Mod_mul_right q₁ (by omega) hL₁)
    (AC0Mod_subset_AC0Mod_mul_left (by omega) q₂ hM₂)

/-- **`ACC⁰` is closed under union**: circuits with moduli `q₁` and `q₂` embed into
`AC⁰[q₁ * q₂]`. -/
theorem sup (hL : L ∈ ACC0) (hM : M ∈ ACC0) : L ⊔ M ∈ ACC0 := by
  obtain ⟨q₁, hq₁, hL₁⟩ := mem_ACC0_iff.1 hL
  obtain ⟨q₂, hq₂, hM₂⟩ := mem_ACC0_iff.1 hM
  refine mem_ACC0_iff.2 ⟨q₁ * q₂, by nlinarith, ?_⟩
  exact AC0Mod.sup
    (AC0Mod_subset_AC0Mod_mul_right q₁ (by omega) hL₁)
    (AC0Mod_subset_AC0Mod_mul_left (by omega) q₂ hM₂)

end ACC0

/-- **`ACC⁰ ⊆ TC⁰`** [Vollmer, Chapter 4][Vollmer1999]: every `AC⁰[q]` is contained in `TC⁰`. -/
theorem ACC0_subset_TC0 : ACC0 ⊆ TC0 :=
  iUnion₂_subset fun q _ => AC0Mod_subset_TC0 q

end Cslib.Circuits.Boolean
