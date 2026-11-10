/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.Immune.Core
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Computable
import CslibFrontier.Computability.Complexity.Classes.EXP.Separation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Machine
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime

/-!
# Polynomial complexity cores of machines

[Lynch][Lynch1975] defines a polynomial complexity core of a decidable set `A` in terms of the
machines deciding it: `X` is a core (`Cslib.Complexity.IsPolyTimeCore`) when every machine
deciding `A` runs for more than `p (|x|)` steps on all but finitely many `x ∈ X`, for every
polynomially bounded `p`. Lynch allows any deterministic machine; here machines have a binary
alphabet and finitely many states, as in `P`, which changes running times only polynomially.

For decidable `A` these are the complexity cores of `A` for `P`
(`Cslib.Complexity.isPolyTimeCore_iff_isComplexityCore`):

* Let `X` be a core for `P`, let a machine decide `A`, and let `p` be polynomially bounded. The
  instances on which the machine halts within `p` steps with a given answer form a problem in `P`:
  the universal machine simulates it for `c (n + 1) ^ d ≥ p n` steps in polynomial time. That
  problem lies inside `A` or inside its complement, so it meets `X` in a finite set
  (`Cslib.Complexity.IsComplexityCore.isPolyTimeCore`).
* Conversely, let `X` be a machine core and let `B ∈ P` lie inside `A`. Decide `B` first, answer
  `true` on `B`, and run a decider of `A` elsewhere. This decides `A` and runs in polynomial time
  on `B`, so it halts in time on only finitely many instances of `B ∩ X`
  (`Cslib.Complexity.IsPolyTimeCore.isComplexityCore`).

No machine decides an undecidable set, so every set is a machine core of an undecidable set; the
second direction needs decidability.

Combined with the class-generic core theorem
(`Cslib.Complexity.exists_infinite_isComplexityCore_P_subset`), this gives
[Lynch, Lemma 1][Lynch1975] in a proper-core form: a problem is outside `P` exactly when it has an
infinite polynomial complexity core inside it
(`Cslib.Complexity.notMem_P_iff_exists_infinite_isPolyTimeCore`). Lynch's lemma gives, for a
recursive set outside `P`, an infinite recursive core that need not lie inside the set. The core
here lies inside the set, which is stronger, but it is not claimed to be recursive. For decidable
problems on bit strings, `Immune.RecursiveCore` chooses it decidable as well
(`Cslib.Complexity.exists_infinite_isDecidable_isPolyTimeCore`). Problems hard for `E` or `EXP`
are outside `P`, so they have infinite cores
(`Cslib.Complexity.PolyTimeHard.exists_infinite_isPolyTimeCore_E`,
`Cslib.Complexity.PolyTimeHard.exists_infinite_isPolyTimeCore_EXP`).

The universe is a machine core of `A` when every machine deciding `A` runs in superpolynomial time
on almost all instances. For decidable `A` with `A` and its complement infinite, this is
`P`-bi-immunity ([Balcázar and Schöning][BalcazarSchoening1985],
`Cslib.Complexity.isBiImmune_P_iff_isPolyTimeCore_univ`).

## Main definitions

* `Cslib.Complexity.IsPolyTimeCore`: a polynomial complexity core in terms of machines.

## Main results

* `Cslib.Complexity.IsComplexityCore.isPolyTimeCore`,
  `Cslib.Complexity.IsPolyTimeCore.isComplexityCore`,
  `Cslib.Complexity.isPolyTimeCore_iff_isComplexityCore`: for decidable problems, machine cores are
  the complexity cores for `P`.
* `Cslib.Complexity.notMem_P_iff_exists_infinite_isPolyTimeCore`: Lynch's Lemma 1, with a proper
  core that is not claimed to be recursive.
* `Cslib.Complexity.isBiImmune_P_iff_isPolyTimeCore_univ`: a decidable problem is `P`-bi-immune
  exactly when it and its complement are infinite and every decider runs in superpolynomial time
  almost everywhere.
* `Cslib.Complexity.PolyTimeHard.exists_infinite_isPolyTimeCore_E`,
  `Cslib.Complexity.PolyTimeHard.exists_infinite_isPolyTimeCore_EXP`: problems hard for `E` or `EXP`
  have infinite cores.

## References

* [J. L. Balcázar, U. Schöning, *Bi-immune sets for complexity classes*][BalcazarSchoening1985]
* [N. Lynch, *On reducibility to complex or sparse sets*][Lynch1975]
-/

public section

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

namespace Cslib.Complexity

variable {β : Type} {enc : β ↪ List Bool} {A X : Set β}

/-- `X` is a **polynomial complexity core** of `A` [Lynch][Lynch1975]: for every machine with a
binary alphabet and finitely many states deciding `A`, and every polynomially bounded `p`, the
machine halts within `p (enc x).length` steps on only finitely many `x ∈ X`. -/
def IsPolyTimeCore (enc : β ↪ List Bool) (A X : Set β) : Prop :=
  ∀ (k : ℕ) (State : Type) [Finite State] (tm : MultiTapeTM k Bool State),
    (∀ a, tm.Computes (enc a) [indicator A a]) → ∀ p : ℕ → ℕ, PolynomiallyBounded p →
      {x ∈ X | (tm.runFrom (tm.initCfg (enc x)) (p (enc x).length)).Halted}.Finite

theorem isPolyTimeCore_iff : IsPolyTimeCore enc A X ↔
    ∀ (k : ℕ) (State : Type) [Finite State] (tm : MultiTapeTM k Bool State),
      (∀ a, tm.Computes (enc a) [indicator A a]) → ∀ p : ℕ → ℕ, PolynomiallyBounded p →
        {x ∈ X | (tm.runFrom (tm.initCfg (enc x)) (p (enc x).length)).Halted}.Finite :=
  Iff.rfl

/-- **Complexity cores for `P` are polynomial complexity cores**: the instances on which a decider
halts in time with a given answer form a problem in `P`, by universal simulation. -/
theorem IsComplexityCore.isPolyTimeCore (h : IsComplexityCore (P enc) A X) :
    IsPolyTimeCore enc A X := by
  classical
  intro k State _ tm htm p hp
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.mp hp
  -- the instances on which the simulation for `c (n + 1) ^ d` steps halts with answer `b`
  let B : Bool → Set β := fun b =>
    {a | universal (desc eS eBit tm, (enc a).map eBit, c * ((enc a).length + 1) ^ d) =
      ([eBit b], true)}
  have hBP (b : Bool) : B b ∈ P enc := by
    refine ⟨fun a => decide (universal (desc eS eBit tm, (enc a).map eBit,
      c * ((enc a).length + 1) ^ d) = ([eBit b], true)), ?_, fun a => by simp [B]⟩
    have he : ComputableInPolyTime (fun a : β => enc a) enc encBits := .of_eq fun _ => rfl
    fun_prop
  have hBind {b : Bool} {a : β} (ha : a ∈ B b) : indicator A a = b := by
    simp only [B, Set.mem_ofPred_eq, universal_desc, Prod.mk.injEq] at ha
    obtain ⟨hout, hhalt⟩ := ha
    have hh : (tm.runFrom (tm.initCfg (enc a)) (c * ((enc a).length + 1) ^ d)).Halted :=
      Option.isNone_iff_eq_none.mp hhalt
    rw [(htm a).output_eq_of_halted hh, List.map_singleton, List.singleton_inj] at hout
    exact eBit.injective hout
  have hfin (b : Bool) : (B b ∩ X).Finite := by
    refine isComplexityCore_iff.mp h _ (hBP b) ?_
    cases b
    · refine .inr fun a ha => ?_
      have := hBind ha
      simp only [indicator] at this
      simpa using this
    · refine .inl fun a ha => ?_
      have := hBind ha
      simp only [indicator] at this
      simpa using this
  -- halting within `p` steps means halting within `c (n + 1) ^ d` steps, with the right answer
  refine ((hfin false).union (hfin true)).subset ?_
  rintro x ⟨hxX, hx⟩
  have hle : p (enc x).length ≤ c * ((enc x).length + 1) ^ d := hcd _
  have hhalt : (tm.runFrom (tm.initCfg (enc x)) (c * ((enc x).length + 1) ^ d)).Halted := by
    rw [runFrom_eq_of_halt tm _ hle hx]
    exact hx
  have hmem : x ∈ B (indicator A x) := by
    simp only [B, Set.mem_ofPred_eq, universal_desc, (htm x).output_eq_of_halted hhalt,
      List.map_singleton, Prod.mk.injEq, true_and]
    exact Option.isNone_iff_eq_none.mpr hhalt
  cases hb : indicator A x
  · exact .inl ⟨hb ▸ hmem, hxX⟩
  · exact .inr ⟨hb ▸ hmem, hxX⟩

/-- A problem in `P` on which the decidable problem `A` is constant, with value `b`, meets every
polynomial complexity core of `A` in a finite set: deciding `B` first and answering `b` on it
decides `A` within a polynomial time bound on `B`. -/
private theorem IsPolyTimeCore.finite_inter_of_indicator_eq {B : Set β}
    (h : IsPolyTimeCore enc A X) (hA : IsDecidable A enc) (hB : B ∈ P enc) {b : Bool}
    (hBA : ∀ x ∈ B, indicator A x = b) : (B ∩ X).Finite := by
  obtain ⟨c, hc, hcB⟩ := mem_P.mp hB
  obtain ⟨Tc, Sc, hTc, -, hcO⟩ := hc.exists_computableInO
  obtain ⟨tA, sA, hAc⟩ := hA
  have hAO : ComputableInO (indicator A) enc encBool tA (fun a => tA a + sA a) :=
    .of_bounds hAc 1 (fun _ => by omega) (fun _ => by omega) fun a =>
      le_trans (hAc.length_le a) (by omega)
  -- decide `B`, answer `b` on `B`, and run the decider of `A` elsewhere
  have hite := hcO.ite (ComputableInO.const (encMid := encBool) b) hAO
  have heq : (fun x => if c x then b else indicator A x) = indicator A := by
    funext x
    split_ifs with hx
    · exact (hBA x ((hcB x).mpr hx)).symm
    · rfl
  rw [heq] at hite
  obtain ⟨k, ⟨k', State, hfinite, tm, htm⟩, -⟩ := hite
  obtain ⟨c₁, d₁, hcd⟩ := hTc.exists_le
  -- on `B` the combined machine halts within `k (c₁ (n + 1) ^ d₁ + n + 1)` steps
  have hp : PolynomiallyBounded fun n => k * (c₁ * (n + 1) ^ d₁ + n + 1) := by fun_prop
  refine (h k' State tm (fun a => (htm a).1) _ hp).subset fun x ⟨hxB, hxX⟩ => ⟨hxX, ?_⟩
  have hcx : c x = true := (hcB x).mp hxB
  refine ((htm x).runFrom_of_le ?_).1
  simp only [hcx, ↓reduceIte]
  have := hcd x
  exact Nat.mul_le_mul_left k (by omega)

/-- **Polynomial complexity cores of decidable problems are complexity cores for `P`.** -/
theorem IsPolyTimeCore.isComplexityCore (h : IsPolyTimeCore enc A X) (hA : IsDecidable A enc) :
    IsComplexityCore (P enc) A X := by
  classical
  refine isComplexityCore_iff.mpr ?_
  rintro B hB (hBA | hBA)
  · exact h.finite_inter_of_indicator_eq hA hB (b := true) fun x hx => by
      simp [indicator, hBA hx]
  · exact h.finite_inter_of_indicator_eq hA hB (b := false) fun x hx => by
      simp [indicator, show x ∉ A from hBA hx]

/-- **For decidable problems, polynomial complexity cores are the complexity cores for `P`.** -/
theorem isPolyTimeCore_iff_isComplexityCore (hA : IsDecidable A enc) :
    IsPolyTimeCore enc A X ↔ IsComplexityCore (P enc) A X :=
  ⟨fun h => h.isComplexityCore hA, IsComplexityCore.isPolyTimeCore⟩

/-- A problem in `P` has only finite polynomial complexity cores: its polynomial-time decider halts
in time on every instance. -/
theorem IsPolyTimeCore.finite_of_mem_P (h : IsPolyTimeCore enc A X) (hA : A ∈ P enc) :
    X.Finite := by
  obtain ⟨t, s, ht, -, k, State, hfinite, tm, htm⟩ :=
    mem_P_iff_exists_decidableInTimeAndSpace.mp hA
  refine (h k State tm (fun a => (htm a).1) t ht).subset fun x hx => ⟨hx, ?_⟩
  exact ((htm x).runFrom_of_le le_rfl).1

/-- **Problems outside `P` have infinite polynomial complexity cores** ([Lynch, Lemma 1][Lynch1975],
proper-core strengthening): a problem is outside `P` exactly when it has an infinite polynomial
complexity core inside it. Unlike Lynch's core, this one is not claimed to be recursive; for a
decidable core of a decidable problem on bit strings, see
`Cslib.Complexity.exists_infinite_isDecidable_isPolyTimeCore`. -/
theorem notMem_P_iff_exists_infinite_isPolyTimeCore :
    A ∉ P enc ↔ ∃ X ⊆ A, X.Infinite ∧ IsPolyTimeCore enc A X := by
  refine ⟨fun hA => ?_, fun ⟨_, _, hX, h⟩ hA => hX (h.finite_of_mem_P hA)⟩
  obtain ⟨X, hXA, hX, hcore⟩ := exists_infinite_isComplexityCore_P_subset hA
  exact ⟨X, hXA, hX, hcore.isPolyTimeCore⟩

/-- **`P`-bi-immunity in terms of machines** [Balcázar and Schöning][BalcazarSchoening1985]: a
decidable problem is `P`-bi-immune exactly when it and its complement are infinite and every
machine deciding it runs in superpolynomial time on almost every instance. -/
theorem isBiImmune_P_iff_isPolyTimeCore_univ (hA : IsDecidable A enc) :
    IsBiImmune (P enc) A ↔ A.Infinite ∧ Aᶜ.Infinite ∧ IsPolyTimeCore enc A Set.univ := by
  rw [isBiImmune_iff_isComplexityCore_univ, isPolyTimeCore_iff_isComplexityCore hA]

/-- Every machine deciding a `P`-bi-immune problem runs in superpolynomial time on almost every
instance. -/
theorem IsBiImmune.isPolyTimeCore_univ (h : IsBiImmune (P enc) A) :
    IsPolyTimeCore enc A Set.univ :=
  (isBiImmune_iff_isComplexityCore_univ.mp h).2.2.isPolyTimeCore

/-- **Problems hard for `E` have infinite polynomial complexity cores**, since they are not in
`P`. -/
theorem PolyTimeHard.exists_infinite_isPolyTimeCore_E (h : PolyTimeHard @E enc A) :
    ∃ X ⊆ A, X.Infinite ∧ IsPolyTimeCore enc A X :=
  notMem_P_iff_exists_infinite_isPolyTimeCore.mp fun hA =>
    let ⟨_, hB, hBP⟩ := Set.exists_of_ssubset P_ssubset_E
    hBP ((h encBits _ hB).mem_P hA)

/-- **Problems hard for `EXP` have infinite polynomial complexity cores**, since they are not in
`P`. -/
theorem PolyTimeHard.exists_infinite_isPolyTimeCore_EXP (h : PolyTimeHard @EXP enc A) :
    ∃ X ⊆ A, X.Infinite ∧ IsPolyTimeCore enc A X :=
  notMem_P_iff_exists_infinite_isPolyTimeCore.mp fun hA =>
    let ⟨_, hB, hBP⟩ := Set.exists_of_ssubset P_ssubset_EXP
    hBP ((h encBits _ hB).mem_P hA)

end Cslib.Complexity
