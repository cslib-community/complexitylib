/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Complexity.CookLevin.Correctness
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Run
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Length-checked verifiers

An `NP` verifier `V` is only required by `Cslib.Complexity.IsVerifier` to decide membership when
given a certificate of the prescribed length `p |enc a|`; its behavior on shorter or longer strings
is unconstrained. Wrapping `V` in `Cslib.Complexity.strictVerifier` adds an explicit polynomial-time
check that the certificate has length `p |enc a|`.

For a deterministic machine `tm` computing `strictVerifier enc p V`, any accepting run of `tm` on
`frame (enc a) ++ w` that has halted by step `T` must have `|w| = p |enc a|`, even when the
certificate length `L = |w|` is existential rather than computed in advance: because halted
configurations are fixed points of `tm.step`, a run that has halted by step `T` is in the same
halted configuration as at `tm`'s time bound. Consequently, in Fagin's theorem the existential
second-order sentence can existentially guess where the certificate ends without evaluating the
polynomial `p` in first-order logic.

## Main definitions

* `Cslib.Complexity.strictVerifier`: a verifier guarded by the certificate-length check
  `w.length == p.eval (enc a).length`.

## Main results

* `Cslib.Complexity.IsVerifier.strictVerifier`: `strictVerifier` verifies the same problem with the
  same certificate polynomial.
* `Cslib.Complexity.computableInPolyTime_strictVerifier`: `strictVerifier` is computable in
  polynomial time when `V` is.
* `Cslib.Complexity.CookLevin.strictVerifier_eq_true_of_tableau_satisfiable`,
  `Cslib.Complexity.CookLevin.exists_tableau_satisfiable_iff_of_strictVerifier`: when `tm` computes
  `strictVerifier enc p V` and the time bound `T` covers certificates of length `p |enc a|`, a
  problem instance `a` belongs to `A` iff `tableau tm (frame (enc a)) L T` is satisfiable for some
  `L ≤ M` (for any bound `M ≥ p |enc a|`).

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM

variable {α : Type}

/-- A verifier augmented with an explicit check that the certificate has the prescribed length
`p.eval (enc a).length`. -/
def strictVerifier (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (V : α × List Bool → Bool) (x : α × List Bool) : Bool :=
  (x.2.length == p.eval (enc x.1).length) && V x

@[simp]
theorem strictVerifier_eq_true_iff (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (V : α × List Bool → Bool) (a : α) (w : List Bool) :
    strictVerifier enc p V (a, w) = true ↔
      w.length = p.eval (enc a).length ∧ V (a, w) = true := by
  simp [strictVerifier]

private theorem length_eq_of_strictVerifier_eq_true {enc : α ↪ List Bool} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} {a : α} {w : List Bool}
    (h : strictVerifier enc p V (a, w) = true) :
    w.length = p.eval (enc a).length :=
  ((strictVerifier_eq_true_iff enc p V a w).1 h).1

/-- Guarding a verifier by its certificate-length check preserves `IsVerifier`. -/
theorem IsVerifier.strictVerifier {enc : α ↪ List Bool} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} {A : Set α} (hV : IsVerifier enc p V A) :
    IsVerifier enc p (Cslib.Complexity.strictVerifier enc p V) A := by
  intro a
  rw [hV a]
  simp [strictVerifier_eq_true_iff]

/-- Because `strictVerifier` checks the certificate length itself, an instance belongs to `A` iff
some certificate of any length is accepted. -/
theorem IsVerifier.exists_strictVerifier_eq_true_iff {enc : α ↪ List Bool} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} {A : Set α} (hV : IsVerifier enc p V A) (a : α) :
    a ∈ A ↔ ∃ w : List Bool, Cslib.Complexity.strictVerifier enc p V (a, w) = true := by
  rw [hV a]
  simp [strictVerifier_eq_true_iff]

/-- Guarding a polynomial-time verifier by its certificate-length check preserves polynomial-time
computability. -/
@[fun_prop]
theorem computableInPolyTime_strictVerifier (enc : α ↪ List Bool) (p : Polynomial ℕ)
    {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) :
    ComputableInPolyTime (strictVerifier enc p V) (encPair enc encBits) encBool := by
  unfold strictVerifier
  fun_prop

namespace CookLevin

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]

/-- If `tm` computes `strictVerifier enc p V`, any certificate `w` whose run halts with `[true]` by
step `T` is accepted by `strictVerifier enc p V`, regardless of whether `T` is above `tm`'s time
bound on `(a, w)`: once halted, a deterministic configuration does not change. -/
theorem strictVerifier_eq_true_of_tableau_satisfiable {enc : α ↪ List Bool} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} {tm : MultiTapeTM k Bool State}
    {t s : α × List Bool → ℕ}
    (htm : tm.ComputesFunTidilyInTimeAndSpace (encPair enc encBits) encBool
      (strictVerifier enc p V) t s)
    {a : α} {L T : ℕ} (hsat : (tableau tm (frame (enc a)) L T).Satisfiable) :
    ∃ w : List Bool, w.length = L ∧ strictVerifier enc p V (a, w) = true := by
  obtain ⟨w, hw, hhalt, hout⟩ := tableau_satisfiable_iff.1 hsat
  obtain ⟨hhalt₀, hout₀⟩ := (htm (a, w)).runFrom_initCfg
  rw [encPair_apply, encBits_apply] at hhalt₀ hout₀
  have h₁ := runFrom_eq_of_halt tm (tm.initCfg (frame (enc a) ++ w)) (Nat.le_max_left T (t (a, w)))
    hhalt
  have h₂ := runFrom_eq_of_halt tm (tm.initCfg (frame (enc a) ++ w)) (Nat.le_max_right T (t (a, w)))
    hhalt₀
  have hout_eq : (tm.runFrom (tm.initCfg (frame (enc a) ++ w)) T).output =
      (tm.runFrom (tm.initCfg (frame (enc a) ++ w)) (t (a, w))).output := by
    rw [← h₁, ← h₂]
  rw [hout, hout₀, encBool_apply, List.singleton_inj] at hout_eq
  exact ⟨w, hw, hout_eq.symm⟩

/-- **Existential-length Cook–Levin characterization.** When `tm` computes `strictVerifier enc p V`
within time `t` and `T` is at least `t (a, w)` for certificates of the prescribed length
`p.eval (enc a).length`, an instance `a` belongs to `A` iff `tableau tm (frame (enc a)) L T` is
satisfiable for some certificate length `L ≤ M`, for any upper bound `M ≥ p.eval (enc a).length`. -/
theorem exists_tableau_satisfiable_iff_of_strictVerifier {enc : α ↪ List Bool} {A : Set α}
    {p : Polynomial ℕ} {V : α × List Bool → Bool} (hV : IsVerifier enc p V A)
    {tm : MultiTapeTM k Bool State} {t s : α × List Bool → ℕ}
    (htm : tm.ComputesFunTidilyInTimeAndSpace (encPair enc encBits) encBool
      (strictVerifier enc p V) t s)
    {a : α} {M T : ℕ} (hM : p.eval (enc a).length ≤ M)
    (hT : ∀ w : List Bool, w.length = p.eval (enc a).length → t (a, w) ≤ T) :
    (∃ L ≤ M, (tableau tm (frame (enc a)) L T).Satisfiable) ↔ a ∈ A := by
  rw [hV.exists_strictVerifier_eq_true_iff]
  constructor
  · rintro ⟨L, -, hsat⟩
    obtain ⟨w, -, hw⟩ := strictVerifier_eq_true_of_tableau_satisfiable htm hsat
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    have hlen := length_eq_of_strictVerifier_eq_true hw
    refine ⟨w.length, hlen ▸ hM, tableau_satisfiable_iff.2 ⟨w, rfl, ?_⟩⟩
    obtain ⟨hhalt₀, hout₀⟩ := (htm (a, w)).runFrom_initCfg
    have hstay := runFrom_eq_of_halt tm _ (hT w hlen) hhalt₀
    rw [encPair_apply, encBits_apply] at hhalt₀ hout₀ hstay
    rw [hstay, hout₀, hw, encBool_apply]
    exact ⟨hhalt₀, rfl⟩

end CookLevin

end Cslib.Complexity
