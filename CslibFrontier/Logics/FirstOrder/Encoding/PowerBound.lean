/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Encoding
public import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Logics.FirstOrder.Encoding.Layout

/-!
# Polynomial bounds in the length of an encoded structure

A well-formed input `a` of cardinality `n ≥ 1` has encoding length at most
`(v.count + 1) * (2 * n ^ v.maxArity + 1)`, a polynomial in `n` fixed by the vocabulary. So every
polynomial bound in the encoding length is eventually below one fixed power `n ^ k`. Machine
simulations in descriptive complexity (Fagin, Immerman–Vardi, Grädel, NL ⊆ FO(TC)) choose their
tuple width `k` this way, so that the power universe `Fin (n ^ k)` holds the machine's input, its
running time and its configurations.

## Main results

* `Cslib.Logic.Vocabulary.length_encStructure_le_pow`: the encoding of a well-formed input of
  cardinality `n ≥ 1` has length at most `(v.count + 1) * (2 * n ^ v.maxArity + 1)`.
* `Cslib.Logic.Vocabulary.exists_pow_bound`: for a polynomially bounded `g`, a tuple width
  `k ≥ 1` bounding all arities of `v` with `g (encStructure a).length < a.1 ^ k` on every
  well-formed input of cardinality at least two.
-/

public section

namespace Cslib.Logic.Vocabulary

open Turing.MultiTapeTM

variable {L : FirstOrder.Language} (v : Vocabulary L)

/-- For a well-formed input `a` with `1 ≤ a.1`, the `m`-th prefix of `encStructure a` has length at
most `(m + 1) * (2 * a.1 ^ v.maxArity + 1)`. -/
private theorem length_encStructurePrefix_le_pow {a : EncodedStructure} (ha : v.WellFormed a)
    (ha1 : 1 ≤ a.1) (m : ℕ) (hm : m ≤ v.count) :
    (v.encStructurePrefix a m).length ≤ (m + 1) * (2 * a.1 ^ v.maxArity + 1) := by
  induction m with
  | zero =>
    rw [v.encStructurePrefix_zero, Nat.zero_add, Nat.one_mul, length_frame, encUnary_apply,
      List.length_replicate]
    have hpow : a.1 ≤ a.1 ^ v.maxArity := by
      simpa using Nat.pow_le_pow_right ha1 v.one_le_maxArity
    omega
  | succ m ih =>
    have hi : m < v.count := by omega
    let idx : Fin v.count := ⟨m, hi⟩
    have h1 := ih (by omega)
    have h2 : (v.table a (v.symbol idx)).length = a.1 ^ v.arity idx :=
      Vocabulary.WellFormed.length_table v ha (v.symbol idx)
    have h3 : a.1 ^ v.arity idx ≤ a.1 ^ v.maxArity :=
      Nat.pow_le_pow_right ha1 (v.arity_le_maxArity idx)
    have hsucc := congrArg List.length (v.encStructurePrefix_succ a idx)
    rw [List.length_append, length_frame, h2] at hsucc
    change (v.encStructurePrefix a (m + 1)).length =
      (v.encStructurePrefix a m).length + (2 * a.1 ^ v.arity idx + 1) at hsucc
    rw [hsucc, Nat.add_mul, Nat.one_mul]
    omega

/-- For a well-formed input `a` with `1 ≤ a.1`, `(encStructure a).length` is bounded by
`(v.count + 1) * (2 * a.1 ^ v.maxArity + 1)`. -/
theorem length_encStructure_le_pow {a : EncodedStructure} (ha : v.WellFormed a) (ha1 : 1 ≤ a.1) :
    (encStructure a).length ≤ (v.count + 1) * (2 * a.1 ^ v.maxArity + 1) := by
  rw [← v.encStructurePrefix_count ha]
  exact v.length_encStructurePrefix_le_pow ha ha1 v.count le_rfl

/-- A polynomial bound in the encoding length is below a single power of the cardinality: for a
polynomially bounded `g` there is an exponent `k ≥ 1` bounding all relation arities of `v` such
that `g (encStructure a).length < a.1 ^ k` for every well-formed input `a` with `a.1 ≥ 2`. -/
theorem exists_pow_bound (g : ℕ → ℕ) (hg : PolynomiallyBounded g) :
    ∃ k : ℕ, 1 ≤ k ∧ (∀ i : Fin v.count, v.arity i ≤ k) ∧
      ∀ a : EncodedStructure, v.WellFormed a → 2 ≤ a.1 → g (encStructure a).length < a.1 ^ k := by
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.mp hg
  let F : ℕ → ℕ := fun n => c * ((v.count + 1) * (2 * n ^ v.maxArity + 1) + 1) ^ d
  have hF : PolynomiallyBounded F := by
    dsimp only [F]
    fun_prop
  obtain ⟨C, D, hCD⟩ := polynomiallyBounded_iff_le.mp hF
  refine ⟨max v.maxArity (C + 2 * D), v.one_le_maxArity.trans (le_max_left _ _),
    fun i => (v.arity_le_maxArity i).trans (le_max_left _ _), fun a ha h2 => ?_⟩
  have hlen := v.length_encStructure_le_pow ha (by omega)
  have hn : a.1 + 1 ≤ a.1 ^ 2 := by nlinarith
  calc g (encStructure a).length
      ≤ c * ((encStructure a).length + 1) ^ d := hcd _
    _ ≤ F a.1 := Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d)
    _ ≤ C * (a.1 + 1) ^ D := hCD a.1
    _ < a.1 ^ C * a.1 ^ (2 * D) :=
      Nat.mul_lt_mul_of_lt_of_le (C.lt_two_pow_self.trans_le (Nat.pow_le_pow_left h2 C))
        (by rw [pow_mul]; exact Nat.pow_le_pow_left hn D) (Nat.pos_of_ne_zero (by positivity))
    _ = a.1 ^ (C + 2 * D) := (pow_add _ _ _).symm
    _ ≤ a.1 ^ max v.maxArity (C + 2 * D) := Nat.pow_le_pow_right (by omega) (le_max_right _ _)

end Cslib.Logic.Vocabulary
