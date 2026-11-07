/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.BlumComplexity.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Recursive relatedness of Blum complexity measures

Any two Blum complexity measures `Φ` and `Ψ` on the same numbering are *recursively related*
[Blum, *A machine-independent theory of the complexity of recursive functions*][Blum1967]. There is
a computable `r` such that, for every program `c`, `Ψ c n ≤ r n (Φ c n)` and
`Φ c n ≤ r n (Ψ c n)` for all sufficiently large `n`. So a theorem proved for one measure transfers
to every other measure, up to a computable distortion.

The bound `r n m` is the least `B` such that, for each program numbered at most `n`, a cost `m` in
one measure implies a cost at most `B` in the other. Such a `B` exists because Blum's first axiom
makes both costs defined together. The search for it is decidable by Blum's second axiom.

## Main results

* `Cslib.BlumComplexity.BlumMeasure.recursively_related`: any two complexity measures are
  recursively related.

## References

* [M. Blum, *A machine-independent theory of the complexity of recursive functions*][Blum1967]
-/

public section

namespace Cslib.BlumComplexity.BlumMeasure

open Encodable Denumerable Nat.Partrec Filter

/-- **Recursive relatedness** [Blum1967]: for any two complexity measures `Φ` and `Ψ` there is a
computable `r` with `Ψ c n ≤ r n (Φ c n)` and `Φ c n ≤ r n (Ψ c n)` for every program `c` and all
sufficiently large `n` (here, all `n ≥ encode c`). -/
theorem recursively_related (Φ Ψ : BlumMeasure) :
    ∃ r : ℕ → ℕ → ℕ, Computable₂ r ∧ ∀ c : Code, ∀ᶠ n in atTop,
      ∀ m ∈ Φ.cost c n, ∀ m' ∈ Ψ.cost c n, m' ≤ r n m ∧ m ≤ r n m' := by
  classical
  -- `R (n, m) B`: for each program numbered `≤ n`, a cost `m` on `n` in one measure implies a
  -- cost `≤ B` on `n` in the other.
  let R : ℕ × ℕ → ℕ → Prop := fun x B =>
    ∀ i < x.1 + 1,
      (x.2 ∈ Φ.cost (ofNat Code i) x.1 → ∃ m' < B + 1, m' ∈ Ψ.cost (ofNat Code i) x.1) ∧
      (x.2 ∈ Ψ.cost (ofNat Code i) x.1 → ∃ m' < B + 1, m' ∈ Φ.cost (ofNat Code i) x.1)
  have hex : ∀ x, ∃ B, R x B := by
    rintro ⟨n, m⟩
    have hb : ∀ i, ∃ b,
        (m ∈ Φ.cost (ofNat Code i) n → ∃ m' < b + 1, m' ∈ Ψ.cost (ofNat Code i) n) ∧
        (m ∈ Ψ.cost (ofNat Code i) n → ∃ m' < b + 1, m' ∈ Φ.cost (ofNat Code i) n) := by
      intro i
      by_cases hd : ((ofNat Code i).eval n).Dom
      · have hΦ := (Φ.dom_cost_iff _ _).2 hd
        have hΨ := (Ψ.dom_cost_iff _ _).2 hd
        exact ⟨(Ψ.cost (ofNat Code i) n).get hΨ + (Φ.cost (ofNat Code i) n).get hΦ,
          fun _ => ⟨_, by omega, Part.get_mem hΨ⟩, fun _ => ⟨_, by omega, Part.get_mem hΦ⟩⟩
      · exact ⟨0, fun h => absurd ((Φ.dom_cost_iff _ _).1 (Part.dom_iff_mem.2 ⟨m, h⟩)) hd,
          fun h => absurd ((Ψ.dom_cost_iff _ _).1 (Part.dom_iff_mem.2 ⟨m, h⟩)) hd⟩
    choose b hb using hb
    refine ⟨∑ i ∈ Finset.range (n + 1), b i, fun i hi => ?_⟩
    have hle : b i ≤ ∑ i ∈ Finset.range (n + 1), b i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hi)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨m', hm', h'⟩ := (hb i).1 h
      exact ⟨m', by omega, h'⟩
    · obtain ⟨m', hm', h'⟩ := (hb i).2 h
      exact ⟨m', by omega, h'⟩
  have hR : ComputablePred fun x : (ℕ × ℕ) × ℕ => R x.1 x.2 := by
    refine ComputablePred.forall_lt
      (p := fun (y : (ℕ × ℕ) × ℕ) i =>
        (y.1.2 ∈ Φ.cost (ofNat Code i) y.1.1 →
          ∃ m' < y.2 + 1, m' ∈ Ψ.cost (ofNat Code i) y.1.1) ∧
        (y.1.2 ∈ Ψ.cost (ofNat Code i) y.1.1 →
          ∃ m' < y.2 + 1, m' ∈ Φ.cost (ofNat Code i) y.1.1))
      ?_ (Computable.succ.comp (Computable.fst.comp Computable.fst))
    have hcode : Computable fun z : ((ℕ × ℕ) × ℕ) × ℕ => ofNat Code z.2 :=
      (Computable.ofNat Code).comp Computable.snd
    have hn : Computable fun z : ((ℕ × ℕ) × ℕ) × ℕ => z.1.1.1 :=
      Computable.fst.comp (Computable.fst.comp Computable.fst)
    have hm : Computable fun z : ((ℕ × ℕ) × ℕ) × ℕ => z.1.1.2 :=
      Computable.snd.comp (Computable.fst.comp Computable.fst)
    have hB : Computable fun z : ((ℕ × ℕ) × ℕ) × ℕ => z.1.2 + 1 :=
      Computable.succ.comp (Computable.snd.comp Computable.fst)
    have hex' : ∀ M : BlumMeasure, ComputablePred fun z : ((ℕ × ℕ) × ℕ) × ℕ =>
        ∃ m' < z.1.2 + 1, m' ∈ M.cost (ofNat Code z.2) z.1.1.1 := fun M =>
      ComputablePred.exists_lt
        (p := fun (z : ((ℕ × ℕ) × ℕ) × ℕ) m' => m' ∈ M.cost (ofNat Code z.2) z.1.1.1)
        (M.computablePred_mem_cost_comp (hcode.comp Computable.fst) (hn.comp Computable.fst)
          Computable.snd) hB
    exact ((Φ.computablePred_mem_cost_comp hcode hn hm).imp (hex' Ψ)).and
      ((Ψ.computablePred_mem_cost_comp hcode hn hm).imp (hex' Φ))
  refine ⟨fun n m => Nat.find (hex (n, m)), Computable.find hR hex, fun c => ?_⟩
  filter_upwards [eventually_ge_atTop (encode c)] with n hn m hm m' hm'
  have h1 := (Nat.find_spec (hex (n, m))) (encode c) (Nat.lt_succ_of_le hn)
  have h2 := (Nat.find_spec (hex (n, m'))) (encode c) (Nat.lt_succ_of_le hn)
  simp only [ofNat_encode] at h1 h2
  obtain ⟨k, hk, hk'⟩ := h1.1 hm
  obtain ⟨k', hk2, hk2'⟩ := h2.2 hm'
  rw [Part.mem_unique hm' hk'] at *
  rw [Part.mem_unique hm hk2'] at *
  omega

end Cslib.BlumComplexity.BlumMeasure
