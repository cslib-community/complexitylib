/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Kilian.Soundness
public import Complexity.Computability.Complexity.Classes.NP
import Complexity.Computability.PCP.Completeness

/-!
# Kilian's arguments for NP

With the PCP theorem (`NP_subset_PCP_log`), every language `L ∈ NP` has a polynomial-time PCP
verifier `V` with `O(log n)` random bits and a constant number of queries. Kilian's protocol over
`V` and a collision-resistant `HashFamily` is then an interactive argument for `L`
(`exists_kilianSound_of_mem_NP`):

* the witnesses of the honest prover are the compact tables accepted by `V.tableVerifier`, and
  these characterize `L` (`x ∈ L` exactly when some table is accepted), so they form an NP relation
  for `L` (`PCP_log_subset_NP`); on them the honest prover is accepted with probability one and runs
  in polynomial time (`eval_kilianHonestGame`, `computableInPolyTime_kilianCommit`,
  `computableInPolyTime_kilianRespond`);
* the protocol is computationally sound (`HashFamily.kilianSound`).

**Gap.** The honest prover is efficient on this particular NP relation, not on an arbitrary given
NP relation for `L`: that would need a polynomial-time map from witnesses of the given relation to
PCP proofs (Barak and Goldreich's "relatively-efficient oracle-construction", [BarakGoldreich2001],
Definition 3.2), which the library's proof of the PCP theorem does not provide. Succinctness
(communication and verifier time) is not accounted for here.

## Main results

* `Cslib.Crypto.exists_kilianSound_of_mem_NP`: every language in NP has a Kilian argument.

## References

* [J. Kilian, *A note on efficient zero-knowledge proofs and arguments*][Kilian1992]
* [B. Barak, O. Goldreich, *Universal Arguments and their Applications*][BarakGoldreich2001]
-/

public section

namespace Cslib.Crypto

open Complexity

variable {α : Type} {H : List Bool → List Bool → List Bool}

/-- **Kilian's arguments for NP**: for a collision-resistant `HashFamily H`, every language `L` in
NP has a polynomial-time PCP verifier `V` with `O(log n)` random bits whose accepted compact tables
characterize `L`, such that Kilian's protocol over `V` and `H` accepts the honest prover on every
accepted table with probability one and is computationally sound for `L`. -/
theorem exists_kilianSound_of_mem_NP (hH : HashFamily H) {enc : α ↪ List Bool} {L : Set α}
    (hL : L ∈ NP enc) :
    ∃ (V : PCPVerifier α) (c : ℕ), V.PolyTime enc ∧
      (∀ x, V.coins x ≤ c * (Nat.log 2 (enc x).length + 1)) ∧
      (∀ x, x ∈ L ↔ ∃ table, V.tableVerifier (x, table) = true) ∧
      (∀ x table, V.tableVerifier (x, table) = true →
        ∀ n, ProbComp.eval (kilianHonestGame H V x table n) = PMF.pure true) ∧
      KilianSound H V enc L := by
  obtain ⟨V, c, d, hV, hpcp⟩ := NP_subset_PCP_log enc hL
  refine ⟨V, c, hV, hpcp.1, fun x => ⟨fun hx => ?_, fun ⟨table, htable⟩ => ?_⟩,
    fun x table htable n => eval_kilianHonestGame H V htable n, hH.kilianSound hV hpcp⟩
  · obtain ⟨proof, hproof⟩ := hpcp.2.2.1 x hx
    exact ⟨_, by simpa using PCPVerifier.tableVerifier_complete x proof [] hproof⟩
  · by_contra hx
    obtain ⟨proof, hproof⟩ := PCPVerifier.tableVerifier_sound x table htable
    have hs := hpcp.2.2.2 x hx proof
    have hc : acceptCount (fun y => V.accepts y.1 proof y.2) x (V.coins x) = 2 ^ V.coins x := by
      simp [acceptCount, hproof]
    rw [hc] at hs
    have hp : 0 < 2 ^ V.coins x := Nat.two_pow_pos _
    lia

end Cslib.Crypto
