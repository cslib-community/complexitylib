/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Kilian.Soundness
public import Complexity.Crypto.Computational.Kilian.Succinct
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
* the protocol is computationally sound (`HashFamily.kilianSound`);
* the honest transcript after the statement has `O(n² · (log₂ |enc x| + 1))` payload bits at
  security parameter `n` (`kilianCommunication_honest_le_log`).

**Gap.** The honest prover is efficient on this particular NP relation, not on an arbitrary given
NP relation for `L`: that would need a polynomial-time map from witnesses of the given relation to
PCP proofs (Barak and Goldreich's "relatively-efficient oracle-construction", [BarakGoldreich2001],
Definition 3.2), which the library's proof of the PCP theorem does not provide.

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
accepted table with probability one, is computationally sound for `L`, and has honest transcripts
of `O(n² · (log₂ |enc x| + 1))` payload bits at security parameter `n`. -/
theorem exists_kilianSound_of_mem_NP (hH : HashFamily H) {enc : α ↪ List Bool} {L : Set α}
    (hL : L ∈ NP enc) :
    ∃ (V : PCPVerifier α) (c : ℕ), V.PolyTime enc ∧
      (∀ x, V.coins x ≤ c * (Nat.log 2 (enc x).length + 1)) ∧
      (∀ x, x ∈ L ↔ ∃ table, V.tableVerifier (x, table) = true) ∧
      (∀ x table, V.tableVerifier (x, table) = true →
        ∀ n, ProbComp.eval (kilianHonestGame H V x table n) = PMF.pure true) ∧
      KilianSound H V enc L ∧
      ∃ C : ℕ, ∀ (n : ℕ) (k : List Bool) (x : α) (table : List Bool) (ρs : List (List Bool)),
        k.length = n → ρs.length = n → (∀ ρ ∈ ρs, ρ.length = V.coins x) →
          kilianCommunication k (kilianCommit H V k x table) ρs
            (kilianRespond H V k x table ρs) ≤
          C * (n + 1) ^ 2 * (Nat.log 2 (enc x).length + 1) := by
  obtain ⟨V, c, d, hV, hpcp⟩ := NP_subset_PCP_log enc hL
  refine ⟨V, c, hV, hpcp.1, fun x => ⟨fun hx => ?_, fun ⟨table, htable⟩ => ?_⟩,
    fun x table htable n => eval_kilianHonestGame H V htable n, hH.kilianSound hV hpcp,
    _, fun n k x table ρs hk hn hρs => kilianCommunication_honest_le_log hH.length_eq hk hn hρs
      (fun ρ hρ => hpcp.2.1 x ρ hρ) (hpcp.1 x)⟩
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
