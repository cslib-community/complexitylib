/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Oracle.Replay
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Computability.Probabilistic.PPT

/-!
# Saved coins independent of a generated auxiliary input

A strict-PPT generator bounds its supported public inputs. Substituting this bound into an oracle
machine's clock gives one polynomial coin budget depending only on the security parameter.
Replay still truncates the supplied tape at the original input-dependent clock. This padding
preserves the joint output and external state, without fixing the randomness of the handler.

## Main results

* `Cslib.Probability.IsOraclePPT.exists_savedCoins_of_keyGen`: key-independent padding derived
  from an actual strict-PPT key generator, with the original efficient full-input replay.

## References

Original padding consequence of `IsOraclePPTOn.exists_savedCoins` and `IsPPTOn.length_le`.
-/

public section

namespace Cslib.Probability

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM

/-- Generate the auxiliary word by an actual strict-PPT program, then use a coin law independent
of that word. The prefix cutoff remains the original machine clock. The replay equality holds
for every key satisfying the derived size bound and every stateful handler. -/
theorem IsOraclePPT.exists_savedCoins_of_keyGen {Operation Key β : Type}
    [DecidableEq Operation] {keyEncoding : Key ↪ List Bool} {output : β ↪ List Bool}
    {gen : ℕ → ProbComp (List Bool × Key)}
    (hgen : IsPPTOn encUnary (encPair encBits keyEncoding) gen)
    {program : ℕ → List Bool → WordOracleComp Operation β}
    (h : IsOraclePPT output program) :
    ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM k Bool Control Operation) (c d keyC keyD : ℕ),
      (∀ n keys, keys ∈ (ProbComp.eval (gen n)).support →
        keys.1.length ≤ keyC * (n + 1) ^ keyD) ∧
      IsOraclePPTOn (encPair encBits encBits) encBits
        (fun p : List Bool × List Bool =>
          machine.runCoins (fun op word => ProbOracleComp.query (op, word)) p.1 p.2) ∧
      (∀ n pk, pk.length ≤ keyC * (n + 1) ^ keyD →
        c * ((encPair encUnary encBits (n, pk)).length + 1) ^ d ≤
          c * (2 * n + 2 + keyC * (n + 1) ^ keyD) ^ d) ∧
      ∀ n pk, pk.length ≤ keyC * (n + 1) ^ keyD →
        ∀ (Store : Type) (oracle : Operation × List Bool → StateT Store PMF (List Bool)) s,
        ProbOracleComp.runWith oracle (output <$> program n pk) s =
          (BitString.uniformList (c * (2 * n + 2 + keyC * (n + 1) ^ keyD) ^ d)).bind
            (fun coins => ProbOracleComp.runWith oracle
                (machine.runCoins (fun op word => ProbOracleComp.query (op, word))
                  (coins.take (c * ((encPair encUnary encBits (n, pk)).length + 1) ^ d))
                  (encPair encUnary encBits (n, pk))) s) := by
  obtain ⟨keyC, keyD, hkeys⟩ := hgen.length_le
  obtain ⟨k, Control, hfinite, machine, c, d, hefficient, hrun⟩ := h.on.exists_savedCoins
  have hbound (n : ℕ) (pk : List Bool) (hpk : pk.length ≤ keyC * (n + 1) ^ keyD) :
      c * ((encPair encUnary encBits (n, pk)).length + 1) ^ d ≤
        c * (2 * n + 2 + keyC * (n + 1) ^ keyD) ^ d := by
    apply Nat.mul_le_mul_left c
    apply Nat.pow_le_pow_left
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
    omega
  refine ⟨k, Control, hfinite, machine, c, d, keyC, keyD, ?_, hefficient, hbound, ?_⟩
  · intro n keys hkeys'
    have hk := hkeys n keys hkeys'
    simp only [encUnary_apply, List.length_replicate] at hk
    exact (length_le_encPair_left encBits keyEncoding keys).trans hk
  · intro n pk hpk Store oracle s
    rw [hrun (n, pk) Store oracle s,
      ← BitString.uniformList_take (hbound n pk hpk), PMF.bind_map]
    rfl

end Cslib.Probability
