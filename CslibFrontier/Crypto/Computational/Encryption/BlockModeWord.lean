/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.RandomFunctionHybrid
public import CslibFrontier.Crypto.Computational.Encryption.SymmetricCPA
public import CslibFrontier.Foundations.Data.BitString.PadBlocks
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount
import CslibFrontier.Languages.Probabilistic.QueryCount.Scale

/-!
# Word requests as block-mode queries

In the asymptotic CPA game `symmetricCPAGameOn blockPairValid`, an adversary at parameter `n`
submits pairs of words. `blockModeWordAdversary adversary n` reads it as a `BlockModeAdversary n`
for the typed experiments of `RandomFunctionHybrid.lean`. An admissible request `(m₀, m₁)` becomes
the query made of their `n`-bit blocks (`BitString.padBlocks`); the answer `(iv, cs)` is flattened
back into the word `iv ++ cs`. Inadmissible requests are answered with `[]` and no query. Word-level
reductions for block modes are compared with the typed reductions through this adapter, which
inherits a block budget from the word adversary's query budget.

## Main definitions

* `Cslib.Crypto.blockModeWordQuery`: one word request as a block-mode query.
* `Cslib.Crypto.blockModeWordAdversary`: a word adversary as a block-mode adversary.

## Main results

* `Cslib.Crypto.blockModeSelect_padBlocks`: an admissible pair of at most `ℓ` blocks selects the
  blocks of the chosen message.
* `Cslib.Crypto.isCostBounded_blockModeWordAdversary`: `Q` requests ask for at most `Q * ℓ`
  blocks when the queries are capped at `ℓ` blocks each.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- One word request as a block-mode query: an admissible pair is sent as the `n`-bit blocks of
both messages, and the answer `(iv, cs)` is returned as the word `iv ++ cs`. An inadmissible
request is answered with `[]` and no query. -/
@[expose]
def blockModeWordQuery (n : ℕ) (request : Unit × List Bool) :
    ProbOracleComp (BlockModeSpec n) (List Bool) :=
  let m0 := unframe request.2
  let m1 := dropFrame request.2
  if blockPairValid n m0 m1 then
    (fun answer : BitString n × List (BitString n) =>
        List.ofFn answer.1 ++ answer.2.flatMap List.ofFn) <$>
      ProbOracleComp.query (spec := BlockModeSpec n)
        (BitString.padBlocks n m0.length m0, BitString.padBlocks n m1.length m1)
  else
    pure []

/-- A word CPA adversary at parameter `n`, with empty auxiliary input, as a block-mode adversary.
-/
@[expose]
noncomputable def blockModeWordAdversary (adversary : OracleDistinguisher) (n : ℕ) :
    BlockModeAdversary n :=
  ProbOracleComp.simulate (blockModeWordQuery n) (adversary n [])

/-- An admissible pair whose messages have at most `ℓ` blocks selects the blocks of the message
chosen by `bit`. -/
theorem blockModeSelect_padBlocks {n ℓ : ℕ} {m₀ m₁ : List Bool} (bit : Bool)
    (hvalid : blockPairValid n m₀ m₁ = true) (hℓ : m₀.length / n ≤ ℓ) :
    blockModeSelect ℓ bit
        (BitString.padBlocks n m₀.length m₀, BitString.padBlocks n m₁.length m₁) =
      BitString.padBlocks n (if bit then m₁ else m₀).length (if bit then m₁ else m₀) := by
  have hlen : m₀.length = m₁.length := by
    simpa [blockPairValid] using ((Bool.and_eq_true _ _).mp hvalid).1
  have hcond : (BitString.padBlocks n m₀.length m₀).length =
      (BitString.padBlocks n m₁.length m₁).length ∧
      (BitString.padBlocks n m₀.length m₀).length ≤ ℓ := by
    rw [BitString.length_padBlocks, BitString.length_padBlocks, ← hlen]
    exact ⟨rfl, hℓ⟩
  rw [blockModeSelect, ite_eq_left hcond]
  cases bit <;> rfl

/-- If the word adversary makes at most `Q` requests, the block-mode adversary asks for at most
`Q * ℓ` blocks, counting each query's blocks only up to the cap `ℓ` as `blockModeCost ℓ` does. -/
theorem isCostBounded_blockModeWordAdversary {adversary : OracleDistinguisher} {n Q : ℕ}
    (hQ : (adversary n []).IsQueryBounded Q) (ℓ : ℕ) :
    OracleComp.IsCostBounded (blockModeCost ℓ) (blockModeWordAdversary adversary n) (Q * ℓ) := by
  have h : OracleComp.IsCostBounded (Sum.elim (fun _ => 0) fun _ => ℓ) (adversary n []) (Q * ℓ) :=
    hQ.mul_of_le fun q => by cases q <;> simp
  refine ProbOracleComp.isCostBounded_simulate (cost := fun _ => ℓ) (fun request => ?_) h
  unfold blockModeWordQuery
  dsimp only
  split
  · rw [OracleComp.isCostBounded_map_iff]
    exact (ProbOracleComp.isCostBounded_query _ _).mono (blockModeBlocks_le ℓ _)
  · exact OracleComp.IsCostBounded.pure _ ℓ

end Cslib.Crypto
