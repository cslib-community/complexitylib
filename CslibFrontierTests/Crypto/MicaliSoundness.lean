/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Kilian.MicaliSoundness

/-!
# Tests for Micali's CS-proof soundness in the random oracle model

1. **Pure / fixed-trace soundness and dual collision extraction.** On the one-bit, two-address toy
   PCP verifier under `idHash`, a trace recording the opened paths of `honestProof` is
   collision-free, `micaliExtractCompactTable` recovers `[true, true]`, and
   `micaliVerifyPure_sound_of_traceCollisionFree` proves that `toyVerifier` accepts the extracted
   PCP proof on every Fiat–Shamir challenge. Under a colliding hash `collideLeafHash` that maps
   `[true]` to `[false]`, a forged Micali proof for the rejected table `[true, false]` is accepted
   by `micaliVerifyPure`, while `toyVerifier` rejects the first-recorded extracted proof on
   challenge `[true]`; `exists_collision_of_micaliVerifyPure_of_rejects` witnesses a concrete hash
   collision in the trace.
2. **Fiat–Shamir challenge union bound & two-stage ROM soundness.** For a PCP verifier
   `halfVerifier` whose soundness error is `1 / 2` per repetition against every candidate proof
   table, we check `toOuterMeasure_sampleList_accepts_le`,
   `toOuterMeasure_kilianChallenges_accepts_le`, `toOuterMeasure_run_memoize_not_fsTraceSound_le`,
   and `toOuterMeasure_twoStageMicali_le`.
3. **Adaptive two-channel ROM soundness, succinctness, and `NP` corollary.** We check
   `micaliExtractProof_cons_of_ne`, apply `micaliSoundness_bound` to an adaptive cheating prover
   that interleaves Merkle and Fiat–Shamir oracle calls, and instantiate
   `micaliProofBits_micaliProvePure_le` and `exists_micaliCSProof_of_mem_NP`.
-/

namespace ComplexityTests.Crypto.MicaliSoundness

open Cslib Cslib.Complexity Cslib.Crypto Cslib.Probability OracleComp
open scoped ENNReal

/-! ### Part 1: Pure / Fixed-Trace Soundness and Dual Collision Extraction -/

/-- Identity Merkle hash. -/
def idHash (x : List Bool) : List Bool := x

/-- Toy PCP verifier: one random bit chooses address `0` (on `false`) or `1` (on `true`), and the
bit read must be `true`. -/
def toyVerifier : PCPVerifier (List Bool) where
  coins _ := 1
  queries := fun (_, ρ) => [if ρ.headD false then 1 else 0]
  verdict := fun (_, answers) => answers == [true]

/-- The statement. -/
abbrev x : List Bool := [true, false]

/-- Deterministic Fiat–Shamir oracle returning both one-bit challenges `[[false], [true]]`. -/
def fixedFS : List Bool × List Bool → List (List Bool) := fun _ => [[false], [true]]

/-- Honest Micali proof on the accepted compact table `[true, true]`. -/
abbrev honestProof : MicaliProof :=
  micaliProvePure idHash fixedFS toyVerifier x [true, true]

/-- Record `(q, hTree q)` for every hash evaluation along the openings of `proof`. -/
def openingTrace (hTree : List Bool → List Bool) (proof : MicaliProof) :
    List (List Bool × List Bool) :=
  ((kilianOpenings toyVerifier x (fixedFS (x, proof.root)) proof.response).flatMap fun o =>
    (merkleInputs (fun _ => hTree) [] [o.2.1]
      (kilianPosition toyVerifier x o.1) o.2.2).map fun q => (q, hTree q)).eraseDups

abbrev trHonest : List (List Bool × List Bool) := openingTrace idHash honestProof

example : TraceConsistentWith idHash trHonest := by decide

example : TraceCollisionFree trHonest := by decide

example : AllOpeningsQueriedInTrace (fun _ => idHash) [] toyVerifier trHonest x
    (fixedFS (x, honestProof.root)) honestProof.response := by decide

-- Straight-line extraction recovers the compact table `[true, true]` and the full PCP proof bits at
-- addresses `0` and `1`.
example : micaliExtractCompactTable toyVerifier trHonest x honestProof.root = [true, true] := by
  decide

example : (micaliExtractProof toyVerifier trHonest x honestProof.root).getD 0 false = true := by
  decide

example : (micaliExtractProof toyVerifier trHonest x honestProof.root).getD 1 false = true := by
  decide

-- `micaliVerifyPure_sound_of_traceCollisionFree` and
-- `not_traceCollisionFree_or_accepts_of_micaliVerifyPure` certify that `toyVerifier` accepts the
-- extracted proof on both challenges `[false]` and `[true]`.
example : toyVerifier.accepts x
    (micaliExtractProof toyVerifier trHonest x honestProof.root) [false] = true :=
  micaliVerifyPure_sound_of_traceCollisionFree (hTree := idHash) (hFS := fixedFS)
    (by decide) (by decide) (by decide) (by decide) (by decide)

example : toyVerifier.accepts x
    (micaliExtractProof toyVerifier trHonest x honestProof.root) [true] = true :=
  micaliVerifyPure_sound_of_traceCollisionFree (hTree := idHash) (hFS := fixedFS)
    (by decide) (by decide) (by decide) (by decide) (by decide)

example : ¬ TraceCollisionFree trHonest ∨
    ∀ ρ ∈ fixedFS (x, honestProof.root), ρ.length = toyVerifier.coins x →
      toyVerifier.accepts x (micaliExtractProof toyVerifier trHonest x honestProof.root) ρ =
        true :=
  not_traceCollisionFree_or_accepts_of_micaliVerifyPure (hTree := idHash) (hFS := fixedFS)
    (by decide) (by decide)

/-- A colliding leaf hash that maps `[true]` to `[false]` and acts as the identity elsewhere. -/
def collideLeafHash (q : List Bool) : List Bool :=
  if q == [true] then [false] else q

/-- Under `collideLeafHash`, the rejected table `[false, false]` has the same Merkle root and
authentication paths as `[true, true]`, so a cheating prover can open positions `0` and `1` as
`true`. -/
abbrev forgedProof : MicaliProof :=
  ⟨kilianCommit (fun _ => collideLeafHash) toyVerifier [] x [false, false],
   [[(true, merklePath (fun _ => collideLeafHash) [] [[false], [false]] 0)],
    [(true, merklePath (fun _ => collideLeafHash) [] [[false], [false]] 1)]]⟩

/-- Trace recording the honest `[false, false]` tree queries followed by the colliding `[true]`
openings. -/
abbrev trCollide : List (List Bool × List Bool) :=
  openingTrace collideLeafHash
    (micaliProvePure collideLeafHash fixedFS toyVerifier x [false, false]) ++
    openingTrace collideLeafHash forgedProof

example : TraceConsistentWith collideLeafHash trCollide := by decide

example : AllOpeningsQueriedInTrace (fun _ => collideLeafHash) [] toyVerifier trCollide x
    (fixedFS (x, forgedProof.root)) forgedProof.response := by decide

example : micaliVerifyPure collideLeafHash fixedFS toyVerifier x forgedProof = true := by decide

-- Because `trCollide` records `[false]` before `[true]` for both leaves, the extracted compact
-- table is `[false, false]`, which `toyVerifier` rejects on challenge `[true]`.
example : micaliExtractCompactTable toyVerifier trCollide x forgedProof.root = [false, false] := by
  decide

example : toyVerifier.accepts x
    (micaliExtractProof toyVerifier trCollide x forgedProof.root) [true] = false := by decide

-- `exists_collision_of_micaliVerifyPure_of_rejects` extracts a concrete hash collision in
-- `trCollide`.
example : ∃ q₁ ∈ trCollide.map Prod.fst, ∃ q₂ ∈ trCollide.map Prod.fst,
    q₁ ≠ q₂ ∧ collideLeafHash q₁ = collideLeafHash q₂ :=
  exists_collision_of_micaliVerifyPure_of_rejects (H := fun _ => collideLeafHash) (k := [])
    (hFS := fixedFS) (V := toyVerifier) (tr := trCollide) (x := x) (proof := forgedProof)
    (ρ := [true]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ### Part 2: Fiat–Shamir Challenge Union Bound & Two-Stage ROM Soundness -/

/-- A one-coin, one-query PCP verifier that accepts iff the single bit read at address `0` equals
the challenge bit `ρ.headD false`. Every candidate proof table is accepted on exactly `1` of the `2`
possible challenge strings, so its soundness error is `1 / 2`. -/
def halfVerifier : PCPVerifier (List Bool) where
  coins _ := 1
  queries := fun _ => [0]
  verdict := fun ((_, ρ), answers) => answers == [ρ.headD false]

theorem halfVerifier_sound (s : List Bool) (π : List Bool) :
    2 * acceptCount (fun y => halfVerifier.accepts y.1 π y.2) s (halfVerifier.coins s) ≤
      2 ^ halfVerifier.coins s := by
  change 2 * (Finset.univ.filter fun w : Fin 1 → Bool =>
    ([π.getD 0 false] == [(List.ofFn w).headD false]) = true).card ≤ 2 ^ 1
  generalize π.getD 0 false = b
  cases b <;> decide

example (π : List Bool) :
    (ProbComp.eval (BitString.sampleList (halfVerifier.coins x))).toOuterMeasure
      {ρ | halfVerifier.accepts x π ρ = true} ≤ 1 / 2 :=
  toOuterMeasure_sampleList_accepts_le halfVerifier (halfVerifier_sound x π)

example (m : ℕ) (π : List Bool) :
    (ProbComp.eval (kilianChallenges halfVerifier m x)).toOuterMeasure
      {ρs | ∀ ρ ∈ ρs, halfVerifier.accepts x π ρ = true} ≤ (1 / 2) ^ m :=
  toOuterMeasure_kilianChallenges_accepts_le halfVerifier m (halfVerifier_sound x π)

/-- A two-query Fiat–Shamir program querying `(x, [false])` and `(x, [true])`. -/
def twoFSQueriesProg : OracleComp (MicaliFSSpec (List Bool)) (List (List Bool)) := do
  let _ ← query (spec := MicaliFSSpec (List Bool)) (x, [false])
  query (spec := MicaliFSSpec (List Bool)) (x, [true])

theorem isQueryBounded_twoFSQueriesProg : IsQueryBounded twoFSQueriesProg 2 :=
  .liftBind _ _ 1 fun _ => .liftBind _ _ 0 fun _ => .pure _ 0

example (m : ℕ) (tr : List (List Bool × List Bool)) :
    ((OracleComp.interpret
      (memoize (fun q : List Bool × List Bool =>
        ProbComp.eval (kilianChallenges halfVerifier m q.1)))
      twoFSQueriesProg).run []).toOuterMeasure
      {out | ¬ FSTraceSound halfVerifier ∅ tr out.2} ≤ (2 : ℝ≥0∞) * (1 / 2) ^ m :=
  toOuterMeasure_run_memoize_not_fsTraceSound_le halfVerifier ∅ m tr
    (fun s _ π => halfVerifier_sound s π) isQueryBounded_twoFSQueriesProg

/-! ### Part 3: Adaptive Two-Channel ROM Soundness & Succinctness -/

-- Prepending a Merkle query whose digest avoids existing root/child digests leaves
-- `micaliExtractProof` unchanged.
example : micaliExtractProof toyVerifier (([true, true], [true, true, true]) :: trHonest)
    x honestProof.root = micaliExtractProof toyVerifier trHonest x honestProof.root :=
  micaliExtractProof_cons_of_ne toyVerifier trHonest [true, true] x (by decide) (by decide)

/-- A concrete adaptive cheating prover that makes a Merkle query, uses the digest as a Fiat–Shamir
root query, makes another Merkle query, and outputs a fixed candidate proof. -/
def adaptiveCheatingProver : OracleComp (MicaliSpec (List Bool)) (List Bool × MicaliProof) := do
  let rt ← query (spec := MicaliSpec (List Bool)) (.inl [false])
  let _ ← query (spec := MicaliSpec (List Bool)) (.inr (x, rt))
  let sib ← query (spec := MicaliSpec (List Bool)) (.inl [true])
  return (x, { root := rt, response := [[(false, [sib])]] })

theorem isCostBounded_FS_adaptiveCheatingProver :
    IsCostBounded micaliFSCost adaptiveCheatingProver 1 :=
  IsCostBounded.liftBind (cost := micaliFSCost) (Sum.inl [false]) _ 1 fun rt =>
    IsCostBounded.liftBind (cost := micaliFSCost) (Sum.inr (x, rt)) _ 0 fun _ =>
      IsCostBounded.liftBind (cost := micaliFSCost) (Sum.inl [true]) _ 0 fun sib =>
        IsCostBounded.pure (cost := micaliFSCost)
          (x, MicaliProof.mk rt [[(false, [sib])]]) 0

theorem isCostBounded_MT_adaptiveCheatingProver :
    IsCostBounded micaliMTCost adaptiveCheatingProver 2 :=
  IsCostBounded.liftBind (cost := micaliMTCost) (Sum.inl [false]) _ 1 fun rt =>
    IsCostBounded.liftBind (cost := micaliMTCost) (Sum.inr (x, rt)) _ 1 fun _ =>
      IsCostBounded.liftBind (cost := micaliMTCost) (Sum.inl [true]) _ 0 fun sib =>
        IsCostBounded.pure (cost := micaliMTCost)
          (x, MicaliProof.mk rt [[(false, [sib])]]) 0

/-- The supplied single opening is hashed at most twice, regardless of the FS answer. -/
theorem isCostBounded_MT_halfVerifier (rt sib : List Bool) :
    IsCostBounded micaliMTCost
      (micaliVerify halfVerifier x { root := rt, response := [[(false, [sib])]] }) 2 := by
  unfold micaliVerify
  refine IsCostBounded.liftBind (cost := micaliMTCost) (Sum.inr (x, rt)) _ 2 ?_
  intro challenges
  apply isCostBounded_micaliMTCost_liftLeft
  cases challenges with
  | nil => exact .pure _ 2
  | cons ρ ρs =>
      simp only [kilianVerifyProg, List.zip_cons_cons, List.zip_nil_right,
        List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind]
      exact .liftBind _ _ 1 fun _ => .liftBind _ _ 0 fun _ => .pure _ 0

/-- Every possible output has the bounded shape actually emitted by the adaptive prover. -/
theorem isCostBounded_MT_verifier_of_mem_support_adaptiveCheatingProver
    (s : List Bool) (proof : MicaliProof) (hmem : (s, proof) ∈ adaptiveCheatingProver.support) :
    IsCostBounded micaliMTCost (micaliVerify halfVerifier s proof) 2 := by
  simp only [adaptiveCheatingProver, mem_supportWith_bind_iff, supportWith_query,
    Set.mem_univ, true_and, supportWith_pure, Set.mem_singleton_iff] at hmem
  obtain ⟨rt, _, sib, h⟩ := hmem
  cases h
  exact isCostBounded_MT_halfVerifier rt sib

/-- Two prover hashes and at most two verifier hashes give a genuine total budget of four. -/
theorem isCostBounded_MT_soundness_adaptiveCheatingProver :
    IsCostBounded micaliMTCost (micaliSoundnessProg halfVerifier ∅ adaptiveCheatingProver) 4 :=
  isCostBounded_micaliMTCost_micaliSoundnessProg halfVerifier ∅
    isCostBounded_MT_adaptiveCheatingProver
    isCostBounded_MT_verifier_of_mem_support_adaptiveCheatingProver

-- Honest proof payload bit length and succinctness bound.
example : micaliProofBits honestProof = 8 := by decide

example : micaliProofBits
    (micaliProvePure (fun y => y.take 2 ++ List.replicate (2 - y.length) false)
      fixedFS toyVerifier x [true, true]) ≤
    2 + 2 * (1 * (1 + (toyVerifier.coins x + Nat.clog 2 1) * 2)) :=
  micaliProofBits_micaliProvePure_le
    (hlen := fun y => by
      have : y.length ≤ 2 ∨ 2 ≤ y.length := le_total y.length 2
      rcases this with h | h <;> simp [h])
    (hm := rfl)
    (hρs := by decide)
    (hq := fun _ _ => le_rfl)

-- Instantiating the adaptive two-channel ROM soundness theorems and the `NP` CS-proof corollary.
example (σ m : ℕ) :
    micaliSoundnessGame halfVerifier ∅ adaptiveCheatingProver σ m true ≤
      ((1 + 1 : ℕ) : ℝ≥0∞) * (1 / 2) ^ m +
        (4 : ℝ≥0∞) * (((3 * 4 + (1 + 1) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  micaliSoundness_bound halfVerifier ∅ σ m (fun s _ π => halfVerifier_sound s π)
    isCostBounded_FS_adaptiveCheatingProver isCostBounded_MT_soundness_adaptiveCheatingProver

example (σ m : ℕ) :
    micaliSoundnessGame halfVerifier ∅ adaptiveCheatingProver σ m true ≤
      ((1 + 1 : ℕ) : ℝ≥0∞) * (1 / 2) ^ m +
        ((2 + 2 : ℕ) : ℝ≥0∞) *
          (((3 * (2 + 2) + (1 + 1) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  micaliSoundness_bound_of_prover_verifier halfVerifier ∅ σ m
    (fun s _ π => halfVerifier_sound s π)
    isCostBounded_MT_adaptiveCheatingProver isCostBounded_FS_adaptiveCheatingProver
    isCostBounded_MT_verifier_of_mem_support_adaptiveCheatingProver

example {enc : List Bool ↪ List Bool} {L : Set (List Bool)} (hL : L ∈ NP enc) :
    ∃ (V : PCPVerifier (List Bool)) (c d : ℕ),
      V.PolyTime enc ∧
      (∀ s, V.coins s ≤ c * (Nat.log 2 (enc s).length + 1)) ∧
      (∀ s ρ, ρ.length = V.coins s → (V.queries (s, ρ)).length ≤ d) ∧
      (∀ s, s ∈ L ↔ ∃ table, V.tableVerifier (s, table) = true) ∧
      (∀ s table, V.tableVerifier (s, table) = true →
        ∀ σ m, micaliHonestGame V s table σ m = PMF.pure true) ∧
      (∀ (P : OracleComp (MicaliSpec (List Bool)) (List Bool × MicaliProof))
         (t_FS Q_MT σ m : ℕ),
        IsCostBounded micaliFSCost P t_FS →
        IsCostBounded micaliMTCost (micaliSoundnessProg V L P) Q_MT →
        micaliSoundnessGame V L P σ m true ≤
          ((t_FS + 1 : ℕ) : ℝ≥0∞) * (1 / 2) ^ m +
            (Q_MT : ℝ≥0∞) *
              (((3 * Q_MT + (t_FS + 1) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ))) ∧
      (∃ C : ℕ, ∀ (σ m : ℕ) (hTree : List Bool → List Bool)
          (hFS : List Bool × List Bool → List (List Bool)) (s : List Bool) (table : List Bool),
        (∀ y, (hTree y).length = σ) →
        (hFS (s, kilianCommit (fun _ => hTree) V [] s table)).length = m →
        (∀ ρ ∈ hFS (s, kilianCommit (fun _ => hTree) V [] s table), ρ.length = V.coins s) →
        micaliProofBits (micaliProvePure hTree hFS V s table) ≤
          C * (σ + m + 1) ^ 2 * (Nat.log 2 (enc s).length + 1)) :=
  exists_micaliCSProof_of_mem_NP hL

end ComplexityTests.Crypto.MicaliSoundness
