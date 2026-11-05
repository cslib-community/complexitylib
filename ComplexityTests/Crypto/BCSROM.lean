/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Protocols.BCS.ROM
import Complexity.Languages.Probabilistic.QueryCount.Support
import Complexity.Probability.PMF.UniformBound

/-!
# Tests for BCS ROM soundness and straight-line knowledge soundness

Exercises a concrete two-round (`r = 2`), depth-one (`d = 1`) public-coin IOP `romIOP` under the
two-channel BCS random-oracle transform (`Complexity.Crypto.Protocols.BCS.ROM`):
1. **Transcript-chained Fiat–Shamir simulation and completeness.** Evaluates `chainedFSChallenges`,
   `bcsProveROM`, `bcsVerifyROM`, and `bcsHonestROMProg` via `OracleComp.evalPure` on concrete
   deterministic channels, verifies agreement with `bcsProve` / `bcsVerify` under `chainedFS`, and
   instantiates `bcsHonestROMGame_eq_pure_true`.
2. **Straight-line multi-round extraction, extension invariance, and dual collision extraction.**
   On a full prover Merkle trace `trProver` under an injective hash `idTreeHash`,
   `bcsExtractWitness` recovers the committed witness `(true, true)` straight-line with
   `defaultSym = false` (whereas an empty trace falls back to `(false, false)`),
   `iopVerify_bcsExtractOracles_of_bcsVerify` certifies acceptance of the extracted tables, and
   `bcsExtractOracles_cons_of_ne` checks trace-extension invariance. Under a leaf-colliding hash
   `collideLeafHash`, a forged proof passes `bcsVerify` while `iopVerify` rejects
   `bcsExtractOracles`, and `exists_collision_of_bcsVerify_of_iopVerify_eq_false` extracts a hash
   collision from the trace.
3. **Adaptive out-of-order cheating prover and two-channel ROM soundness & knowledge soundness.**
   Proves `IOPRoundByRoundKnowledgeSoundness` for `romIOP` with exact escape bound `1 / 2`, defines
   an adaptive cheating prover `adaptiveBCSCheater` making out-of-order Fiat–Shamir queries, an
   oversized 5-root Fiat–Shamir query, and adaptive Merkle queries, discharges tight prover and
   `P.support`-restricted verifier query budgets, and instantiates `bcsROMSoundness_bound`,
   `bcsROMSoundness_bound_of_prover_verifier`, `bcsROMKnowledgeSoundness_trace_bound`,
   `bcsROMKnowledgeSoundness_bound`, and `bcsROMKnowledgeSoundness_bound_of_prover_verifier`,
   including a concrete larger-alphabet instantiation (`Chal = Fin 64`, `σ = 16`) with final
   soundness and knowledge-soundness error strictly `< 1 / 3 < 1`.
-/

namespace ComplexityTests.Crypto.BCSROM

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.BCS Cslib.Probability Cslib.OracleComp
open Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ### Protocol Setup: Concrete 2-Round, Depth-1 Public-Coin IOP -/

/-- Encode a single-bit IOP symbol as a one-bit Merkle leaf. -/
def encSym (b : Bool) : List Bool := [b]

/-- Decode a Merkle leaf bitstring back to a single-bit IOP symbol. -/
def decSym (bs : List Bool) : Bool := bs.headD false

theorem decSym_encSym : Function.LeftInverse decSym encSym := by
  intro b
  rfl

/-- Witness relation on `Stmt = Bool × Bool` and `Wit = Bool × Bool`: `s = (claimFlag, target)` is
valid (`claimFlag = true`) and both witness coordinates equal `target`. Statements `(false, target)`
have no valid witness, providing concrete false statements outside `{s | ∃ w, romRel s w}`. -/
def romRel (s w : Bool × Bool) : Prop :=
  s.1 = true ∧ w.1 = s.2 ∧ w.2 = s.2

/-- Concrete 2-round (`r = 2`), depth-1 (`d = 1`) public-coin IOP for `romRel`:
* Round `0` commits to `(w.1, w.2)` at indices `0` and `1`.
* Round `1` receives challenge `c₀` and commits to `(xor w.1 c₀, xor w.2 c₀)`.
* Verifier queries index `c₀` in round `0` and index `c₁` in round `1`, checking `s.1 = true` and
  answers `[s.2, xor s.2 c₀]`. -/
def romIOP : PublicCoinIOP 2 1 (Bool × Bool) (Bool × Bool) Bool Bool where
  proveRound j _ w prevChals :=
    if h : j.val = 0 then
      fun idx => if idx.val = 0 then w.1 else w.2
    else
      have h0 : 0 < j.val := Nat.pos_of_ne_zero h
      fun idx => xor (if idx.val = 0 then w.1 else w.2) (prevChals ⟨0, h0⟩)
  queries _ chals :=
    [(⟨0, by decide⟩, if chals ⟨0, by decide⟩ then ⟨1, by decide⟩ else ⟨0, by decide⟩),
     (⟨1, by decide⟩, if chals ⟨1, by decide⟩ then ⟨1, by decide⟩ else ⟨0, by decide⟩)]
  decide s chals answers :=
    s.1 && (answers == [s.2, xor s.2 (chals ⟨0, by decide⟩)])

theorem romIOP_complete : IOPCompleteness romIOP romRel := by
  rintro ⟨flag, target⟩ ⟨w₀, w₁⟩ ⟨hflag, hw₀, hw₁⟩ chals
  dsimp only [romRel] at hflag hw₀ hw₁
  subst hflag hw₀ hw₁
  have h0 : ∀ p : 0 < 2, chals ⟨0, p⟩ = chals 0 := fun _ => rfl
  simp only [iopVerify, iopAnswers, iopProverOracles, prefixChallenges, romIOP, h0]
  generalize chals 0 = c₀
  generalize chals ⟨1, by decide⟩ = c₁
  cases c₀ <;> cases c₁ <;> cases w₁ <;> rfl

/-! ### Part 1: Transcript-Chained Fiat–Shamir Bridge, Pure Simulation & ROM Completeness -/

/-- Injective deterministic Merkle hash on bitstrings. -/
def idTreeHash (msg : List Bool) : List Bool := msg

/-- Deterministic transcript-chained Fiat–Shamir oracle inspecting statement, root count, and
previous challenge history. -/
def xorChainedFS : BCSFSQuery (Bool × Bool) Bool → Bool
  | ((flag, target), rts, prev) =>
    xor flag (xor target (xor (rts.length % 2 == 1) (prev.headD false)))

-- Concrete transcript-chained challenge derivation across two rounds.
example : chainedFSChallenges xorChainedFS (true, true) [[true], [false]] = [true, true] :=
  rfl

-- Concrete pure simulation of `bcsProveROM` openings, roots, and `bcsHonestROMProg` via `evalPure`.
example :
    (OracleComp.evalPure (bcsOracle idTreeHash xorChainedFS)
      (bcsProveROM romIOP encSym (true, true) (true, true))).openings =
    (bcsProve romIOP (fun _ => idTreeHash) [] encSym (chainedFS xorChainedFS)
      (true, true) (true, true)).openings :=
  rfl

example :
    OracleComp.evalPure (bcsOracle idTreeHash xorChainedFS)
      (bcsProveROM romIOP encSym (true, true) (true, true)) =
    bcsProve romIOP (fun _ => idTreeHash) [] encSym (chainedFS xorChainedFS)
      (true, true) (true, true) :=
  evalPure_bcsProveROM idTreeHash xorChainedFS romIOP encSym (true, true) (true, true)

example :
    OracleComp.evalPure (bcsOracle idTreeHash xorChainedFS)
      (bcsHonestROMProg romIOP encSym (true, true) (true, true)) = true :=
  rfl

-- Perfect completeness in the lazy two-channel random-oracle model for every digest length `σ`.
example (σ : ℕ) :
    bcsHonestROMGame romIOP encSym (true, true) (true, true) σ = PMF.pure true :=
  bcsHonestROMGame_eq_pure_true romIOP_complete encSym ⟨rfl, rfl, rfl⟩ σ

/-! ### Part 2: Straight-Line Multi-Round Extraction, Invariance & Dual Collision Extraction -/

/-- Straight-line IOP witness extractor reading both leaves of the round-`0` oracle table. -/
def romExtract (_ : Bool × Bool) (oracles : Fin 2 → OracleTable 1 Bool) : Bool × Bool :=
  (oracles ⟨0, by decide⟩ ⟨0, by decide⟩, oracles ⟨0, by decide⟩ ⟨1, by decide⟩)

/-- Honest BCS proof for valid statement `(true, true)` and witness `(true, true)`. -/
abbrev honestProof : BCSProof 2 Bool :=
  bcsProve romIOP (fun _ => idTreeHash) [] encSym (chainedFS xorChainedFS)
    (true, true) (true, true)

/-- Record `(q, hTree q)` for all leaf-to-root hash steps of a depth-1 2-leaf table `[b₀, b₁]`. -/
def fullTableTrace (hTree : List Bool → List Bool) (b₀ b₁ : Bool) :
    List (List Bool × List Bool) :=
  let leaves := [[b₀], [b₁]]
  ((merkleInputs (fun _ => hTree) [] [b₀] 0 (merklePath (fun _ => hTree) [] leaves 0) ++
    merkleInputs (fun _ => hTree) [] [b₁] 1 (merklePath (fun _ => hTree) [] leaves 1)).map
      fun q => (q, hTree q)).eraseDups

/-- Full prover Merkle trace recording both round-`0` and round-`1` trees of `honestProof`. -/
abbrev trProver : List (List Bool × List Bool) :=
  (fullTableTrace idTreeHash true true ++ fullTableTrace idTreeHash false false).eraseDups

example : TraceConsistentWith idTreeHash trProver := by decide

example : TraceCollisionFree trProver := by decide

example : BCSOpeningsQueriedInTrace (fun _ => idTreeHash) [] romIOP encSym trProver (true, true)
    (bcsChallenge (chainedFS xorChainedFS) (true, true) honestProof.roots) honestProof := by
  decide

-- Boundary case: on the empty trace `[]`, straight-line extraction falls back to
-- `defaultSym = false`.
example :
    bcsExtractWitness romExtract decSym false [] (true, true) honestProof.roots = (false, false) :=
  rfl

-- Straight-line witness extraction recovers `(true, true)` from `trProver` even though
-- `defaultSym = false`.
example :
    bcsExtractWitness romExtract decSym false trProver (true, true) honestProof.roots =
      (true, true) := by
  decide

-- Fixed-trace consistency: `iopVerify` accepts `bcsExtractOracles` on `trProver`.
example :
    iopVerify romIOP (true, true)
      (bcsChallenge (chainedFS xorChainedFS) (true, true) honestProof.roots)
      (bcsExtractOracles decSym false trProver 1 honestProof.roots) = true :=
  iopVerify_bcsExtractOracles_of_bcsVerify (H := fun _ => idTreeHash) (k := []) decSym_encSym false
    (by decide) (by decide) (by decide)

-- Trace-extension invariance: prepending a Merkle query whose digest avoids existing roots and
-- child digests leaves `bcsExtractOracles` unchanged across both rounds.
example :
    bcsExtractOracles decSym false (([true, true, false], [true, true, true, true]) :: trProver)
      1 honestProof.roots =
    bcsExtractOracles decSym false trProver 1 honestProof.roots :=
  bcsExtractOracles_cons_of_ne decSym false trProver [true, true, false]
    (by intro j; fin_cases j <;> decide) (by decide)

/-- Leaf-colliding hash mapping `[true]` to `[false]` and acting as identity elsewhere. -/
def collideLeafHash (msg : List Bool) : List Bool :=
  if msg == [true] then [false] else msg

/-- Forged BCS proof for `(true, true)` committed to the rejected `(false, false)` round-`0` table
under `collideLeafHash`, but opening round `0` as `true`. -/
def forgedROMProof : BCSProof 2 Bool :=
  let roots := bcsHonestRoots romIOP (fun _ => collideLeafHash) [] encSym
    (chainedFS xorChainedFS) (true, true) (false, false)
  let c₀ := bcsChallenge (chainedFS xorChainedFS) (true, true) roots ⟨0, by decide⟩
  let c₁ := bcsChallenge (chainedFS xorChainedFS) (true, true) roots ⟨1, by decide⟩
  let r1Bit := xor false c₀
  { roots := roots
    openings :=
      [(true, merklePath (fun _ => collideLeafHash) [] [[false], [false]] (if c₀ then 1 else 0)),
       (xor true c₀, merklePath (fun _ => collideLeafHash) [] [[r1Bit], [r1Bit]]
         (if c₁ then 1 else 0))] }

/-- Trace recording the committed `(false, false)` leaves before the colliding `[true]` openings. -/
abbrev trCollide : List (List Bool × List Bool) :=
  (fullTableTrace collideLeafHash false false ++
    fullTableTrace collideLeafHash true true).eraseDups

example : bcsVerify romIOP (fun _ => collideLeafHash) [] encSym (chainedFS xorChainedFS)
    (true, true) forgedROMProof = true := by
  decide

example :
    iopVerify romIOP (true, true)
      (bcsChallenge (chainedFS xorChainedFS) (true, true) forgedROMProof.roots)
      (bcsExtractOracles decSym false trCollide 1 forgedROMProof.roots) = false := by
  decide

-- Dual collision extraction witnesses a concrete hash collision in `trCollide`.
example : ∃ q₁ ∈ trCollide.map Prod.fst, ∃ q₂ ∈ trCollide.map Prod.fst,
    q₁ ≠ q₂ ∧ collideLeafHash q₁ = collideLeafHash q₂ :=
  exists_collision_of_bcsVerify_of_iopVerify_eq_false (H := fun _ => collideLeafHash) (k := [])
    (iop := romIOP) (hFS := chainedFS xorChainedFS) (tr_MT := trCollide) (x := (true, true))
    (prf := forgedROMProof) decSym_encSym false (by decide) (by decide) (by decide) (by decide)

/-! ### Part 3: Adaptive Cheating Prover & Two-Channel ROM Soundness / Knowledge Soundness -/

/-- Round-by-round doomed predicate for `romIOP` knowledge soundness: either no rounds have elapsed,
the round-`0` table already encodes a valid witness for `s`, `s` is invalid (`s.1 = false`), or the
round-`0` challenge `c₀` caught a disagreeing entry in `π₀`. -/
def romDoomed (s : Bool × Bool) (tr : List (OracleTable 1 Bool × Bool)) : Prop :=
  match tr with
  | [] => True
  | (π₀, c₀) :: _ =>
    romRel s (π₀ ⟨0, by decide⟩, π₀ ⟨1, by decide⟩) ∨
      s.1 = false ∨
      π₀ (if c₀ then ⟨1, by decide⟩ else ⟨0, by decide⟩) ≠ s.2

/-- Non-escaping step relation for `romIOP` knowledge soundness. -/
def romGoodStep (s : Bool × Bool) (tr : List (OracleTable 1 Bool × Bool))
    (π : OracleTable 1 Bool) (c : Bool) : Prop :=
  tr = [] →
    romRel s (π ⟨0, by decide⟩, π ⟨1, by decide⟩) ∨
      s.1 = false ∨
      π (if c then ⟨1, by decide⟩ else ⟨0, by decide⟩) ≠ s.2

theorem romIOP_rbrKS :
    IOPRoundByRoundKnowledgeSoundness romIOP romRel romExtract romDoomed romGoodStep where
  init_doomed _ := trivial
  step_doomed _ pref _ _ hd hgood := by
    cases pref with
    | nil => exact hgood rfl
    | cons _ _ => exact hd
  extract_of_doomed s oracles chals hd hver := by
    change romRel s (romExtract s oracles) ∨ s.1 = false ∨
      oracles ⟨0, by decide⟩ (if chals ⟨0, by decide⟩ then ⟨1, by decide⟩ else ⟨0, by decide⟩) ≠
        s.2 at hd
    simp only [iopVerify, iopAnswers, romIOP, List.map_cons, List.map_nil, Bool.and_eq_true,
      beq_iff_eq, List.cons.injEq] at hver
    rcases hd with hrel | hs_false | hne
    · exact hrel
    · rw [hs_false] at hver
      cases hver.1
    · exact False.elim (hne hver.2.1)

/-- At most one challenge `c ∈ {false, true}` escapes `romGoodStep`, giving escape bound `1 / 2`. -/
theorem romIOP_escape (s : Bool × Bool) (pref : List (OracleTable 1 Bool × Bool))
    (π : OracleTable 1 Bool) (_ : romDoomed s pref) :
    (PMF.uniformOfFintype Bool).toOuterMeasure {c | ¬ romGoodStep s pref π c} ≤ 1 / 2 := by
  cases pref with
  | cons hd tl =>
    have hempty : {c : Bool | ¬ romGoodStep s (hd :: tl) π c} = ∅ := by
      ext c
      simp [romGoodStep]
    simp [hempty]
  | nil =>
    let badChal : Bool := if π ⟨0, by decide⟩ == s.2 then false else true
    calc (PMF.uniformOfFintype Bool).toOuterMeasure {c | ¬ romGoodStep s [] π c}
        ≤ (PMF.uniformOfFintype Bool).toOuterMeasure {c | c ∈ [badChal]} := by
          refine (PMF.uniformOfFintype Bool).toOuterMeasure.mono fun c hc => ?_
          change ¬ romGoodStep s [] π c at hc
          cases c <;> simp only [romGoodStep, romRel, List.mem_singleton, badChal,
            Bool.false_eq_true, ↓reduceIte] at hc ⊢ <;>
          · rcases s with ⟨flag, target⟩
            generalize π ⟨0, by decide⟩ = a₀ at hc ⊢
            generalize π ⟨1, by decide⟩ = a₁ at hc
            cases flag <;> cases target <;> cases a₀ <;> cases a₁ <;> simp_all
      _ ≤ (([badChal].length : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Bool) :=
          PMF.toOuterMeasure_uniformOfFintype_mem_list_le [badChal]
      _ = 1 / 2 := by norm_num

-- Concrete check of `IOPRoundByRoundKnowledgeSoundness.rel_iopExtract_of_goodSteps`.
example :
    let oracles := bcsExtractOracles decSym false trProver 1 honestProof.roots
    romRel (true, true) (romExtract (true, true) oracles) := by
  intro oracles
  refine romIOP_rbrKS.rel_iopExtract_of_goodSteps (true, true) oracles
    (bcsChallenge (chainedFS xorChainedFS) (true, true) honestProof.roots) ?_ (by decide)
  intro j
  fin_cases j
  · intro _
    exact Or.inl ⟨rfl, by decide, by decide⟩
  · intro hnil
    nomatch hnil

/-- Adaptive cheating prover over `BCSROMSpec (Bool × Bool) Bool` that:
1. Queries Merkle leaf `[false]` to obtain `d₀`,
2. Queries Fiat–Shamir on an oversized 5-root list `[d₀, d₀, d₀, d₀, d₀]` (`5 > r = 2`),
3. Queries Fiat–Shamir out-of-order at round `1` (`[d₀, d₀]`, `[false]`) before round `0`,
4. Queries Fiat–Shamir at round `0` (`[d₀]`, `[]`), and
5. Adaptively queries a second Merkle leaf `[xor c₀ c₁]` and emits a candidate proof for the false
   statement `(false, true)`. -/
def adaptiveBCSCheater :
    OracleComp (BCSROMSpec (Bool × Bool) Bool) ((Bool × Bool) × BCSProof 2 Bool) := do
  let d₀ ← query (spec := BCSROMSpec (Bool × Bool) Bool) (.inl [false])
  let _ ← query (spec := BCSROMSpec (Bool × Bool) Bool)
    (.inr ((false, true), [d₀, d₀, d₀, d₀, d₀], [true, false, true, false]))
  let c₁ ← query (spec := BCSROMSpec (Bool × Bool) Bool)
    (.inr ((false, true), [d₀, d₀], [false]))
  let c₀ ← query (spec := BCSROMSpec (Bool × Bool) Bool)
    (.inr ((false, true), [d₀], []))
  let sib ← query (spec := BCSROMSpec (Bool × Bool) Bool) (.inl [xor c₀ c₁])
  return ((false, true),
    { roots := fun _ => d₀
      openings := [(true, [sib]), (xor true c₀, [sib])] })

theorem isCostBounded_FS_adaptiveBCSCheater :
    IsCostBounded bcsFSCost adaptiveBCSCheater 3 :=
  IsCostBounded.liftBind (cost := bcsFSCost) (Sum.inl [false]) _ 3 fun d₀ =>
    IsCostBounded.liftBind (cost := bcsFSCost)
      (Sum.inr ((false, true), [d₀, d₀, d₀, d₀, d₀], [true, false, true, false])) _ 2 fun _ =>
      IsCostBounded.liftBind (cost := bcsFSCost)
        (Sum.inr ((false, true), [d₀, d₀], [false])) _ 1 fun c₁ =>
        IsCostBounded.liftBind (cost := bcsFSCost)
          (Sum.inr ((false, true), [d₀], [])) _ 0 fun c₀ =>
          IsCostBounded.liftBind (cost := bcsFSCost) (Sum.inl [xor c₀ c₁]) _ 0 fun _ =>
            IsCostBounded.pure (cost := bcsFSCost) _ 0

theorem isCostBounded_MT_adaptiveBCSCheater :
    IsCostBounded bcsMTCost adaptiveBCSCheater 2 :=
  IsCostBounded.liftBind (cost := bcsMTCost) (Sum.inl [false]) _ 1 fun d₀ =>
    IsCostBounded.liftBind (cost := bcsMTCost)
      (Sum.inr ((false, true), [d₀, d₀, d₀, d₀, d₀], [true, false, true, false])) _ 1 fun _ =>
      IsCostBounded.liftBind (cost := bcsMTCost)
        (Sum.inr ((false, true), [d₀, d₀], [false])) _ 1 fun c₁ =>
        IsCostBounded.liftBind (cost := bcsMTCost)
          (Sum.inr ((false, true), [d₀], [])) _ 1 fun c₀ =>
          IsCostBounded.liftBind (cost := bcsMTCost) (Sum.inl [xor c₀ c₁]) _ 0 fun _ =>
            IsCostBounded.pure (cost := bcsMTCost) _ 0

/-- Verifier Merkle budget discharged only on `(s, prf) ∈ adaptiveBCSCheater.support`: each emitted
proof has two openings of path length `1`, so `bcsVerifyROM` makes at most `2 * (1 + 1) = 4` Merkle
queries. -/
theorem isCostBounded_MT_verifier_of_mem_support_adaptiveBCSCheater
    (s : Bool × Bool) (prf : BCSProof 2 Bool) (hmem : (s, prf) ∈ adaptiveBCSCheater.support) :
    IsCostBounded bcsMTCost (bcsVerifyROM romIOP encSym s prf) 4 := by
  simp only [adaptiveBCSCheater, mem_supportWith_bind_iff, supportWith_query, Set.mem_univ,
    true_and, supportWith_pure, Set.mem_singleton_iff] at hmem
  obtain ⟨d₀, _, c₁, c₀, sib, h⟩ := hmem
  cases h
  exact isCostBounded_bcsMTCost_bcsVerifyROM_of_queries_le romIOP encSym (false, true) _
    (q_iop := 2) (L_path := 1) (fun _ => le_rfl) (by simp)

-- Adaptive two-channel BCS ROM soundness (combined Merkle budget `Q_MT = 6` and separate
-- prover/verifier budgets `t_MT = 2`, `q_V = 4`, `t_FS = 3`, `r = 2`, `|Chal| = 2`, `ε_rbr = 1/2`,
-- independent of the 5-root garbage FS query).
example (σ : ℕ) :
    bcsSoundnessGame romIOP encSym {s | ∃ w, romRel s w} adaptiveBCSCheater σ true ≤
      ((3 + 2 : ℕ) : ℝ≥0∞) *
          (1 / 2 + ((3 + 2 : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Bool)) +
        (6 : ℝ≥0∞) *
          (((3 * 6 + 2 * (3 + 2) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMSoundness_bound romIOP_rbrKS.toRoundByRoundSoundness
    (fun s _ pref π hd => romIOP_escape s pref π hd.2) decSym_encSym false σ
    isCostBounded_FS_adaptiveBCSCheater
    (isCostBounded_bcsMTCost_bcsSoundnessProg romIOP encSym _ isCostBounded_MT_adaptiveBCSCheater
      isCostBounded_MT_verifier_of_mem_support_adaptiveBCSCheater)

example (σ : ℕ) :
    bcsSoundnessGame romIOP encSym {s | ∃ w, romRel s w} adaptiveBCSCheater σ true ≤
      ((3 + 2 : ℕ) : ℝ≥0∞) *
          (1 / 2 + ((3 + 2 : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Bool)) +
        ((2 + 4 : ℕ) : ℝ≥0∞) *
          (((3 * (2 + 4) + 2 * (3 + 2) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMSoundness_bound_of_prover_verifier romIOP_rbrKS.toRoundByRoundSoundness
    (fun s _ pref π hd => romIOP_escape s pref π hd.2) decSym_encSym false σ
    isCostBounded_MT_adaptiveBCSCheater isCostBounded_FS_adaptiveBCSCheater
    isCostBounded_MT_verifier_of_mem_support_adaptiveBCSCheater

-- Adaptive straight-line BCS ROM knowledge soundness (trace-level on `bcsExecROM`, combined budget
-- `bcsROMKnowledgeSoundness_bound`, and separate-budget corollary).
example (σ : ℕ) :
    ((OracleComp.interpret (bcsMemoize σ) (bcsExecROM romIOP encSym adaptiveBCSCheater)).run
        ([], [])).toOuterMeasure
        {out | match out with
          | (((s, prf), ok), (tr_MT, _)) =>
            ok = true ∧
              ¬ romRel s (romExtract s (bcsExtractOracles decSym false tr_MT 1 prf.roots))} ≤
      ((3 + 2 : ℕ) : ℝ≥0∞) *
          (1 / 2 + ((3 + 2 : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Bool)) +
        ((2 + 4 : ℕ) : ℝ≥0∞) *
          (((3 * (2 + 4) + 2 * (3 + 2) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMKnowledgeSoundness_trace_bound romIOP_rbrKS romIOP_escape decSym_encSym false σ
    isCostBounded_FS_adaptiveBCSCheater
    (isCostBounded_bcsMTCost_bcsExecROM romIOP encSym isCostBounded_MT_adaptiveBCSCheater
      isCostBounded_MT_verifier_of_mem_support_adaptiveBCSCheater)

example (σ : ℕ) :
    bcsKnowledgeSoundnessGame romIOP romRel romExtract encSym decSym false
        adaptiveBCSCheater σ true ≤
      ((3 + 2 : ℕ) : ℝ≥0∞) *
          (1 / 2 + ((3 + 2 : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Bool)) +
        (6 : ℝ≥0∞) *
          (((3 * 6 + 2 * (3 + 2) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMKnowledgeSoundness_bound romIOP_rbrKS romIOP_escape decSym_encSym false σ
    isCostBounded_FS_adaptiveBCSCheater
    (isCostBounded_bcsMTCost_bcsExecROM romIOP encSym isCostBounded_MT_adaptiveBCSCheater
      isCostBounded_MT_verifier_of_mem_support_adaptiveBCSCheater)

example (σ : ℕ) :
    bcsKnowledgeSoundnessGame romIOP romRel romExtract encSym decSym false
        adaptiveBCSCheater σ true ≤
      ((3 + 2 : ℕ) : ℝ≥0∞) *
          (1 / 2 + ((3 + 2 : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Bool)) +
        ((2 + 4 : ℕ) : ℝ≥0∞) *
          (((3 * (2 + 4) + 2 * (3 + 2) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMKnowledgeSoundness_bound_of_prover_verifier romIOP_rbrKS romIOP_escape decSym_encSym
    false σ isCostBounded_MT_adaptiveBCSCheater isCostBounded_FS_adaptiveBCSCheater
    isCostBounded_MT_verifier_of_mem_support_adaptiveBCSCheater

/-! ### Part 4: Concrete `< 1 / 3` Numerical Security Bound (`Chal = Fin 64`, `σ = 16`) -/

/-- Witness relation on `Stmt = Bool`, `Wit = Bool` for the larger-challenge (`Fin 64`) test IOP. -/
def largeRel (x w : Bool) : Prop :=
  x = true ∧ w = true

/-- Straight-line IOP extractor reading leaf `0` of the round-`0` table. -/
def largeExtract (_ : Bool) (oracles : Fin 2 → OracleTable 1 Bool) : Bool :=
  oracles ⟨0, by decide⟩ ⟨0, by decide⟩

/-- Concrete 2-round, depth-1 IOP over `Chal = Fin 64` with genuine soundness/knowledge escape on
`c₀ = 0` (`ε_rbr = 1 / 64`). -/
def largeChalIOP : PublicCoinIOP 2 1 Bool Bool Bool (Fin 64) where
  proveRound _ _ w _ := fun _ => w
  queries _ _ := [(⟨0, by decide⟩, ⟨0, by decide⟩), (⟨1, by decide⟩, ⟨0, by decide⟩)]
  decide x chals ans :=
    match ans with
    | [a₀, a₁] => x && (a₀ || decide (chals ⟨0, by decide⟩ = 0)) && a₁
    | _ => false

theorem largeChalIOP_complete : IOPCompleteness largeChalIOP largeRel := by
  intro x w ⟨hx, hw⟩ chals
  subst hx hw
  simp [iopVerify, iopAnswers, iopProverOracles, largeChalIOP]

def largeDoomed (_ : Bool) (tr : List (OracleTable 1 Bool × Fin 64)) : Prop :=
  match tr with
  | [] => True
  | (_, c₀) :: _ => c₀ ≠ 0

def largeGoodStep (_ : Bool) (tr : List (OracleTable 1 Bool × Fin 64))
    (_ : OracleTable 1 Bool) (c : Fin 64) : Prop :=
  tr = [] → c ≠ 0

theorem largeChalIOP_rbrKS :
    IOPRoundByRoundKnowledgeSoundness largeChalIOP largeRel largeExtract
      largeDoomed largeGoodStep where
  init_doomed _ := trivial
  step_doomed _ pref _ _ hd hgood := by
    cases pref with
    | nil => exact hgood rfl
    | cons _ _ => exact hd
  extract_of_doomed x oracles chals hd hver := by
    change chals ⟨0, by decide⟩ ≠ 0 at hd
    simp only [iopVerify, iopAnswers, largeChalIOP, List.map_cons, List.map_nil, hd, decide_false,
      Bool.or_false, Bool.and_eq_true] at hver
    exact hver.1

theorem largeChalIOP_escape (x : Bool) (pref : List (OracleTable 1 Bool × Fin 64))
    (π : OracleTable 1 Bool) (_ : largeDoomed x pref) :
    (PMF.uniformOfFintype (Fin 64)).toOuterMeasure {c | ¬ largeGoodStep x pref π c} ≤ 1 / 64 := by
  cases pref with
  | cons hd tl =>
    have hempty : {c : Fin 64 | ¬ largeGoodStep x (hd :: tl) π c} = ∅ := by
      ext c
      simp [largeGoodStep]
    simp [hempty]
  | nil =>
    calc (PMF.uniformOfFintype (Fin 64)).toOuterMeasure {c | ¬ largeGoodStep x [] π c}
        ≤ (PMF.uniformOfFintype (Fin 64)).toOuterMeasure {c | c ∈ ([0] : List (Fin 64))} := by
          refine (PMF.uniformOfFintype (Fin 64)).toOuterMeasure.mono fun c hc => ?_
          simpa [largeGoodStep] using hc
      _ ≤ ((([0] : List (Fin 64)).length : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / Fintype.card (Fin 64)) :=
          PMF.toOuterMeasure_uniformOfFintype_mem_list_le [0]
      _ = 1 / 64 := by simp [Fintype.card_fin]

/-- Adaptive out-of-order cheating prover over `Chal = Fin 64` (`t_FS = 2`, `t_MT = 2`). -/
def largeChalCheater :
    OracleComp (BCSROMSpec Bool (Fin 64)) (Bool × BCSProof 2 Bool) := do
  let d₀ ← query (spec := BCSROMSpec Bool (Fin 64)) (.inl [false])
  let c₁ ← query (spec := BCSROMSpec Bool (Fin 64)) (.inr (false, [d₀, d₀], [0]))
  let c₀ ← query (spec := BCSROMSpec Bool (Fin 64)) (.inr (false, [d₀], []))
  let sib ← query (spec := BCSROMSpec Bool (Fin 64)) (.inl [decide (c₀ = c₁)])
  return (false,
    { roots := fun _ => d₀
      openings := [(true, [sib]), (true, [sib])] })

theorem isCostBounded_FS_largeChalCheater :
    IsCostBounded bcsFSCost largeChalCheater 2 :=
  IsCostBounded.liftBind (cost := bcsFSCost) (Sum.inl [false]) _ 2 fun d₀ =>
    IsCostBounded.liftBind (cost := bcsFSCost) (Sum.inr (false, [d₀, d₀], [0])) _ 1 fun c₁ =>
      IsCostBounded.liftBind (cost := bcsFSCost) (Sum.inr (false, [d₀], [])) _ 0 fun c₀ =>
        IsCostBounded.liftBind (cost := bcsFSCost) (Sum.inl [decide (c₀ = c₁)]) _ 0 fun _ =>
          IsCostBounded.pure (cost := bcsFSCost) _ 0

theorem isCostBounded_MT_largeChalCheater :
    IsCostBounded bcsMTCost largeChalCheater 2 :=
  IsCostBounded.liftBind (cost := bcsMTCost) (Sum.inl [false]) _ 1 fun d₀ =>
    IsCostBounded.liftBind (cost := bcsMTCost) (Sum.inr (false, [d₀, d₀], [0])) _ 1 fun c₁ =>
      IsCostBounded.liftBind (cost := bcsMTCost) (Sum.inr (false, [d₀], [])) _ 1 fun c₀ =>
        IsCostBounded.liftBind (cost := bcsMTCost) (Sum.inl [decide (c₀ = c₁)]) _ 0 fun _ =>
          IsCostBounded.pure (cost := bcsMTCost) _ 0

theorem isCostBounded_MT_verifier_largeChalCheater
    (x : Bool) (prf : BCSProof 2 Bool) (hmem : (x, prf) ∈ largeChalCheater.support) :
    IsCostBounded bcsMTCost (bcsVerifyROM largeChalIOP encSym x prf) 4 := by
  simp only [largeChalCheater, mem_supportWith_bind_iff, supportWith_query, Set.mem_univ,
    true_and, supportWith_pure, Set.mem_singleton_iff] at hmem
  obtain ⟨d₀, c₁, c₀, sib, h⟩ := hmem
  cases h
  exact isCostBounded_bcsMTCost_bcsVerifyROM_of_queries_le largeChalIOP encSym false _
    (q_iop := 2) (L_path := 1) (fun _ => le_rfl) (by simp)

private theorem largeChal_bound_lt_one_third :
    ((2 + 2 : ℕ) : ℝ≥0∞) *
        (1 / 64 + ((2 + 2 : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card (Fin 64))) +
      ((2 + 4 : ℕ) : ℝ≥0∞) *
        (((3 * (2 + 4) + 2 * (2 + 2) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ 16)) < 1 / 3 := by
  have hnn : (4 * (64⁻¹ + 4 * 64⁻¹) + 6 * (26 * 65536⁻¹) : ℝ≥0) < 3⁻¹ := by norm_num
  have hcast :
      ((4 * (64⁻¹ + 4 * 64⁻¹) + 6 * (26 * 65536⁻¹) : ℝ≥0) : ℝ≥0∞) < ((3⁻¹ : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.coe_lt_coe.mpr hnn
  simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_ofNat,
    ENNReal.coe_inv (by norm_num : (64 : ℝ≥0) ≠ 0),
    ENNReal.coe_inv (by norm_num : (65536 : ℝ≥0) ≠ 0),
    ENNReal.coe_inv (by norm_num : (3 : ℝ≥0) ≠ 0)] at hcast
  simpa only [Fintype.card_fin, one_div,
    (by norm_num : ((2 + 2 : ℕ) : ℝ≥0∞) = 4),
    (by norm_num : ((2 + 4 : ℕ) : ℝ≥0∞) = 6),
    (by norm_num : ((3 * (2 + 4) + 2 * (2 + 2) : ℕ) : ℝ≥0∞) = 26),
    (by norm_num : ((64 : ℕ) : ℝ≥0∞) = 64),
    (by norm_num : (2 : ℝ≥0∞) ^ 16 = 65536)] using hcast

-- At `σ = 16` (`2 ^ 16 = 65536`) and `|Chal| = 64`, both the adaptive ROM soundness error and
-- straight-line knowledge-soundness error are strictly `< 1 / 3 < 1` (`5159 / 16384`).
example :
    bcsSoundnessGame largeChalIOP encSym {x | ∃ w, largeRel x w} largeChalCheater 16 true <
      1 / 3 :=
  lt_of_le_of_lt
    (bcsROMSoundness_bound_of_prover_verifier largeChalIOP_rbrKS.toRoundByRoundSoundness
      (fun x _ pref π hd => largeChalIOP_escape x pref π hd.2) decSym_encSym false 16
      isCostBounded_MT_largeChalCheater isCostBounded_FS_largeChalCheater
      isCostBounded_MT_verifier_largeChalCheater)
    largeChal_bound_lt_one_third

example :
    bcsKnowledgeSoundnessGame largeChalIOP largeRel largeExtract encSym decSym false
      largeChalCheater 16 true < 1 / 3 :=
  lt_of_le_of_lt
    (bcsROMKnowledgeSoundness_bound_of_prover_verifier largeChalIOP_rbrKS largeChalIOP_escape
      decSym_encSym false 16 isCostBounded_MT_largeChalCheater isCostBounded_FS_largeChalCheater
      isCostBounded_MT_verifier_largeChalCheater)
    largeChal_bound_lt_one_third

end ComplexityTests.Crypto.BCSROM
