/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/
module
-- upstream: candidate
public import CslibFrontier.Crypto.Primitives.BlockCipher.Modes
public import CslibFrontier.Crypto.Primitives.PRF.Finite
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.QueryCount
import CslibFrontier.Crypto.Game.UntilBad
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Languages.Probabilistic.UntilBad.TwoCost
import CslibFrontier.Probability.Product
/-!
# CPA Security of Counter (CTR) Mode

Counter mode ([KatzLindell2020], Section 3.6.3, Figure 3.9) encrypts a message of `k`
blocks under a block function `f` and a uniform initialization vector `iv` by adding the keystream
`f (counter iv 0), f (counter iv 1), …` to the message blocks. [KatzLindell2020] (Section 3.6.3, p. 92) states that
CTR mode is CPA-secure whenever `f` is a pseudorandom function; this file proves a concrete
version of that statement.

The security notion is the left-or-right multiple-encryption experiment of [KatzLindell2020],
Definition 3.22: the adversary repeatedly submits pairs of equal-length messages and receives the
encryption of the left or the right message, according to a hidden bit `b`. By [KatzLindell2020],
Theorem 3.23, this is equivalent to CPA security.

The proof follows the template of [KatzLindell2020], Theorem 3.33 (CTR mode):
1. The CTR experiment is the real PRF experiment for a reduction that encrypts with its oracle
   (`ctrCpaGame_eq_realGame`); the reduction makes one oracle call per encrypted block
   (`isQueryBounded_ctrReduction`).
2. Against a uniform random function, sampled lazily, the reduction's view differs from fresh
   uniform ciphertexts only when some keystream input repeats an earlier input. The chain
   collision bound `toOuterMeasure_badChain_le` limits this event to probability
   `K (K + ℓ) / 2 ^ n` when the queries ask at most `K` blocks in total and at most `ℓ` blocks
   each (`advantage_idealGame_ctrReduction_le`).
3. Fresh uniform ciphertexts do not depend on the challenge bit, so the hybrids and the two PRF
   advantages give the final bound (`advantage_ctrCpaGame_le`).

The PRF experiments are the concrete ones of `Cslib.Crypto.PRF` ([BonehShoup2023], Chapter 4).

## Main definitions

* `CTRQuery`, `CTRSpec`, `CTRAdversary`: left-or-right queries and adaptive adversaries.
* `ctrSelect`, `ctrBlocks`, `ctrCost`: the plaintext encrypted for a query, its number of blocks,
  and the block cost of a call. A query whose messages differ in length or exceed `ℓ` blocks
  encrypts the empty message.
* `ctrOracle`, `ctrCpaGame`: the CTR encryption oracle and the left-or-right experiment.
* `ctrIdealOracle`, `ctrIdealGame`: the experiment with fresh uniform ciphertexts.
* `ctrChainQueries`, `ctrQueryProgram`, `ctrReduction`: the PRF distinguisher built from an CTR
  adversary.

## Main results

* `ctrCpaGame_eq_realGame`: the CTR experiment is the real PRF experiment for the reduction.
* `isQueryBounded_ctrReduction`: the reduction makes at most `K` oracle calls.
* `advantage_idealGame_ctrReduction_le`: with a uniform random function, the reduction's view is
  within `K (K + ℓ) / 2 ^ n` of the ideal experiment.
* `advantage_ctrCpaGame_randomFunction_le`: CTR mode with a uniform random function has
  left-or-right advantage at most `2 K (K + ℓ) / 2 ^ n`.
* `advantage_ctrCpaGame_le`: CTR mode with a keyed function `F` has left-or-right advantage at
  most the PRF advantages of two reductions plus `2 K (K + ℓ) / 2 ^ n`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 3.6.3 (Figure 3.9, p. 92), Definition 3.22 (p. 74), Theorem 3.23 (p. 75) and
  Theorem 3.33 (p. 93).
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Chapter 4.
-/
public section
namespace Cslib.Crypto
open Cslib.Probability
open OracleComp (sumHandler)
open scoped ENNReal NNReal
variable {n : ℕ}
/-! ### Section 1: The CTR Left-or-Right Experiment -/

/-- A left-or-right query: two candidate plaintexts, each a list of `n`-bit blocks. -/
abbrev CTRQuery (n : ℕ) : Type := List (BitString n) × List (BitString n)

/-- The answer to a left-or-right query: an initialization vector and the ciphertext blocks. -/
abbrev CTRSpec (n : ℕ) : CTRQuery n → Type := fun _ => BitString n × List (BitString n)

/-- An adaptive adversary in the left-or-right experiment, with private coins. -/
abbrev CTRAdversary (n : ℕ) : Type := ProbOracleComp (CTRSpec n) Bool

/-- The plaintext encrypted for the query `q` under the challenge bit `b`: the right message if
`b = true` and the left one otherwise. A query whose messages differ in length or exceed `ℓ`
blocks encrypts the empty message. -/
@[expose]
def ctrSelect (ℓ : ℕ) (b : Bool) (q : CTRQuery n) : List (BitString n) :=
  if q.1.length = q.2.length ∧ q.1.length ≤ ℓ then (if b then q.2 else q.1) else []

/-- The number of blocks encrypted for the query `q`: the common length of the two messages of a
valid query, and `0` otherwise. -/
@[expose]
def ctrBlocks (ℓ : ℕ) (q : CTRQuery n) : ℕ :=
  if q.1.length = q.2.length ∧ q.1.length ≤ ℓ then q.1.length else 0

/-- The encrypted plaintext has `ctrBlocks ℓ q` blocks, whatever the challenge bit. -/
@[simp]
theorem length_ctrSelect (ℓ : ℕ) (b : Bool) (q : CTRQuery n) :
    (ctrSelect ℓ b q).length = ctrBlocks ℓ q := by
  unfold ctrSelect ctrBlocks
  split_ifs <;> simp_all

/-- A query encrypts at most `ℓ` blocks. -/
theorem ctrBlocks_le (ℓ : ℕ) (q : CTRQuery n) : ctrBlocks ℓ q ≤ ℓ := by
  unfold ctrBlocks
  split_ifs with h
  · exact h.2
  · exact Nat.zero_le ℓ

/-- The cost of a call in the left-or-right experiment: private draws are free and a query costs
its number of encrypted blocks. -/
@[expose]
def ctrCost (ℓ : ℕ) : ℕ ⊕ CTRQuery n → ℕ :=
  Sum.elim (fun _ => 0) (ctrBlocks ℓ)

/-- The CTR left-or-right oracle for the block function `f` and the challenge bit `b`: a fresh
uniform initialization vector and the CTR encryption of the selected plaintext
([KatzLindell2020], Section 3.6.3, Figure 3.9). -/
@[expose]
noncomputable def ctrOracle (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) (f : BitString n → BitString n) (b : Bool)
    (q : CTRQuery n) : ProbComp (BitString n × List (BitString n)) := do
  let iv ← ProbComp.uniform (BitString n)
  return (iv, ctrEncryptBlocks f counter iv (ctrSelect ℓ b q))

/-- The ideal oracle: a uniform initialization vector and `ctrBlocks ℓ q` independent uniform
ciphertext blocks, independent of the challenge bit. -/
@[expose]
noncomputable def ctrIdealOracle (ℓ : ℕ) (q : CTRQuery n) :
    ProbComp (BitString n × List (BitString n)) := do
  let iv ← ProbComp.uniform (BitString n)
  let c ← ProbComp.uniform (Fin (ctrBlocks ℓ q) → BitString n)
  return (iv, List.ofFn c)

/-- The CTR left-or-right experiment for the keyed block function `F` with challenge bit `b`
([KatzLindell2020], Definition 3.22): a uniform key, then the adversary with oracle access to CTR
encryption under that key. -/
@[expose]
noncomputable def ctrCpaGame {Key : Type} (counter : BitString n → ℕ → BitString n) [Fintype Key] [Nonempty Key]
    (F : Key → BitString n → BitString n) (ℓ : ℕ) (b : Bool) (adversary : CTRAdversary n) :
    Game :=
  ProbComp.eval do
    let key ← ProbComp.uniform Key
    OracleComp.interpret (sumHandler ProbComp.unifFin (ctrOracle counter ℓ (F key) b)) adversary

/-- The ideal experiment: the adversary receives fresh uniform ciphertexts. -/
@[expose]
noncomputable def ctrIdealGame (ℓ : ℕ) (adversary : CTRAdversary n) : Game :=
  ProbComp.eval
    (OracleComp.interpret (sumHandler ProbComp.unifFin (ctrIdealOracle ℓ)) adversary)

/-! ### Section 2: The Reduction to a Pseudorandom Function -/

/-- The CTR keystream of length `k` from `x`, computed with `k` calls to a function oracle. -/
@[expose]
def ctrQueries (counter : BitString n → ℕ → BitString n) (iv : BitString n) (k : ℕ) :
    ProbOracleComp (fun _ : BitString n => BitString n) (List (BitString n)) :=
  (List.range k).mapM fun i => ProbOracleComp.query (counter iv i)

/-- One CTR encryption computed with a function oracle: a private uniform initialization vector,
then the keystream from the oracle, added to the selected plaintext. -/
@[expose]
noncomputable def ctrQueryProgram (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) (b : Bool) (q : CTRQuery n) :
    ProbOracleComp (fun _ : BitString n => BitString n) (BitString n × List (BitString n)) := do
  let iv ← ProbOracleComp.sample (ProbComp.uniform (BitString n))
  let ks ← ctrQueries counter iv (ctrSelect ℓ b q).length
  return (iv, List.zipWith (· + ·) ks (ctrSelect ℓ b q))

/-- The PRF distinguisher built from a left-or-right adversary ([KatzLindell2020], proof of
Theorem 3.33): run the adversary and answer each query by CTR encryption with the oracle, under
the challenge bit `b`. -/
@[expose]
noncomputable def ctrReduction (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) (b : Bool) (adversary : CTRAdversary n) :
    PRF.Adversary (BitString n) (BitString n) :=
  (OracleComp.interpret
    (sumHandler (fun i => ProbOracleComp.sample (ProbComp.unifFin i)) (ctrQueryProgram counter ℓ b))
    adversary : ProbOracleComp (fun _ : BitString n => BitString n) Bool)

/-- Answering the keystream calls with a fixed function `f` computes the CTR chain of `f`. -/
theorem interpret_ctrQueries (counter : BitString n → ℕ → BitString n) (f : BitString n → BitString n) (iv : BitString n) (k : ℕ) :
    OracleComp.interpret (sumHandler ProbComp.unifFin fun y => pure (f y))
      (ctrQueries counter iv k) = (pure (ctrMaskBlocks f counter iv k) : ProbComp (List (BitString n))) := by
  simp [ctrQueries, ctrMaskBlocks, OracleComp.interpret_mapM_query_pure]

private theorem interpret_unifFin_self {α : Type} (p : ProbComp α) :
    OracleComp.interpret ProbComp.unifFin p = p :=
  OracleComp.interpret_query_eq_self p

/-- The CTR experiment for the keyed block function `F` is the real PRF experiment for `F` and
the reduction `ctrReduction counter ℓ b adversary`. -/
theorem ctrCpaGame_eq_realGame {Key : Type} [Fintype Key] [Nonempty Key]
    (F : Key → BitString n → BitString n) (ℓ : ℕ) (b : Bool) (adversary : CTRAdversary n) :
    ctrCpaGame F ℓ b adversary = PRF.realGame F (ctrReduction counter ℓ b adversary) := by
  unfold ctrCpaGame PRF.realGame ctrReduction
  congr 1
  refine bind_congr fun key => ?_
  rw [OracleComp.interpret_interpret]
  congr 1
  funext q
  cases q with
  | inl i =>
    simp only [ProbOracleComp.interpret_sample, interpret_unifFin_self]
  | inr q =>
    simp [ctrOracle, ctrQueryProgram, ctrEncryptBlocks, ProbOracleComp.interpret_sample,
      interpret_unifFin_self, interpret_ctrQueries counter]

/-- The keystream program makes exactly `k` oracle calls. -/
theorem isQueryBounded_ctrQueries (x : BitString n) (k : ℕ) :
    ProbOracleComp.IsQueryBounded (ctrChainQueries x k) k := by
  induction k generalizing x with
  | zero =>
    simp only [ctrChainQueries]
    exact OracleComp.IsCostBounded.pure _ _
  | succ k ih =>
    simp only [ctrChainQueries]
    exact OracleComp.IsCostBounded.mono
      (OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query (Sum.inr x)) fun y =>
        OracleComp.IsCostBounded.bind (ih y) fun ys => OracleComp.IsCostBounded.pure (y :: ys) 0)
      (by simp only [Sum.elim_inr]; omega)

/-- If the queries of `adversary` ask at most `K` blocks in total, the reduction makes at most
`K` oracle calls. -/
theorem isQueryBounded_ctrReduction (ℓ : ℕ) (b : Bool) {adversary : CTRAdversary n} {K : ℕ}
    (h : OracleComp.IsCostBounded (ctrCost ℓ) adversary K) :
    ProbOracleComp.IsQueryBounded (ctrReduction counter ℓ b adversary) K := by
  refine OracleComp.IsCostBounded.interpret (fun q => ?_) h
  cases q with
  | inl i => exact ProbOracleComp.isCostBounded_sample _ _
  | inr q =>
    have hq := OracleComp.IsCostBounded.bind
      (ProbOracleComp.isCostBounded_sample (spec := fun _ : BitString n => BitString n)
        (fun _ => 1) (ProbComp.uniform (BitString n))) fun iv =>
      OracleComp.IsCostBounded.bind (isQueryBounded_ctrQueries counter iv (ctrSelect ℓ b q).length)
        fun ks => OracleComp.IsCostBounded.pure (iv, List.zipWith (· + ·) ks (ctrSelect ℓ b q)) 0
    exact OracleComp.IsCostBounded.mono hq (by simp [ctrCost])

/-! ### Section 3: Lazy Sampling with a Repetition Flag -/

/-- A lazily sampled function table and a flag recording a repeated input. -/
private abbrev FlagState (n : ℕ) : Type := List (BitString n × BitString n) × Bool

/-- Lazy sampling of a uniform function: a cached input returns its cached value and raises the
flag, and a new input draws a uniform value. -/
private noncomputable def lazyStep (x : BitString n) : StateT (FlagState n) PMF (BitString n) :=
  fun s => match s.1.lookup x with
    | some y => PMF.pure (y, (s.1, true))
    | none => (PMF.uniformOfFintype (BitString n)).map fun u => (u, ((x, u) :: s.1, s.2))

/-- Fresh sampling: every input draws a new uniform value, and a repeated input raises the
flag. -/
private noncomputable def freshStep (x : BitString n) : StateT (FlagState n) PMF (BitString n) :=
  fun s => (PMF.uniformOfFintype (BitString n)).map fun u =>
    (u, ((x, u) :: s.1, s.2 || (s.1.lookup x).isSome))

private theorem map_eq_bind_pure {α β : Type} (f : α → β) (p : PMF α) :
    p.map f = p.bind fun a => PMF.pure (f a) := rfl

private theorem snd_eq_of_mem_support_lift {α σ : Type} {p : PMF α} {s : σ} {z : α × σ}
    (hz : z ∈ ((StateT.lift p : StateT σ PMF α) s).support) : z.2 = s := by
  simp only [StateT.lift, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hz
  obtain ⟨a, -, rfl⟩ := hz
  rfl

private theorem prop_of_mem_support_map {α β : Type} {p : PMF α} {f : α → β} {z : β}
    (hz : z ∈ (p.map f).support) {P : β → Prop} (h : ∀ a, P (f a)) : P z := by
  obtain ⟨a, -, rfl⟩ := (PMF.mem_support_map_iff f p z).1 hz
  exact h a

private theorem flag_of_mem_support_pure {y : BitString n}
    {c : List (BitString n × BitString n)} {z : BitString n × FlagState n}
    (hz : z ∈ (PMF.pure (y, (c, true))).support) : z.2.2 = true := by
  rw [PMF.mem_support_pure_iff] at hz
  subst hz
  rfl

private theorem toOuterMeasure_lift_eq_zero {α σ : Type} {bad : σ → Prop} (p : PMF α) (s : σ)
    (hs : ¬bad s) : ((StateT.lift p : StateT σ PMF α) s).toOuterMeasure {x | bad x.2} = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro x hx hbad
  have h2 : x.2 = s := snd_eq_of_mem_support_lift hx
  exact hs (h2 ▸ hbad)

private theorem lazyStep_map_fst (x : BitString n) (s : FlagState n) :
    (lazyStep x s).map (fun (a, s') => (a, s'.1)) =
      memoize (fun _ => PMF.uniformOfFintype (BitString n)) x s.1 := by
  unfold lazyStep
  cases h : s.1.lookup x with
  | some y =>
    rw [memoize_of_some _ _ _ _ h]
    simp only [PMF.pure_map, Probability.PMF.monad_pure_eq_pure]
  | none =>
    rw [memoize_of_none _ _ _ h]
    simp only [map_eq_bind_pure, PMF.bind_bind, PMF.pure_bind,
      Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure]

private theorem runWith_memoize_eq {α : Type}
    (program : ProbOracleComp (fun _ : BitString n => BitString n) α) :
    (ProbOracleComp.runWith (memoize fun _ => PMF.uniformOfFintype (BitString n)) program
      []).map Prod.fst =
      (ProbOracleComp.runWith lazyStep program ([], false)).map Prod.fst := by
  rw [← ProbOracleComp.runWith_map_state lazyStep
    (memoize fun _ => PMF.uniformOfFintype (BitString n)) Prod.fst lazyStep_map_fst program
    ([], false), PMF.map_comp]
  exact congrArg (fun f => PMF.map f _) (funext fun ⟨_, _⟩ => rfl)

private theorem identicalUntilBad_lazyStep_freshStep :
    OracleComp.IdenticalUntilBad
      (sumHandler (fun i => StateT.lift (ProbComp.unifOracle i)) (lazyStep (n := n)))
      (sumHandler (fun i => StateT.lift (ProbComp.unifOracle i)) (freshStep (n := n)))
      (fun s : FlagState n => s.2 = true) where
  agree q s _ a s' hs' := by
    cases q with
    | inl i => rfl
    | inr x =>
      change lazyStep x s (a, s') = freshStep x s (a, s')
      simp only [lazyStep, freshStep]
      cases h : s.1.lookup x with
      | none => simp only [Option.isSome_none, Bool.or_false]
      | some y =>
        simp only [Option.isSome_some, Bool.or_true]
        have h1 : (PMF.pure (y, (s.1, true)) : PMF (BitString n × FlagState n)) (a, s') = 0 :=
          (PMF.apply_eq_zero_iff _ _).2 fun hz => hs' (flag_of_mem_support_pure hz)
        have h2 : ((PMF.uniformOfFintype (BitString n)).map fun u =>
            (u, ((x, u) :: s.1, true))) (a, s') = 0 :=
          (PMF.apply_eq_zero_iff _ _).2 fun hz =>
            hs' (prop_of_mem_support_map hz (P := fun z => z.2.2 = true) fun _ => rfl)
        rw [h1, h2]
  absorb_first q s hs x hx := by
    have hs' : s.2 = true := hs
    cases q with
    | inl i =>
      rw [snd_eq_of_mem_support_lift hx]
      exact hs
    | inr y =>
      change x ∈ (lazyStep y s).support at hx
      simp only [lazyStep] at hx
      split at hx
      · exact flag_of_mem_support_pure hx
      · exact prop_of_mem_support_map hx (P := fun z => z.2.2 = true) fun _ => hs'
  absorb_second q s hs x hx := by
    have hs' : s.2 = true := hs
    cases q with
    | inl i =>
      rw [snd_eq_of_mem_support_lift hx]
      exact hs
    | inr y =>
      change x ∈ (freshStep y s).support at hx
      exact prop_of_mem_support_map hx (P := fun z => z.2.2 = true) fun _ => by simp [hs']

private theorem idealGame_ctrReduction_eq (ℓ : ℕ) (b : Bool) (adversary : CTRAdversary n) :
    PRF.idealGame (ctrReduction counter ℓ b adversary) =
      (ProbOracleComp.runWith lazyStep (ctrReduction counter ℓ b adversary) ([], false)).map
        Prod.fst := by
  rw [← runWith_memoize_eq]
  have h := RandomOracle.interpret_prob_eq_memoize
    (fun _ : BitString n => PMF.uniformOfFintype (BitString n)) (ctrReduction counter ℓ b adversary)
  rw [← h]
  simp only [PRF.idealGame, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbOracleComp.eval_interpret, ProbComp.eval_pure, PMF.pi_uniformOfFintype,
    Probability.PMF.monad_bind_eq_bind]

private theorem advantage_lazy_fresh_le (program : PRF.Adversary (BitString n) (BitString n)) :
    (Game.advantage ((ProbOracleComp.runWith lazyStep program ([], false)).map Prod.fst)
        ((ProbOracleComp.runWith freshStep program ([], false)).map Prod.fst) : ℝ) ≤
      ((ProbOracleComp.runWith freshStep program ([], false)).toOuterMeasure
        {x | x.2.2 = true}).toReal := by
  have h := identicalUntilBad_lazyStep_freshStep.advantage_le program ([], false)
    fun x => PMF.pure x.1
  rw [identicalUntilBad_lazyStep_freshStep.bad_eq] at h
  exact h


/-! ### Section 4: The Collision Bound for Fresh Sampling -/

/-- The table after fresh sampling along a keystream from `x`: each draw is recorded under the
input that produced it. -/
private def chainCache :
    List (BitString n × BitString n) → BitString n → List (BitString n) →
      List (BitString n × BitString n)
  | c, _, [] => c
  | c, x, u :: us => chainCache ((x, u) :: c) u us

/-- Whether fresh sampling along a keystream from `x` meets an input already in the table. -/
private def chainFlag :
    List (BitString n × BitString n) → BitString n → List (BitString n) → Bool
  | _, _, [] => false
  | c, x, u :: us => (c.lookup x).isSome || chainFlag ((x, u) :: c) u us

private theorem length_chainCache (c : List (BitString n × BitString n)) (x : BitString n)
    (us : List (BitString n)) : (chainCache c x us).length = c.length + us.length := by
  induction us generalizing c x with
  | nil => simp [chainCache]
  | cons u us ih =>
    simp only [chainCache, ih, List.length_cons]
    omega

private theorem isSome_lookup_iff (c : List (BitString n × BitString n)) (x : BitString n) :
    (c.lookup x).isSome = true ↔ x ∈ c.map Prod.fst := by
  induction c with
  | nil => simp [List.lookup]
  | cons p c ih =>
    obtain ⟨k, v⟩ := p
    by_cases h : x = k
    · subst h
      simp [List.lookup]
    · have hb : (x == k) = false := by simpa using h
      simp [List.lookup, hb, ih, h]

private theorem not_goodChain_of_chainFlag (c : List (BitString n × BitString n))
    (x : BitString n) (us : List (BitString n)) (h : chainFlag c x us = true) :
    ¬goodChain (c.map Prod.fst) x (List.replicate us.length 0) us := by
  induction us generalizing c x with
  | nil => simp [chainFlag] at h
  | cons u us ih =>
    simp only [List.length_cons, List.replicate_succ, goodChain, add_zero, not_and]
    intro hx
    simp only [chainFlag, Bool.or_eq_true] at h
    rcases h with h | h
    · exact absurd ((isSome_lookup_iff c x).1 h) hx
    · exact ih ((x, u) :: c) u h

private theorem length_of_mem_support_uniformBlocks {k : ℕ} {us : List (BitString n)}
    (h : us ∈ (uniformBlocks (n := n) k).support) : us.length = k := by
  rw [uniformBlocks, PMF.support_map] at h
  obtain ⟨f, -, rfl⟩ := h
  simp

private theorem length_of_mem_support_chainDraws {k : ℕ}
    {p : BitString n × List (BitString n)}
    (h : p ∈ ((PMF.uniformOfFintype (BitString n)).bind fun iv =>
      (uniformBlocks (n := n) k).map (iv, ·)).support) : p.2.length = k := by
  rw [PMF.mem_support_bind_iff] at h
  obtain ⟨iv, -, hp⟩ := h
  rw [PMF.support_map] at hp
  obtain ⟨us, hus, rfl⟩ := hp
  exact length_of_mem_support_uniformBlocks hus

/-- Fresh sampling along a keystream of length `k` draws `k` uniform blocks. -/
private theorem runWith_freshStep_ctrChainQueries (x : BitString n) (k : ℕ) (s : FlagState n) :
    ProbOracleComp.runWith freshStep (ctrChainQueries x k) s =
      (uniformBlocks k).map fun us =>
        (us, (chainCache s.1 x us, s.2 || chainFlag s.1 x us)) := by
  induction k generalizing x s with
  | zero => simp [ctrChainQueries, chainCache, chainFlag]
  | succ k ih =>
    simp only [ctrChainQueries, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
      ProbOracleComp.runWith_pure, ih, freshStep, uniformBlocks_succ, map_eq_bind_pure,
      PMF.bind_bind, PMF.pure_bind, chainCache, chainFlag, Bool.or_assoc]

/-- One encryption under fresh sampling: a uniform initialization vector and uniform keystream
blocks, added to the selected plaintext. -/
private theorem runWith_freshStep_ctrQueryProgram (ℓ : ℕ) (b : Bool) (q : CTRQuery n)
    (s : FlagState n) :
    ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q) s =
      ((PMF.uniformOfFintype (BitString n)).bind fun iv =>
        (uniformBlocks (ctrBlocks ℓ q)).map (iv, ·)).map fun p =>
          ((p.1, List.zipWith (· + ·) p.2 (ctrSelect ℓ b q)),
            (chainCache s.1 p.1 p.2, s.2 || chainFlag s.1 p.1 p.2)) := by
  simp only [ctrQueryProgram, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
    ProbComp.eval_uniform, runWith_freshStep_ctrChainQueries, ProbOracleComp.runWith_pure,
    length_ctrSelect, map_eq_bind_pure, PMF.bind_bind, PMF.pure_bind]

private theorem length_of_mem_support_freshQuery (ℓ : ℕ) (b : Bool) (q : CTRQuery n)
    (s : FlagState n) {x : (BitString n × List (BitString n)) × FlagState n}
    (hx : x ∈ (ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q) s).support) :
    x.2.1.length = s.1.length + ctrBlocks ℓ q := by
  rw [runWith_freshStep_ctrQueryProgram, PMF.support_map] at hx
  obtain ⟨⟨iv, us⟩, hp, rfl⟩ := hx
  have hlen : us.length = ctrBlocks ℓ q := length_of_mem_support_chainDraws hp
  simp only [length_chainCache, hlen]

/-- One encryption under fresh sampling raises the flag with probability at most
`k (t + k) / 2 ^ n`, where `k` is the number of blocks and `t` the size of the table. -/
private theorem toOuterMeasure_bad_freshQuery_le (ℓ : ℕ) (b : Bool) (q : CTRQuery n)
    (s : FlagState n) (hs : ¬s.2 = true) :
    (ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q) s).toOuterMeasure
        {x | x.2.2 = true} ≤
      ((ctrBlocks ℓ q * (s.1.length + ctrBlocks ℓ q) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [runWith_freshStep_ctrQueryProgram, PMF.toOuterMeasure_map_apply]
  have hbad := toOuterMeasure_badChain_le (List.replicate (ctrBlocks ℓ q) (0 : BitString n))
    (s.1.map Prod.fst)
  simp only [List.length_replicate, List.length_map] at hbad
  refine le_trans (PMF.toOuterMeasure_mono _ ?_) hbad
  rintro ⟨iv, us⟩ ⟨hflag, hp⟩
  have hlen : us.length = ctrBlocks ℓ q := length_of_mem_support_chainDraws hp
  have hs' : s.2 = false := by simpa using hs
  have hflag' : chainFlag s.1 iv us = true := by simpa [hs'] using hflag
  have h := not_goodChain_of_chainFlag s.1 iv us hflag'
  rw [hlen] at h
  exact h

/-- The flag is raised with probability at most `K (K + ℓ) / 2 ^ n` when the queries ask at most
`K` blocks in total and at most `ℓ` blocks each. -/
private theorem toOuterMeasure_bad_fresh_le (ℓ : ℕ) (b : Bool) {adversary : CTRAdversary n}
    {K : ℕ} (h : OracleComp.IsCostBounded (ctrCost ℓ) adversary K) :
    (ProbOracleComp.runWith freshStep (ctrReduction counter ℓ b adversary) ([], false)).toOuterMeasure
        {x | x.2.2 = true} ≤
      ((K * (K + ℓ) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [ctrReduction, ProbOracleComp.runWith_interpret_sumHandler]
  refine (OracleComp.toOuterMeasure_bad_le_two_budgets
    (handler := sumHandler (fun i => StateT.lift (ProbComp.unifOracle i))
      fun q => ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q))
    (bad := fun s : FlagState n => s.2 = true) (ctrCost ℓ) (fun _ => 0)
    (fun s => ((s.1.length + ℓ : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹) (fun _ => 0)
    ((2 : ℝ≥0∞) ^ n)⁻¹ 0 0 0 ?_ ?_ ?_ h
    (OracleComp.IsCostBounded.of_forall_cost_eq_zero (fun _ => rfl) adversary)
    (s := ([], false)) (by simp)).trans (le_of_eq ?_)
  · intro q s hs
    cases q with
    | inl i =>
      exact (toOuterMeasure_lift_eq_zero (bad := fun s : FlagState n => s.2 = true)
        (ProbComp.unifOracle i) s hs).trans_le zero_le
    | inr q =>
      calc (ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q) s).toOuterMeasure
            {x | x.2.2 = true}
          ≤ ((ctrBlocks ℓ q * (s.1.length + ctrBlocks ℓ q) : ℕ) : ℝ≥0∞) *
              ((2 : ℝ≥0∞) ^ n)⁻¹ :=
            toOuterMeasure_bad_freshQuery_le ℓ b q s hs
        _ ≤ (ctrBlocks ℓ q : ℝ≥0∞) *
              (((s.1.length + ℓ : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹) := by
            rw [Nat.cast_mul, mul_assoc]
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ zero_le) zero_le
            exact Nat.cast_le.2 (Nat.add_le_add_left (ctrBlocks_le ℓ q) _)
        _ = _ := by simp [ctrCost]
  · intro q s _ x hx _
    cases q with
    | inl i =>
      rw [snd_eq_of_mem_support_lift hx]
      exact le_add_right (le_add_right le_rfl)
    | inr q =>
      have hlen := length_of_mem_support_freshQuery ℓ b q s hx
      simp only [hlen, ctrCost, Sum.elim_inr]
      refine le_of_eq ?_
      push_cast
      ring
  · intro q s _ x _ _
    exact zero_le
  · simp only [List.length_nil, Nat.cast_mul, Nat.cast_add, Nat.cast_zero]
    ring

/-! ### Section 5: Fresh Sampling Gives the Ideal Experiment -/

private theorem uniformBlocks_eq (k : ℕ) :
    uniformBlocks (n := n) k = (PMF.uniformOfFintype (Fin k → BitString n)).map List.ofFn := by
  rw [uniformBlocks, PMF.iid_uniformOfFintype]

/-- Adding a fixed message to uniform blocks leaves them uniform. -/
private theorem map_zipWith_uniformBlocks :
    ∀ ms : List (BitString n),
      (uniformBlocks ms.length).map (fun us => List.zipWith (· + ·) us ms) =
        uniformBlocks ms.length
  | [] => by simp
  | m :: ms => by
    have hshift : (PMF.uniformOfFintype (BitString n)).map (· + m) =
        PMF.uniformOfFintype (BitString n) :=
      PMF.uniformOfFintype_map_equiv (Equiv.addRight m)
    calc (uniformBlocks (m :: ms).length).map (fun us => List.zipWith (· + ·) us (m :: ms))
        = (PMF.uniformOfFintype (BitString n)).bind fun u =>
            ((uniformBlocks ms.length).map fun us => List.zipWith (· + ·) us ms).map
              ((u + m) :: ·) := by
          rw [List.length_cons, uniformBlocks_succ]
          simp only [map_eq_bind_pure, PMF.bind_bind, PMF.pure_bind, List.zipWith_cons_cons]
      _ = (PMF.uniformOfFintype (BitString n)).bind fun u =>
            (uniformBlocks ms.length).map ((u + m) :: ·) := by
          rw [map_zipWith_uniformBlocks ms]
      _ = ((PMF.uniformOfFintype (BitString n)).map (· + m)).bind fun u =>
            (uniformBlocks ms.length).map (u :: ·) :=
          (PMF.bind_map (PMF.uniformOfFintype (BitString n)) (· + m) fun u =>
            (uniformBlocks ms.length).map (u :: ·)).symm
      _ = uniformBlocks (m :: ms).length := by
          rw [hshift, List.length_cons, uniformBlocks_succ]

/-- Adding a fixed message to the keystream draws leaves the draws uniform. -/
private theorem map_chainDraws_zipWith (ms : List (BitString n)) :
    ((PMF.uniformOfFintype (BitString n)).bind fun iv =>
        (uniformBlocks (n := n) ms.length).map (iv, ·)).map
      (fun p => (p.1, List.zipWith (· + ·) p.2 ms)) =
      (PMF.uniformOfFintype (BitString n)).bind fun iv =>
        (uniformBlocks (n := n) ms.length).map (iv, ·) := by
  calc ((PMF.uniformOfFintype (BitString n)).bind fun iv =>
          (uniformBlocks (n := n) ms.length).map (iv, ·)).map
        (fun p => (p.1, List.zipWith (· + ·) p.2 ms))
      = (PMF.uniformOfFintype (BitString n)).bind fun iv =>
          ((uniformBlocks (n := n) ms.length).map fun us => List.zipWith (· + ·) us ms).map
            (iv, ·) := by
        simp only [map_eq_bind_pure, PMF.bind_bind, PMF.pure_bind]
    _ = (PMF.uniformOfFintype (BitString n)).bind fun iv =>
          (uniformBlocks (n := n) ms.length).map (iv, ·) := by
        rw [map_zipWith_uniformBlocks ms]

private theorem eval_ctrIdealOracle (ℓ : ℕ) (q : CTRQuery n) :
    ProbComp.eval (ctrIdealOracle ℓ q) =
      (PMF.uniformOfFintype (BitString n)).bind fun iv =>
        (uniformBlocks (n := n) (ctrBlocks ℓ q)).map (iv, ·) := by
  simp only [ctrIdealOracle, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
    uniformBlocks_eq, map_eq_bind_pure, PMF.bind_bind, PMF.pure_bind]

/-- Forgetting the table, one encryption under fresh sampling is one call to the ideal
oracle. -/
private theorem map_unit_runWith_freshStep_ctrQueryProgram (ℓ : ℕ) (b : Bool) (q : CTRQuery n)
    (s : FlagState n) :
    (ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q) s).map (fun x => (x.1, ())) =
      (ProbComp.eval (ctrIdealOracle ℓ q)).map (·, ()) := by
  have hpad := map_chainDraws_zipWith (ctrSelect ℓ b q)
  rw [length_ctrSelect] at hpad
  rw [runWith_freshStep_ctrQueryProgram, eval_ctrIdealOracle]
  conv_rhs => rw [← hpad]
  exact (PMF.map_comp _ _ _).trans (Eq.symm (PMF.map_comp _ _ _))

private theorem map_fst_map_unit {α σ : Type} (p : PMF (α × σ)) :
    (p.map fun x => (x.1, ())).map Prod.fst = p.map Prod.fst :=
  PMF.map_comp _ _ _

private theorem map_fst_map_pair_unit {α : Type} (p : PMF α) :
    (p.map fun a => (a, ())).map Prod.fst = p :=
  (PMF.map_comp _ _ _).trans (PMF.map_id _)

/-- Under fresh sampling, the reduction's output is distributed as in the ideal experiment. -/
private theorem freshGame_eq_ctrIdealGame (ℓ : ℕ) (b : Bool) (adversary : CTRAdversary n) :
    (ProbOracleComp.runWith freshStep (ctrReduction counter ℓ b adversary) ([], false)).map Prod.fst =
      ctrIdealGame ℓ adversary := by
  have hstate :
      (ProbOracleComp.runWith (fun q => ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q))
          adversary ([], false)).map (fun x => (x.1, ())) =
        ProbOracleComp.runWith
          (fun q (u : Unit) => (ProbComp.eval (ctrIdealOracle ℓ q)).map (·, u)) adversary () :=
    ProbOracleComp.runWith_map_state
      (fun q => ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q))
      (fun q (u : Unit) => (ProbComp.eval (ctrIdealOracle ℓ q)).map (·, u)) (fun _ => ())
      (fun q s => map_unit_runWith_freshStep_ctrQueryProgram counter ℓ b q s) adversary ([], false)
  have hro :
      ProbOracleComp.runWith
          (fun q (u : Unit) => (ProbComp.eval (ctrIdealOracle ℓ q)).map (·, u)) adversary () =
        (OracleComp.interpret
          (sumHandler ProbComp.unifOracle fun q => ProbComp.eval (ctrIdealOracle ℓ q))
          adversary).map (·, ()) :=
    ProbOracleComp.runWith_readOnly (fun q _ => ProbComp.eval (ctrIdealOracle ℓ q)) adversary ()
  rw [ctrReduction, ProbOracleComp.runWith_interpret_sumHandler, ← map_fst_map_unit, hstate, hro,
    map_fst_map_pair_unit, ctrIdealGame, ProbOracleComp.eval_interpret]

/-! ### Section 6: Security of CTR Mode -/

private theorem advantage_le_two (g₀ g₁ g₂ : Game) :
    (Game.advantage g₀ g₂ : ℝ) ≤ Game.advantage g₀ g₁ + Game.advantage g₂ g₁ := by
  rw [Game.advantage_comm g₂ g₁]
  exact_mod_cast Game.advantage_triangle g₀ g₁ g₂

private theorem advantage_le_four (g₀ g₁ g₂ g₃ g₄ : Game) :
    (Game.advantage g₀ g₄ : ℝ) ≤
      Game.advantage g₀ g₁ + Game.advantage g₁ g₂ + Game.advantage g₃ g₂ +
        Game.advantage g₄ g₃ := by
  have h₁ : (Game.advantage g₀ g₄ : ℝ) ≤ Game.advantage g₀ g₁ + Game.advantage g₁ g₄ := by
    exact_mod_cast Game.advantage_triangle g₀ g₁ g₄
  have h₂ : (Game.advantage g₁ g₄ : ℝ) ≤ Game.advantage g₁ g₂ + Game.advantage g₂ g₄ := by
    exact_mod_cast Game.advantage_triangle g₁ g₂ g₄
  have h₃ : (Game.advantage g₂ g₄ : ℝ) ≤ Game.advantage g₃ g₂ + Game.advantage g₄ g₃ :=
    (advantage_le_two g₂ g₃ g₄).trans_eq (by rw [Game.advantage_comm g₂ g₃, add_comm])
  linarith

/-- **The reduction against a uniform random function.** If the queries of `adversary` ask at
most `K` blocks in total, then with a uniform random function the output of the reduction
`ctrReduction counter ℓ b adversary` is within `K (K + ℓ) / 2 ^ n` of the ideal experiment, whatever the
challenge bit `b`. -/
theorem advantage_idealGame_ctrReduction_le (ℓ : ℕ) (b : Bool) {adversary : CTRAdversary n}
    {K : ℕ} (h : OracleComp.IsCostBounded (ctrCost ℓ) adversary K) :
    (Game.advantage (PRF.idealGame (ctrReduction counter ℓ b adversary)) (ctrIdealGame ℓ adversary) :
        ℝ) ≤ (K : ℝ) * (K + ℓ) / 2 ^ n := by
  rw [idealGame_ctrReduction_eq, ← freshGame_eq_ctrIdealGame ℓ b adversary]
  refine (advantage_lazy_fresh_le _).trans ?_
  have hne : ((K * (K + ℓ) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.inv_ne_top.2 (pow_ne_zero _ two_ne_zero))
  refine (ENNReal.toReal_mono hne (toOuterMeasure_bad_fresh_le ℓ b h)).trans (le_of_eq ?_)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat]
  push_cast
  ring

/-- **CTR mode with a uniform random function** ([KatzLindell2020], Section 3.6.3). If the
queries of `adversary` ask at most `K` blocks in total and at most `ℓ` blocks each, its
left-or-right advantage against CTR mode with a uniform random block function is at most
`2 K (K + ℓ) / 2 ^ n`. -/
theorem advantage_ctrCpaGame_randomFunction_le (ℓ : ℕ) {adversary : CTRAdversary n} {K : ℕ}
    (h : OracleComp.IsCostBounded (ctrCost ℓ) adversary K) :
    (Game.advantage (ctrCpaGame (fun f : BitString n → BitString n => f) ℓ false adversary)
        (ctrCpaGame (fun f : BitString n → BitString n => f) ℓ true adversary) : ℝ) ≤
      2 * ((K : ℝ) * (K + ℓ) / 2 ^ n) := by
  have e : ∀ b, ctrCpaGame (fun f : BitString n → BitString n => f) ℓ b adversary =
      PRF.idealGame (ctrReduction counter ℓ b adversary) := fun b => by
    rw [ctrCpaGame_eq_realGame]
    rfl
  rw [e, e]
  have h₀ := advantage_idealGame_ctrReduction_le ℓ false h
  have h₁ := advantage_idealGame_ctrReduction_le ℓ true h
  have h₂ := advantage_le_two (PRF.idealGame (ctrReduction ℓ false adversary))
    (ctrIdealGame ℓ adversary) (PRF.idealGame (ctrReduction ℓ true adversary))
  linarith

/-- **CTR mode is CPA-secure for a pseudorandom function** ([KatzLindell2020], Section 3.6.3,
following the proof of Theorem 3.33). If the queries of `adversary` ask at most `K` blocks in
total and at most `ℓ` blocks each, its left-or-right advantage against CTR mode with the keyed
function `F` is at most the PRF advantages of the reductions `ctrReduction ℓ false adversary` and
`ctrReduction ℓ true adversary`, each making at most `K` oracle calls
(`isQueryBounded_ctrReduction`), plus `2 K (K + ℓ) / 2 ^ n`. -/
theorem advantage_ctrCpaGame_le {Key : Type} [Fintype Key] [Nonempty Key]
    (F : Key → BitString n → BitString n) (ℓ : ℕ) {adversary : CTRAdversary n} {K : ℕ}
    (h : OracleComp.IsCostBounded (ctrCost ℓ) adversary K) :
    (Game.advantage (ctrCpaGame F ℓ false adversary) (ctrCpaGame F ℓ true adversary) : ℝ) ≤
      PRF.advantage F (ctrReduction ℓ false adversary) +
        PRF.advantage F (ctrReduction ℓ true adversary) + 2 * ((K : ℝ) * (K + ℓ) / 2 ^ n) := by
  rw [ctrCpaGame_eq_realGame, ctrCpaGame_eq_realGame]
  have h₀ := advantage_idealGame_ctrReduction_le ℓ false h
  have h₁ := advantage_idealGame_ctrReduction_le ℓ true h
  have h₄ := advantage_le_four (PRF.realGame F (ctrReduction ℓ false adversary))
    (PRF.idealGame (ctrReduction ℓ false adversary)) (ctrIdealGame ℓ adversary)
    (PRF.idealGame (ctrReduction ℓ true adversary))
    (PRF.realGame F (ctrReduction ℓ true adversary))
  have e₀ : (PRF.advantage F (ctrReduction ℓ false adversary) : ℝ) =
      Game.advantage (PRF.realGame F (ctrReduction ℓ false adversary))
        (PRF.idealGame (ctrReduction ℓ false adversary)) := rfl
  have e₁ : (PRF.advantage F (ctrReduction ℓ true adversary) : ℝ) =
      Game.advantage (PRF.realGame F (ctrReduction ℓ true adversary))
        (PRF.idealGame (ctrReduction ℓ true adversary)) := rfl
  linarith

end Cslib.Crypto
