/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.BlockCipher.Modes
public import CslibFrontier.Crypto.Primitives.PRF.Finite
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.QueryCount
import CslibFrontier.Crypto.Computational.Encryption.RandomFunctionHybrid
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.UntilBad.TwoCost
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event

/-!
# CPA Security of Counter (CTR) Mode

Counter mode ([KatzLindell2020], Section 3.6.3, Figure 3.9) encrypts a message of `k` blocks under
a block function `f`, a counter schedule `counter : BitString n → ℕ → BitString n`, and a uniform
initialization vector `iv` by XORing the keystream `f (counter iv 0), f (counter iv 1), …` with
the plaintext blocks. [KatzLindell2020] (Section 3.6.3, Theorem 3.33, p. 93) proves that CTR mode
is CPA-secure whenever `f` is a pseudorandom function.

The security notion is the left-or-right multiple-encryption experiment of [KatzLindell2020],
Definition 3.22: the adversary repeatedly submits pairs of equal-length messages and receives the
encryption of the left or the right message according to a hidden bit `b`.

The proof works for any counter schedule `counter : BitString n → ℕ → BitString n` satisfying
within-query distinctness (`∀ iv i j, i < ℓ → j < ℓ → i ≠ j → counter iv i ≠ counter iv j`) and
per-offset injectivity in the IV (`∀ i < ℓ, Function.Injective (fun iv => counter iv i)`), and is
instantiated on the canonical modular counter schedule `ctrModCounter` when `ℓ ≤ 2 ^ n`:
1. The CTR experiment is the real PRF experiment for a reduction encrypting with its oracle
   (`ctrCpaGame_eq_realGame`), making at most `K` oracle calls (`isQueryBounded_ctrReduction`).
2. Against a lazily sampled uniform random function, the reduction's view differs from fresh
   uniform ciphertexts only when some `counter iv i` hits an earlier queried input. Within-query
   distinctness rules out intra-query collisions, and per-offset injectivity bounds inter-query
   collisions by `K ^ 2 / 2 ^ n` (`advantage_idealGame_ctrReduction_le`).
3. Combining the ideal hybrids with the two PRF advantages yields the concrete bound
   (`advantage_ctrCpaGame_le`, and `advantage_ctrCpaGame_ctrModCounter_le` for `ctrModCounter`).

## Main definitions

* `Cslib.Crypto.CTRQuery`, `Cslib.Crypto.CTRSpec`, `Cslib.Crypto.CTRAdversary`: left-or-right
  queries and adaptive adversaries.
* `Cslib.Crypto.ctrSelect`, `Cslib.Crypto.ctrBlocks`, `Cslib.Crypto.ctrCost`: query selection,
  block count, and query-block cost.
* `Cslib.Crypto.ctrOracle`, `Cslib.Crypto.ctrCpaGame`, `Cslib.Crypto.ctrIdealOracle`,
  `Cslib.Crypto.ctrIdealGame`: real and ideal CTR left-or-right experiments.
* `Cslib.Crypto.ctrMaskQueriesFrom`, `Cslib.Crypto.ctrQueryProgram`, `Cslib.Crypto.ctrReduction`:
  the PRF distinguisher built from a CTR adversary.
* `Cslib.Crypto.ctrModCounter`: canonical modular-addition counter `iv + i mod 2 ^ n`.

## Main results

* `Cslib.Crypto.ctrCpaGame_eq_realGame`, `Cslib.Crypto.isQueryBounded_ctrReduction`: exact real-PRF
  equivalence and oracle-call bound.
* `Cslib.Crypto.advantage_idealGame_ctrReduction_le`: random-function idealization bound
  `K ^ 2 / 2 ^ n`.
* `Cslib.Crypto.advantage_ctrCpaGame_randomFunction_le`, `Cslib.Crypto.advantage_ctrCpaGame_le`:
  concrete CTR left-or-right CPA security bounds.
* `Cslib.Crypto.ctrModCounter_injective_left`, `Cslib.Crypto.ctrModCounter_injOn`,
  `Cslib.Crypto.advantage_ctrCpaGame_ctrModCounter_randomFunction_le`,
  `Cslib.Crypto.advantage_ctrCpaGame_ctrModCounter_le`: specializations to `ctrModCounter` for
  `ℓ ≤ 2 ^ n`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 3.6.3 (Figure 3.9, p. 92), Definition 3.22 (p. 74), Theorem 3.23 (p. 75), and
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

/-- The answer to a left-or-right query: an initialization vector and ciphertext blocks. -/
abbrev CTRSpec (n : ℕ) : CTRQuery n → Type := fun _ => BitString n × List (BitString n)

/-- An adaptive adversary in the CTR left-or-right experiment, with private coins. -/
abbrev CTRAdversary (n : ℕ) : Type := ProbOracleComp (CTRSpec n) Bool

/-- The plaintext encrypted for query `q` under challenge bit `b`: the right message if `b = true`
and the left one otherwise. Queries whose messages differ in length or exceed `ℓ` blocks encrypt
the empty message. -/
@[expose]
def ctrSelect (ℓ : ℕ) (b : Bool) (q : CTRQuery n) : List (BitString n) :=
  if q.1.length = q.2.length ∧ q.1.length ≤ ℓ then (if b then q.2 else q.1) else []

/-- The number of blocks encrypted for query `q`: the common length of a valid query, or `0`. -/
@[expose]
def ctrBlocks (ℓ : ℕ) (q : CTRQuery n) : ℕ :=
  if q.1.length = q.2.length ∧ q.1.length ≤ ℓ then q.1.length else 0

/-- The encrypted plaintext has `ctrBlocks ℓ q` blocks, regardless of the challenge bit. -/
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

/-- The cost of a call in the CTR left-or-right experiment: private draws are free and each
encryption query costs its block length. -/
@[expose]
def ctrCost (ℓ : ℕ) : ℕ ⊕ CTRQuery n → ℕ :=
  Sum.elim (fun _ => 0) (ctrBlocks ℓ)

/-- The CTR left-or-right oracle for counter schedule `counter`, block function `f`, and challenge
bit `b` ([KatzLindell2020], Section 3.6.3, Figure 3.9). -/
@[expose]
noncomputable def ctrOracle (counter : BitString n → ℕ → BitString n) (ℓ : ℕ)
    (f : BitString n → BitString n) (b : Bool) (q : CTRQuery n) :
    ProbComp (BitString n × List (BitString n)) := do
  let iv ← ProbComp.uniform (BitString n)
  return (iv, ctrEncryptBlocks f counter iv (ctrSelect ℓ b q))

/-- The ideal CTR oracle: a uniform initialization vector and `ctrBlocks ℓ q` independent uniform
ciphertext blocks, independent of the challenge bit. -/
@[expose]
noncomputable def ctrIdealOracle (ℓ : ℕ) (q : CTRQuery n) :
    ProbComp (BitString n × List (BitString n)) := do
  let iv ← ProbComp.uniform (BitString n)
  let c ← ProbComp.uniform (Fin (ctrBlocks ℓ q) → BitString n)
  return (iv, List.ofFn c)

/-- The CTR left-or-right experiment for keyed block function `F` and challenge bit `b`
([KatzLindell2020], Definition 3.22). -/
@[expose]
noncomputable def ctrCpaGame {Key : Type} (counter : BitString n → ℕ → BitString n)
    [Fintype Key] [Nonempty Key] (F : Key → BitString n → BitString n) (ℓ : ℕ) (b : Bool)
    (adversary : CTRAdversary n) : Game :=
  ProbComp.eval do
    let key ← ProbComp.uniform Key
    OracleComp.interpret (sumHandler ProbComp.unifFin (ctrOracle counter ℓ (F key) b)) adversary

/-- The ideal CTR experiment: the adversary receives fresh uniform ciphertext blocks. -/
@[expose]
noncomputable def ctrIdealGame (ℓ : ℕ) (adversary : CTRAdversary n) : Game :=
  ProbComp.eval
    (OracleComp.interpret (sumHandler ProbComp.unifFin (ctrIdealOracle ℓ)) adversary)

/-! ### Section 2: The Reduction to a Pseudorandom Function -/

/-- Query the function oracle on `counter iv i, counter iv (i + 1), …, counter iv (i + k - 1)`. -/
@[expose]
def ctrMaskQueriesFrom (counter : BitString n → ℕ → BitString n) (iv : BitString n) :
    ℕ → ℕ → ProbOracleComp (fun _ : BitString n => BitString n) (List (BitString n))
  | _, 0 => pure []
  | i, k + 1 => do
    let y ← ProbOracleComp.query (counter iv i)
    let ys ← ctrMaskQueriesFrom counter iv (i + 1) k
    return y :: ys

/-- One CTR encryption computed with a function oracle: sample a uniform IV, evaluate the keystream
masks via oracle queries starting at offset `0`, and XOR with the selected plaintext. -/
@[expose]
noncomputable def ctrQueryProgram (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) (b : Bool)
    (q : CTRQuery n) :
    ProbOracleComp (fun _ : BitString n => BitString n) (BitString n × List (BitString n)) := do
  let iv ← ProbOracleComp.sample (ProbComp.uniform (BitString n))
  let ks ← ctrMaskQueriesFrom counter iv 0 (ctrSelect ℓ b q).length
  return (iv, List.zipWith (· + ·) ks (ctrSelect ℓ b q))

/-- The PRF distinguisher built from a CTR left-or-right adversary ([KatzLindell2020], proof of
Theorem 3.33). -/
@[expose]
noncomputable def ctrReduction (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) (b : Bool)
    (adversary : CTRAdversary n) : PRF.Adversary (BitString n) (BitString n) :=
  (OracleComp.interpret
    (sumHandler (fun i => ProbOracleComp.sample (ProbComp.unifFin i))
      (ctrQueryProgram counter ℓ b))
    adversary : ProbOracleComp (fun _ : BitString n => BitString n) Bool)

private theorem range'_map_eq (i k : ℕ) (g : ℕ → BitString n) :
    (List.range' i k).map g = (List.range k).map (fun j => g (i + j)) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    simp only [List.range'_succ, List.map_cons, ih (i + 1), List.range_succ_eq_map,
      List.map_map, Function.comp_def]
    refine congrArg (g i :: ·) (List.map_congr_left fun j _ => congrArg g ?_)
    omega

/-- Answering `ctrMaskQueriesFrom counter iv i k` with a fixed function `f` evaluates
`(List.range' i k).map (fun j => f (counter iv j))`. -/
theorem interpret_ctrMaskQueriesFrom (f : BitString n → BitString n)
    (counter : BitString n → ℕ → BitString n) (iv : BitString n) (i k : ℕ) :
    OracleComp.interpret (sumHandler ProbComp.unifFin fun y => pure (f y))
      (ctrMaskQueriesFrom counter iv i k) =
      (pure ((List.range' i k).map (fun j => f (counter iv j))) :
        ProbComp (List (BitString n))) := by
  induction k generalizing i with
  | zero => simp [ctrMaskQueriesFrom]
  | succ k ih =>
    simp only [ctrMaskQueriesFrom, OracleComp.interpret_bind, ProbOracleComp.interpret_query, ih,
      pure_bind, OracleComp.interpret_pure, List.range'_succ, List.map_cons]

/-- Answering `ctrMaskQueriesFrom counter iv 0 k` with `f` computes `ctrMaskBlocks f counter iv k`.
-/
theorem interpret_ctrMaskQueriesFrom_zero (f : BitString n → BitString n)
    (counter : BitString n → ℕ → BitString n) (iv : BitString n) (k : ℕ) :
    OracleComp.interpret (sumHandler ProbComp.unifFin fun y => pure (f y))
      (ctrMaskQueriesFrom counter iv 0 k) =
      (pure (ctrMaskBlocks f counter iv k) : ProbComp (List (BitString n))) := by
  rw [interpret_ctrMaskQueriesFrom, ctrMaskBlocks, range'_map_eq]
  simp

/-- The CTR experiment for keyed function `F` equals the real PRF experiment for `F` and
`ctrReduction counter ℓ b adversary`. -/
theorem ctrCpaGame_eq_realGame {Key : Type} (counter : BitString n → ℕ → BitString n)
    [Fintype Key] [Nonempty Key] (F : Key → BitString n → BitString n) (ℓ : ℕ) (b : Bool)
    (adversary : CTRAdversary n) :
    ctrCpaGame counter F ℓ b adversary =
      PRF.realGame F (ctrReduction counter ℓ b adversary) := by
  unfold ctrCpaGame PRF.realGame ctrReduction
  congr 1
  refine bind_congr fun key => ?_
  rw [OracleComp.interpret_interpret]
  congr 1
  funext q
  cases q with
  | inl i =>
    simp only [ProbOracleComp.interpret_sample]
    exact (OracleComp.interpret_query_eq_self _).symm
  | inr q =>
    simp only [ctrOracle, ctrQueryProgram, ctrEncryptBlocks, ProbOracleComp.interpret_sample,
      OracleComp.interpret_bind, OracleComp.interpret_pure, pure_bind,
      interpret_ctrMaskQueriesFrom_zero, length_ctrSelect]
    rw [show (ProbComp.unifFin : (k : ℕ) → ProbComp (Fin (k + 1))) = OracleComp.query from rfl,
      OracleComp.interpret_query_eq_self, bind_pure_comp]

/-- `ctrMaskQueriesFrom counter iv i k` makes at most `k` oracle queries. -/
theorem isQueryBounded_ctrMaskQueriesFrom (counter : BitString n → ℕ → BitString n)
    (iv : BitString n) (i k : ℕ) :
    ProbOracleComp.IsQueryBounded (ctrMaskQueriesFrom counter iv i k) k := by
  induction k generalizing i with
  | zero =>
    simp only [ctrMaskQueriesFrom]
    exact OracleComp.IsCostBounded.pure _ _
  | succ k ih =>
    simp only [ctrMaskQueriesFrom]
    exact OracleComp.IsCostBounded.mono
      (OracleComp.IsCostBounded.bind
        (OracleComp.IsCostBounded.query (Sum.inr (counter iv i))) fun y =>
          OracleComp.IsCostBounded.bind (ih (i + 1)) fun ys =>
            OracleComp.IsCostBounded.pure (y :: ys) 0)
      (by simp only [Sum.elim_inr]; omega)

/-- If `adversary` asks at most `K` blocks in total, `ctrReduction counter ℓ b adversary` makes at
most `K` oracle calls. -/
theorem isQueryBounded_ctrReduction (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) (b : Bool)
    {adversary : CTRAdversary n} {K : ℕ} (h : OracleComp.IsCostBounded (ctrCost ℓ) adversary K) :
    ProbOracleComp.IsQueryBounded (ctrReduction counter ℓ b adversary) K := by
  refine OracleComp.IsCostBounded.interpret (fun q => ?_) h
  cases q with
  | inl i => exact ProbOracleComp.isCostBounded_sample _ _
  | inr q =>
    have hq := OracleComp.IsCostBounded.bind
      (ProbOracleComp.isCostBounded_sample (spec := fun _ : BitString n => BitString n)
        (fun _ => 1) (ProbComp.uniform (BitString n))) fun iv =>
      OracleComp.IsCostBounded.bind
        (isQueryBounded_ctrMaskQueriesFrom counter iv 0 (ctrSelect ℓ b q).length)
        fun ks =>
          OracleComp.IsCostBounded.pure (iv, List.zipWith (· + ·) ks (ctrSelect ℓ b q)) 0
    exact OracleComp.IsCostBounded.mono hq (by simp [ctrCost])

/-! ### Section 3: Inter-Query Collision Bound for Fresh CTR Sampling -/

private def ctrCache (c : List (BitString n × BitString n))
    (counter : BitString n → ℕ → BitString n) (iv : BitString n) :
    ℕ → List (BitString n) → List (BitString n × BitString n)
  | _, [] => c
  | i, u :: us => ctrCache ((counter iv i, u) :: c) counter iv (i + 1) us

private def ctrAnyHit (c : List (BitString n × BitString n))
    (counter : BitString n → ℕ → BitString n) (iv : BitString n) : ℕ → ℕ → Bool
  | _, 0 => false
  | i, k + 1 => (c.lookup (counter iv i)).isSome || ctrAnyHit c counter iv (i + 1) k

private theorem length_ctrCache (c : List (BitString n × BitString n))
    (counter : BitString n → ℕ → BitString n) (iv : BitString n) (i : ℕ)
    (us : List (BitString n)) :
    (ctrCache c counter iv i us).length = c.length + us.length := by
  induction us generalizing c i with
  | nil => simp [ctrCache]
  | cons u us ih =>
    simp only [ctrCache, ih, List.length_cons]
    omega

private theorem ctrAnyHit_cons_eq (c : List (BitString n × BitString n))
    (counter : BitString n → ℕ → BitString n) (iv : BitString n) (u : BitString n)
    (i₀ i k : ℕ) (hdistinct : ∀ j < k, counter iv (i + j) ≠ counter iv i₀) :
    ctrAnyHit ((counter iv i₀, u) :: c) counter iv i k = ctrAnyHit c counter iv i k := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    have h0 : counter iv i ≠ counter iv i₀ := by simpa using hdistinct 0 (Nat.zero_lt_succ k)
    have hbeq : (counter iv i == counter iv i₀) = false := by simpa using h0
    have hhead : (((counter iv i₀, u) :: c).lookup (counter iv i)).isSome =
        (c.lookup (counter iv i)).isSome := by
      simp [List.lookup, hbeq]
    have htail := ih (i + 1) fun j hj => by
      have := hdistinct (j + 1) (Nat.add_lt_add_right hj 1)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this
    simp only [ctrAnyHit, hhead, htail]

private theorem ctrAnyHit_eq_true_iff (c : List (BitString n × BitString n))
    (counter : BitString n → ℕ → BitString n) (iv : BitString n) (i k : ℕ) :
    ctrAnyHit c counter iv i k = true ↔ ∃ j < k, counter iv (i + j) ∈ c.map Prod.fst := by
  induction k generalizing i with
  | zero => simp [ctrAnyHit]
  | succ k ih =>
    simp only [ctrAnyHit, Bool.or_eq_true, List.lookup_isSome_iff, ih]
    constructor
    · rintro (⟨p, hp, hpe⟩ | ⟨j, hj, hmem⟩)
      · exact ⟨0, Nat.zero_lt_succ k,
          by simpa using List.mem_map.2 ⟨p, hp, (beq_iff_eq.1 hpe).symm⟩⟩
      · exact ⟨j + 1, Nat.add_lt_add_right hj 1,
          by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hmem⟩
    · rintro ⟨j, hj, hmem⟩
      cases j with
      | zero =>
        obtain ⟨v, hv⟩ : ∃ v, (counter iv i, v) ∈ c := by simpa using hmem
        exact Or.inl ⟨(counter iv i, v), hv, beq_self_eq_true _⟩
      | succ j =>
        exact Or.inr ⟨j, Nat.lt_of_add_lt_add_right hj,
          by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hmem⟩

private theorem runWith_freshStep_ctrMaskQueriesFrom
    (counter : BitString n → ℕ → BitString n) (iv : BitString n) (i k : ℕ) (s : FlagState n)
    (hinj : ∀ a b, i ≤ a → a < i + k → i ≤ b → b < i + k → a ≠ b →
      counter iv a ≠ counter iv b) :
    ProbOracleComp.runWith freshStep (ctrMaskQueriesFrom counter iv i k) s =
      (uniformBlocks k).map fun us =>
        (us, (ctrCache s.1 counter iv i us, s.2 || ctrAnyHit s.1 counter iv i k)) := by
  induction k generalizing i s with
  | zero => simp [ctrMaskQueriesFrom, ctrCache, ctrAnyHit]
  | succ k ih =>
    have hsub : ∀ a b, i + 1 ≤ a → a < i + 1 + k → i + 1 ≤ b → b < i + 1 + k → a ≠ b →
        counter iv a ≠ counter iv b := fun a b ha₀ ha₁ hb₀ hb₁ hab =>
      hinj a b (by omega) (by omega) (by omega) (by omega) hab
    have hdistinct : ∀ j < k, counter iv (i + 1 + j) ≠ counter iv i := fun j hj =>
      hinj (i + 1 + j) i (by omega) (by omega) le_rfl (by omega) (by omega)
    simp only [ctrMaskQueriesFrom, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
      ProbOracleComp.runWith_pure]
    change ((freshStep (counter iv i) s).bind fun p =>
      (ProbOracleComp.runWith freshStep (ctrMaskQueriesFrom counter iv (i + 1) k) p.2).map
        fun q => (p.1 :: q.1, q.2)) = _
    simp only [freshStep, Function.comp_def, ← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind]
    have hstep : ∀ u : BitString n,
        ProbOracleComp.runWith freshStep (ctrMaskQueriesFrom counter iv (i + 1) k)
          ((counter iv i, u) :: s.1, s.2 || (s.1.lookup (counter iv i)).isSome) =
          (uniformBlocks k).map fun us =>
            (us, (ctrCache ((counter iv i, u) :: s.1) counter iv (i + 1) us,
              s.2 || ((s.1.lookup (counter iv i)).isSome || ctrAnyHit s.1 counter iv (i + 1) k))) :=
      fun u => by
        rw [ih (i + 1) _ hsub, ctrAnyHit_cons_eq s.1 counter iv u i (i + 1) k hdistinct]
        simp only [Bool.or_assoc]
    simp only [hstep, uniformBlocks_succ, Function.comp_def, ← PMF.bind_pure_comp, PMF.bind_bind,
      PMF.pure_bind, ctrCache, ctrAnyHit]

private theorem runWith_freshStep_ctrQueryProgram
    (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) (b : Bool) (q : CTRQuery n)
    (s : FlagState n)
    (hintra : ∀ iv i j, i < ℓ → j < ℓ → i ≠ j → counter iv i ≠ counter iv j) :
    ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q) s =
      ((PMF.uniformOfFintype (BitString n)).bind fun iv =>
        (uniformBlocks (ctrBlocks ℓ q)).map (iv, ·)).map fun p =>
          ((p.1, List.zipWith (· + ·) p.2 (ctrSelect ℓ b q)),
            (ctrCache s.1 counter p.1 0 p.2,
              s.2 || ctrAnyHit s.1 counter p.1 0 (ctrBlocks ℓ q))) := by
  simp only [ctrQueryProgram, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
    ProbComp.eval_uniform, length_ctrSelect, Function.comp_def, ← PMF.bind_pure_comp,
    PMF.bind_bind, PMF.pure_bind]
  refine PMF.bind_congr_on_support _ _ _ fun iv _ => ?_
  have hinj : ∀ a b', 0 ≤ a → a < 0 + ctrBlocks ℓ q → 0 ≤ b' → b' < 0 + ctrBlocks ℓ q → a ≠ b' →
      counter iv a ≠ counter iv b' := fun a b' _ ha _ hb hab =>
    hintra iv a b' (lt_of_lt_of_le (by omega) (ctrBlocks_le ℓ q))
      (lt_of_lt_of_le (by omega) (ctrBlocks_le ℓ q)) hab
  rw [runWith_freshStep_ctrMaskQueriesFrom counter iv 0 (ctrBlocks ℓ q) s hinj]
  simp only [ProbOracleComp.runWith_pure, Function.comp_def, ← PMF.bind_pure_comp, PMF.bind_bind,
    PMF.pure_bind]

private theorem length_of_mem_support_freshQuery
    (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) (b : Bool) (q : CTRQuery n)
    (s : FlagState n)
    (hintra : ∀ iv i j, i < ℓ → j < ℓ → i ≠ j → counter iv i ≠ counter iv j)
    {x : (BitString n × List (BitString n)) × FlagState n}
    (hx : x ∈ (ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q) s).support) :
    x.2.1.length = s.1.length + ctrBlocks ℓ q := by
  rw [runWith_freshStep_ctrQueryProgram counter ℓ b q s hintra, PMF.support_map] at hx
  obtain ⟨⟨iv, us⟩, hp, rfl⟩ := hx
  have hlen : us.length = ctrBlocks ℓ q := length_snd_of_mem_support_uniformDraws hp
  simp only [length_ctrCache, hlen]

private theorem toOuterMeasure_eq_val_of_inj {y : BitString n}
    (f : BitString n → BitString n) (hf : Function.Injective f) :
    (PMF.uniformOfFintype (BitString n)).toOuterMeasure {iv | f iv = y} ≤
      ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  classical
  by_cases hne : ∃ iv₀, f iv₀ = y
  · obtain ⟨iv₀, hiv₀⟩ := hne
    have hset : {iv : BitString n | f iv = y} = {iv₀} := by
      ext iv
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro h
        exact hf (h.trans hiv₀.symm)
      · rintro rfl
        exact hiv₀
    rw [hset, PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]
    simp
  · have hset : {iv : BitString n | f iv = y} = ∅ := by
      ext iv
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hne ⟨iv, h⟩
    rw [hset]
    simp

private theorem toOuterMeasure_exists_ctr_mem_le
    (counter : BitString n → ℕ → BitString n) (ks : List (BitString n)) (k : ℕ)
    (hiv : ∀ i < k, Function.Injective (fun iv => counter iv i)) :
    (PMF.uniformOfFintype (BitString n)).toOuterMeasure
        {iv | ∃ j < k, counter iv j ∈ ks} ≤
      ((k * ks.length : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  classical
  have hsub : {iv : BitString n | ∃ j < k, counter iv j ∈ ks} ⊆
      ⋃ j ∈ Finset.range k, ⋃ y ∈ ks.toFinset, {iv | counter iv j = y} := by
    intro iv ⟨j, hj, hmem⟩
    refine Set.mem_biUnion (Finset.mem_range.2 hj) ?_
    exact Set.mem_biUnion (List.mem_toFinset.2 hmem) rfl
  calc (PMF.uniformOfFintype (BitString n)).toOuterMeasure
          {iv | ∃ j < k, counter iv j ∈ ks}
      ≤ (PMF.uniformOfFintype (BitString n)).toOuterMeasure
          (⋃ j ∈ Finset.range k, ⋃ y ∈ ks.toFinset, {iv | counter iv j = y}) :=
        MeasureTheory.measure_mono hsub
    _ ≤ ∑ j ∈ Finset.range k, (PMF.uniformOfFintype (BitString n)).toOuterMeasure
          (⋃ y ∈ ks.toFinset, {iv | counter iv j = y}) :=
        MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range k, ∑ y ∈ ks.toFinset,
          (PMF.uniformOfFintype (BitString n)).toOuterMeasure {iv | counter iv j = y} :=
        Finset.sum_le_sum fun _ _ => MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range k, ∑ _y ∈ ks.toFinset, ((2 : ℝ≥0∞) ^ n)⁻¹ := by
        refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun y _ => ?_
        exact toOuterMeasure_eq_val_of_inj (fun iv => counter iv j)
          (hiv j (Finset.mem_range.1 hj))
    _ = (k : ℝ≥0∞) * ((ks.toFinset.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (k : ℝ≥0∞) * ((ks.length : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹) := by
        gcongr
        exact_mod_cast List.toFinset_card_le ks
    _ = ((k * ks.length : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
        push_cast
        ring

private theorem toOuterMeasure_bad_freshQuery_le
    (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) (b : Bool) (q : CTRQuery n)
    (s : FlagState n) (hs : ¬s.2 = true)
    (hintra : ∀ iv i j, i < ℓ → j < ℓ → i ≠ j → counter iv i ≠ counter iv j)
    (hiv : ∀ i < ℓ, Function.Injective (fun iv => counter iv i)) :
    (ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q) s).toOuterMeasure
        {x | x.2.2 = true} ≤
      ((ctrBlocks ℓ q * s.1.length : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [runWith_freshStep_ctrQueryProgram counter ℓ b q s hintra, PMF.toOuterMeasure_map_apply]
  have hs' : s.2 = false := by simpa using hs
  have hpre :
      ((fun p : BitString n × List (BitString n) =>
          ((p.1, List.zipWith (· + ·) p.2 (ctrSelect ℓ b q)),
            (ctrCache s.1 counter p.1 0 p.2,
              s.2 || ctrAnyHit s.1 counter p.1 0 (ctrBlocks ℓ q)))) ⁻¹'
        {x | x.2.2 = true}) =
      {p : BitString n × List (BitString n) |
        ctrAnyHit s.1 counter p.1 0 (ctrBlocks ℓ q) = true} := by
    ext p
    simp [hs']
  rw [hpre, PMF.toOuterMeasure_bind_apply]
  calc ∑' iv, (PMF.uniformOfFintype (BitString n)) iv *
        ((uniformBlocks (n := n) (ctrBlocks ℓ q)).map (iv, ·)).toOuterMeasure
          {p | ctrAnyHit s.1 counter p.1 0 (ctrBlocks ℓ q) = true}
      ≤ ∑' iv, (PMF.uniformOfFintype (BitString n)) iv *
          ({iv' | ∃ j < ctrBlocks ℓ q, counter iv' j ∈ s.1.map Prod.fst}.indicator 1 iv) := by
        refine tsum_le_tsum fun iv => mul_le_mul_of_nonneg_left ?_ zero_le
        rw [PMF.toOuterMeasure_map_apply]
        by_cases hhit : ctrAnyHit s.1 counter iv 0 (ctrBlocks ℓ q) = true
        · have hex : iv ∈ {iv' | ∃ j < ctrBlocks ℓ q, counter iv' j ∈ s.1.map Prod.fst} := by
            have := (ctrAnyHit_eq_true_iff s.1 counter iv 0 (ctrBlocks ℓ q)).1 hhit
            simpa using this
          rw [Set.indicator_of_mem hex, Pi.one_apply]
          exact PMF.toOuterMeasure_le_one _ _
        · have hpre2 :
              ((iv, ·) ⁻¹' {p : BitString n × List (BitString n) |
                ctrAnyHit s.1 counter p.1 0 (ctrBlocks ℓ q) = true}) = ∅ := by
            ext us
            simp [hhit]
          rw [hpre2]
          simp
    _ = (PMF.uniformOfFintype (BitString n)).toOuterMeasure
          {iv' | ∃ j < ctrBlocks ℓ q, counter iv' j ∈ s.1.map Prod.fst} := by
        rw [← PMF.toOuterMeasure_eq_tsum_mul_indicator]
    _ ≤ ((ctrBlocks ℓ q * (s.1.map Prod.fst).length : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ :=
        toOuterMeasure_exists_ctr_mem_le counter (s.1.map Prod.fst) (ctrBlocks ℓ q)
          fun i hi => hiv i (lt_of_lt_of_le hi (ctrBlocks_le ℓ q))
    _ = ((ctrBlocks ℓ q * s.1.length : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
        simp

private theorem toOuterMeasure_bad_fresh_le
    (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) (b : Bool)
    {adversary : CTRAdversary n} {K : ℕ} (h : OracleComp.IsCostBounded (ctrCost ℓ) adversary K)
    (hintra : ∀ iv i j, i < ℓ → j < ℓ → i ≠ j → counter iv i ≠ counter iv j)
    (hiv : ∀ i < ℓ, Function.Injective (fun iv => counter iv i)) :
    PMF.toOuterMeasure
        (ProbOracleComp.runWith freshStep (ctrReduction counter ℓ b adversary) ([], false))
        {x | x.2.2 = true} ≤
      ((K * K : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [ctrReduction, ProbOracleComp.runWith_interpret_sumHandler]
  refine (OracleComp.toOuterMeasure_bad_le_two_budgets
    (handler := sumHandler (fun i => StateT.lift (ProbComp.unifOracle i))
      fun q => ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q))
    (bad := fun s : FlagState n => s.2 = true) (ctrCost ℓ) (fun _ => 0)
    (fun s => (s.1.length : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹) (fun _ => 0)
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
          ≤ ((ctrBlocks ℓ q * s.1.length : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ :=
            toOuterMeasure_bad_freshQuery_le counter ℓ b q s hs hintra hiv
        _ = _ := by
            simp only [ctrCost, Sum.elim_inr, Nat.cast_zero, zero_mul, add_zero, Nat.cast_mul,
              mul_assoc]
  · intro q s _ x hx _
    cases q with
    | inl i =>
      rw [snd_eq_of_mem_support_lift hx]
      exact le_add_right (le_add_right le_rfl)
    | inr q =>
      have hlen := length_of_mem_support_freshQuery counter ℓ b q s hintra hx
      simp only [hlen, ctrCost, Sum.elim_inr]
      refine le_of_eq ?_
      push_cast
      ring
  · intro _ _ _ _ _ _
    exact zero_le
  · simp only [List.length_nil, Nat.cast_mul, Nat.cast_zero, zero_mul, zero_add, add_zero,
      mul_zero]
    ring

/-! ### Section 4: Fresh Sampling Gives the Ideal Experiment -/

private theorem eval_ctrIdealOracle (ℓ : ℕ) (q : CTRQuery n) :
    ProbComp.eval (ctrIdealOracle ℓ q) =
      (PMF.uniformOfFintype (BitString n)).bind fun iv =>
        (uniformBlocks (n := n) (ctrBlocks ℓ q)).map (iv, ·) := by
  simp only [ctrIdealOracle, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
    uniformBlocks_eq, Function.comp_def, ← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind]

private theorem map_unit_runWith_freshStep_ctrQueryProgram
    (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) (b : Bool) (q : CTRQuery n)
    (s : FlagState n)
    (hintra : ∀ iv i j, i < ℓ → j < ℓ → i ≠ j → counter iv i ≠ counter iv j) :
    (ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q) s).map (fun x => (x.1, ())) =
      (ProbComp.eval (ctrIdealOracle ℓ q)).map (·, ()) := by
  have hpad := map_iv_uniformBlocks_zipWith (ctrSelect ℓ b q)
  rw [length_ctrSelect] at hpad
  rw [runWith_freshStep_ctrQueryProgram counter ℓ b q s hintra, eval_ctrIdealOracle]
  conv_rhs => rw [← hpad]
  exact (PMF.map_comp _ _ _).trans (Eq.symm (PMF.map_comp _ _ _))

private theorem freshGame_eq_ctrIdealGame
    (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) (b : Bool) (adversary : CTRAdversary n)
    (hintra : ∀ iv i j, i < ℓ → j < ℓ → i ≠ j → counter iv i ≠ counter iv j) :
    (ProbOracleComp.runWith freshStep (ctrReduction counter ℓ b adversary) ([], false)).map
        Prod.fst =
      ctrIdealGame ℓ adversary := by
  have hstate :
      (ProbOracleComp.runWith
          (fun q => ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q))
          adversary ([], false)).map (fun x => (x.1, ())) =
        ProbOracleComp.runWith
          (fun q (u : Unit) => (ProbComp.eval (ctrIdealOracle ℓ q)).map (·, u)) adversary () :=
    ProbOracleComp.runWith_map_state
      (fun q => ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q))
      (fun q (u : Unit) => (ProbComp.eval (ctrIdealOracle ℓ q)).map (·, u)) (fun _ => ())
      (fun q s => map_unit_runWith_freshStep_ctrQueryProgram counter ℓ b q s hintra)
      adversary ([], false)
  have hro :
      ProbOracleComp.runWith
          (fun q (u : Unit) => (ProbComp.eval (ctrIdealOracle ℓ q)).map (·, u)) adversary () =
        (OracleComp.interpret
          (sumHandler ProbComp.unifOracle fun q => ProbComp.eval (ctrIdealOracle ℓ q))
          adversary).map (·, ()) :=
    ProbOracleComp.runWith_readOnly (fun q _ => ProbComp.eval (ctrIdealOracle ℓ q)) adversary ()
  rw [ctrReduction, ProbOracleComp.runWith_interpret_sumHandler]
  calc
    (ProbOracleComp.runWith
          (fun q => ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q))
          adversary ([], false)).map Prod.fst
        = ((ProbOracleComp.runWith
              (fun q => ProbOracleComp.runWith freshStep (ctrQueryProgram counter ℓ b q))
              adversary ([], false)).map fun x => (x.1, ())).map Prod.fst :=
          (PMF.map_comp (fun x : Bool × FlagState n => (x.1, ())) _ Prod.fst).symm
    _ = ((OracleComp.interpret
            (sumHandler ProbComp.unifOracle fun q => ProbComp.eval (ctrIdealOracle ℓ q))
            adversary).map (·, ())).map Prod.fst := by rw [hstate, hro]
    _ = ctrIdealGame ℓ adversary := by
          rw [(PMF.map_comp (·, ()) _ Prod.fst).trans (PMF.map_id _),
            ctrIdealGame, ProbOracleComp.eval_interpret]

/-! ### Section 5: Security of CTR Mode and Modular Counter Instantiation -/

/-- **The CTR reduction against a uniform random function.** If the queries of `adversary` ask at
most `K` blocks in total, and `counter` has no intra-query collisions below `ℓ` and is injective in
`iv` at every offset below `ℓ`, then the reduction's output is within `K ^ 2 / 2 ^ n` of the ideal
experiment for each challenge bit `b`. -/
theorem advantage_idealGame_ctrReduction_le
    (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) (b : Bool)
    {adversary : CTRAdversary n} {K : ℕ} (h : OracleComp.IsCostBounded (ctrCost ℓ) adversary K)
    (hintra : ∀ iv i j, i < ℓ → j < ℓ → i ≠ j → counter iv i ≠ counter iv j)
    (hiv : ∀ i < ℓ, Function.Injective (fun iv => counter iv i)) :
    (Game.advantage (PRF.idealGame (ctrReduction counter ℓ b adversary))
        (ctrIdealGame ℓ adversary) : ℝ) ≤
      (K : ℝ) ^ 2 / 2 ^ n := by
  rw [← freshGame_eq_ctrIdealGame counter ℓ b adversary hintra]
  refine (advantage_idealGame_freshStep_le _).trans ?_
  have hne : ((K * K : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.inv_ne_top.2 (pow_ne_zero _ two_ne_zero))
  refine (ENNReal.toReal_mono hne (toOuterMeasure_bad_fresh_le counter ℓ b h hintra hiv)).trans
    (le_of_eq ?_)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat, Nat.cast_mul]
  ring

/-- **CTR mode with a uniform random function** ([KatzLindell2020], Section 3.6.3): when
`adversary` asks at most `K` blocks in total and at most `ℓ` blocks per query, its left-or-right
advantage is at most `2 * K ^ 2 / 2 ^ n`. -/
theorem advantage_ctrCpaGame_randomFunction_le
    (counter : BitString n → ℕ → BitString n) (ℓ : ℕ) {adversary : CTRAdversary n} {K : ℕ}
    (h : OracleComp.IsCostBounded (ctrCost ℓ) adversary K)
    (hintra : ∀ iv i j, i < ℓ → j < ℓ → i ≠ j → counter iv i ≠ counter iv j)
    (hiv : ∀ i < ℓ, Function.Injective (fun iv => counter iv i)) :
    (Game.advantage
        (ctrCpaGame counter (fun f : BitString n → BitString n => f) ℓ false adversary)
        (ctrCpaGame counter (fun f : BitString n → BitString n => f) ℓ true adversary) : ℝ) ≤
      2 * ((K : ℝ) ^ 2 / 2 ^ n) := by
  have e : ∀ b,
      ctrCpaGame counter (fun f : BitString n → BitString n => f) ℓ b adversary =
        PRF.idealGame (ctrReduction counter ℓ b adversary) := fun b => by
    rw [ctrCpaGame_eq_realGame]
    rfl
  rw [e, e]
  have h₀ := advantage_idealGame_ctrReduction_le counter ℓ false h hintra hiv
  have h₁ := advantage_idealGame_ctrReduction_le counter ℓ true h hintra hiv
  have h₂ := advantage_le_two (PRF.idealGame (ctrReduction counter ℓ false adversary))
    (ctrIdealGame ℓ adversary) (PRF.idealGame (ctrReduction counter ℓ true adversary))
  linarith

/-- **CTR mode is CPA-secure for a pseudorandom function** ([KatzLindell2020], Section 3.6.3,
Theorem 3.33, p. 93): if `adversary` asks at most `K` blocks in total and at most `ℓ` blocks per
query, its left-or-right advantage against CTR mode with keyed function `F` is at most the PRF
advantages of the two reductions `ctrReduction counter ℓ false adversary` and
`ctrReduction counter ℓ true adversary` (each making at most `K` queries by
`isQueryBounded_ctrReduction`) plus `2 * K ^ 2 / 2 ^ n`. -/
theorem advantage_ctrCpaGame_le {Key : Type} (counter : BitString n → ℕ → BitString n)
    [Fintype Key] [Nonempty Key] (F : Key → BitString n → BitString n) (ℓ : ℕ)
    {adversary : CTRAdversary n} {K : ℕ} (h : OracleComp.IsCostBounded (ctrCost ℓ) adversary K)
    (hintra : ∀ iv i j, i < ℓ → j < ℓ → i ≠ j → counter iv i ≠ counter iv j)
    (hiv : ∀ i < ℓ, Function.Injective (fun iv => counter iv i)) :
    (Game.advantage (ctrCpaGame counter F ℓ false adversary)
        (ctrCpaGame counter F ℓ true adversary) : ℝ) ≤
      PRF.advantage F (ctrReduction counter ℓ false adversary) +
        PRF.advantage F (ctrReduction counter ℓ true adversary) + 2 * ((K : ℝ) ^ 2 / 2 ^ n) := by
  rw [ctrCpaGame_eq_realGame, ctrCpaGame_eq_realGame]
  have h₀ := advantage_idealGame_ctrReduction_le counter ℓ false h hintra hiv
  have h₁ := advantage_idealGame_ctrReduction_le counter ℓ true h hintra hiv
  have h₄ := advantage_le_four (PRF.realGame F (ctrReduction counter ℓ false adversary))
    (PRF.idealGame (ctrReduction counter ℓ false adversary)) (ctrIdealGame ℓ adversary)
    (PRF.idealGame (ctrReduction counter ℓ true adversary))
    (PRF.realGame F (ctrReduction counter ℓ true adversary))
  have e₀ : (PRF.advantage F (ctrReduction counter ℓ false adversary) : ℝ) =
      Game.advantage (PRF.realGame F (ctrReduction counter ℓ false adversary))
        (PRF.idealGame (ctrReduction counter ℓ false adversary)) := rfl
  have e₁ : (PRF.advantage F (ctrReduction counter ℓ true adversary) : ℝ) =
      Game.advantage (PRF.realGame F (ctrReduction counter ℓ true adversary))
        (PRF.idealGame (ctrReduction counter ℓ true adversary)) := rfl
  linarith

/-- Canonical modular-addition counter schedule `iv + i mod 2 ^ n` ([KatzLindell2020], Figure 3.9),
via `BitString.equivFin`. -/
@[expose]
def ctrModCounter (iv : BitString n) (i : ℕ) : BitString n :=
  (BitString.equivFin n).symm ⟨((BitString.equivFin n iv).val + i) % 2 ^ n,
    Nat.mod_lt _ (pow_pos (by decide) n)⟩

/-- For every offset `i`, `ctrModCounter · i` is injective on the initialization vector `iv`. -/
theorem ctrModCounter_injective_left (i : ℕ) :
    Function.Injective (fun iv : BitString n => ctrModCounter iv i) := by
  intro iv₁ iv₂ h
  have hv := congrArg (fun x => (BitString.equivFin n x).val) h
  simp only [ctrModCounter, Equiv.apply_symm_apply] at hv
  have hmod : (BitString.equivFin n iv₁).val ≡ (BitString.equivFin n iv₂).val [MOD 2 ^ n] :=
    Nat.ModEq.add_right_cancel' i hv
  have heq : (BitString.equivFin n iv₁).val = (BitString.equivFin n iv₂).val := by
    rw [← Nat.mod_eq_of_lt (BitString.equivFin n iv₁).isLt,
      ← Nat.mod_eq_of_lt (BitString.equivFin n iv₂).isLt]
    exact hmod
  exact (BitString.equivFin n).injective (Fin.ext heq)

/-- Whenever `ℓ ≤ 2 ^ n`, distinct offsets below `ℓ` yield distinct `ctrModCounter iv i` blocks. -/
theorem ctrModCounter_injOn {ℓ : ℕ} (hℓ : ℓ ≤ 2 ^ n) (iv : BitString n)
    {i j : ℕ} (hi : i < ℓ) (hj : j < ℓ) (hij : i ≠ j) :
    ctrModCounter iv i ≠ ctrModCounter iv j := by
  intro h
  apply hij
  have hv := congrArg (fun x => (BitString.equivFin n x).val) h
  simp only [ctrModCounter, Equiv.apply_symm_apply] at hv
  have hmod : i ≡ j [MOD 2 ^ n] := Nat.ModEq.add_left_cancel' (BitString.equivFin n iv).val hv
  rw [← Nat.mod_eq_of_lt (lt_of_lt_of_le hi hℓ), ← Nat.mod_eq_of_lt (lt_of_lt_of_le hj hℓ)]
  exact hmod

/-- Modular CTR mode with a uniform random function when `ℓ ≤ 2 ^ n`. -/
theorem advantage_ctrCpaGame_ctrModCounter_randomFunction_le {ℓ : ℕ} (hℓ : ℓ ≤ 2 ^ n)
    {adversary : CTRAdversary n} {K : ℕ} (h : OracleComp.IsCostBounded (ctrCost ℓ) adversary K) :
    (Game.advantage
        (ctrCpaGame ctrModCounter (fun f : BitString n → BitString n => f) ℓ false adversary)
        (ctrCpaGame ctrModCounter (fun f : BitString n → BitString n => f) ℓ true adversary) :
        ℝ) ≤
      2 * ((K : ℝ) ^ 2 / 2 ^ n) :=
  advantage_ctrCpaGame_randomFunction_le ctrModCounter ℓ h
    (fun iv _ _ hi hj hij => ctrModCounter_injOn hℓ iv hi hj hij)
    (fun i _ => ctrModCounter_injective_left i)

/-- Modular CTR mode is CPA-secure for any pseudorandom function `F` whenever `ℓ ≤ 2 ^ n`
([KatzLindell2020], Section 3.6.3, Theorem 3.33). -/
theorem advantage_ctrCpaGame_ctrModCounter_le {Key : Type} [Fintype Key] [Nonempty Key]
    (F : Key → BitString n → BitString n) {ℓ : ℕ} (hℓ : ℓ ≤ 2 ^ n)
    {adversary : CTRAdversary n} {K : ℕ} (h : OracleComp.IsCostBounded (ctrCost ℓ) adversary K) :
    (Game.advantage (ctrCpaGame ctrModCounter F ℓ false adversary)
        (ctrCpaGame ctrModCounter F ℓ true adversary) : ℝ) ≤
      PRF.advantage F (ctrReduction ctrModCounter ℓ false adversary) +
        PRF.advantage F (ctrReduction ctrModCounter ℓ true adversary) + 2 * ((K : ℝ) ^ 2 / 2 ^ n) :=
  advantage_ctrCpaGame_le ctrModCounter F ℓ h
    (fun iv _ _ hi hj hij => ctrModCounter_injOn hℓ iv hi hj hij)
    (fun i _ => ctrModCounter_injective_left i)

end Cslib.Crypto
