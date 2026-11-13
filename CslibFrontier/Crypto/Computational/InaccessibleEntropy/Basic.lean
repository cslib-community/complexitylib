/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Crypto.Negligible
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Languages.Probabilistic.BitString
public import CslibFrontier.Probability.Entropy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.Uniform

/-!
# Real sample entropy and accessible average max-entropy

For a deterministic function $F : \alpha \to \beta$ on a finite uniform domain
$X \leftarrow \alpha$, the **real sample entropy** of $x \in \alpha$ (`realSampleEntropy F x`) is
$\log_2 |F^{-1}(F(x))|$ (`[HHRVW2020]`, Definition 3.1, p. 11); its expectation over uniform
$X \leftarrow \alpha$ equals the conditional Shannon entropy $H(X \mid F(X))$
(`expected_realSampleEntropy_eq_conditionalEntropy`).

An **$F$-collision-finder** (`IsCollisionFinder F A`) is a randomized mapping supported on the
preimage fiber $F^{-1}(F(x))$ (`[HHRVW2020]`, Definition 3.3, p. 12); any randomized mapping is
canonically sanitized to an $F$-collision-finder by falling back to $x$ on non-colliding outputs
(`sanitizeCollisionFinder`, `[HHRVW2020]`, Definition 3.3 and fallback discussion, p. 12).

A family of subsets $L(x) \subseteq F^{-1}(F(x))$ with $x \in L(x)$ witnesses **accessible average
max-entropy** at most $\mathbb{E}_{X}[\log_2 |L(X)|]$ (`accessibleSetExpectation L`).
`AdversaryInaccessibleEntropyFamily` formalizes `[HHRVW2020]`, Definition 3.9 (p. 15) directly,
quantifying an adversary-dependent family $L_A$ after each uniform strict-PPT collision-finder $A$
(`IsWordCollisionFinder`, `IsAccessibleEntropyWitness`); word-level fallback sanitization
(`sanitizeWordCollisionFinder`) lifts this guarantee to arbitrary uniform strict-PPT adversaries
(`AdversaryInaccessibleEntropyFamily.exists_accessibleSet`). `InaccessibleEntropyFamily` packages
the stronger adversary-independent witness produced by Theorem 4.5 (one `accSet` against all
adversaries) and coerces to `AdversaryInaccessibleEntropyFamily`
(`InaccessibleEntropyFamily.toAdversaryInaccessibleEntropyFamily`). The elementary inequality
$-\log_2(1 - \alpha) \ge \alpha$ for $\alpha \in [0, 1)$ lower-bounds the entropy gap
$H(X \mid F(X)) - \mathbb{E}[\log_2 |L(X)|]$ by the expected fraction of fiber elements outside
$L(X)$ (`conditionalEntropy_sub_accessibleSetExpectation_ge`, `[HHRVW2020]`, Section 4.2, p. 24).

## Main definitions

* `Cslib.Crypto.fiberSet`: preimage fiber $F^{-1}(y)$ as a `Finset`.
* `Cslib.Crypto.realSampleEntropy`: $\log_2 |F^{-1}(F(x))|$.
* `Cslib.Crypto.IsCollisionFinder`, `Cslib.Crypto.sanitizeCollisionFinder`,
  `Cslib.Crypto.IsWordCollisionFinder`, `Cslib.Crypto.sanitizeWordCollisionFinder`: finite and
  word-level collision-finding adversaries and canonical fallback sanitization.
* `Cslib.Crypto.accessibleSetExpectation`: $\mathbb{E}_{X \leftarrow \alpha}[\log_2 |L(X)|]$.
* `Cslib.Crypto.accessibleEscapeGame`, `Cslib.Crypto.IsAccessibleEntropyWitness`: security
  experiment and witness predicate for escaping `accSet`.
* `Cslib.Crypto.AdversaryInaccessibleEntropyFamily`,
  `Cslib.Crypto.InaccessibleEntropyFamily`: uniform polynomial-time function families with a
  $1 / \mathrm{denom}(n)$ inaccessible-entropy gap against adversary-dependent (Definition 3.9) and
  adversary-independent accessible sets.

## Main results

* `Cslib.Crypto.expected_realSampleEntropy_eq_conditionalEntropy`: expected real sample entropy over
  a uniform input equals `PMF.conditionalEntropy`.
* `Cslib.Crypto.isCollisionFinder_sanitizeCollisionFinder`,
  `Cslib.Crypto.isWordCollisionFinder_sanitizeWordCollisionFinder`,
  `Cslib.Crypto.isPPT_sanitizeWordCollisionFinder`,
  `Cslib.Crypto.accessibleEscapeGame_sanitizeWordCollisionFinder`: finite and word-level fallback
  sanitization preserves strict PPT and leaves `accessibleEscapeGame` unchanged.
* `Cslib.Crypto.conditionalEntropy_sub_accessibleSetExpectation_ge`: lower bound on
  $H(X \mid F(X)) - \mathbb{E}[\log_2 |L(X)|]$ from the average fiber-escape density.
* `Cslib.Crypto.AdversaryInaccessibleEntropyFamily.exists_accessibleSet`,
  `Cslib.Crypto.InaccessibleEntropyFamily.toAdversaryInaccessibleEntropyFamily`: lifting Definition
  3.9 from collision finders to arbitrary strict-PPT adversaries, and embedding fixed accessible
  families into Definition 3.9.

## References

* [I. Haitner, T. Holenstein, O. Reingold, S. Vadhan, H. Wee, *Inaccessible Entropy II: IE
  Functions and Universal One-Way Hashing*, Section 3 (Definitions 3.1, 3.3, 3.9, pp. 11–15)
  and Section 4.2 (Theorem 4.5, p. 21)][HHRVW2020]
-/

public section

namespace Cslib.Crypto

open Cslib.Probability Finset
open scoped ENNReal

/-! ### Preimage fibers and real sample entropy -/

/-- Preimage fiber $F^{-1}(y) = \{x \in \alpha \mid F(x) = y\}$ of a finite-domain map. -/
@[expose] def fiberSet {α β : Type*} [Fintype α] [DecidableEq β] (F : α → β) (y : β) :
    Finset α :=
  univ.filter fun x => F x = y

@[simp] theorem mem_fiberSet {α β : Type*} [Fintype α] [DecidableEq β] (F : α → β) (y : β)
    (x : α) : x ∈ fiberSet F y ↔ F x = y := by
  simp [fiberSet]

theorem self_mem_fiberSet {α β : Type*} [Fintype α] [DecidableEq β] (F : α → β) (x : α) :
    x ∈ fiberSet F (F x) := by
  simp [fiberSet]

theorem card_fiberSet_pos {α β : Type*} [Fintype α] [DecidableEq β] (F : α → β) (x : α) :
    0 < #(fiberSet F (F x)) :=
  card_pos.mpr ⟨x, self_mem_fiberSet F x⟩

theorem card_fiberSet_eq_fintypeCard {α β : Type*} [Fintype α] [DecidableEq β] (F : α → β)
    (y : β) : #(fiberSet F y) = Fintype.card {x : α // F x = y} :=
  (Fintype.card_of_subtype (fiberSet F y) fun _ => mem_fiberSet F y _).symm

/-- **Real sample entropy** $\log_2 |F^{-1}(F(x))|$ of an input $x$ under uniform sampling on
$\alpha$ (`[HHRVW2020]`, Section 3.1, Definition 3.1, p. 11). -/
@[expose] noncomputable def realSampleEntropy {α β : Type*} [Fintype α] [DecidableEq β]
    (F : α → β) (x : α) : ℝ :=
  Real.logb 2 #(fiberSet F (F x))

theorem realSampleEntropy_nonneg {α β : Type*} [Fintype α] [DecidableEq β]
    (F : α → β) (x : α) : 0 ≤ realSampleEntropy F x :=
  Real.logb_nonneg (by norm_num) (by exact_mod_cast card_fiberSet_pos F x)

theorem realSampleEntropy_le_log_card {α β : Type*} [Fintype α] [DecidableEq β]
    (F : α → β) (x : α) : realSampleEntropy F x ≤ Real.logb 2 (Fintype.card α) := by
  apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast card_fiberSet_pos F x)
  exact_mod_cast card_le_univ (fiberSet F (F x))

/-- Averaging `realSampleEntropy F` over a uniform input recovers the Shannon conditional entropy
$H(X \mid F(X))$ (`[HHRVW2020]`, Section 3.1, p. 11). -/
theorem expected_realSampleEntropy_eq_conditionalEntropy {α β : Type*}
    [Fintype α] [Nonempty α] [Finite β] [DecidableEq β] (F : α → β) :
    (∑ x : α, ((PMF.uniformOfFintype α) x).toReal * realSampleEntropy F x) =
      PMF.conditionalEntropy ((PMF.uniformOfFintype α).map fun x => (F x, x)) := by
  classical
  let := Fintype.ofFinite β
  rw [PMF.conditionalEntropy_eq_sum_surprisal,
    PMF.sum_map_mul (PMF.uniformOfFintype α) (fun x => (F x, x))
      (fun pair => PMF.surprisal
        (PMF.conditionalSnd ((PMF.uniformOfFintype α).map fun a => (F a, a)) pair.1) pair.2)]
  refine sum_congr rfl fun x _ => congrArg (((PMF.uniformOfFintype α) x).toReal * ·) ?_
  dsimp only
  have : Nonempty {a : α // F a = F x} := ⟨⟨x, rfl⟩⟩
  have hcond := congrArg (fun p : PMF α => PMF.surprisal p x)
    (PMF.conditionalSnd_uniform_map F (F x))
  rw [hcond]
  let clsFin : Fintype {a : α // F a = F x} :=
    @Subtype.fintype α (fun a => F a = F x) (Classical.decPred _) ‹_›
  have hmap : ((@PMF.uniformOfFintype {a : α // F a = F x} clsFin _).map Subtype.val) x =
      (@PMF.uniformOfFintype {a : α // F a = F x} clsFin _) ⟨x, rfl⟩ := by
    rw [PMF.map_apply, tsum_eq_single ⟨x, rfl⟩]
    · simp
    · intro b hb
      have hval : x ≠ b.1 := fun h => hb (Subtype.ext h.symm)
      simp [hval]
  rw [realSampleEntropy, PMF.surprisal]
  change Real.logb 2 #(fiberSet F (F x)) =
    -Real.logb 2 (((@PMF.uniformOfFintype {a : α // F a = F x} clsFin _).map Subtype.val) x).toReal
  rw [hmap, PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Real.logb_inv, neg_neg]
  congr 2
  rw [card_fiberSet_eq_fintypeCard, Subsingleton.elim (Subtype.fintype fun a => F a = F x) clsFin]

/-! ### Collision-finding adversaries and canonical sanitization -/

/-- An **$F$-collision-finder** is a randomized mapping that always outputs a preimage in the fiber
$F^{-1}(F(x))$ (`[HHRVW2020]`, Section 3.2, Definition 3.3, p. 12). -/
@[expose] def IsCollisionFinder {α β : Type*} (F : α → β) (A : α → PMF α) : Prop :=
  ∀ x x', x' ∈ (A x).support → F x' = F x

/-- Canonical fallback sanitization replacing any non-colliding output of `A x` by `x` itself
(`[HHRVW2020]`, Section 3.2, Definition 3.3 and fallback discussion, p. 12). -/
@[expose] noncomputable def sanitizeCollisionFinder {α β : Type*} [DecidableEq β]
    (F : α → β) (A : α → PMF α) (x : α) : PMF α :=
  (A x).map fun x' => if F x' = F x then x' else x

theorem isCollisionFinder_sanitizeCollisionFinder {α β : Type*} [DecidableEq β]
    (F : α → β) (A : α → PMF α) : IsCollisionFinder F (sanitizeCollisionFinder F A) := by
  intro x y hy
  obtain ⟨x', _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
  split_ifs with h
  · exact h
  · rfl

/-! ### Accessible set expectation and the fiber-escape entropy gap -/

/-- Expected base-$2$ log-cardinality $\mathbb{E}_{X \leftarrow \alpha}[\log_2 |L(X)|]$ of a family
of accessible preimage sets (`[HHRVW2020]`, Section 3.2, Definition 3.9, p. 15). -/
@[expose] noncomputable def accessibleSetExpectation {α : Type*} [Fintype α] [Nonempty α]
    (L : α → Finset α) : ℝ :=
  ∑ x : α, ((PMF.uniformOfFintype α) x).toReal * Real.logb 2 #(L x)

theorem accessibleSetExpectation_nonneg {α : Type*} [Fintype α] [Nonempty α]
    (L : α → Finset α) : 0 ≤ accessibleSetExpectation L :=
  sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg
    (div_nonneg (Real.log_natCast_nonneg _) (Real.log_nonneg one_le_two))

/-- Pointwise bound behind `[HHRVW2020]`, Claim 4.7 (p. 24): when
$x \in L(x) \subseteq F^{-1}(F(x))$, the gap $\log_2 |F^{-1}(F(x))| - \log_2 |L(x)|$ is at least
$|F^{-1}(F(x)) \setminus L(x)| / |F^{-1}(F(x))|$. -/
theorem expected_realSampleEntropy_sub_accessibleSetExpectation_ge {α β : Type*}
    [Fintype α] [Nonempty α] [DecidableEq α] [DecidableEq β]
    (F : α → β) (L : α → Finset α)
    (hself : ∀ x, x ∈ L x) (hsub : ∀ x, L x ⊆ fiberSet F (F x)) :
    (∑ x : α, ((PMF.uniformOfFintype α) x).toReal *
        ((#(fiberSet F (F x) \ L x) : ℝ) / #(fiberSet F (F x)))) ≤
      (∑ x : α, ((PMF.uniformOfFintype α) x).toReal * realSampleEntropy F x) -
        accessibleSetExpectation L := by
  rw [accessibleSetExpectation, ← sum_sub_distrib]
  refine sum_le_sum fun x _ => ?_
  rw [← mul_sub]
  refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  have ha : (0 : ℝ) < #(L x) := by exact_mod_cast card_pos.mpr ⟨x, hself x⟩
  have hab : (#(L x) : ℝ) ≤ #(fiberSet F (F x)) := by
    exact_mod_cast card_le_card (hsub x)
  have hsdiff : (#(fiberSet F (F x) \ L x) : ℝ) = #(fiberSet F (F x)) - #(L x) := by
    rw [card_sdiff_of_subset (hsub x), Nat.cast_sub (card_le_card (hsub x))]
  rw [hsdiff, realSampleEntropy]
  exact Real.sub_div_le_logb_sub ha hab

/-- Conditional-entropy form of `expected_realSampleEntropy_sub_accessibleSetExpectation_ge`
(`[HHRVW2020]`, Section 4.2, p. 24). -/
theorem conditionalEntropy_sub_accessibleSetExpectation_ge {α β : Type*}
    [Fintype α] [Nonempty α] [DecidableEq α] [Finite β] [DecidableEq β]
    (F : α → β) (L : α → Finset α)
    (hself : ∀ x, x ∈ L x) (hsub : ∀ x, L x ⊆ fiberSet F (F x)) :
    (∑ x : α, ((PMF.uniformOfFintype α) x).toReal *
        ((#(fiberSet F (F x) \ L x) : ℝ) / #(fiberSet F (F x)))) ≤
      PMF.conditionalEntropy ((PMF.uniformOfFintype α).map fun x => (F x, x)) -
        accessibleSetExpectation L := by
  rw [← expected_realSampleEntropy_eq_conditionalEntropy F]
  exact expected_realSampleEntropy_sub_accessibleSetExpectation_ge F L hself hsub

/-! ### Computational accessible-escape game and family interface -/

/-- Fixed-width `BitString` view of a word function on `inLen`-bit inputs, truncated or zero-padded
to `outLen` output bits. -/
@[expose] def wordToFinMap (inLen outLen : ℕ) (f : List Bool → List Bool)
    (z : BitString inLen) : BitString outLen :=
  BitString.ofList outLen (f (List.ofFn z))

/-- Security experiment testing whether an adversary `A` outputs an `(inLen n)`-bit colliding
preimage of `evalWord n` outside the accessible set `accSet n`. -/
@[expose] noncomputable def accessibleEscapeGame (evalWord : ℕ → List Bool → List Bool)
    (inLen : ℕ → ℕ)
    (accSet : (n : ℕ) → BitString (inLen n) → Finset (BitString (inLen n)))
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) : ProbComp Bool := do
  let zWord ← BitString.sampleList (inLen n)
  let raw ← A n zWord
  let z := BitString.ofList (inLen n) zWord
  let z' := BitString.ofList (inLen n) raw
  return decide (raw.length = inLen n ∧ evalWord n raw = evalWord n zWord ∧ z' ∉ accSet n z)

/-- Word-level parameterized **$F$-collision-finder** (`[HHRVW2020]`, Section 3.2, Definition 3.3,
p. 12): on every security parameter `n` and `(inLen n)`-bit input `zWord`, `A n zWord` is supported
on `(inLen n)`-bit preimages in the fiber of `evalWord n zWord`. -/
@[expose] def IsWordCollisionFinder (inLen : ℕ → ℕ) (evalWord : ℕ → List Bool → List Bool)
    (A : ℕ → List Bool → ProbComp (List Bool)) : Prop :=
  ∀ n zWord, zWord.length = inLen n →
    ∀ raw ∈ (ProbComp.eval (A n zWord)).support,
      raw.length = inLen n ∧ evalWord n raw = evalWord n zWord

/-- Every `IsWordCollisionFinder` induces a finite-domain `IsCollisionFinder` on
`BitString (inLen n)`. -/
theorem IsWordCollisionFinder.isCollisionFinder {inLen outLen : ℕ → ℕ}
    {evalWord : ℕ → List Bool → List Bool} {A : ℕ → List Bool → ProbComp (List Bool)}
    (hA : IsWordCollisionFinder inLen evalWord A) (n : ℕ) :
    IsCollisionFinder (wordToFinMap (inLen n) (outLen n) (evalWord n))
      (fun z => (ProbComp.eval (A n (List.ofFn z))).map (BitString.ofList (inLen n))) := by
  intro z z' hz'
  obtain ⟨raw, hraw, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz'
  obtain ⟨hlen, heval⟩ := hA n (List.ofFn z) List.length_ofFn raw hraw
  simp only [wordToFinMap, BitString.ofFn_ofList hlen, heval]

/-- Canonical word-level fallback sanitization (`[HHRVW2020]`, Section 3.2, Definition 3.3 and
fallback discussion, p. 12): runs `A n zWord` and falls back to `zWord` whenever the output does not
have length `inLen n` or fails to collide under `evalWord n`. -/
@[expose] def sanitizeWordCollisionFinder (inLen : ℕ → ℕ) (evalWord : ℕ → List Bool → List Bool)
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) (zWord : List Bool) :
    ProbComp (List Bool) := do
  let raw ← A n zWord
  return if raw.length == inLen n && evalWord n raw == evalWord n zWord then raw else zWord

theorem isWordCollisionFinder_sanitizeWordCollisionFinder (inLen : ℕ → ℕ)
    (evalWord : ℕ → List Bool → List Bool) (A : ℕ → List Bool → ProbComp (List Bool)) :
    IsWordCollisionFinder inLen evalWord (sanitizeWordCollisionFinder inLen evalWord A) := by
  intro n zWord hz raw hraw
  simp only [sanitizeWordCollisionFinder, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hraw
  obtain ⟨u, _, rfl⟩ := hraw
  split_ifs with h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h
  · exact ⟨hz, rfl⟩

theorem isPPT_sanitizeWordCollisionFinder {inLen : ℕ → ℕ}
    {evalWord : ℕ → List Bool → List Bool} {A : ℕ → List Bool → ProbComp (List Bool)}
    (hinLen : Turing.MultiTapeTM.ComputableInPolyTime inLen
      Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encUnary)
    (heval : Turing.MultiTapeTM.ComputableInPolyTime
      (fun p : ℕ × List Bool => evalWord p.1 p.2)
      (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encBits)
      Turing.MultiTapeTM.encBits)
    (hA : Probability.IsPPT Turing.MultiTapeTM.encBits A) :
    Probability.IsPPT Turing.MultiTapeTM.encBits
      (sanitizeWordCollisionFinder inLen evalWord A) := by
  let Q := (ℕ × List Bool) × List Bool
  let encL := Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encBits
  let encQ : Q ↪ List Bool := Turing.MultiTapeTM.encPair encL Turing.MultiTapeTM.encBits
  have hfst : Turing.MultiTapeTM.ComputableInPolyTime (fun q : Q => q.1) encQ encL :=
    Turing.MultiTapeTM.ComputableInPolyTime.fst _ _
  have hn : Turing.MultiTapeTM.ComputableInPolyTime (fun q : Q => q.1.1) encQ
      Turing.MultiTapeTM.encUnary := hfst.fst'
  have hz : Turing.MultiTapeTM.ComputableInPolyTime (fun q : Q => q.1.2) encQ
      Turing.MultiTapeTM.encBits := hfst.snd'
  have hraw : Turing.MultiTapeTM.ComputableInPolyTime (fun q : Q => q.2) encQ
      Turing.MultiTapeTM.encBits := Turing.MultiTapeTM.ComputableInPolyTime.snd _ _
  have hlenCond := (hraw.trans Turing.MultiTapeTM.ComputableInPolyTime.length_bits).beq
    (hinLen.comp hn)
  have hevCond := (heval.comp (hn.prod hraw)).beq (heval.comp hfst)
  have hpost := (hlenCond.bool_and' hevCond).ite hraw hz
  exact IsPPTOn.isPPT (hA.on.bind_with (hpost.of_enc_eq fun _ => rfl).isPPTOn)

/-- Because `z ∈ accSet n z`, falling back to `zWord` on non-colliding outputs leaves
`accessibleEscapeGame` identical as a `ProbComp Bool` program. -/
theorem accessibleEscapeGame_sanitizeWordCollisionFinder
    (evalWord : ℕ → List Bool → List Bool) (inLen : ℕ → ℕ)
    (accSet : (n : ℕ) → BitString (inLen n) → Finset (BitString (inLen n)))
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ)
    (hself : ∀ z, z ∈ accSet n z) :
    accessibleEscapeGame evalWord inLen accSet
      (sanitizeWordCollisionFinder inLen evalWord A) n =
      accessibleEscapeGame evalWord inLen accSet A n := by
  simp only [accessibleEscapeGame, sanitizeWordCollisionFinder, bind_assoc, pure_bind]
  congr 1 with zWord
  congr 1 with raw
  split_ifs with h
  · rfl
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    simp [hself]
    tauto

/-- `accSet` witnesses an eventual `1 / denom n` gap between real Shannon conditional entropy and
accessible average max-entropy against adversary `A` (`[HHRVW2020]`, Section 3.2, Definition 3.9,
p. 15). -/
@[expose] def IsAccessibleEntropyWitness (inLen outLen denom : ℕ → ℕ)
    (evalWord : ℕ → List Bool → List Bool)
    (A : ℕ → List Bool → ProbComp (List Bool))
    (accSet : (n : ℕ) → BitString (inLen n) → Finset (BitString (inLen n))) : Prop :=
  (∀ n z, z ∈ accSet n z) ∧
  (∀ n z, accSet n z ⊆ fiberSet (wordToFinMap (inLen n) (outLen n) (evalWord n))
    (wordToFinMap (inLen n) (outLen n) (evalWord n) z)) ∧
  (∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
    accessibleSetExpectation (accSet n) ≤
      PMF.conditionalEntropy
        ((PMF.uniformOfFintype (BitString (inLen n))).map fun z =>
          (wordToFinMap (inLen n) (outLen n) (evalWord n) z, z)) -
        1 / (denom n : ℝ)) ∧
  Negligible (fun n =>
    Game.succProbability (ProbComp.eval
      (accessibleEscapeGame evalWord inLen accSet A n)))

/-- **`[HHRVW2020]`, Section 3.2, Definition 3.9 (p. 15)**: a uniform polynomial-time fixed-width
function family whose accessible average max-entropy is eventually at most
$H(Z \mid F_0(Z)) - 1 / \mathrm{denom}(n)$ against **adversary-dependent** accessible preimage sets
($\forall$ uniform strict-PPT collision-finder $A$, $\exists L_A$). -/
structure AdversaryInaccessibleEntropyFamily where
  /-- Input bit width $n_0(n)$ at security parameter $n$. -/
  inLen : ℕ → ℕ
  /-- Output bit width $m_0(n)$ at security parameter $n$. -/
  outLen : ℕ → ℕ
  /-- Inverse entropy-gap denominator $D(n) \ge 1$. -/
  denom : ℕ → ℕ
  /-- Word-level evaluator $(n, z) \mapsto F_0(n, z)$. -/
  evalWord : ℕ → List Bool → List Bool
  /-- Plain polynomial-time unary input-length certificate. -/
  polyTime_inLen : Turing.MultiTapeTM.ComputableInPolyTime inLen
    Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encUnary
  /-- Plain polynomial-time unary output-length certificate. -/
  polyTime_outLen : Turing.MultiTapeTM.ComputableInPolyTime outLen
    Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encUnary
  /-- Plain polynomial-time unary gap-denominator certificate. -/
  polyTime_denom : Turing.MultiTapeTM.ComputableInPolyTime denom
    Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encUnary
  /-- Positive gap denominator at every security parameter. -/
  denom_pos : ∀ n, 1 ≤ denom n
  /-- Plain polynomial-time word-evaluation certificate. -/
  polyTime_evalWord : Turing.MultiTapeTM.ComputableInPolyTime
    (fun p : ℕ × List Bool => evalWord p.1 p.2)
    (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encBits)
    Turing.MultiTapeTM.encBits
  /-- Fixed output width `outLen n` on `(inLen n)`-bit inputs. -/
  length_evalWord : ∀ n z, z.length = inLen n → (evalWord n z).length = outLen n
  /-- Definition 3.9 ($\forall A, \exists L_A$): every uniform strict-PPT collision finder admits a
  witnessing accessible-set family. -/
  exists_accessibleSet_of_collisionFinder :
    ∀ A : ℕ → List Bool → ProbComp (List Bool),
      Probability.IsPPT Turing.MultiTapeTM.encBits A →
      IsWordCollisionFinder inLen evalWord A →
      ∃ accSet : (n : ℕ) → BitString (inLen n) → Finset (BitString (inLen n)),
        IsAccessibleEntropyWitness inLen outLen denom evalWord A accSet

/-- Sanitization lifts Definition 3.9 from strict-PPT collision finders to arbitrary uniform
strict-PPT adversaries. -/
theorem AdversaryInaccessibleEntropyFamily.exists_accessibleSet
    (F : AdversaryInaccessibleEntropyFamily)
    (A : ℕ → List Bool → ProbComp (List Bool))
    (hA : Probability.IsPPT Turing.MultiTapeTM.encBits A) :
    ∃ accSet : (n : ℕ) → BitString (F.inLen n) → Finset (BitString (F.inLen n)),
      IsAccessibleEntropyWitness F.inLen F.outLen F.denom F.evalWord A accSet := by
  obtain ⟨accSet, hself, hsub, hgap, hesc⟩ := F.exists_accessibleSet_of_collisionFinder
    (sanitizeWordCollisionFinder F.inLen F.evalWord A)
    (isPPT_sanitizeWordCollisionFinder F.polyTime_inLen F.polyTime_evalWord hA)
    (isWordCollisionFinder_sanitizeWordCollisionFinder F.inLen F.evalWord A)
  refine ⟨accSet, hself, hsub, hgap, ?_⟩
  have heq (n : ℕ) :
      accessibleEscapeGame F.evalWord F.inLen accSet
        (sanitizeWordCollisionFinder F.inLen F.evalWord A) n =
      accessibleEscapeGame F.evalWord F.inLen accSet A n :=
    accessibleEscapeGame_sanitizeWordCollisionFinder F.evalWord F.inLen accSet A n (hself n)
  simpa only [heq] using hesc

/-- A uniform polynomial-time fixed-width function family with one adversary-independent
accessible-set family `accSet n` exhibiting an eventual `1 / denom n` gap between real conditional
Shannon entropy $H(Z \mid F(Z))$ and $\mathbb{E}[\log_2 |L(Z)|]$ against all uniform strict-PPT
adversaries (cf. `[HHRVW2020]`, Section 3.2, Definition 3.9, p. 15). -/
structure InaccessibleEntropyFamily where
  /-- Input bit width $n_0(n)$ at security parameter $n$. -/
  inLen : ℕ → ℕ
  /-- Output bit width $m_0(n)$ at security parameter $n$. -/
  outLen : ℕ → ℕ
  /-- Inverse entropy-gap denominator $D(n) \ge 1$. -/
  denom : ℕ → ℕ
  /-- Word-level evaluator $(n, z) \mapsto F_0(n, z)$. -/
  evalWord : ℕ → List Bool → List Bool
  /-- Accessible preimage subset $L_0(n, z) \subseteq F_0(n)^{-1}(F_0(n, z))$ for each input $z$. -/
  accSet : (n : ℕ) → BitString (inLen n) → Finset (BitString (inLen n))
  /-- Plain polynomial-time unary input-length certificate. -/
  polyTime_inLen : Turing.MultiTapeTM.ComputableInPolyTime inLen
    Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encUnary
  /-- Plain polynomial-time unary output-length certificate. -/
  polyTime_outLen : Turing.MultiTapeTM.ComputableInPolyTime outLen
    Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encUnary
  /-- Plain polynomial-time unary gap-denominator certificate. -/
  polyTime_denom : Turing.MultiTapeTM.ComputableInPolyTime denom
    Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encUnary
  /-- Positive gap denominator at every security parameter. -/
  denom_pos : ∀ n, 1 ≤ denom n
  /-- Plain polynomial-time word-evaluation certificate. -/
  polyTime_evalWord : Turing.MultiTapeTM.ComputableInPolyTime
    (fun p : ℕ × List Bool => evalWord p.1 p.2)
    (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encBits)
    Turing.MultiTapeTM.encBits
  /-- Fixed output width `outLen n` on `(inLen n)`-bit inputs. -/
  length_evalWord : ∀ n z, z.length = inLen n → (evalWord n z).length = outLen n
  /-- Reflexivity $z \in L_0(n, z)$ at every input. -/
  self_mem_accSet : ∀ n z, z ∈ accSet n z
  /-- Inclusion $L_0(n, z) \subseteq F_0(n)^{-1}(F_0(n, z))$ at every input. -/
  accSet_subset_fiber : ∀ n z,
    accSet n z ⊆ fiberSet (wordToFinMap (inLen n) (outLen n) (evalWord n))
      (wordToFinMap (inLen n) (outLen n) (evalWord n) z)
  /-- Eventual $1 / \mathrm{denom}(n)$ gap between real Shannon entropy and accessible average
  max-entropy. -/
  eventually_entropy_gap : ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
    accessibleSetExpectation (accSet n) ≤
      PMF.conditionalEntropy
        ((PMF.uniformOfFintype (BitString (inLen n))).map fun z =>
          (wordToFinMap (inLen n) (outLen n) (evalWord n) z, z)) -
        1 / (denom n : ℝ)
  /-- Every uniform strict-PPT adversary has negligible probability of outputting an `(inLen n)`-bit
  colliding preimage outside `accSet n`. -/
  escape_negligible : ∀ A : ℕ → List Bool → ProbComp (List Bool),
    Probability.IsPPT Turing.MultiTapeTM.encBits A →
      Negligible (fun n =>
        Game.succProbability (ProbComp.eval
          (accessibleEscapeGame evalWord inLen accSet A n)))

/-- Every `InaccessibleEntropyFamily` ($\exists L\;\forall A$) satisfies Definition 3.9's
adversary-dependent specification `AdversaryInaccessibleEntropyFamily` ($\forall A\;\exists L_A$),
witnessed by the fixed family `F.accSet` for every adversary. -/
def InaccessibleEntropyFamily.toAdversaryInaccessibleEntropyFamily
    (F : InaccessibleEntropyFamily) : AdversaryInaccessibleEntropyFamily where
  inLen := F.inLen
  outLen := F.outLen
  denom := F.denom
  evalWord := F.evalWord
  polyTime_inLen := F.polyTime_inLen
  polyTime_outLen := F.polyTime_outLen
  polyTime_denom := F.polyTime_denom
  denom_pos := F.denom_pos
  polyTime_evalWord := F.polyTime_evalWord
  length_evalWord := F.length_evalWord
  exists_accessibleSet_of_collisionFinder A hA _ :=
    ⟨F.accSet, F.self_mem_accSet, F.accSet_subset_fiber, F.eventually_entropy_gap,
      F.escape_negligible A hA⟩

end Cslib.Crypto
