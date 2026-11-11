/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.MCSP.AntiChecker.Certificate
public import CslibFrontier.Foundations.Data.BitString.BlockPower
public import CslibFrontier.Foundations.Data.BitString.Enumeration
public import CslibFrontier.Probability.BitString.AffineHash
public import CslibFrontier.Probability.PairwiseIndependentHash.Covering
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A deterministic greedy anti-checker against a threshold oracle

Let `G` be a finite family of descriptions, each evaluating to a Boolean function on `α`, and let
`f : α → Bool`. After labelled samples `P`, the descriptions still *consistent* are those that agree
with every sample (`Cslib.MCSP.AntiChecker.consistent`). A *threshold oracle* with power `ℓ`
answers queries `(P, u)` and separates `#consistent ^ ℓ` from `2 ^ u` up to a factor `2 (u + 1)`
(`Cslib.MCSP.AntiChecker.IsThresholdOracle`): a yes-answer guarantees fewer than `2 ^ (u + 1)`, at
threshold `0` it guarantees that no description is consistent, and fewer than `2 ^ u / (u + 1)`
forces a yes-answer.

The greedy (`Cslib.MCSP.AntiChecker.greedy`) runs `R` rounds with thresholds `R - 1, …, 0`. In
the round with threshold `u` it appends the first candidate `y`, labelled `f y`, on which the
oracle answers yes, or a default candidate if there is none
(`Cslib.MCSP.AntiChecker.select`). Suppose every nonempty subfamily of `G` is refuted on a sixteenth
of its members by some candidate, as for circuits of bounded size against a function needing more
gates than their strict majorities (`Cslib.MCSP.exists_card_le_sixteen_mul_validCertificates`).
If `#G ≤ 2 ^ L` and `4 (L ℓ + 1) 15 ^ ℓ ≤ 16 ^ ℓ`, then after `R = L ℓ + 1` rounds no description is
consistent (`Cslib.MCSP.AntiChecker.consistent_greedy_eq_empty`). Before the round with threshold
`u`, `#consistent ^ ℓ < 2 ^ (u + 2)`. A refuting candidate leaves at most `15 / 16` of the
consistent descriptions, so the oracle must answer yes on it: the factor `(15 / 16) ^ ℓ` absorbs the
slack `4 (u + 1)`, which is why the oracle measures a power of the count. The choice
`ℓ = L + 200` meets the condition for every `L`
(`Cslib.MCSP.AntiChecker.four_mul_mul_add_one_mul_fifteen_pow_le_sixteen_pow`).

A threshold oracle comes from covering by pairwise independent hashing
(`Cslib.Probability.IsPairwiseIndependentHash.exists_covers_of_card`). The `ℓ`-th Cartesian power
of the consistent set is *large at threshold `u`* if `u + 1` affine hash functions to strings of
`u` bits are jointly surjective on it (`Cslib.MCSP.AntiChecker.IsLarge`). The oracle answering
whether the power is not large (`Cslib.MCSP.AntiChecker.hashOracle`) is a threshold oracle for
every `ℓ > 0` (`Cslib.MCSP.AntiChecker.isThresholdOracle_hashOracle`). With the valid circuit
descriptions this gives an explicit anti-checker of `L (L + 200) + 1` inputs, where `L` is the
certificate length (`Cslib.MCSP.AntiChecker.isAntiChecker_hashAntiChecker`).

This is the library's deterministic greedy against a counting oracle, not the proof of
[Oliveira, Pich and Santhanam, Lemma 4.1][OliveiraPichSanthanam2019]. Their proof counts with
Stockmeyer's randomized approximate counting, fixes the randomness non-uniformly, and lists the
few surviving circuits at the end. Here the greedy drives the count to zero, so no listing step is
needed, and the oracle is deterministic. Raising the consistent set to a Cartesian power before
hashing it with linear hash functions follows the approximate counting in
[Chen, Hirahara, Oliveira, Pich, Rajgopal and Santhanam, proof of Lemma 27 and Claim 28]
[ChenHiraharaOliveiraPichRajgopalSanthanam2020]. There, linear maps that are injective on pieces
certify an upper bound on the count. Here, jointly surjective maps certify a lower bound. The
efficient generator, which needs circuits for the oracle and for the selection, is not formalized
here.

## Main definitions

* `Cslib.MCSP.AntiChecker.consistent`: the descriptions consistent with labelled samples.
* `Cslib.MCSP.AntiChecker.IsThresholdOracle`: two-sided threshold oracles for the consistent
  count.
* `Cslib.MCSP.AntiChecker.greedy`: the greedy choice of samples against an oracle.
* `Cslib.MCSP.AntiChecker.IsLarge`: covering by `u + 1` affine hash functions to `u` bits.
* `Cslib.MCSP.AntiChecker.hashOracle`: the hash threshold oracle.
* `Cslib.MCSP.AntiChecker.hashAntiChecker`: the greedy anti-checker for circuits.

## Main results

* `Cslib.MCSP.AntiChecker.consistent_greedy_eq_empty`: the greedy refutes every description.
* `Cslib.MCSP.AntiChecker.four_mul_mul_add_one_mul_fifteen_pow_le_sixteen_pow`: the power
  `ℓ = L + 200` suffices.
* `Cslib.MCSP.AntiChecker.isThresholdOracle_hashOracle`: hashing gives a threshold oracle.
* `Cslib.MCSP.AntiChecker.isAntiChecker_greedy`: against any threshold oracle, the greedy is an
  anti-checker for circuits.
* `Cslib.MCSP.AntiChecker.isAntiChecker_hashAntiChecker`: the greedy anti-checker for circuits.

## References

* [I. C. Oliveira, J. Pich, R. Santhanam, *Hardness magnification near state-of-the-art lower
  bounds*][OliveiraPichSanthanam2019]
* [L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal, R. Santhanam, *Beyond natural
  proofs: hardness magnification and locality*][ChenHiraharaOliveiraPichRajgopalSanthanam2020]
-/

public section

namespace Cslib.MCSP.AntiChecker

open Finset Circuits Circuits.Boolean Cslib.Probability Cslib.BitString.LinearHash

variable {α β : Type*}

/-! ### Consistent descriptions -/

section Consistent

variable (G : Finset β) (eval : β → α → Bool)

/-- The descriptions in `G` that agree with every labelled sample `(y, b)` of `P`:
`eval g y = b`. -/
def consistent (P : List (α × Bool)) : Finset β :=
  G.filter fun g => ∀ q ∈ P, eval g q.1 = q.2

variable {G eval}

/-- A description is consistent with `P` when it lies in `G` and agrees with every sample. -/
theorem mem_consistent {P : List (α × Bool)} {g : β} :
    g ∈ consistent G eval P ↔ g ∈ G ∧ ∀ q ∈ P, eval g q.1 = q.2 := by
  rw [consistent, mem_filter]

/-- Every description is consistent with no samples. -/
@[simp] theorem consistent_nil : consistent G eval [] = G := by
  ext g
  simp [mem_consistent]

/-- The consistent descriptions lie in `G`. -/
theorem consistent_subset (P : List (α × Bool)) : consistent G eval P ⊆ G :=
  filter_subset _ _

/-- More samples leave fewer consistent descriptions. -/
theorem consistent_anti {P Q : List (α × Bool)} (h : P <+: Q) :
    consistent G eval Q ⊆ consistent G eval P := fun g hg => by
  rw [mem_consistent] at hg ⊢
  exact ⟨hg.1, fun q hq => hg.2 q (h.subset hq)⟩

/-- A further sample `(y, b)` keeps the consistent descriptions with `eval g y = b`. -/
theorem consistent_append_singleton (P : List (α × Bool)) (y : α) (b : Bool) :
    consistent G eval (P ++ [(y, b)]) = (consistent G eval P).filter fun g => eval g y = b := by
  ext g
  simp only [mem_consistent, mem_filter, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨hg, h⟩
    exact ⟨⟨hg, fun q hq => h q (Or.inl hq)⟩, h _ (Or.inr rfl)⟩
  · rintro ⟨⟨hg, h⟩, hy⟩
    refine ⟨hg, fun q hq => hq.elim (h q) fun e => ?_⟩
    subst e
    exact hy

/-- If no description is consistent with `P`, every description in `G` errs on a sample of `P`. -/
theorem exists_mem_ne_of_consistent_eq_empty {P : List (α × Bool)}
    (h : consistent G eval P = ∅) {g : β} (hg : g ∈ G) : ∃ q ∈ P, eval g q.1 ≠ q.2 := by
  by_contra! hall
  have hmem : g ∈ consistent G eval P := mem_consistent.2 ⟨hg, hall⟩
  simp [h] at hmem

end Consistent

/-! ### Threshold oracles -/

/-- An oracle answering queries `(P, u)` is a *threshold oracle* with power `ℓ` for the
descriptions `G` if a yes-answer guarantees `#consistent ^ ℓ < 2 ^ (u + 1)`, a yes-answer at
threshold `0` guarantees that no description is consistent, and
`(u + 1) #consistent ^ ℓ < 2 ^ u` forces a yes-answer. -/
structure IsThresholdOracle (G : Finset β) (eval : β → α → Bool) (ℓ : ℕ)
    (O : List (α × Bool) → ℕ → Bool) : Prop where
  /-- A yes-answer bounds the power of the consistent count. -/
  card_pow_lt {P : List (α × Bool)} {u : ℕ} :
    O P u = true → #(consistent G eval P) ^ ℓ < 2 ^ (u + 1)
  /-- A small enough power of the consistent count forces a yes-answer. -/
  apply_eq_true_of_lt {P : List (α × Bool)} {u : ℕ} :
    (u + 1) * #(consistent G eval P) ^ ℓ < 2 ^ u → O P u = true
  /-- A yes-answer at threshold `0` leaves no consistent description. -/
  consistent_eq_empty {P : List (α × Bool)} : O P 0 = true → consistent G eval P = ∅

/-! ### The greedy -/

section Greedy

variable [Inhabited α] (O : List (α × Bool) → ℕ → Bool) (f : α → Bool) (cands : List α)

/-- The candidate chosen after the samples `P` in the round with threshold `u`: the first
candidate `y` on which the oracle answers yes to `(P ++ [(y, f y)], u)`, or the default if there is
none. -/
@[expose] def select (u : ℕ) (P : List (α × Bool)) : α :=
  (cands.find? fun y => O (P ++ [(y, f y)]) u).getD default

/-- The round with threshold `u`: append the selected candidate with its label. -/
@[expose] def step (u : ℕ) (P : List (α × Bool)) : List (α × Bool) :=
  P ++ [(select O f cands u P, f (select O f cands u P))]

/-- The greedy: `k` rounds after the samples `P`, with thresholds `k - 1, …, 0`. -/
@[expose] def greedy : ℕ → List (α × Bool) → List (α × Bool)
  | 0, P => P
  | k + 1, P => greedy k (step O f cands k P)

@[simp] theorem greedy_zero (P : List (α × Bool)) : greedy O f cands 0 P = P :=
  rfl

theorem greedy_succ (k : ℕ) (P : List (α × Bool)) :
    greedy O f cands (k + 1) P = greedy O f cands k (step O f cands k P) :=
  rfl

/-- The greedy appends one sample per round. -/
@[simp] theorem length_greedy (k : ℕ) (P : List (α × Bool)) :
    (greedy O f cands k P).length = P.length + k := by
  induction k generalizing P with
  | zero => rfl
  | succ k ih =>
    rw [greedy_succ, ih, step, List.length_append, List.length_singleton]
    omega

/-- The greedy extends its initial samples. -/
theorem prefix_greedy (k : ℕ) (P : List (α × Bool)) : P <+: greedy O f cands k P := by
  induction k generalizing P with
  | zero => exact List.prefix_refl P
  | succ k ih => exact (List.prefix_append _ _).trans (ih _)

/-- The greedy labels its samples by `f`. -/
theorem forall_mem_greedy_snd_eq {P : List (α × Bool)} (hP : ∀ q ∈ P, q.2 = f q.1) (k : ℕ) :
    ∀ q ∈ greedy O f cands k P, q.2 = f q.1 := by
  induction k generalizing P with
  | zero => exact hP
  | succ k ih =>
    refine ih fun q hq => ?_
    rw [step, List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact hP q hq
    · rfl

variable {O f cands}

/-- If the oracle answers yes on some candidate, it answers yes on the selected one. -/
theorem apply_step_eq_true {u : ℕ} {P : List (α × Bool)}
    (h : ∃ y ∈ cands, O (P ++ [(y, f y)]) u = true) : O (step O f cands u P) u = true := by
  obtain ⟨y, hy, hO⟩ := h
  rw [step, select]
  cases hfind : cands.find? (fun y => O (P ++ [(y, f y)]) u) with
  | none => exact absurd hO (by simpa using List.find?_eq_none.1 hfind y hy)
  | some z => simpa using List.find?_some hfind

variable {G : Finset β} {eval : β → α → Bool} {ℓ : ℕ}

/-- **One round.** If `#consistent ^ ℓ < 2 ^ (u + 2)` before the round with threshold `u` and
`4 (u + 1) 15 ^ ℓ ≤ 16 ^ ℓ`, then after it no description is consistent or the oracle answered
yes. A candidate refuting a sixteenth of the consistent descriptions leaves
`(u + 1) #consistent ^ ℓ < 2 ^ u`, so the oracle answers yes on it. -/
theorem consistent_step_eq_empty_or (ho : IsThresholdOracle G eval ℓ O)
    (hgood : ∀ G' ⊆ G, G'.Nonempty → ∃ x ∈ cands, #G' ≤ 16 * #{g ∈ G' | eval g x ≠ f x})
    {u : ℕ} (hℓ : 4 * (u + 1) * 15 ^ ℓ ≤ 16 ^ ℓ) {P : List (α × Bool)}
    (hP : #(consistent G eval P) ^ ℓ < 2 ^ (u + 2)) :
    consistent G eval (step O f cands u P) = ∅ ∨ O (step O f cands u P) u = true := by
  rcases (consistent G eval P).eq_empty_or_nonempty with he | hne
  · left
    rw [← subset_empty, ← he]
    exact consistent_anti (List.prefix_append _ _)
  right
  obtain ⟨x, hx, hcount⟩ := hgood _ (consistent_subset P) hne
  refine apply_step_eq_true ⟨x, hx, ho.apply_eq_true_of_lt ?_⟩
  rw [consistent_append_singleton]
  have hsplit : #{g ∈ consistent G eval P | eval g x = f x} +
      #{g ∈ consistent G eval P | eval g x ≠ f x} = #(consistent G eval P) :=
    card_filter_add_card_filter_not _
  set a := #{g ∈ consistent G eval P | eval g x = f x}
  set c := #(consistent G eval P)
  have h16 : 16 * a ≤ 15 * c := by omega
  have hpow : 16 ^ ℓ * a ^ ℓ ≤ 15 ^ ℓ * c ^ ℓ := by
    rw [← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left h16 ℓ
  refine lt_of_mul_lt_mul_left ?_ (Nat.zero_le (16 ^ ℓ))
  calc 16 ^ ℓ * ((u + 1) * a ^ ℓ) = (u + 1) * (16 ^ ℓ * a ^ ℓ) := by ring
    _ ≤ (u + 1) * (15 ^ ℓ * c ^ ℓ) := Nat.mul_le_mul_left _ hpow
    _ < (u + 1) * (15 ^ ℓ * 2 ^ (u + 2)) := by gcongr
    _ = 4 * (u + 1) * 15 ^ ℓ * 2 ^ u := by ring
    _ ≤ 16 ^ ℓ * 2 ^ u := Nat.mul_le_mul_right _ hℓ

/-- The invariant of the greedy: if `#consistent ^ ℓ < 2 ^ (k + 2)` before the rounds with
thresholds `k, …, 0` and `4 (k + 1) 15 ^ ℓ ≤ 16 ^ ℓ`, then after them no description is
consistent. -/
theorem consistent_greedy_succ_eq_empty (ho : IsThresholdOracle G eval ℓ O)
    (hgood : ∀ G' ⊆ G, G'.Nonempty → ∃ x ∈ cands, #G' ≤ 16 * #{g ∈ G' | eval g x ≠ f x}) :
    ∀ (k : ℕ) (P : List (α × Bool)), 4 * (k + 1) * 15 ^ ℓ ≤ 16 ^ ℓ →
      #(consistent G eval P) ^ ℓ < 2 ^ (k + 2) →
        consistent G eval (greedy O f cands (k + 1) P) = ∅
  | 0, P, hℓ, hP => by
    rw [greedy_succ, greedy_zero]
    rcases consistent_step_eq_empty_or ho hgood hℓ hP with h | h
    · exact h
    · exact ho.consistent_eq_empty h
  | k + 1, P, hℓ, hP => by
    rw [greedy_succ]
    have hℓ' : 4 * (k + 1) * 15 ^ ℓ ≤ 16 ^ ℓ :=
      le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 (Nat.le_succ _))) hℓ
    rcases consistent_step_eq_empty_or ho hgood hℓ hP with h | h
    · rw [← subset_empty, ← h]
      exact consistent_anti (prefix_greedy _ _ _ _ _)
    · exact consistent_greedy_succ_eq_empty ho hgood k _ hℓ' (ho.card_pow_lt h)

/-- **The greedy refutes every description.** If `#G ≤ 2 ^ L`, every nonempty subfamily of `G`
is refuted on a sixteenth of its members by some candidate, and `4 (L ℓ + 1) 15 ^ ℓ ≤ 16 ^ ℓ`,
then after `L ℓ + 1` rounds against a threshold oracle with power `ℓ` no description is
consistent. -/
theorem consistent_greedy_eq_empty (ho : IsThresholdOracle G eval ℓ O)
    (hgood : ∀ G' ⊆ G, G'.Nonempty → ∃ x ∈ cands, #G' ≤ 16 * #{g ∈ G' | eval g x ≠ f x})
    {L : ℕ} (hG : #G ≤ 2 ^ L) (hℓ : 4 * (L * ℓ + 1) * 15 ^ ℓ ≤ 16 ^ ℓ) :
    consistent G eval (greedy O f cands (L * ℓ + 1) []) = ∅ := by
  refine consistent_greedy_succ_eq_empty ho hgood (L * ℓ) [] hℓ ?_
  rw [consistent_nil]
  calc #G ^ ℓ ≤ (2 ^ L) ^ ℓ := Nat.pow_le_pow_left hG ℓ
    _ = 2 ^ (L * ℓ) := (pow_mul 2 L ℓ).symm
    _ < 2 ^ (L * ℓ + 2) := Nat.pow_lt_pow_right (by decide) (by omega)

end Greedy

/-! ### The power -/

/-- `4 (L + 201) ^ 2 15 ^ (L + 200) ≤ 16 ^ (L + 200)`, by induction from `L = 0`: the step needs
`15 (m + 1) ^ 2 ≤ 16 m ^ 2` for `m = L + 201`. -/
private theorem four_mul_sq_mul_fifteen_pow_le_sixteen_pow (L : ℕ) :
    4 * (L + 201) ^ 2 * 15 ^ (L + 200) ≤ 16 ^ (L + 200) := by
  induction L with
  | zero => norm_num
  | succ L ih =>
    have hq : 15 * (L + 1 + 201) ^ 2 ≤ 16 * (L + 201) ^ 2 :=
      Nat.le.intro (k := L ^ 2 + 372 * L + 34356) (by ring)
    calc 4 * (L + 1 + 201) ^ 2 * 15 ^ (L + 1 + 200)
        = 4 * (15 * (L + 1 + 201) ^ 2) * 15 ^ (L + 200) := by ring
      _ ≤ 4 * (16 * (L + 201) ^ 2) * 15 ^ (L + 200) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hq)
      _ = 16 * (4 * (L + 201) ^ 2 * 15 ^ (L + 200)) := by ring
      _ ≤ 16 * 16 ^ (L + 200) := Nat.mul_le_mul_left 16 ih
      _ = 16 ^ (L + 1 + 200) := by ring

/-- **The power `ℓ = L + 200` suffices**: `4 (L ℓ + 1) 15 ^ ℓ ≤ 16 ^ ℓ`. -/
theorem four_mul_mul_add_one_mul_fifteen_pow_le_sixteen_pow (L : ℕ) :
    4 * (L * (L + 200) + 1) * 15 ^ (L + 200) ≤ 16 ^ (L + 200) :=
  le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 (by nlinarith)))
    (four_mul_sq_mul_fifteen_pow_le_sixteen_pow L)

/-! ### The hash threshold oracle -/

section Hash

/-- A set `T` of strings of `N` bits is *large at threshold `u`* if `u + 1` affine hash functions
to strings of `u` bits are jointly surjective on `T`. -/
@[expose] def IsLarge {N : ℕ} (u : ℕ) (T : Finset (BitString N)) : Prop :=
  ∃ seeds : Fin (u + 1) → (Fin u → BitString N) × BitString u, Covers affineHash T seeds

instance {N u : ℕ} (T : Finset (BitString N)) : Decidable (IsLarge u T) :=
  inferInstanceAs
    (Decidable (∃ seeds : Fin (u + 1) → (Fin u → BitString N) × BitString u,
      Covers affineHash T seeds))

variable {N u : ℕ} {T : Finset (BitString N)}

/-- Sets of at least `2 ^ (u + 1)` strings are large at threshold `u`. -/
theorem isLarge_of_card (h : 2 ^ (u + 1) ≤ #T) : IsLarge u T :=
  (isPairwiseIndependentHash_affineHash u N).exists_covers_of_card (q := 2)
    (by rwa [BitString.card, ← pow_succ'])
    (by rw [BitString.card]; exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self u))

/-- Sets large at threshold `u` have at least `2 ^ u / (u + 1)` strings. -/
theorem IsLarge.two_pow_le (h : IsLarge u T) : 2 ^ u ≤ (u + 1) * #T := by
  obtain ⟨seeds, hc⟩ := h
  have hle := hc.card_le_mul
  rwa [BitString.card] at hle

/-- At threshold `0`, the large sets are the nonempty ones. -/
theorem isLarge_zero_iff : IsLarge 0 T ↔ T.Nonempty :=
  ⟨fun ⟨_, hc⟩ => (covers_iff_nonempty (Nat.succ_pos 0)).1 hc,
    fun hT => ⟨fun _ => default, (covers_iff_nonempty (Nat.succ_pos 0)).2 hT⟩⟩

variable {L : ℕ}

/-- The hash threshold oracle with power `ℓ`: it answers yes to `(P, u)` when the `ℓ`-th
Cartesian power of the descriptions consistent with `P` is not large at threshold `u`. -/
def hashOracle (G : Finset (BitString L)) (eval : BitString L → α → Bool) (ℓ : ℕ)
    (P : List (α × Bool)) (u : ℕ) : Bool :=
  !decide (IsLarge u (BitString.blockPower (consistent G eval P) ℓ))

@[simp] theorem hashOracle_eq_true {G : Finset (BitString L)} {eval : BitString L → α → Bool}
    {ℓ : ℕ} {P : List (α × Bool)} :
    hashOracle G eval ℓ P u = true ↔
      ¬ IsLarge u (BitString.blockPower (consistent G eval P) ℓ) := by
  simp [hashOracle]

/-- **Hashing gives a threshold oracle**: for every power `ℓ > 0`, the hash oracle is a threshold
oracle. -/
theorem isThresholdOracle_hashOracle (G : Finset (BitString L)) (eval : BitString L → α → Bool)
    {ℓ : ℕ} (hℓ : 0 < ℓ) : IsThresholdOracle G eval ℓ (hashOracle G eval ℓ) where
  card_pow_lt h := by
    rw [hashOracle_eq_true] at h
    by_contra! hle
    exact h (isLarge_of_card (by rwa [BitString.card_blockPower]))
  apply_eq_true_of_lt h := by
    rw [hashOracle_eq_true]
    intro hl
    have hle := hl.two_pow_le
    rw [BitString.card_blockPower] at hle
    exact not_le.2 h hle
  consistent_eq_empty h := by
    rwa [hashOracle_eq_true, isLarge_zero_iff, not_nonempty_iff_eq_empty,
      BitString.blockPower_eq_empty_iff hℓ.ne'] at h

end Hash

/-! ### The anti-checker for circuits -/

/-- The greedy anti-checker for the circuits on `n` inputs with at most `s` gates: the inputs
chosen in `L (L + 200) + 1` rounds against the hash threshold oracle with power `L + 200` for the
valid descriptions, where `L` is the certificate length, with the candidates in the order of
`Cslib.BitString.enum`. -/
def hashAntiChecker (n s : ℕ) (f : BooleanFunction n) : List (BitString n) :=
  (greedy (hashOracle (validCertificates n s) (certificateFunction n s) (certLength n s + 200)) f
    (BitString.enum n) (certLength n s * (certLength n s + 200) + 1) []).map Prod.fst

/-- The greedy anti-checker has `L (L + 200) + 1` inputs, where `L` is the certificate length. -/
@[simp] theorem length_hashAntiChecker (n s : ℕ) (f : BooleanFunction n) :
    (hashAntiChecker n s f).length = certLength n s * (certLength n s + 200) + 1 := by
  simp [hashAntiChecker]

/-- **The greedy is an anti-checker for circuits against any threshold oracle.** If `f` needs more
gates than `n` circuits with at most `s` gates and a circuit for their strict majority, then
against any threshold oracle with power `L + 200` for the valid descriptions, where `L` is the
certificate length, every circuit with at most `s` gates differs from `f` on an input chosen in
the `L (L + 200) + 1` rounds of the greedy. -/
theorem isAntiChecker_greedy {n s : ℕ} (hn : 0 < n) {f : BooleanFunction n}
    (hf : n * s + complexity interpretation (single (strictMajority n)) <
      complexity interpretation (single f))
    {O : List (BitString n × Bool) → ℕ → Bool}
    (ho : IsThresholdOracle (validCertificates n s) (certificateFunction n s)
      (certLength n s + 200) O) :
    IsAntiChecker (computableFunctions n s) f
      {x | x ∈ (greedy O f (BitString.enum n) (certLength n s * (certLength n s + 200) + 1)
        []).map Prod.fst} := by
  have hempty := consistent_greedy_eq_empty (f := f) (cands := BitString.enum n) ho
    (fun _ hG' hne => (exists_card_le_sixteen_mul_validCertificates hn le_rfl hf hne hG').imp
      fun x hx => ⟨BitString.mem_enum n x, hx⟩)
    (card_validCertificates_le n s) (four_mul_mul_add_one_mul_fifteen_pow_le_sixteen_pow _)
  intro g hg
  rw [← image_validCertificates] at hg
  obtain ⟨w, hw, rfl⟩ := hg
  obtain ⟨q, hq, hne⟩ := exists_mem_ne_of_consistent_eq_empty hempty (mem_coe.1 hw)
  refine ⟨q.1, ?_, ?_⟩
  · exact List.mem_map.2 ⟨q, hq, rfl⟩
  · rwa [forall_mem_greedy_snd_eq _ f _ (P := []) (by simp) _ q hq] at hne

/-- **The greedy anti-checker for circuits.** If `f` needs more gates than `n` circuits with at
most `s` gates and a circuit for their strict majority, then every circuit with at most `s` gates
differs from `f` on an input of the greedy anti-checker. -/
theorem isAntiChecker_hashAntiChecker {n s : ℕ} (hn : 0 < n) {f : BooleanFunction n}
    (hf : n * s + complexity interpretation (single (strictMajority n)) <
      complexity interpretation (single f)) :
    IsAntiChecker (computableFunctions n s) f {x | x ∈ hashAntiChecker n s f} :=
  isAntiChecker_greedy hn hf (isThresholdOracle_hashOracle (validCertificates n s)
    (certificateFunction n s) (Nat.succ_pos _))

end Cslib.MCSP.AntiChecker
