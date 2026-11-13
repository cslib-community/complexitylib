/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.MachineLearning.PACLearning.VCDimension
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Powerset
import CslibFrontier.Foundations.Data.Nat.Choose.Sum

/-!
# The Natarajan dimension and Natarajan's lemma

The *Natarajan dimension* extends the VC dimension from binary to multiclass concept classes
`C : ConceptClass α β` [ShalevShwartzBenDavid2014, Section 29.1; Natarajan1989]. A set `W` is
*N-shattered* by `C` if there are two labelings `f₀ f₁ : α → β` that differ at every point of `W`
such that for every `B ⊆ W` some concept of `C` agrees with `f₀` on `B` and with `f₁` on `W \ B`
(Definition 29.1). The Natarajan dimension is the largest size of an N-shattered finite set
(Definition 29.2). With `Bool` labels N-shattering is ordinary shattering, so the Natarajan
dimension is the VC dimension (`natarajanShatters_iff_setShatters`, `natarajanDim_eq_vcDim`).

*Natarajan's lemma* replaces Sauer's lemma in the multiclass fundamental theorem
[ShalevShwartzBenDavid2014, Lemma 29.4]. With `k` labels, a set of labelings of `n` points whose
N-shattered sets have at most `d` points has at most

`∑_{i ≤ d} (n choose i) (k choose 2) ^ i`

elements (`ncard_le_natarajanSum`). The proof is the induction suggested in
[ShalevShwartzBenDavid2014, Exercise 29.3], splitting off one point: a labeling of the remaining
points that extends with `s` labels at the new point is counted once among the tails and once for
each of the `s choose 2 ≥ s - 1` pairs of those labels, and the tails extending with both labels
of a fixed pair N-shatter only sets of at most `d - 1` points. The hint sums over ordered pairs of
labels; unordered pairs give the factor `k choose 2`. With at least one label the sum is at most
`(n + 1) ^ d k ^ (2 d)` (`natarajanSum_le`). For a class on a finite domain `α` this gives
`|C| ≤ |α| ^ Ndim(C) k ^ (2 Ndim(C))`, the form of Lemma 29.4 (`ncard_le_card_pow_natarajanDim`).
The source states Lemma 29.4 for classes of functions from `X` to `[k]`; here the labels are any
finite type.

## Main definitions

- `NatarajanShatters C W`: the concept class `C` N-shatters the set `W`.
- `natarajanDim C`: the Natarajan dimension of `C`.
- `HasFiniteNatarajanDim C`: the N-shattered finite sets of `C` have bounded size.
- `natarajanSum n k d`: the bound `∑_{i ≤ d} (n choose i) (k choose 2) ^ i` of Natarajan's lemma.

## Main results

- `NatarajanShatters.subset`, `NatarajanShatters.superset`: (anti)monotonicity.
- `NatarajanShatters.of_restrict`: N-shattering transfers from the restriction of a class to
  sample points back to the points themselves.
- `natarajanShatters_iff_setShatters`, `natarajanDim_eq_vcDim`: with `Bool` labels the Natarajan
  dimension is the VC dimension.
- `ncard_le_natarajanSum`, `ncard_restriction_le_natarajanSum`: **Natarajan's lemma** for sets of
  labelings and for the labelings a class realizes on sample points.
- `natarajanSum_le`, `ncard_le_card_pow_natarajanDim`: the polynomial form of Lemma 29.4.

## References

* [B. K. Natarajan, *On learning sets and functions*][Natarajan1989]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open Finset

namespace Cslib.MachineLearning.PACLearning

variable {α β γ : Type*}

/-- A concept class `C` *N-shatters* a set `W` if there are labelings `f₀ f₁ : α → β` that differ
at every point of `W` such that for every `B ⊆ W` some concept `c ∈ C` agrees with `f₀` on `B` and
with `f₁` on `W \ B` [ShalevShwartzBenDavid2014, Definition 29.1]. -/
@[expose] def NatarajanShatters (C : ConceptClass α β) (W : Set α) : Prop :=
  ∃ f₀ f₁ : α → β, (∀ x ∈ W, f₀ x ≠ f₁ x) ∧
    ∀ B ⊆ W, ∃ c ∈ C, (∀ x ∈ B, c x = f₀ x) ∧ ∀ x ∈ W \ B, c x = f₁ x

/-- The *Natarajan dimension* of `C`: the supremum of the sizes of the finite sets N-shattered by
`C` [ShalevShwartzBenDavid2014, Definition 29.2]. As for `vcDim`, it is `0` when these sizes are
unbounded, so it is meaningful under `HasFiniteNatarajanDim C`. -/
noncomputable def natarajanDim (C : ConceptClass α β) : ℕ :=
  sSup {n : ℕ | ∃ W : Finset α, W.card = n ∧ NatarajanShatters C ↑W}

/-- The finite sets N-shattered by `C` have bounded size. -/
def HasFiniteNatarajanDim (C : ConceptClass α β) : Prop :=
  BddAbove {n : ℕ | ∃ W : Finset α, W.card = n ∧ NatarajanShatters C ↑W}

/-- N-shattering is anti-monotone in the shattered set. -/
theorem NatarajanShatters.subset {C : ConceptClass α β} {W V : Set α}
    (hW : NatarajanShatters C W) (hVW : V ⊆ W) : NatarajanShatters C V := by
  obtain ⟨f₀, f₁, hne, h⟩ := hW
  refine ⟨f₀, f₁, fun x hx => hne x (hVW hx), fun B hB => ?_⟩
  obtain ⟨c, hc, h₀, h₁⟩ := h B (hB.trans hVW)
  exact ⟨c, hc, h₀, fun x hx => h₁ x ⟨hVW hx.1, hx.2⟩⟩

/-- N-shattering is monotone in the concept class. -/
theorem NatarajanShatters.superset {C C' : ConceptClass α β} {W : Set α}
    (hW : NatarajanShatters C W) (hCC' : C ⊆ C') : NatarajanShatters C' W := by
  obtain ⟨f₀, f₁, hne, h⟩ := hW
  refine ⟨f₀, f₁, hne, fun B hB => ?_⟩
  obtain ⟨c, hc, h₀, h₁⟩ := h B hB
  exact ⟨c, hCC' hc, h₀, h₁⟩

/-- A class N-shatters some set only if it is nonempty. -/
theorem NatarajanShatters.nonempty {C : ConceptClass α β} {W : Set α}
    (hW : NatarajanShatters C W) : C.Nonempty := by
  obtain ⟨_, _, _, h⟩ := hW
  obtain ⟨c, hc, _⟩ := h ∅ (Set.empty_subset W)
  exact ⟨c, hc⟩

/-- Every nonempty class N-shatters the empty set. -/
theorem natarajanShatters_empty {C : ConceptClass α β} (hC : C.Nonempty) :
    NatarajanShatters C ∅ := by
  obtain ⟨c, hc⟩ := hC
  exact ⟨c, c, fun _ hx => hx.elim, fun B _ => ⟨c, hc, fun _ _ => rfl, fun _ _ => rfl⟩⟩

/-- N-shattering transfers from the labelings a class realizes on the points `e : γ → α` back to
the points: if `(· ∘ e) '' C` N-shatters `W`, then `e` is injective on `W` and `C` N-shatters
`e '' W`. -/
theorem NatarajanShatters.of_restrict {C : ConceptClass α β} {e : γ → α} {W : Set γ}
    (hW : NatarajanShatters ((· ∘ e) '' C) W) : Set.InjOn e W ∧ NatarajanShatters C (e '' W) := by
  obtain ⟨f₀, f₁, hne, h⟩ := hW
  have hinj : Set.InjOn e W := by
    intro i hi j hj hij
    by_contra hne'
    obtain ⟨_, ⟨c, -, rfl⟩, -, h₁⟩ := h ∅ (Set.empty_subset W)
    obtain ⟨_, ⟨c', -, rfl⟩, h₀', h₁'⟩ := h {i} (Set.singleton_subset_iff.2 hi)
    have hci : c (e i) = f₁ i := h₁ i ⟨hi, Set.notMem_empty i⟩
    have hcj : c (e j) = f₁ j := h₁ j ⟨hj, Set.notMem_empty j⟩
    have hc'i : c' (e i) = f₀ i := h₀' i rfl
    have hc'j : c' (e j) = f₁ j := h₁' j ⟨hj, fun h => hne' (Set.mem_singleton_iff.1 h).symm⟩
    exact hne i hi (by rw [← hc'i, hij, hc'j, ← hcj, ← hij, hci])
  refine ⟨hinj, ?_⟩
  rcases W.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · obtain ⟨_, ⟨c, hc, rfl⟩, -⟩ := h ∅ (Set.empty_subset _)
    rw [Set.image_empty]
    exact natarajanShatters_empty ⟨c, hc⟩
  have : Nonempty γ := ⟨i₀⟩
  set g := Function.invFunOn e W
  have hg : ∀ i ∈ W, g (e i) = i := fun i hi => hinj.leftInvOn_invFunOn hi
  refine ⟨f₀ ∘ g, f₁ ∘ g, ?_, fun B hB => ?_⟩
  · rintro _ ⟨i, hi, rfl⟩
    simpa only [Function.comp_apply, hg i hi] using hne i hi
  · obtain ⟨_, ⟨c, hc, rfl⟩, h₀, h₁⟩ := h (W ∩ e ⁻¹' B) Set.inter_subset_left
    refine ⟨c, hc, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := hB hx
      simpa only [Function.comp_apply, hg i hi] using h₀ i ⟨hi, hx⟩
    · rintro x ⟨⟨i, hi, rfl⟩, hx⟩
      simpa only [Function.comp_apply, hg i hi] using h₁ i ⟨hi, fun h => hx h.2⟩

/-- With `Bool` labels, N-shattering is ordinary shattering. -/
theorem natarajanShatters_iff_setShatters {C : ConceptClass α Bool} {W : Set α} :
    NatarajanShatters C W ↔ SetShatters C W := by
  classical
  constructor
  · rintro ⟨f₀, f₁, hne, h⟩ W' hW'
    obtain ⟨c, hc, h₀, h₁⟩ := h {x ∈ W | f₀ x = decide (x ∈ W')} (fun x hx => hx.1)
    refine ⟨c, hc, Set.ext fun x => ?_⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun ⟨hcx, hx⟩ => ?_, fun hx => ⟨?_, hW' hx⟩⟩
    · by_cases hB : f₀ x = decide (x ∈ W')
      · simpa [hB, hcx] using (h₀ x ⟨hx, hB⟩).symm
      · have := h₁ x ⟨hx, fun h => hB h.2⟩
        have hne' := hne x hx
        cases hf : f₀ x <;> cases hg : f₁ x <;> simp_all
    · by_cases hB : f₀ x = decide (x ∈ W')
      · simpa [hx] using (h₀ x ⟨hW' hx, hB⟩).trans hB
      · have := h₁ x ⟨hW' hx, fun h => hB h.2⟩
        have hne' := hne x (hW' hx)
        cases hf : f₀ x <;> cases hg : f₁ x <;> simp_all
  · intro h
    refine ⟨fun _ => true, fun _ => false, fun _ _ => by simp, fun B hB => ?_⟩
    obtain ⟨c, hc, hcB⟩ := h B hB
    refine ⟨c, hc, fun x hx => ?_, fun x hx => ?_⟩
    · have : x ∈ c ⁻¹' {true} ∩ W := hcB ▸ hx
      exact this.1
    · have : x ∉ c ⁻¹' {true} ∩ W := hcB ▸ hx.2
      simpa [hx.1] using this

/-- With `Bool` labels, the Natarajan dimension is the VC dimension. -/
theorem natarajanDim_eq_vcDim (C : ConceptClass α Bool) : natarajanDim C = vcDim C := by
  simp only [natarajanDim, vcDim, natarajanShatters_iff_setShatters]

/-- A class has finite Natarajan dimension iff its N-shattered finite sets have uniformly bounded
size. -/
theorem hasFiniteNatarajanDim_iff {C : ConceptClass α β} :
    HasFiniteNatarajanDim C ↔
      ∃ N : ℕ, ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ N :=
  ⟨fun ⟨N, hN⟩ => ⟨N, fun W hW => hN ⟨W, rfl, hW⟩⟩,
   fun ⟨N, hN⟩ => ⟨N, fun _ ⟨W, hWc, hW⟩ => hWc ▸ hN W hW⟩⟩

/-- A finite set N-shattered by a class of finite Natarajan dimension has at most
`natarajanDim C` points. -/
theorem NatarajanShatters.card_le_natarajanDim {C : ConceptClass α β}
    (hC : HasFiniteNatarajanDim C) {W : Finset α} (hW : NatarajanShatters C ↑W) :
    W.card ≤ natarajanDim C :=
  le_csSup hC ⟨W, rfl, hW⟩

/-- Every class on a finite domain has finite Natarajan dimension. -/
theorem hasFiniteNatarajanDim_of_finite [Finite α] (C : ConceptClass α β) :
    HasFiniteNatarajanDim C :=
  have := Fintype.ofFinite α
  hasFiniteNatarajanDim_iff.mpr ⟨Fintype.card α, fun W _ => W.card_le_univ⟩

/-- An upper bound on the N-shattered finite sets bounds the Natarajan dimension. -/
theorem natarajanDim_le {C : ConceptClass α β} {n : ℕ}
    (h : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ n) : natarajanDim C ≤ n :=
  csSup_le' fun _ ⟨W, hWc, hW⟩ => hWc ▸ h W hW

/-- A positive Natarajan dimension of a class of finite Natarajan dimension is attained: some
finite set of exactly `natarajanDim C` points is N-shattered. -/
theorem exists_natarajanShatters_card_eq {C : ConceptClass α β} (hC : HasFiniteNatarajanDim C)
    (hpos : 0 < natarajanDim C) :
    ∃ W : Finset α, W.card = natarajanDim C ∧ NatarajanShatters C ↑W := by
  have hne : {n : ℕ | ∃ W : Finset α, W.card = n ∧ NatarajanShatters C ↑W}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    simp [natarajanDim, h] at hpos
  exact Nat.sSup_mem hne hC

/-! ### Natarajan's lemma -/

/-- The bound `∑_{i ≤ d} (n choose i) (k choose 2) ^ i` of Natarajan's lemma on the number of
labelings of `n` points with `k` labels whose N-shattered sets have at most `d` points. The body
is exposed so that clients can evaluate the bound. -/
@[expose] def natarajanSum (n k d : ℕ) : ℕ :=
  ∑ i ∈ range (d + 1), n.choose i * k.choose 2 ^ i

@[simp] theorem natarajanSum_zero_left (k d : ℕ) : natarajanSum 0 k d = 1 := by
  simp only [natarajanSum]
  rw [sum_range_succ']
  simp

@[simp] theorem natarajanSum_zero_right (n k : ℕ) : natarajanSum n k 0 = 1 := by
  simp [natarajanSum]

/-- Pascal's rule for `natarajanSum`. -/
theorem natarajanSum_succ (n k d : ℕ) :
    natarajanSum (n + 1) k (d + 1) =
      natarajanSum n k (d + 1) + k.choose 2 * natarajanSum n k d := by
  simp only [natarajanSum]
  rw [sum_range_succ', sum_range_succ' (fun i => n.choose i * k.choose 2 ^ i), mul_sum]
  simp only [Nat.choose_succ_succ', Nat.choose_zero_right, pow_zero, add_mul, sum_add_distrib]
  have : ∀ i ∈ range (d + 1), n.choose i * k.choose 2 ^ (i + 1) =
      k.choose 2 * (n.choose i * k.choose 2 ^ i) := fun i _ => by ring
  rw [sum_congr rfl this]
  ring

private theorem le_one_add_choose_two (s : ℕ) : s ≤ 1 + s.choose 2 := by
  rcases s with _ | s
  · simp
  · have h : (s + 1).choose 2 = s.choose 1 + s.choose 2 := Nat.choose_succ_succ s 1
    rw [Nat.choose_one_right] at h
    omega

/-- The step `W ↦ succ '' W` of the induction: if the tails of the members of `R` N-shatter `W`,
then `R` N-shatters `Fin.succ '' W`. -/
private theorem natarajanShatters_image_succ {n : ℕ} {R : Set (Fin (n + 1) → β)}
    {W : Set (Fin n)} (hW : NatarajanShatters (Fin.tail '' R) W) :
    NatarajanShatters R (Fin.succ '' W) := by
  obtain ⟨f₀, f₁, hne, h⟩ := hW
  obtain ⟨_, ⟨f, hf, rfl⟩, -⟩ := h ∅ (Set.empty_subset W)
  refine ⟨Fin.cons (f 0) f₀, Fin.cons (f 0) f₁, ?_, fun B hB => ?_⟩
  · rintro _ ⟨i, hi, rfl⟩
    simpa only [Fin.cons_succ] using hne i hi
  · obtain ⟨_, ⟨c, hc, rfl⟩, h₀, h₁⟩ := h (Fin.succ ⁻¹' B) fun i hi => by
      obtain ⟨j, hj, hji⟩ := hB hi
      rwa [Fin.succ_inj.1 hji] at hj
    refine ⟨c, hc, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, -, rfl⟩ := hB hx
      simpa only [Fin.tail, Fin.cons_succ] using h₀ i hx
    · rintro _ ⟨⟨i, hi, rfl⟩, hx⟩
      simpa only [Fin.tail, Fin.cons_succ] using h₁ i ⟨hi, hx⟩

/-- The other step of the induction: if the tails extending with both labels `b₀ ≠ b₁` at `0`
N-shatter `W`, then `R` N-shatters `insert 0 (Fin.succ '' W)`. -/
private theorem natarajanShatters_insert_zero {n : ℕ} {R : Set (Fin (n + 1) → β)} {b₀ b₁ : β}
    (hb : b₀ ≠ b₁) {W : Set (Fin n)}
    (hW : NatarajanShatters {g | Fin.cons b₀ g ∈ R ∧ Fin.cons b₁ g ∈ R} W) :
    NatarajanShatters R (insert 0 (Fin.succ '' W)) := by
  classical
  obtain ⟨f₀, f₁, hne, h⟩ := hW
  refine ⟨Fin.cons b₀ f₀, Fin.cons b₁ f₁, ?_, fun B hB => ?_⟩
  · intro x hx
    rcases hx with rfl | ⟨i, hi, rfl⟩
    · simpa only [Fin.cons_zero] using hb
    · simpa only [Fin.cons_succ] using hne i hi
  · obtain ⟨g, ⟨hg₀, hg₁⟩, h₀, h₁⟩ := h (W ∩ Fin.succ ⁻¹' B) Set.inter_subset_left
    refine ⟨Fin.cons (if (0 : Fin (n + 1)) ∈ B then b₀ else b₁) g, ?_, ?_, ?_⟩
    · split_ifs
      · exact hg₀
      · exact hg₁
    · intro x hx
      rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨i, rfl⟩
      · simp only [Fin.cons_zero, hx, ↓reduceIte]
      · have hi : i ∈ W := by
          rcases hB hx with h0 | ⟨j, hj, hji⟩
          · exact absurd h0 (Fin.succ_ne_zero i)
          · rwa [Fin.succ_inj.1 hji] at hj
        simpa only [Fin.cons_succ] using h₀ i ⟨hi, hx⟩
    · rintro x ⟨hx, hxB⟩
      rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨i, rfl⟩
      · simp only [Fin.cons_zero, hxB, ↓reduceIte]
      · have hi : i ∈ W := by
          rcases hx with h0 | ⟨j, hj, hji⟩
          · exact absurd h0 (Fin.succ_ne_zero i)
          · rwa [Fin.succ_inj.1 hji] at hj
        simpa only [Fin.cons_succ] using h₁ i ⟨hi, fun h => hxB h.2⟩

/-- **Natarajan's lemma** for finite sets of labelings of `Fin n`. -/
private theorem card_le_natarajanSum [Fintype β] :
    ∀ (n d : ℕ) (R : Finset (Fin n → β)),
      (∀ W : Finset (Fin n), NatarajanShatters (R : Set (Fin n → β)) ↑W → W.card ≤ d) →
      R.card ≤ natarajanSum n (Fintype.card β) d := by
  classical
  intro n
  induction n with
  | zero =>
    intro d R _
    rw [natarajanSum_zero_left]
    exact Finset.card_le_one.2 fun a _ b _ => Subsingleton.elim a b
  | succ n ih =>
    intro d R hR
    -- Labels at `0` with which a tail `g` extends inside `R`.
    set V : (Fin n → β) → Finset β := fun g => univ.filter fun b => Fin.cons b g ∈ R
    set R' := R.image Fin.tail
    set Rp : Finset β → Finset (Fin n → β) := fun p =>
      R'.filter fun g => p ⊆ V g
    -- Each member of `R` is determined by its tail and its label at `0`.
    have hfib : ∀ g ∈ R', (R.filter fun f => Fin.tail f = g).card = (V g).card := by
      intro g _
      refine card_nbij' (fun f => f 0) (fun b => Fin.cons b g) ?_ ?_ ?_ ?_
      · intro f hf
        simp only [mem_coe, mem_filter] at hf
        simp only [mem_coe, mem_filter, mem_univ, true_and, V]
        rw [← hf.2, Fin.cons_self_tail]
        exact hf.1
      · intro b hb
        simp only [mem_coe, mem_filter, mem_univ, true_and, V] at hb
        simp only [mem_coe, mem_filter, Fin.tail_cons, and_true]
        exact hb
      · intro f hf
        simp only [mem_coe, mem_filter] at hf
        dsimp only
        rw [← hf.2, Fin.cons_self_tail]
      · intro b _
        simp only [Fin.cons_zero]
    have hcount : R.card ≤ R'.card + ∑ p ∈ univ.powersetCard 2, (Rp p).card := by
      calc R.card = ∑ g ∈ R', (R.filter fun f => Fin.tail f = g).card :=
            card_eq_sum_card_fiberwise fun f hf => mem_image_of_mem _ hf
        _ = ∑ g ∈ R', (V g).card := sum_congr rfl hfib
        _ ≤ ∑ g ∈ R', (1 + (V g).card.choose 2) :=
            sum_le_sum fun g _ => le_one_add_choose_two _
        _ = R'.card + ∑ g ∈ R',
              (((univ : Finset β).powersetCard 2).filter fun p => p ⊆ V g).card := by
            rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one]
            congr 1
            refine sum_congr rfl fun g _ => ?_
            rw [← card_powersetCard]
            congr 1
            ext p
            simp only [mem_powersetCard, mem_filter, subset_univ, true_and]
            tauto
        _ = R'.card + ∑ p ∈ univ.powersetCard 2, (Rp p).card := by
            congr 1
            simp only [card_filter, Rp]
            exact sum_comm
    -- The tails N-shatter only sets of at most `d` points.
    have hR' : ∀ W : Finset (Fin n), NatarajanShatters (R' : Set (Fin n → β)) ↑W →
        W.card ≤ d := by
      intro W hW
      rw [coe_image] at hW
      have := hR (W.map (Fin.succEmb n)) (by
        rw [coe_map]
        exact natarajanShatters_image_succ hW)
      rwa [card_map] at this
    -- The tails extending with both labels of a pair N-shatter only sets of at most `d - 1`
    -- points.
    have hRp : ∀ p ∈ (univ : Finset β).powersetCard 2, ∀ W : Finset (Fin n),
        NatarajanShatters (Rp p : Set (Fin n → β)) ↑W → W.card + 1 ≤ d := by
      intro p hp W hW
      obtain ⟨b₀, b₁, hb, rfl⟩ := card_eq_two.1 (mem_powersetCard.1 hp).2
      have hW' : NatarajanShatters {g | Fin.cons b₀ g ∈ R ∧ Fin.cons b₁ g ∈ R} ↑W := by
        refine hW.superset fun g hg => ?_
        simp only [coe_filter, Set.mem_ofPred_eq, insert_subset_iff, singleton_subset_iff,
          mem_filter, mem_univ, true_and, Rp, V] at hg
        exact hg.2
      have h0 : (0 : Fin (n + 1)) ∉ W.map (Fin.succEmb n) := by
        simp only [mem_map, Fin.coe_succEmb, not_exists, not_and]
        exact fun i _ => Fin.succ_ne_zero i
      have := hR (insert 0 (W.map (Fin.succEmb n))) (by
        rw [coe_insert, coe_map]
        exact natarajanShatters_insert_zero hb hW')
      rwa [card_insert_of_notMem h0, card_map] at this
    rcases d with _ | d
    · -- With `d = 0` no pair of labels extends a common tail.
      have hzero : ∀ p ∈ (univ : Finset β).powersetCard 2, (Rp p).card = 0 := by
        intro p hp
        rw [card_eq_zero, ← not_nonempty_iff_eq_empty]
        intro hne
        have := hRp p hp ∅ (by
          rw [coe_empty]
          exact natarajanShatters_empty (hne.coe_sort.elim fun g => ⟨g, g.2⟩))
        simp at this
      rw [sum_congr rfl hzero, sum_const_zero, add_zero] at hcount
      have hR'1 : R'.card ≤ natarajanSum n (Fintype.card β) 0 := ih 0 R' hR'
      rw [natarajanSum_zero_right] at hR'1 ⊢
      omega
    · have hle : ∀ p ∈ (univ : Finset β).powersetCard 2,
          (Rp p).card ≤ natarajanSum n (Fintype.card β) d :=
        fun p hp => ih d (Rp p) fun W hW => by have := hRp p hp W hW; omega
      calc R.card ≤ R'.card + ∑ p ∈ univ.powersetCard 2, (Rp p).card := hcount
        _ ≤ natarajanSum n (Fintype.card β) (d + 1) +
            ∑ _p ∈ (univ : Finset β).powersetCard 2, natarajanSum n (Fintype.card β) d :=
          add_le_add (ih (d + 1) R' hR') (sum_le_sum hle)
        _ = natarajanSum (n + 1) (Fintype.card β) (d + 1) := by
          rw [sum_const, card_powersetCard, card_univ, smul_eq_mul, natarajanSum_succ]

/-- **Natarajan's lemma** [ShalevShwartzBenDavid2014, Lemma 29.4 and Exercise 29.3]: a set of
labelings of `n` points with `k` labels whose N-shattered finite sets have at most `d` points has
at most `∑_{i ≤ d} (n choose i) (k choose 2) ^ i` elements. -/
theorem ncard_le_natarajanSum [Fintype β] {n d : ℕ} {R : Set (Fin n → β)}
    (hR : ∀ W : Finset (Fin n), NatarajanShatters R ↑W → W.card ≤ d) :
    R.ncard ≤ natarajanSum n (Fintype.card β) d := by
  classical
  have hfin : R.Finite := Set.toFinite R
  rw [Set.ncard_eq_toFinset_card R hfin]
  exact card_le_natarajanSum n d hfin.toFinset fun W hW => hR W (by rwa [hfin.coe_toFinset] at hW)

/-- **Natarajan's lemma** for the labelings `i ↦ c (x i)` that a class realizes on sample points
`x : Fin n → α`: if `C` N-shatters no finite set of more than `d` points, there are at most
`∑_{i ≤ d} (n choose i) (k choose 2) ^ i` of them. Repeated sample points are allowed. -/
theorem ncard_restriction_le_natarajanSum [Fintype β] {C : ConceptClass α β} {d : ℕ}
    (hC : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ d) {n : ℕ} (x : Fin n → α) :
    ((· ∘ x) '' C).ncard ≤ natarajanSum n (Fintype.card β) d := by
  classical
  refine ncard_le_natarajanSum fun W hW => ?_
  obtain ⟨hinj, hsh⟩ := hW.of_restrict
  have := hC (W.image x) (by rwa [coe_image])
  rwa [card_image_of_injOn hinj] at this

/-- `k choose 2 ≤ k ^ 2 / 2`, in the form `2 (k choose 2) ≤ k ^ 2`. -/
private theorem two_mul_choose_two_le (k : ℕ) : 2 * k.choose 2 ≤ k ^ 2 := by
  rw [Nat.choose_two_right, sq]
  exact (Nat.mul_div_le _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

/-- The polynomial form of Natarajan's lemma: with at least one label,
`∑_{i ≤ d} (n choose i) (k choose 2) ^ i` is at most `(n + 1) ^ d k ^ (2 d)`. -/
theorem natarajanSum_le (n d : ℕ) {k : ℕ} (hk : 0 < k) :
    natarajanSum n k d ≤ (n + 1) ^ d * k ^ (2 * d) := by
  have hK : k.choose 2 ≤ k ^ 2 := by have := two_mul_choose_two_le k; omega
  calc natarajanSum n k d ≤ ∑ i ∈ range (d + 1), n.choose i * (k ^ 2) ^ d := by
        refine sum_le_sum fun i hi => Nat.mul_le_mul_left _ ?_
        calc k.choose 2 ^ i ≤ (k ^ 2) ^ i := Nat.pow_le_pow_left hK i
          _ ≤ (k ^ 2) ^ d :=
            Nat.pow_le_pow_right (by positivity) (Nat.lt_succ_iff.1 (mem_range.1 hi))
    _ = (∑ i ∈ range (d + 1), n.choose i) * (k ^ 2) ^ d := (sum_mul _ _ _).symm
    _ ≤ (n + 1) ^ d * (k ^ 2) ^ d := Nat.mul_le_mul_right _ (sum_range_choose_le_add_one_pow n d)
    _ = (n + 1) ^ d * k ^ (2 * d) := by rw [← pow_mul]

/-- **Natarajan's lemma** in the form of [ShalevShwartzBenDavid2014, Lemma 29.4]: a class on a
finite domain `α` with `k` labels has at most `|α| ^ Ndim(C) k ^ (2 Ndim(C))` members. -/
theorem ncard_le_card_pow_natarajanDim [Fintype α] [Fintype β] (C : ConceptClass α β) :
    C.ncard ≤ Fintype.card α ^ natarajanDim C * Fintype.card β ^ (2 * natarajanDim C) := by
  classical
  set e := (Fintype.equivFin α).symm
  have hC : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ natarajanDim C :=
    fun W hW => hW.card_le_natarajanDim (hasFiniteNatarajanDim_of_finite C)
  have hcard : ((· ∘ e) '' C).ncard = C.ncard :=
    Set.ncard_image_of_injective C fun f g hfg => by
      funext a
      simpa using congr_fun hfg (e.symm a)
  have hbound := ncard_restriction_le_natarajanSum hC e
  rw [hcard] at hbound
  rcases Nat.eq_zero_or_pos (natarajanDim C) with hd | hd
  · rw [hd, natarajanSum_zero_right] at hbound
    rw [hd]
    simpa using hbound
  -- A shattered set of `d ≥ 1` points forces `|α| ≥ 1` and `k ≥ 2`.
  obtain ⟨W, hWc, hW⟩ := exists_natarajanShatters_card_eq (hasFiniteNatarajanDim_of_finite C) hd
  obtain ⟨a, ha⟩ : W.Nonempty := card_pos.1 (hWc ▸ hd)
  obtain ⟨f₀, f₁, hne, -⟩ := hW
  have hα : 1 ≤ Fintype.card α := Fintype.card_pos_iff.2 ⟨a⟩
  have hk : 2 ≤ Fintype.card β := Fintype.one_lt_card_iff.2 ⟨f₀ a, f₁ a, hne a ha⟩
  refine hbound.trans ?_
  set n := Fintype.card α
  set k := Fintype.card β
  set d := natarajanDim C
  have h2K : 2 * k.choose 2 ≤ k ^ 2 := two_mul_choose_two_le k
  calc natarajanSum n k d ≤ ∑ i ∈ range (d + 1), n.choose i * k.choose 2 ^ d := by
        refine sum_le_sum fun i hi => Nat.mul_le_mul_left _ ?_
        exact Nat.pow_le_pow_right (Nat.choose_pos (by omega)) (Nat.lt_succ_iff.1 (mem_range.1 hi))
    _ = (∑ i ∈ range (d + 1), n.choose i) * k.choose 2 ^ d := (sum_mul _ _ _).symm
    _ ≤ (n + 1) ^ d * k.choose 2 ^ d := Nat.mul_le_mul_right _ (sum_range_choose_le_add_one_pow n d)
    _ ≤ (2 * n) ^ d * k.choose 2 ^ d := by gcongr; omega
    _ = n ^ d * (2 * k.choose 2) ^ d := by ring
    _ ≤ n ^ d * (k ^ 2) ^ d := by gcongr
    _ = n ^ d * k ^ (2 * d) := by rw [← pow_mul]

end Cslib.MachineLearning.PACLearning
