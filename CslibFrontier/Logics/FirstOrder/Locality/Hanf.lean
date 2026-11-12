/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.Basic
public import CslibFrontier.Logics.FirstOrder.Locality.Gaifman
import CslibFrontier.Foundations.Data.Fintype.FiberEquiv
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Hanf locality and Gaifman locality of first-order logic

Two tuples `a` in `M` and `b` in `N` are **Hanf-equivalent at radius `d`** (`HanfEquiv L d a b`,
Libkin's `(M, a) ⇆_d (N, b)`) when some bijection `f : M ≃ N` matches every point `c` with a point
`f c` so that the radius-`d` neighborhoods of `a` with `c` added and of `b` with `f c` added are
isomorphic. *Hanf's theorem*, in the form of [Libkin, Theorem 4.12][Libkin2004], says that over
finite structures this bounds first-order expressiveness: Hanf-equivalence at radius
`(3 ^ n - 1) / 2` implies that Duplicator wins the `n`-round Ehrenfeucht–Fraïssé game
(`HanfEquiv.duplicatorWins`), so the tuples satisfy the same formulas of quantifier rank at most
`n` (`HanfEquiv.realize_iff`, `realize_sentence_iff_of_nbhdIso`). *Gaifman locality*
([Libkin, Corollary 4.13][Libkin2004]) follows: in a finite structure, tuples with isomorphic
radius-`(3 ^ (n + 1) - 1) / 2` neighborhoods satisfy the same formulas of quantifier rank at most
`n` (`NbhdIso.realize_iff`).

The proof follows [Libkin, §4.2–4.3][Libkin2004]. The key step `hanfEquiv_of_nbhdIso` is
[Libkin, Lemma 4.9][Libkin2004]: if `M ⇆_d N` and `a`, `b` have isomorphic radius-`(3d + 1)`
neighborhoods, then `(M, a) ⇆_d (N, b)`. The required bijection agrees with the neighborhood
isomorphism on the radius-`(2d + 1)` ball and matches the remaining points by neighborhood type
(`exists_compl_equiv_nbhdIso`), which is possible because both bijections preserve the number of
points of each type. Corollary 4.10 (`HanfEquiv.exists_equiv`) and an induction on the number of
rounds finish the proof, with the radius recursion `hanf_radius_succ`. The exact Hanf and Gaifman
locality ranks `2 ^ (n - 1) - 1` and `2 ^ n - 1` ([Libkin, Exercises 4.10 and 4.11][Libkin2004])
are proved in `CslibFrontier.Logics.FirstOrder.Locality.Sharp`.

**Hypotheses.** Both structures are finite (the bijection forces `N` finite when `M` is). The
theorem for Hanf-equivalence also assumes `M` nonempty: two empty structures that disagree on a
nullary relation are Hanf-equivalent at every radius but disagree on a sentence of rank `0`. The
Gaifman forms need no such assumption. The game statements hold for every language; the statements
about formulas need a relational language (`L.IsRelational`), since the Gaifman graph ignores
function symbols.

## Main definitions

* `Cslib.Logic.FO.Locality.HanfEquiv`: Hanf-equivalence of tuples at a given radius.

## Main results

* `Cslib.Logic.FO.Locality.exists_compl_equiv_nbhdIso`: complement matching by singleton
  neighborhood type.
* `Cslib.Logic.FO.Locality.hanfEquiv_of_nbhdIso`: [Libkin, Lemma 4.9][Libkin2004].
* `Cslib.Logic.FO.Locality.HanfEquiv.duplicatorWins`,
  `Cslib.Logic.FO.Locality.HanfEquiv.realize_iff`,
  `Cslib.Logic.FO.Locality.realize_sentence_iff_of_nbhdIso`: Hanf locality
  ([Libkin, Theorem 4.12][Libkin2004]).
* `Cslib.Logic.FO.Locality.NbhdIso.duplicatorWins`, `Cslib.Logic.FO.Locality.NbhdIso.realize_iff`:
  Gaifman locality ([Libkin, Corollary 4.13][Libkin2004]).

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Chapter 4: Definition 4.3,
  Lemma 4.9, Corollary 4.10, Theorem 4.12 and Corollary 4.13. Libkin's §4.6 credits the first
  locality theorem to Hanf (1965, for infinite structures) and its finite version to Fagin,
  Stockmeyer and Vardi; the proof formalized here is Libkin's.
-/

public section

open FirstOrder Language Structure

namespace Cslib.Logic.FO.Locality

universe u v w w'

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- A neighborhood isomorphism makes the tuples a partial isomorphism. -/
theorem IsNbhdIso.partialIso {k r : ℕ} {a : Fin k → M} {b : Fin k → N} {h : M → N}
    (H : IsNbhdIso L r a b h) : PartialIso L a b := by
  refine ⟨fun i j => ?_, fun R f => ?_⟩
  · rw [← H.map_tuple i, ← H.map_tuple j]
    exact (H.bijOn.injOn.eq_iff (mem_ball_self a r i) (mem_ball_self a r j)).symm
  · have : b ∘ f = h ∘ (a ∘ f) := funext fun i => (H.map_tuple (f i)).symm
    rw [this, H.relMap_iff R (a ∘ f) (fun i => mem_ball_self a r (f i))]

theorem NbhdIso.partialIso {k r : ℕ} {a : Fin k → M} {b : Fin k → N} (H : NbhdIso L r a b) :
    PartialIso L a b :=
  let ⟨_, H⟩ := nbhdIso_iff.1 H; H.partialIso

/-! ### Counting points by neighborhood type -/

/-- If a bijection `e : α ≃ β` and a bijection `h` between `s` and `t` both preserve labels
`κa`, `κb`, then the complements contain equally many points of each label, so a
label-preserving bijection between them exists. -/
private theorem exists_equiv_compl {α β Q : Type*} [Finite α] {κa : α → Q} {κb : β → Q}
    (e : α ≃ β) (he : ∀ x, κb (e x) = κa x) {s : Set α} {t : Set β} {h : α → β}
    (hh : Set.BijOn h s t) (hκ : ∀ x ∈ s, κb (h x) = κa x) :
    ∃ g : (sᶜ : Set α) ≃ (tᶜ : Set β), ∀ x, κb (g x) = κa x := by
  have : Finite β := Finite.of_equiv α e
  have key : ∀ q, Nat.card {x : (sᶜ : Set α) // κa x = q} =
      Nat.card {y : (tᶜ : Set β) // κb y = q} := by
    intro q
    let A : Set α := {x | κa x = q}
    let B : Set β := {y | κb y = q}
    have hA : Nat.card {x : (sᶜ : Set α) // κa x = q} = (A \ s).ncard := by
      rw [← Nat.card_coe_set_eq]
      exact Nat.card_congr
        { toFun := fun x => ⟨x.1.1, x.2, x.1.2⟩
          invFun := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hB : Nat.card {y : (tᶜ : Set β) // κb y = q} = (B \ t).ncard := by
      rw [← Nat.card_coe_set_eq]
      exact Nat.card_congr
        { toFun := fun x => ⟨x.1.1, x.2, x.1.2⟩
          invFun := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hAB : A.ncard = B.ncard := by
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact Nat.card_congr (e.subtypeEquiv fun x => by simp [A, B, he])
    have hAsBt : (A ∩ s).ncard = (B ∩ t).ncard := by
      rw [← (hh.injOn.mono Set.inter_subset_right).ncard_image]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨hxA, hxs⟩, rfl⟩
        exact ⟨(hκ x hxs).trans hxA, hh.mapsTo hxs⟩
      · rintro ⟨hyB, hyt⟩
        obtain ⟨x, hxs, rfl⟩ := hh.surjOn hyt
        exact ⟨x, ⟨(hκ x hxs).symm.trans hyB, hxs⟩, rfl⟩
    have h1 := Set.ncard_inter_add_ncard_sdiff_eq_ncard A s
    have h2 := Set.ncard_inter_add_ncard_sdiff_eq_ncard B t
    rw [hA, hB]
    omega
  exact Equiv.exists_apply_eq_iff_card_fiber_eq.2 key

/-! ### Hanf-equivalence -/

variable (L) in
/-- `(M, a)` and `(N, b)` are Hanf-equivalent at radius `d` (Libkin's `(M, a) ⇆_d (N, b)`,
[Libkin, Definition 4.3][Libkin2004]): some bijection `f : M ≃ N` matches every point `c` with
`f c` so that the radius-`d` neighborhoods of `a` with `c` added and of `b` with `f c` added are
isomorphic. -/
def HanfEquiv {k : ℕ} (d : ℕ) (a : Fin k → M) (b : Fin k → N) : Prop :=
  ∃ f : M ≃ N, ∀ c, NbhdIso L d (Fin.snoc a c : Fin (k + 1) → M)
    (Fin.snoc b (f c) : Fin (k + 1) → N)

theorem hanfEquiv_iff {k d : ℕ} {a : Fin k → M} {b : Fin k → N} :
    HanfEquiv L d a b ↔ ∃ f : M ≃ N, ∀ c, NbhdIso L d (Fin.snoc a c : Fin (k + 1) → M)
      (Fin.snoc b (f c) : Fin (k + 1) → N) := Iff.rfl

theorem HanfEquiv.refl (d : ℕ) {k : ℕ} (a : Fin k → M) : HanfEquiv L d a a :=
  ⟨Equiv.refl M, fun _ => NbhdIso.refl _ _⟩

theorem HanfEquiv.mono {k d r : ℕ} {a : Fin k → M} {b : Fin k → N} (H : HanfEquiv L r a b)
    (hdr : d ≤ r) : HanfEquiv L d a b :=
  let ⟨f, hf⟩ := H; ⟨f, fun c => (hf c).mono hdr⟩

/-- For structures (with no tuple), Hanf-equivalence is Libkin's `M ⇆_d N`: a bijection matching
points with isomorphic radius-`d` neighborhoods. -/
theorem hanfEquiv_zero_iff {d : ℕ} {a : Fin 0 → M} {b : Fin 0 → N} :
    HanfEquiv L d a b ↔
      ∃ f : M ≃ N, ∀ c, NbhdIso L d (fun _ : Fin 1 => c) (fun _ : Fin 1 => f c) := by
  simp only [hanfEquiv_iff, Fin.snoc_zero]

/-- Hanf-equivalent tuples in a nonempty structure have isomorphic neighborhoods
([Libkin, Lemma 4.4][Libkin2004], third item). Nonemptiness is needed: two empty structures that
disagree on a nullary relation are Hanf-equivalent at every radius, but their neighborhoods of the
empty tuple are not isomorphic. -/
theorem HanfEquiv.nbhdIso [Nonempty M] {k d : ℕ} {a : Fin k → M} {b : Fin k → N}
    (H : HanfEquiv L d a b) : NbhdIso L d a b := by
  obtain ⟨f, hf⟩ := H
  obtain ⟨h, Hh⟩ := nbhdIso_iff.1 (hf (Classical.arbitrary M))
  have := Hh.restrict (x := a) (l := 0) (d := d)
    (fun i => mem_ball_snoc.2 (.inl (mem_ball_self a 0 i))) (by omega)
  have hb : h ∘ a = b := funext fun i => by simpa using Hh.map_tuple i.castSucc
  exact (hb ▸ this).nbhdIso

private theorem snoc_mem {k : ℕ} {S : Set M} {x : Fin k → M} {c : M} (hx : ∀ i, x i ∈ S)
    (hc : c ∈ S) (j : Fin (k + 1)) : (Fin.snoc x c : Fin (k + 1) → M) j ∈ S := by
  induction j using Fin.lastCases with
  | last => simpa using hc
  | cast i => simpa using hx i

/-- Points with isomorphic radius-`d` neighborhoods. -/
private def ptSetoid [Nonempty M] (d : ℕ) : Setoid M where
  r x y := NbhdIso L d (fun _ : Fin 1 => x) (fun _ : Fin 1 => y)
  iseqv := ⟨fun _ => NbhdIso.refl _ _, fun h => h.symm, fun h h' => h.trans h'⟩

/-- If `e : M ≃ N` and a bijection `h` between `s : Set M` and `t : Set N` both match points with
isomorphic radius-`d` neighborhoods, then so does some bijection between the complements `sᶜ` and
`tᶜ`. -/
theorem exists_compl_equiv_nbhdIso [Finite M] {d : ℕ} (e : M ≃ N)
    (he : ∀ c, NbhdIso L d (fun _ : Fin 1 => c) (fun _ : Fin 1 => e c))
    {s : Set M} {t : Set N} {h : M → N} (hh : Set.BijOn h s t)
    (hs : ∀ x ∈ s, NbhdIso L d (fun _ : Fin 1 => x) (fun _ : Fin 1 => h x)) :
    ∃ g : (sᶜ : Set M) ≃ (tᶜ : Set N),
      ∀ x : (sᶜ : Set M), NbhdIso L d (fun _ : Fin 1 => (x : M)) (fun _ : Fin 1 => (g x : N)) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · have : IsEmpty N := e.symm.isEmpty
    exact ⟨Equiv.equivOfIsEmpty _ _, fun x => isEmptyElim (x : M)⟩
  · let κa : M → Quotient (ptSetoid (L := L) (M := M) d) := Quotient.mk _
    let κb : N → Quotient (ptSetoid (L := L) (M := M) d) := fun y => Quotient.mk _ (e.symm y)
    have hbe : ∀ x, κb (e x) = κa x := fun x => by simp [κa, κb]
    have hκ : ∀ x ∈ s, κb (h x) = κa x := fun x hx =>
      Quotient.sound ((he (e.symm (h x))).trans (by simpa using (hs x hx).symm))
    obtain ⟨g, hg⟩ := exists_equiv_compl e hbe hh hκ
    exact ⟨g, fun x => (Quotient.exact (hg x)).symm.trans (by simpa using he (e.symm (g x)))⟩

/-- [Libkin, Lemma 4.9][Libkin2004]: if a bijection `e : M ≃ N` matches points with isomorphic
radius-`d` neighborhoods (`M ⇆_d N`) and `a`, `b` have isomorphic radius-`(3d + 1)`
neighborhoods, then `(M, a) ⇆_d (N, b)`. -/
theorem hanfEquiv_of_nbhdIso [Finite M] {k d : ℕ} {a : Fin k → M} {b : Fin k → N}
    (e : M ≃ N) (he : ∀ c, NbhdIso L d (fun _ : Fin 1 => c) (fun _ : Fin 1 => e c))
    (hab : NbhdIso L (3 * d + 1) a b) : HanfEquiv L d a b := by
  obtain ⟨h, Hh⟩ := nbhdIso_iff.1 hab
  set S := ball L a (2 * d + 1)
  have HS : IsNbhdIso L (2 * d + 1) a b h := Hh.mono (by omega)
  -- a point near `a` and its image under `h` have isomorphic radius-`d` neighborhoods
  have hpt : ∀ x ∈ S, NbhdIso L d (fun _ : Fin 1 => x) (fun _ : Fin 1 => h x) := fun x hx =>
    (Hh.restrict (x := fun _ : Fin 1 => x) (l := 2 * d + 1) (fun _ => hx) (by omega)).nbhdIso
  obtain ⟨g, hg⟩ := exists_compl_equiv_nbhdIso e he HS.bijOn hpt
  classical
  let F : M ≃ N :=
    ((Equiv.Set.sumCompl S).symm.trans (Equiv.sumCongr (HS.bijOn.equiv h) g)).trans
      (Equiv.Set.sumCompl (ball L b (2 * d + 1)))
  have hFS : ∀ x ∈ S, F x = h x := fun x hx => by
    simp [F, Equiv.Set.sumCompl_symm_apply_of_mem hx, Set.BijOn.equiv]
  have hFS' : ∀ x (hx : x ∉ S), F x = g ⟨x, hx⟩ := fun x hx => by
    simp [F, Equiv.Set.sumCompl_symm_apply_of_notMem hx]
  refine ⟨F, fun c => ?_⟩
  by_cases hc : c ∈ S
  · -- near `a`, use `h` itself
    rw [hFS c hc]
    have := Hh.restrict (x := (Fin.snoc a c : Fin (k + 1) → M)) (l := 2 * d + 1) (d := d)
      (snoc_mem (fun j => ball_mono (by omega) (mem_ball_self a 0 j)) hc) (by omega)
    rw [Fin.comp_snoc, show h ∘ a = b from funext Hh.map_tuple] at this
    exact this.nbhdIso
  · -- far from `a`, combine the neighborhood of `a` with that of `c`
    rw [hFS' c hc]
    obtain ⟨h₂, H₂⟩ := nbhdIso_iff.1 (hg ⟨c, hc⟩)
    refine (Hh.mono (by omega)).snoc H₂ (fun i => ?_) (fun i => ?_)
    · exact lt_of_not_ge fun h' => hc (mem_ball.2 ⟨i, h'⟩)
    · exact lt_of_not_ge fun h' => (g ⟨c, hc⟩).2 (mem_ball.2 ⟨i, h'⟩)

/-- [Libkin, Corollary 4.10][Libkin2004]: if `(M, a) ⇆_{3d+1} (N, b)`, then some bijection
`f : M ≃ N` gives `(M, a c) ⇆_d (N, b (f c))` for every `c`. -/
theorem HanfEquiv.exists_equiv [Finite M] {k d : ℕ} {a : Fin k → M} {b : Fin k → N}
    (H : HanfEquiv L (3 * d + 1) a b) :
    ∃ f : M ≃ N, ∀ c, HanfEquiv L d (Fin.snoc a c : Fin (k + 1) → M)
      (Fin.snoc b (f c) : Fin (k + 1) → N) := by
  obtain ⟨f, hf⟩ := H
  refine ⟨f, fun c => hanfEquiv_of_nbhdIso f (fun c' => ?_) (hf c)⟩
  obtain ⟨h, Hh⟩ := nbhdIso_iff.1 (hf c')
  have := Hh.restrict (x := fun _ : Fin 1 => c') (l := 0) (d := d)
    (fun _ => mem_ball_snoc.2 (.inr (mem_ball_self _ 0 0))) (by omega)
  have hc : h c' = f c' := by simpa using Hh.map_tuple (Fin.last k)
  exact (by simpa [Function.comp_def, hc] using this : IsNbhdIso L d _ _ h).nbhdIso

/-- The radius recursion: `(3 ^ (n + 1) - 1) / 2 = 3 * ((3 ^ n - 1) / 2) + 1`. -/
theorem hanf_radius_succ (n : ℕ) : (3 ^ (n + 1) - 1) / 2 = 3 * ((3 ^ n - 1) / 2) + 1 := by
  obtain ⟨m, hm⟩ : Odd (3 ^ n) := Odd.pow (by decide)
  rw [pow_succ, hm]
  omega

/-! ### Hanf locality -/

/-- **Hanf locality** ([Libkin, Theorem 4.12][Libkin2004]): over a finite nonempty structure,
tuples that are Hanf-equivalent at radius `(3 ^ n - 1) / 2` are `n`-round
Ehrenfeucht–Fraïssé-equivalent. The language is arbitrary. -/
theorem HanfEquiv.duplicatorWins [Finite M] [Nonempty M] :
    ∀ {n k : ℕ} {a : Fin k → M} {b : Fin k → N}, HanfEquiv L ((3 ^ n - 1) / 2) a b →
      DuplicatorWins L n a b
  | 0, _, _, _, H => duplicatorWins_zero.2 H.nbhdIso.partialIso
  | n + 1, _, _, _, H => by
    have hP := H.nbhdIso.partialIso
    rw [hanf_radius_succ] at H
    obtain ⟨f, hf⟩ := H.exists_equiv
    exact duplicatorWins_succ.2 ⟨hP, fun c => ⟨f c, (hf c).duplicatorWins⟩,
      fun c' => ⟨f.symm c', by simpa using (hf (f.symm c')).duplicatorWins⟩⟩

/-- **Hanf locality for formulas** ([Libkin, Theorem 4.12][Libkin2004]): over a finite nonempty
structure and a relational language, tuples that are Hanf-equivalent at radius `(3 ^ n - 1) / 2`
satisfy the same formulas of quantifier rank at most `n`. -/
theorem HanfEquiv.realize_iff [L.IsRelational] [Finite M] [Nonempty M] {n k : ℕ}
    {a : Fin k → M} {b : Fin k → N} (h : HanfEquiv L ((3 ^ n - 1) / 2) a b)
    {φ : L.BoundedFormula Empty k} (hφ : quantifierRank φ ≤ n) :
    φ.Realize default a ↔ φ.Realize default b :=
  h.duplicatorWins.realize_iff hφ

/-- **Hanf locality for sentences** ([Libkin, Theorem 4.12][Libkin2004], Boolean queries): if a
bijection between a finite nonempty structure `M` and `N` matches points with isomorphic
radius-`(3 ^ n - 1) / 2` neighborhoods, then `M` and `N` satisfy the same sentences of quantifier
rank at most `n`. -/
theorem realize_sentence_iff_of_nbhdIso [L.IsRelational] [Finite M] [Nonempty M] {n : ℕ}
    (e : M ≃ N)
    (he : ∀ c, NbhdIso L ((3 ^ n - 1) / 2) (fun _ : Fin 1 => c) (fun _ : Fin 1 => e c))
    {φ : L.Sentence} (hφ : quantifierRank φ ≤ n) : M ⊨ φ ↔ N ⊨ φ :=
  (hanfEquiv_zero_iff.2 ⟨e, he⟩ : HanfEquiv L _ (default : Fin 0 → M)
    (default : Fin 0 → N)).realize_iff hφ

/-! ### Gaifman locality -/

/-- Over empty structures, a partial isomorphism wins every game: Spoiler has no move. -/
theorem duplicatorWins_of_isEmpty [IsEmpty M] (e : M ≃ N) :
    ∀ {n k : ℕ} {a : Fin k → M} {b : Fin k → N}, PartialIso L a b → DuplicatorWins L n a b
  | 0, _, _, _, h => duplicatorWins_zero.2 h
  | _ + 1, _, _, _, h => duplicatorWins_succ.2
      ⟨h, fun c => isEmptyElim c, fun d => isEmptyElim (e.symm d)⟩

/-- **Gaifman locality, two-structure form** ([Libkin, Lemma 4.9 and Theorem 4.12][Libkin2004]):
if a bijection `e : M ≃ N` from a finite structure matches points with isomorphic
radius-`(3 ^ n - 1) / 2` neighborhoods, then tuples with isomorphic radius-`(3 ^ (n + 1) - 1) / 2`
neighborhoods are `n`-round Ehrenfeucht–Fraïssé-equivalent. -/
theorem NbhdIso.duplicatorWins [Finite M] {n k : ℕ} {a : Fin k → M} {b : Fin k → N} (e : M ≃ N)
    (he : ∀ c, NbhdIso L ((3 ^ n - 1) / 2) (fun _ : Fin 1 => c) (fun _ : Fin 1 => e c))
    (hab : NbhdIso L ((3 ^ (n + 1) - 1) / 2) a b) : DuplicatorWins L n a b := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact duplicatorWins_of_isEmpty e hab.partialIso
  · rw [hanf_radius_succ] at hab
    exact (hanfEquiv_of_nbhdIso e he hab).duplicatorWins

/-- **Gaifman locality** ([Libkin, Corollary 4.13][Libkin2004]): in a finite structure over a
relational language, tuples with isomorphic radius-`(3 ^ (n + 1) - 1) / 2` neighborhoods satisfy
the same formulas of quantifier rank at most `n`. -/
theorem NbhdIso.realize_iff [L.IsRelational] [Finite M] {n k : ℕ} {a₁ a₂ : Fin k → M}
    (h : NbhdIso L ((3 ^ (n + 1) - 1) / 2) a₁ a₂) {φ : L.BoundedFormula Empty k}
    (hφ : quantifierRank φ ≤ n) : φ.Realize default a₁ ↔ φ.Realize default a₂ :=
  (h.duplicatorWins (Equiv.refl M) fun _ => NbhdIso.refl _ _).realize_iff hφ

/-- **Gaifman locality for formulas with free variables** ([Libkin, Corollary 4.13][Libkin2004]):
the form of `NbhdIso.realize_iff` for `φ : L.Formula (Fin k)`, the free variables naming the
tuple. -/
theorem NbhdIso.formula_realize_iff [L.IsRelational] [Finite M] {n k : ℕ} {a₁ a₂ : Fin k → M}
    (h : NbhdIso L ((3 ^ (n + 1) - 1) / 2) a₁ a₂) {φ : L.Formula (Fin k)}
    (hφ : quantifierRank φ ≤ n) : φ.Realize a₁ ↔ φ.Realize a₂ :=
  (h.duplicatorWins (Equiv.refl M) fun _ => NbhdIso.refl _ _).formula_realize_iff hφ

end Cslib.Logic.FO.Locality
