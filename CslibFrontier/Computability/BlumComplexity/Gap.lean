/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.BlumComplexity.Basic
import Mathlib.Data.Finset.Card

/-!
# Borodin's gap theorem

For every Blum complexity measure `Φ` and every computable `g` with `g n ≥ n`, there is a
computable bound `t` such that stretching it to `g ∘ t` adds no function to the complexity class:
`C_{g ∘ t} = C_t` [Borodin, *Computational complexity and the existence of complexity
gaps*][Borodin1972]. Taking `g n = 2 ^ n`, for instance, exponentially more resources compute
exactly the same functions beyond `t`. Hence complexity classes for arbitrary computable bounds
need not form a hierarchy. Hierarchy theorems need constructible bounds. The stretch may also
depend on the input: for every computable `g` with `g n y ≥ y`, some computable `t` has
`C_{n ↦ g n (t n)} = C_t` (`gap_theorem₂`).

The proof constructs `t n` by searching for a `k` such that no program numbered at most `n` has
cost on input `n` in the interval `(k, g n k]`. Iterating `k ↦ max k (g n k)` gives `n + 2`
disjoint intervals, and each of the `n + 1` programs has its cost in at most one of them, so the
search terminates. Blum's second axiom makes each test decidable. Each program `c` is accounted
for at every input `n ≥ encode c`, which gives the pointwise statement `exists_gap₂`: for those
inputs, `Φ c n ≤ t n` or `Φ c n > g n (t n)`.

## Conventions and strength

`complexityClass t` uses Borodin's almost-everywhere convention: `f ∈ C_t` when some program for
`f` has cost at most `t n` for all sufficiently large `n` (see
`CslibFrontier.Computability.BlumComplexity.Basic`). `exists_gap₂` gives an explicit threshold for
each program, namely `n ≥ encode c`. So the class equality holds for this almost-everywhere class,
as in the source. All statements also allow a computable lower bound `a`: the gap function `t` can
be chosen strictly increasing with `t ≥ a`, so gaps occur above every computable function.
Dropping these extra conclusions leaves the statement `C_{g ∘ t} = C_t` for a computable `t`. The
one-argument forms `exists_gap` and `gap_theorem` are the special case where `g n y` does not
depend on `n`.

## Main results

* `Cslib.BlumComplexity.BlumMeasure.exists_gap₂`, `Cslib.BlumComplexity.BlumMeasure.exists_gap`:
  the pointwise gap property of `t`, for a two-argument and a one-argument stretch.
* `Cslib.BlumComplexity.BlumMeasure.gap_theorem₂`: **Borodin's gap theorem** with a two-argument
  stretch, `C_{n ↦ g n (t n)} = C_t`.
* `Cslib.BlumComplexity.BlumMeasure.gap_theorem`: **Borodin's gap theorem**, `C_{g ∘ t} = C_t`.

## References

* [A. Borodin, *Computational complexity and the existence of complexity gaps*][Borodin1972]
-/

public section

namespace Cslib.BlumComplexity.BlumMeasure

open Encodable Denumerable Nat.Partrec Filter

/-- No program numbered at most `n` has cost on `n` in the interval `(k, g n k]`. -/
private def NoCostIn (Φ : BlumMeasure) (g : ℕ → ℕ → ℕ) (n k : ℕ) : Prop :=
  ∀ i < n + 1, ∀ m < g n k + 1, k < m → m ∉ Φ.cost (ofNat Code i) n

/-- Borodin's pigeonhole step: above every `L` there is a `k` such that no program numbered at
most `n` has cost on `n` in `(k, g n k]`. Iterating `k ↦ max k (g n k)` from `L` gives `n + 2`
disjoint intervals, and each of the `n + 1` programs has its cost in at most one of them. -/
private theorem exists_noCostIn (Φ : BlumMeasure) (g : ℕ → ℕ → ℕ) (n L : ℕ) :
    ∃ k, L ≤ k ∧ NoCostIn Φ g n k := by
  let s : ℕ → ℕ := fun j => (fun k => max k (g n k))^[j] L
  have hs_succ : ∀ j, s (j + 1) = max (s j) (g n (s j)) := fun j =>
    Function.iterate_succ_apply' _ _ _
  have hs_mono : Monotone s :=
    monotone_nat_of_le_succ fun j => (hs_succ j).symm ▸ le_max_left _ _
  by_contra hne
  have hw : ∀ j, ∃ i < n + 1, ∃ m < g n (s j) + 1, s j < m ∧ m ∈ Φ.cost (ofNat Code i) n := by
    intro j
    by_contra hj
    refine hne ⟨s j, hs_mono (Nat.zero_le j), fun i hi m hm hlt hmem => hj ?_⟩
    exact ⟨i, hi, m, hm, hlt, hmem⟩
  choose idx hidx m hm hlt hmem using hw
  -- Two intervals cannot hold the cost of the same program.
  have key : ∀ j j', j < j' → idx j = idx j' → False := by
    intro j j' hjj' he
    have h1 := hmem j
    rw [he] at h1
    have heq := Part.mem_unique h1 (hmem j')
    have h2 : g n (s j) ≤ s j' :=
      (le_max_right _ _).trans ((hs_succ j).symm ▸ hs_mono (Nat.succ_le_of_lt hjj'))
    have := hm j
    have := hlt j'
    omega
  obtain ⟨j, -, j', -, hne', heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (n + 2)) (t := Finset.range (n + 1)) (f := idx) (by simp)
    (fun j _ => Finset.mem_coe.2 (Finset.mem_range.2 (hidx j)))
  rcases lt_or_gt_of_ne hne' with h | h
  · exact key j j' h heq
  · exact key j' j h heq.symm

private theorem computablePred_noCostIn (Φ : BlumMeasure) {g : ℕ → ℕ → ℕ} (hg : Computable₂ g) :
    ComputablePred fun x : (ℕ × ℕ) × ℕ => x.1.2 ≤ x.2 ∧ NoCostIn Φ g x.1.1 x.2 := by
  refine (ComputablePred.nat_le (Computable.snd.comp Computable.fst) Computable.snd).and ?_
  refine ComputablePred.forall_lt
    (p := fun (x : (ℕ × ℕ) × ℕ) i =>
      ∀ m < g x.1.1 x.2 + 1, x.2 < m → m ∉ Φ.cost (ofNat Code i) x.1.1)
    ?_ (Computable.succ.comp (Computable.fst.comp Computable.fst))
  refine ComputablePred.forall_lt
    (p := fun (y : ((ℕ × ℕ) × ℕ) × ℕ) m => y.1.2 < m → m ∉ Φ.cost (ofNat Code y.2) y.1.1.1)
    ?_ (Computable.succ.comp (hg.comp (Computable.fst.comp (Computable.fst.comp
      Computable.fst)) (Computable.snd.comp Computable.fst)))
  exact (ComputablePred.nat_lt (Computable.snd.comp (Computable.fst.comp Computable.fst))
    Computable.snd).imp (Φ.computablePred_mem_cost_comp
      ((Computable.ofNat Code).comp (Computable.snd.comp Computable.fst))
      (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)))
      Computable.snd).not

variable (Φ : BlumMeasure)

/-- **Pointwise gap** [Borodin1972], with a two-argument stretch. For every computable `g` and
every computable lower bound `a`, there is a computable, strictly increasing `t ≥ a` such that, for
every program `c` and every input `n ≥ encode c`, the cost `Φ c n`, if defined, is at most `t n`
or greater than `g n (t n)`. -/
theorem exists_gap₂ {g : ℕ → ℕ → ℕ} {a : ℕ → ℕ} (hg : Computable₂ g) (ha : Computable a) :
    ∃ t : ℕ → ℕ, Computable t ∧ StrictMono t ∧ (∀ n, a n ≤ t n) ∧
      ∀ c : Code, ∀ n, encode c ≤ n → ∀ m ∈ Φ.cost c n, m ≤ t n ∨ g n (t n) < m := by
  classical
  have hex : ∀ x : ℕ × ℕ, ∃ k, x.2 ≤ k ∧ NoCostIn Φ g x.1 k := fun x =>
    Φ.exists_noCostIn g x.1 x.2
  -- `F (n, L)` is the least `k ≥ L` such that no program numbered `≤ n` has cost on `n` in
  -- `(k, g n k]`.
  let F : ℕ × ℕ → ℕ := fun x => Nat.find (hex x)
  have hF : Computable F :=
    Computable.find (P := fun (x : ℕ × ℕ) k => x.2 ≤ k ∧ NoCostIn Φ g x.1 k)
      (Φ.computablePred_noCostIn hg) hex
  have hspec : ∀ x, x.2 ≤ F x ∧ NoCostIn Φ g x.1 (F x) := fun x => Nat.find_spec (hex x)
  -- `t 0 = F (0, a 0)` and `t (n + 1) = F (n + 1, max (a (n + 1)) (t n + 1))`.
  let t : ℕ → ℕ := fun n => Nat.rec (motive := fun _ => ℕ) (F (0, a 0))
    (fun i ti => F (i + 1, max (a (i + 1)) (ti + 1))) n
  have ht : Computable t :=
    Computable.nat_rec (f := id) (g := fun _ => F (0, a 0))
      (h := fun _ p => F (p.1 + 1, max (a (p.1 + 1)) (p.2 + 1))) Computable.id
      (hF.comp (Computable.pair (Computable.const 0) (Computable.const (a 0))))
      (hF.comp (Computable.pair (Computable.succ.comp (Computable.fst.comp Computable.snd))
        (Primrec.nat_max.to_comp.comp
          (ha.comp (Computable.succ.comp (Computable.fst.comp Computable.snd)))
          (Computable.succ.comp (Computable.snd.comp Computable.snd))))).to₂
  have hstep : ∀ n, max (a (n + 1)) (t n + 1) ≤ t (n + 1) := fun n =>
    (hspec (n + 1, max (a (n + 1)) (t n + 1))).1
  have hgap : ∀ n, NoCostIn Φ g n (t n) := by
    intro n
    cases n with
    | zero => exact (hspec (0, a 0)).2
    | succ n => exact (hspec (n + 1, max (a (n + 1)) (t n + 1))).2
  refine ⟨t, ht, strictMono_nat_of_lt_succ fun n => ?_, fun n => ?_, ?_⟩
  · have := hstep n
    omega
  · cases n with
    | zero => exact (hspec (0, a 0)).1
    | succ n =>
      have := hstep n
      omega
  · intro c n hc m hm
    by_contra hcon
    push Not at hcon
    have := hgap n (encode c) (Nat.lt_succ_of_le hc) m (Nat.lt_succ_of_le hcon.2) hcon.1
    rw [ofNat_encode] at this
    exact this hm

/-- **Pointwise gap** [Borodin1972]. For every computable `g` and every computable lower bound
`a`, there is a computable, strictly increasing `t ≥ a` such that, for every program `c` and
every input `n ≥ encode c`, the cost `Φ c n`, if defined, is at most `t n` or greater than
`g (t n)`. -/
theorem exists_gap {g a : ℕ → ℕ} (hg : Computable g) (ha : Computable a) :
    ∃ t : ℕ → ℕ, Computable t ∧ StrictMono t ∧ (∀ n, a n ≤ t n) ∧
      ∀ c : Code, ∀ n, encode c ≤ n → ∀ m ∈ Φ.cost c n, m ≤ t n ∨ g (t n) < m :=
  Φ.exists_gap₂ (g := fun _ k => g k) (hg.comp Computable.snd).to₂ ha

/-- **Borodin's gap theorem** [Borodin1972], with a two-argument stretch. For every computable `g`
with `g n y ≥ y` and every computable lower bound `a`, there is a computable, strictly increasing
`t ≥ a` with `C_{n ↦ g n (t n)} = C_t`. -/
theorem gap_theorem₂ {g : ℕ → ℕ → ℕ} {a : ℕ → ℕ} (hg : Computable₂ g)
    (hgn : ∀ n y, y ≤ g n y) (ha : Computable a) :
    ∃ t : ℕ → ℕ, Computable t ∧ StrictMono t ∧ (∀ n, a n ≤ t n) ∧
      Φ.complexityClass (fun n => g n (t n)) = Φ.complexityClass t := by
  obtain ⟨t, ht, htm, hat, hgap⟩ := Φ.exists_gap₂ hg ha
  refine ⟨t, ht, htm, hat, Set.Subset.antisymm (fun f hf => ?_)
    (complexityClass_mono (Eventually.of_forall fun n => hgn n (t n)))⟩
  obtain ⟨c, hc, hev⟩ := mem_complexityClass.1 hf
  refine mem_complexityClass.2 ⟨c, hc, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (encode c)] with n hn hcn m hm
  exact (hgap c n hcn m hm).resolve_right (not_lt.2 (hn m hm))

/-- **Borodin's gap theorem** [Borodin1972]. For every computable `g` with `g n ≥ n` and every
computable lower bound `a`, there is a computable, strictly increasing `t ≥ a` with
`C_{g ∘ t} = C_t`. -/
theorem gap_theorem {g a : ℕ → ℕ} (hg : Computable g) (hgn : ∀ n, n ≤ g n) (ha : Computable a) :
    ∃ t : ℕ → ℕ, Computable t ∧ StrictMono t ∧ (∀ n, a n ≤ t n) ∧
      Φ.complexityClass (g ∘ t) = Φ.complexityClass t :=
  Φ.gap_theorem₂ (g := fun _ k => g k) (hg.comp Computable.snd).to₂ (fun _ => hgn) ha

end Cslib.BlumComplexity.BlumMeasure
