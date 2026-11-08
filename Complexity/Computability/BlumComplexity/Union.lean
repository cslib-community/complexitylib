/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.BlumComplexity.Basic
import Complexity.Computability.BlumComplexity.Cancellation

/-!
# The union theorem

For every Blum complexity measure `Φ` and every uniformly computable family of bounds
`T 0, T 1, …` that increases pointwise in the index, there is a single computable bound `t` with
`C_t = ⋃ i, C_{T i}`. This is the union theorem, attributed to McCreight and Meyer
[McCreight and Meyer, *Classes of computable functions defined by bounds on
computation*][McCreightMeyer1969]. For example, a union of polynomial classes is the class of one
computable bound, which is necessarily not a polynomial.

## Construction

The proof is a cancellation run (`Cslib.BlumComplexity.Cancellation.canc`) without the recursion
theorem; it is not taken from the source. Requirement `p = ⟪j, i⟫` with `j ≤ i` is *eligible* at
stage `y` when the program numbered `j` does not halt on `y` within cost `T i y`. By Blum's second
axiom (`Cslib.BlumComplexity.BlumMeasure.computablePred_cost_le`), eligibility is decidable. At
each stage the least eligible requirement not cancelled earlier is cancelled, and the bound is
`t y = T i y` for the cancelled requirement `⟪j, i⟫`, or `t y = T y y` if nothing is cancelled.

* Each requirement is cancelled at most once, and only the finitely many requirements below
  `⟪I, I⟫` have `i < I`. So eventually `t y = T i y` with `i ≥ I`, and `T I ≤ t` almost
  everywhere.
* If program `j` exceeds every `T i` infinitely often, then every requirement `⟪j, i⟫` with
  `i ≥ j` is eligible infinitely often, so it is cancelled at some stage `y`
  (`Cslib.BlumComplexity.Cancellation.eventually_not_eligible`). There `t y = T i y` and program
  `j` exceeds `t y`. Since `y ≥ ⟪j, i⟫ ≥ i`, such stages are unbounded.

## Conventions and strength

`complexityClass t` uses Borodin's almost-everywhere convention (see
`Complexity.Computability.BlumComplexity.Basic`). `exists_union_bound` states the pointwise
content for every program, including programs that diverge somewhere: a program that halts within
`t` almost everywhere halts within some `T i` almost everywhere. The bound `t` is diagonal: at each
`n` it equals `T i n` for some `i ≤ n`.

`union_theorem` assumes `T i n ≤ T (i + 1) n` for all `i` and `n`. `union_theorem_of_eventuallyLE`
only assumes `T i ≤ T (i + 1)` almost everywhere, and `union_theorem_of_directed` only assumes that
any two bounds are dominated almost everywhere by a third. Both reduce to `union_theorem` through
the running maximum of the family. The exact hypotheses of the source have not been checked
against the paper.

## Main results

* `Cslib.BlumComplexity.BlumMeasure.exists_union_bound`: the diagonal bound and its pointwise
  properties.
* `Cslib.BlumComplexity.BlumMeasure.union_theorem`: **the union theorem**,
  `C_t = ⋃ i, C_{T i}` for a pointwise increasing family.
* `Cslib.BlumComplexity.BlumMeasure.union_theorem_of_eventuallyLE`: the same for a family that
  increases almost everywhere.
* `Cslib.BlumComplexity.BlumMeasure.union_theorem_of_directed`: the same for a family that is
  directed under almost-everywhere domination.

## References

* [E. M. McCreight and A. R. Meyer, *Classes of computable functions defined by bounds on
  computation*][McCreightMeyer1969]
* [A. Borodin, *Computational complexity and the existence of complexity gaps*][Borodin1972]
-/

public section

namespace Cslib.BlumComplexity.BlumMeasure

open Encodable Denumerable Filter Cancellation
open Nat.Partrec (Code)

variable (Φ : BlumMeasure)

namespace UnionBound

/-- Requirement `p = ⟪j, i⟫` with `j ≤ i` is eligible at stage `y` when the program numbered `j`
does not halt on `y` within cost `T i y`. -/
private def Elig (T : ℕ → ℕ → ℕ) (p y : ℕ) : Prop :=
  (Nat.unpair p).1 ≤ (Nat.unpair p).2 ∧
    ¬∃ m ∈ Φ.cost (ofNat Code (Nat.unpair p).1) y, m ≤ T (Nat.unpair p).2 y

/-- `Elig` as a Boolean, decided classically. It is computable by `computable_elig`. -/
private noncomputable def elig (T : ℕ → ℕ → ℕ) (p y : ℕ) : Bool :=
  @decide (Elig Φ T p y) (Classical.dec _)

private theorem elig_eq_true {T : ℕ → ℕ → ℕ} {p y : ℕ} : elig Φ T p y = true ↔ Elig Φ T p y :=
  @decide_eq_true_iff _ (Classical.dec _)

private theorem computable_elig {T : ℕ → ℕ → ℕ} (hT : Computable₂ T) :
    Computable fun q : ℕ × ℕ × ℕ => elig Φ T q.2.1 q.2.2 := by
  have hu : Computable fun q : ℕ × ℕ × ℕ => Nat.unpair q.2.1 :=
    Primrec.unpair.to_comp.comp (Computable.fst.comp Computable.snd)
  have hy : Computable fun q : ℕ × ℕ × ℕ => q.2.2 := Computable.snd.comp Computable.snd
  have h : ComputablePred fun q : ℕ × ℕ × ℕ => Elig Φ T q.2.1 q.2.2 := by
    refine (ComputablePred.nat_le (Computable.fst.comp hu) (Computable.snd.comp hu)).and ?_
    exact (Φ.computablePred_cost_le.comp ((((Computable.ofNat Code).comp
      (Computable.fst.comp hu)).pair hy).pair (hT.comp (Computable.snd.comp hu) hy))).not
  exact @ComputablePred.decide _ _ _ (fun _ => Classical.dec _) h

/-- The requirement cancelled at stage `y`, if any. -/
private noncomputable def run (T : ℕ → ℕ → ℕ) (y : ℕ) : Option ℕ :=
  canc (elig Φ T) (fun _ => false) 0 y

/-- The index of the bound used at stage `y`: `i` if `⟪j, i⟫` is cancelled there, else `y`. -/
private noncomputable def idx (T : ℕ → ℕ → ℕ) (y : ℕ) : ℕ :=
  ((run Φ T y).map fun p => (Nat.unpair p).2).getD y

private theorem computable_idx {T : ℕ → ℕ → ℕ} (hT : Computable₂ T) : Computable (idx Φ T) := by
  have hrun : Computable (run Φ T) :=
    computable_canc (α := ℕ) (E := fun _ => elig Φ T) (ov := fun _ _ => false)
      (computable_elig Φ hT) (Computable.const false).to₂ (Computable.const 0) Computable.id
  exact Computable.option_getD (Computable.option_map hrun
    (Computable.snd.comp (Primrec.unpair.to_comp.comp Computable.snd)).to₂) Computable.id

private theorem idx_le (T : ℕ → ℕ → ℕ) (y : ℕ) : idx Φ T y ≤ y := by
  unfold idx
  cases h : run Φ T y with
  | none => exact le_rfl
  | some p => exact (Nat.unpair_right_le p).trans (canc_le h).2

/-- Eventually the index is at least `I`: only the requirements below `⟪I, I⟫` have `i < I`, and
each is cancelled at most once. -/
private theorem eventually_le_idx (T : ℕ → ℕ → ℕ) (I : ℕ) : ∀ᶠ y in atTop, I ≤ idx Φ T y := by
  filter_upwards [eventually_canc_ne (elig Φ T) (fun _ => false) 0 (Nat.pair I I),
    eventually_ge_atTop I] with y hy hIy
  unfold idx
  cases h : run Φ T y with
  | none => exact hIy
  | some p =>
    rw [Option.map_some, Option.getD_some]
    by_contra hlt
    push Not at hlt
    have hji := ((elig_eq_true Φ).1 (canc_eq_some.1 h).2.2.2.1).1
    have hp : p < Nat.pair I I := by
      rw [← Nat.pair_unpair p]
      exact (Nat.pair_lt_pair_left _ (hji.trans_lt hlt)).trans (Nat.pair_lt_pair_right _ hlt)
    exact hy p hp h

/-- If program `c` halts within `T (idx y) y` from stage `N` on, then it halts within some fixed
`T i` almost everywhere. Otherwise the requirement `⟪encode c, encode c + N⟫` is eligible
infinitely often, hence cancelled at some stage `y ≥ N`, where `c` exceeds the bound. -/
private theorem exists_index (T : ℕ → ℕ → ℕ) (c : Code) (N : ℕ)
    (hN : ∀ y, N ≤ y → ∃ m ∈ Φ.cost c y, m ≤ T (idx Φ T y) y) :
    ∃ i, ∀ᶠ y in atTop, ∃ m ∈ Φ.cost c y, m ≤ T i y := by
  by_contra hne
  let i := encode c + N
  let p := Nat.pair (encode c) i
  have hup : Nat.unpair p = (encode c, i) := Nat.unpair_pair _ _
  have hfreq : ∃ᶠ y in atTop, ¬∃ m ∈ Φ.cost c y, m ≤ T i y :=
    Filter.not_eventually.1 fun h => hne ⟨i, h⟩
  have helig : ∀ y, (¬∃ m ∈ Φ.cost c y, m ≤ T i y) → Elig Φ T p y := fun y hy => by
    refine ⟨?_, ?_⟩
    · rw [hup]
      exact Nat.le_add_right _ _
    · rw [hup]
      simpa only [ofNat_encode] using hy
  obtain ⟨y, hy⟩ : ∃ y, run Φ T y = some p := by
    by_contra hnone
    push Not at hnone
    obtain ⟨y, hy1, hy2⟩ := (hfreq.and_eventually (eventually_not_eligible hnone)).exists
    rw [← Bool.not_eq_true, elig_eq_true] at hy2
    exact hy2 (helig y hy1)
  have hpy := (canc_le hy).2
  have hNy : N ≤ y := (Nat.le_add_left N (encode c)).trans ((Nat.right_le_pair _ _).trans hpy)
  have hidx : idx Φ T y = i := by
    unfold idx
    rw [hy, Option.map_some, Option.getD_some, hup]
  have hE := ((elig_eq_true Φ).1 (canc_eq_some.1 hy).2.2.2.1).2
  rw [hup] at hE
  simp only [ofNat_encode] at hE
  exact hE (hidx ▸ hN y hNy)

/-- The running maximum `max (T 0 n) … (T i n)`. -/
private def runMax (T : ℕ → ℕ → ℕ) (i n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (T 0 n) (fun k s => max s (T (k + 1) n)) i

private theorem runMax_succ (T : ℕ → ℕ → ℕ) (i n : ℕ) :
    runMax T (i + 1) n = max (runMax T i n) (T (i + 1) n) := rfl

private theorem le_runMax (T : ℕ → ℕ → ℕ) (i n : ℕ) : T i n ≤ runMax T i n := by
  cases i with
  | zero => exact le_rfl
  | succ i => exact runMax_succ T i n ▸ le_max_right _ _

private theorem computable_runMax {T : ℕ → ℕ → ℕ} (hT : Computable₂ T) :
    Computable₂ (runMax T) :=
  Computable.nat_rec (f := fun p : ℕ × ℕ => p.1) (g := fun p => T 0 p.2)
    (h := fun p q => max q.2 (T (q.1 + 1) p.2)) Computable.fst
    (hT.comp (Computable.const 0) Computable.snd)
    (Primrec.nat_max.to_comp.comp (Computable.snd.comp Computable.snd)
      (hT.comp (Computable.succ.comp (Computable.fst.comp Computable.snd))
        (Computable.snd.comp Computable.fst))).to₂

/-- In a directed family, every running maximum is dominated almost everywhere by a member. -/
private theorem exists_runMax_le {T : ℕ → ℕ → ℕ}
    (hdir : ∀ i j, ∃ k, T i ≤ᶠ[atTop] T k ∧ T j ≤ᶠ[atTop] T k) (i : ℕ) :
    ∃ k, runMax T i ≤ᶠ[atTop] T k := by
  induction i with
  | zero => exact ⟨0, EventuallyLE.refl _ _⟩
  | succ i ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨k', h1, h2⟩ := hdir k (i + 1)
    refine ⟨k', ?_⟩
    filter_upwards [hk, h1, h2] with n hn h1n h2n
    rw [runMax_succ]
    exact max_le (hn.trans h1n) h2n

/-- A total program's cost is bounded by `b` at `n` exactly when some value of its cost is. -/
private theorem forall_iff_exists_of_total {f : ℕ → ℕ} {c : Code} (hc : ∀ n, f n ∈ c.eval n)
    (b : ℕ → ℕ) (n : ℕ) : (∀ m ∈ Φ.cost c n, m ≤ b n) ↔ ∃ m ∈ Φ.cost c n, m ≤ b n := by
  obtain ⟨m, hm⟩ := Part.dom_iff_mem.1 (Φ.dom_cost_of_total hc n)
  exact ⟨fun h => ⟨m, hm, h m hm⟩, fun ⟨m', hm', h⟩ m'' hm'' => Part.mem_unique hm' hm'' ▸ h⟩

end UnionBound

open UnionBound

/-- **The union bound**, pointwise. For a uniformly computable family `T` that increases pointwise
in the index, there is a computable `t` such that

* `t` is diagonal: `t n = T i n` for some `i ≤ n`;
* every `T i` is at most `t` almost everywhere;
* every program `c` that halts within `t n` for almost all `n` halts within `T i n` for almost all
  `n`, for some fixed `i`. The program need not be total. -/
theorem exists_union_bound {T : ℕ → ℕ → ℕ} (hT : Computable₂ T)
    (hmono : ∀ i n, T i n ≤ T (i + 1) n) :
    ∃ t : ℕ → ℕ, Computable t ∧ (∀ n, ∃ i ≤ n, t n = T i n) ∧ (∀ i, T i ≤ᶠ[atTop] t) ∧
      ∀ c : Code, (∀ᶠ n in atTop, ∃ m ∈ Φ.cost c n, m ≤ t n) →
        ∃ i, ∀ᶠ n in atTop, ∃ m ∈ Φ.cost c n, m ≤ T i n := by
  have hmono' : ∀ n, Monotone fun i => T i n := fun n =>
    monotone_nat_of_le_succ fun i => hmono i n
  refine ⟨fun n => T (idx Φ T n) n, hT.comp (computable_idx Φ hT) Computable.id,
    fun n => ⟨idx Φ T n, idx_le Φ T n, rfl⟩, fun i => ?_, fun c hc => ?_⟩
  · filter_upwards [eventually_le_idx Φ T i] with n hn
    exact hmono' n hn
  · obtain ⟨N, hN⟩ := eventually_atTop.1 hc
    exact exists_index Φ T c N hN

/-- **The union theorem** [McCreightMeyer1969]. For a uniformly computable family of bounds `T`
that increases pointwise in the index, some computable `t` has `C_t = ⋃ i, C_{T i}`. The bound is
diagonal: `t n = T i n` for some `i ≤ n`. -/
theorem union_theorem {T : ℕ → ℕ → ℕ} (hT : Computable₂ T)
    (hmono : ∀ i n, T i n ≤ T (i + 1) n) :
    ∃ t : ℕ → ℕ, Computable t ∧ (∀ n, ∃ i ≤ n, t n = T i n) ∧
      Φ.complexityClass t = ⋃ i, Φ.complexityClass (T i) := by
  obtain ⟨t, ht, hdiag, hle, hcls⟩ := Φ.exists_union_bound hT hmono
  refine ⟨t, ht, hdiag, Set.Subset.antisymm (fun f hf => ?_)
    (Set.iUnion_subset fun i => complexityClass_mono (hle i))⟩
  obtain ⟨c, hc, hev⟩ := mem_complexityClass.1 hf
  have hev' : ∀ᶠ n in atTop, ∃ m ∈ Φ.cost c n, m ≤ t n :=
    hev.mono fun n hn => (forall_iff_exists_of_total Φ hc t n).1 hn
  obtain ⟨i, hi⟩ := hcls c hev'
  exact Set.mem_iUnion.2 ⟨i, mem_complexityClass.2
    ⟨c, hc, hi.mono fun n hn => (forall_iff_exists_of_total Φ hc _ n).2 hn⟩⟩

/-- **The union theorem** for a directed family [McCreightMeyer1969]. If any two bounds of a
uniformly computable family `T` are dominated almost everywhere by a third, some computable `t`
has `C_t = ⋃ i, C_{T i}`. -/
theorem union_theorem_of_directed {T : ℕ → ℕ → ℕ} (hT : Computable₂ T)
    (hdir : ∀ i j, ∃ k, T i ≤ᶠ[atTop] T k ∧ T j ≤ᶠ[atTop] T k) :
    ∃ t : ℕ → ℕ, Computable t ∧ Φ.complexityClass t = ⋃ i, Φ.complexityClass (T i) := by
  obtain ⟨t, ht, -, heq⟩ := Φ.union_theorem (computable_runMax hT)
    fun i n => (runMax_succ T i n).symm ▸ le_max_left _ _
  refine ⟨t, ht, heq.trans (Set.Subset.antisymm (Set.iUnion_subset fun i => ?_)
    (Set.iUnion_subset fun i => ?_))⟩
  · obtain ⟨k, hk⟩ := exists_runMax_le hdir i
    exact (complexityClass_mono hk).trans (Set.subset_iUnion (fun k => Φ.complexityClass (T k)) k)
  · refine (complexityClass_mono ?_).trans
      (Set.subset_iUnion (fun k => Φ.complexityClass (runMax T k)) i)
    exact Eventually.of_forall fun n => le_runMax T i n

/-- **The union theorem** for a family that increases almost everywhere [McCreightMeyer1969]. If
`T i ≤ T (i + 1)` almost everywhere for every `i`, some computable `t` has
`C_t = ⋃ i, C_{T i}`. -/
theorem union_theorem_of_eventuallyLE {T : ℕ → ℕ → ℕ} (hT : Computable₂ T)
    (hmono : ∀ i, T i ≤ᶠ[atTop] T (i + 1)) :
    ∃ t : ℕ → ℕ, Computable t ∧ Φ.complexityClass t = ⋃ i, Φ.complexityClass (T i) := by
  have hle : ∀ i k, i ≤ k → T i ≤ᶠ[atTop] T k := by
    intro i k hik
    induction hik with
    | refl => exact EventuallyLE.refl _ _
    | step _ ih => exact ih.trans (hmono _)
  exact Φ.union_theorem_of_directed hT fun i j =>
    ⟨max i j, hle i _ (le_max_left i j), hle j _ (le_max_right i j)⟩

end Cslib.BlumComplexity.BlumMeasure
