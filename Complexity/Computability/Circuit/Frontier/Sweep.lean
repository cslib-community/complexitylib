/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Rectangle
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Lattice.Nat
import Complexity.Foundations.Data.Set.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Sweeps and the frontier counting lemma

A *sweep* of a set of inputs `S ⊆ U^ι` reveals the coordinates of an input a few at a time:
`∅ = X 0, X 1, ..., X T = ι`. At each time `t` an input has a *message* `μ t x`, which may
depend on the whole input. The defining property is that messages permit splicing: if two inputs
of `S` send the same message at time `t`, then the revealed part of one may be spliced onto the
unrevealed part of the other without leaving `S`. The last message, sent once everything is
revealed, is the same for all inputs of `S`.

Between times `t` and `t + 1` an input `x` takes the *transition*
`(μ t x, μ (t + 1) x, x|_{X (t + 1) \ X t})`: the message before the step, the message after it,
and the coordinates revealed during it.

**The frontier counting lemma** (`Sweep.ncard_le`). If `S` is `K`-rectangle-free and has at
least `K` elements, then `|S| ≤ (K - 1) ^ 2 · ∑ₜ #{transitions taken at step t}`.

The proof charges each input `x` to the first time `t + 1` at which the inputs sharing its
message (its *peers*) have at least `K` distinct revealed parts. The rectangular hull of the
peers lies inside `S`, so they have fewer than `K` distinct unrevealed parts. At time `t` the
peers of `x` still had fewer than `K` distinct revealed parts. An input charged to a step is
determined by its transition, its part revealed by time `t` and its part unrevealed at time
`t + 1`; hence at most `(K - 1) ^ 2` inputs share a charged step and a transition.

Nothing here mentions graphs or circuits: a sweep is an abstract family of splicing messages,
and its charging argument is shared by everything swept along a layout. The chosen accepting
paths of a read-once branching program form a sweep of its accepted set, which gives the
rectangle bound for such programs (`Cslib.Circuits.Frontier.ReadOnceNBP.ncard_accepted_le`), and
through them the counting lemma for constraint networks. Constraint
networks swept along a layout with extra messages, such as a ledger, produce sweeps whose
messages are the extra messages and the values on the edges of the frontier
(`Cslib.Circuits.Frontier.Network.frontierSweep`).

## Main definitions

* `Cslib.Circuits.Frontier.Sweep S M`: a sweep of `S` with messages in `M`.
* `Cslib.Circuits.Frontier.Sweep.transition`: the transition taken by an input at a step.
* `Cslib.Circuits.Frontier.Sweep.transitionCount`: the number of transitions taken by inputs of
  `S`, summed over the steps.

## Main results

* `Cslib.Circuits.Frontier.Sweep.ncard_le_mul_transitionCount`: the charging argument, for any
  two thresholds that bound the two sides of every message class.
* `Cslib.Circuits.Frontier.Sweep.ncard_le`: the frontier counting lemma.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set

variable {ι U : Type*}

/-- A *sweep* of a set of inputs `S`: coordinates revealed over time, starting from none and
ending with all, and a message at each time such that inputs of `S` sending the same message
can exchange their unrevealed parts. -/
structure Sweep (S : Set (ι → U)) (M : Type*) where
  /-- The number of steps. -/
  length : ℕ
  /-- The coordinates revealed by time `t`. -/
  revealed : ℕ → Set ι
  /-- Nothing is revealed at the start. -/
  revealed_zero : revealed 0 = ∅
  /-- Everything is revealed at the end. -/
  revealed_length : revealed length = univ
  /-- The message at time `t`, possibly depending on the whole input. -/
  message : ℕ → (ι → U) → M
  /-- The final message is the same for all inputs of `S`. -/
  message_length : ∀ x ∈ S, ∀ y ∈ S, message length x = message length y
  /-- Messages permit splicing: if two inputs of `S` send the same message at time `t`, the
  revealed part of one and the unrevealed part of the other form an input of `S`. -/
  splice : ∀ t, ∀ x ∈ S, ∀ y ∈ S, message t x = message t y →
    ∀ z, EqOn z x (revealed t) → EqOn z y (revealed t)ᶜ → z ∈ S

namespace Sweep

variable {M : Type*} {S : Set (ι → U)} (P : Sweep S M)

/-- The coordinates revealed during step `t`, between times `t` and `t + 1`. -/
def newly (t : ℕ) : Set ι :=
  P.revealed (t + 1) \ P.revealed t

/-- The transition taken by `x` at step `t`: its messages before and after the step, and its
part revealed during the step. -/
def transition (t : ℕ) (x : ι → U) : M × M × (P.newly t → U) :=
  (P.message t x, P.message (t + 1) x, (P.newly t).domRestrict x)

/-- The number of transitions taken by inputs of `S`, summed over the steps of the sweep. -/
noncomputable def transitionCount : ℕ :=
  ∑ t ∈ Finset.range P.length, (P.transition t '' S).ncard

/-- Counting transitions by what determines them: if on `S` the transition at step `t` is a
function of `h` and of a quantity `g` with values in a finite type `D`, then there are at most
`#(values of h on S) * |D|` transitions at step `t`. -/
theorem ncard_transition_le_of_factorsThrough [Finite ι] [Finite U] {t : ℕ} {R D : Type*}
    [Finite D] (h : (ι → U) → R) (g : (ι → U) → D)
    (hg : ∀ x ∈ S, ∀ y ∈ S, h x = h y → g x = g y → P.transition t x = P.transition t y) :
    (P.transition t '' S).ncard ≤ (h '' S).ncard * Nat.card D := by
  calc (P.transition t '' S).ncard
      ≤ ((fun x => (h x, g x)) '' S).ncard :=
        ncard_image_le_ncard_image_of_factorsThrough (toFinite _) fun x hx y hy hxy =>
          hg x hx y hy (Prod.ext_iff.mp hxy).1 (Prod.ext_iff.mp hxy).2
    _ ≤ ((h '' S) ×ˢ (univ : Set D)).ncard :=
        ncard_le_ncard (image_subset_iff.mpr fun x hx => ⟨mem_image_of_mem h hx, mem_univ _⟩)
          ((toFinite S).image h |>.prod finite_univ)
    _ = (h '' S).ncard * Nat.card D := by rw [ncard_prod, ncard_univ]

/-! ### The charging argument -/

/-- The *peers* of `x` at time `t`: the inputs of `S` that send the same message as `x`. -/
def peers (t : ℕ) (x : ι → U) : Set (ι → U) :=
  {y ∈ S | P.message t y = P.message t x}

/-- The distinct parts revealed by time `t` among the peers of `x`. -/
def pastSide (t : ℕ) (x : ι → U) : Set (P.revealed t → U) :=
  (P.revealed t).domRestrict '' P.peers t x

/-- The distinct parts unrevealed at time `t` among the peers of `x`. -/
def futureSide (t : ℕ) (x : ι → U) : Set (↥(P.revealed t)ᶜ → U) :=
  (P.revealed t)ᶜ.domRestrict '' P.peers t x

/-- The rectangular hull of the peers of `x` lies inside `S`, so in a rectangle-free set one of
its sides is small. -/
theorem pastSide_lt_or_futureSide_lt {K : ℕ} (hS : RectangleFree S K) (t : ℕ) (x : ι → U) :
    (P.pastSide t x).ncard < K ∨ (P.futureSide t x).ncard < K := by
  refine hS.ncard_lt_or _ _ _ fun z ⟨⟨y, ⟨hy, hyx⟩, hzy⟩, ⟨y', ⟨hy', hy'x⟩, hzy'⟩⟩ => ?_
  exact P.splice t y hy y' hy' (hyx.trans hy'x.symm) z
    (domRestrict_eq_domRestrict_iff.mp hzy).symm (domRestrict_eq_domRestrict_iff.mp hzy').symm

/-- An input of `S` is among its own peers, so its past side is nonempty. -/
theorem one_le_ncard_pastSide [Finite ι] [Finite U] {x : ι → U} (hx : x ∈ S) (t : ℕ) :
    1 ≤ (P.pastSide t x).ncard :=
  (ncard_pos (toFinite _)).mpr ⟨_, x, ⟨hx, rfl⟩, rfl⟩

/-- An input of `S` is among its own peers, so its future side is nonempty. -/
theorem one_le_ncard_futureSide [Finite ι] [Finite U] {x : ι → U} (hx : x ∈ S) (t : ℕ) :
    1 ≤ (P.futureSide t x).ncard :=
  (ncard_pos (toFinite _)).mpr ⟨_, x, ⟨hx, rfl⟩, rfl⟩

/-- At the start nothing is revealed, so there is at most one revealed part. -/
private theorem ncard_pastSide_zero_le (x : ι → U) : (P.pastSide 0 x).ncard ≤ 1 := by
  have : Subsingleton (P.revealed 0 → U) :=
    ⟨fun a b => funext fun i => absurd i.2 (by simp [P.revealed_zero])⟩
  exact (ncard_le_one (toFinite _)).mpr fun a _ b _ => Subsingleton.elim a b

/-- At the end everything is revealed and every input of `S` is a peer, so the revealed parts
are as numerous as `S`. -/
private theorem ncard_pastSide_length {x : ι → U} (hx : x ∈ S) :
    (P.pastSide P.length x).ncard = S.ncard := by
  have hpeers : P.peers P.length x = S :=
    subset_antisymm (fun _ hy => hy.1) fun y hy => ⟨hy, P.message_length y hy x hx⟩
  rw [pastSide, hpeers]
  refine ncard_image_of_injective _ fun y y' h => funext fun i => ?_
  exact domRestrict_eq_domRestrict_iff.mp h (by simp [P.revealed_length])

/-- The time at which `x` is charged: the first time its peers have at least `K` distinct
revealed parts. -/
private noncomputable def chargeTime (K : ℕ) (x : ι → U) : ℕ :=
  sInf {t | K ≤ (P.pastSide t x).ncard}

/-- **The charging argument.** If at every time up to the end each input of `S` has fewer than
`KL` distinct revealed parts or fewer than `KR` distinct unrevealed parts among its peers, then
`|S| ≤ (KL - 1) (KR - 1) · #transitions`, provided `1 < KL ≤ |S|`. -/
theorem ncard_le_mul_transitionCount [Finite ι] [Finite U] {KL KR : ℕ} (hKL : 1 < KL)
    (hK : KL ≤ S.ncard) (hsides : ∀ t ≤ P.length, ∀ x ∈ S,
      (P.pastSide t x).ncard < KL ∨ (P.futureSide t x).ncard < KR) :
    S.ncard ≤ (KL - 1) * (KR - 1) * P.transitionCount := by
  -- The charge time is well defined, positive, and at most the length of the sweep.
  have hlength : ∀ x ∈ S, P.length ∈ {t | KL ≤ (P.pastSide t x).ncard} := fun x hx => by
    simpa [P.ncard_pastSide_length hx] using hK
  have hcharged : ∀ x ∈ S, KL ≤ (P.pastSide (P.chargeTime KL x) x).ncard := fun x hx =>
    Nat.sInf_mem ⟨_, hlength x hx⟩
  have hbefore : ∀ x, ∀ t < P.chargeTime KL x, (P.pastSide t x).ncard < KL := fun x t ht =>
    not_le.mp (Nat.notMem_of_lt_sInf (s := {t | KL ≤ (P.pastSide t x).ncard}) ht)
  have hle_length : ∀ x ∈ S, P.chargeTime KL x ≤ P.length := fun x hx =>
    Nat.sInf_le (hlength x hx)
  have hpos : ∀ x ∈ S, 0 < P.chargeTime KL x := fun x hx => by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have := h0 ▸ hcharged x hx
    have := P.ncard_pastSide_zero_le x
    omega
  -- Each input is charged to the step `t` whose completion charges it: `chargeTime = t + 1`.
  set step : (ι → U) → ℕ := fun x => P.chargeTime KL x - 1
  -- An input charged at step `t` is determined by its transition, its part revealed by time
  -- `t`, and its part unrevealed at time `t + 1`; each of the last two takes few values.
  have hfiber : ∀ t τ, {y ∈ {y ∈ S | step y = t} | P.transition t y = τ}.ncard ≤
      (KL - 1) * (KR - 1) := by
    intro t τ
    rcases eq_empty_or_nonempty {y ∈ {y ∈ S | step y = t} | P.transition t y = τ} with h | h
    · rw [h, ncard_empty]
      exact Nat.zero_le _
    obtain ⟨x, ⟨hxS, hxt : P.chargeTime KL x - 1 = t⟩, hxτ⟩ := h
    have hxcharge : P.chargeTime KL x = t + 1 := by have := hpos x hxS; omega
    have hpast : (P.pastSide t x).ncard ≤ KL - 1 := by
      have := hbefore x t (by omega); omega
    have hfuture : (P.futureSide (t + 1) x).ncard ≤ KR - 1 := by
      have := hxcharge ▸ hcharged x hxS
      rcases hsides (t + 1) (hxcharge ▸ hle_length x hxS) x hxS with h | h <;> omega
    calc {y ∈ {y ∈ S | step y = t} | P.transition t y = τ}.ncard
        ≤ (P.pastSide t x ×ˢ P.futureSide (t + 1) x).ncard := by
          refine ncard_le_ncard_of_injOn
            (fun y => ((P.revealed t).domRestrict y, (P.revealed (t + 1))ᶜ.domRestrict y))
            ?_ ?_ (toFinite _)
          · rintro y ⟨⟨hyS, -⟩, hyτ⟩
            have hyx : P.transition t y = P.transition t x := hyτ.trans hxτ.symm
            simp only [transition, Prod.mk.injEq] at hyx
            exact ⟨⟨y, ⟨hyS, hyx.1⟩, rfl⟩, ⟨y, ⟨hyS, hyx.2.1⟩, rfl⟩⟩
          · rintro y ⟨-, hyτ⟩ y' ⟨-, hy'τ⟩ hyy'
            simp only [Prod.mk.injEq, domRestrict_eq_domRestrict_iff] at hyy'
            have hnew : EqOn y y' (P.newly t) := by
              have h := hyτ.trans hy'τ.symm
              simp only [transition, Prod.mk.injEq, domRestrict_eq_domRestrict_iff] at h
              exact h.2.2
            funext i
            by_cases h₁ : i ∈ P.revealed t
            · exact hyy'.1 h₁
            by_cases h₂ : i ∈ P.revealed (t + 1)
            · exact hnew ⟨h₂, h₁⟩
            · exact hyy'.2 h₂
      _ = (P.pastSide t x).ncard * (P.futureSide (t + 1) x).ncard := ncard_prod
      _ ≤ (KL - 1) * (KR - 1) := Nat.mul_le_mul hpast hfuture
  -- Sum over the steps.
  calc S.ncard
      = ∑ t ∈ Finset.range P.length, {y ∈ S | step y = t}.ncard :=
        ncard_eq_sum_ncard_fiberwise (toFinite S) fun x hx => by
          have := hle_length x hx
          have := hpos x hx
          simp only [Finset.coe_range, mem_Iio, step]
          omega
    _ ≤ ∑ t ∈ Finset.range P.length, (KL - 1) * (KR - 1) * (P.transition t '' S).ncard := by
        refine Finset.sum_le_sum fun t _ => ?_
        refine (ncard_le_mul_ncard_image (toFinite _) (P.transition t) _
          fun τ _ => hfiber t τ).trans (Nat.mul_le_mul_left _ (ncard_le_ncard ?_))
        exact image_mono fun y hy => hy.1
    _ = (KL - 1) * (KR - 1) * P.transitionCount := (Finset.mul_sum ..).symm

/-- **The frontier counting lemma.** A `K`-rectangle-free set with at least `K` elements has at
most `(K - 1) ^ 2` elements per transition of any of its sweeps. -/
theorem ncard_le [Finite ι] [Finite U] {K : ℕ} (hS : RectangleFree S K) (hK : K ≤ S.ncard) :
    S.ncard ≤ (K - 1) ^ 2 * P.transitionCount := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  simpa only [sq] using P.ncard_le_mul_transitionCount (hS.one_lt hne) hK
    fun t _ x _ => P.pastSide_lt_or_futureSide_lt hS t x

end Sweep

end Cslib.Circuits.Frontier
