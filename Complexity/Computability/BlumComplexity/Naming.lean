/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.BlumComplexity.Basic
import Complexity.Computability.BlumComplexity.Cancellation
import Mathlib.Data.List.GetD
import Mathlib.Order.Filter.Finite

/-!
# The naming theorem

For every Blum complexity measure `Φ` there is a *measured* family of functions that contains a
name for every complexity class of a computable bound. That is the naming theorem
[Odifreddi1999, Theorem VII.3.6], attributed there to Meyer and McCreight
[McCreight and Meyer, *Classes of computable functions defined by bounds on
computation*][McCreightMeyer1969]. A family `φ_{h 0}, φ_{h 1}, …` is measured
[Odifreddi1999, Definition VII.2.9] when the predicate `φ_{h i} x = y` is decidable, uniformly
in `i`, `x` and `y`. A bound `t'` is a name for `C_t` when `C_{t'} = C_t`.

`naming_theorem` gives a computable `h : Code → Code` such that

1. the predicate `φ_{h i} x = y` is decidable, uniformly in `i`, `x` and `y`;
2. if `φ_i` is total, so is `φ_{h i}`;
3. if `φ_i` is total, then `C_{φ_{h i}} = C_{φ_i}`.

These are items 1–3 of the source. The function `φ_{h i}` is `Φ.name i`, defined directly from
`i` by a priority construction; `naming_theorem` packages `Φ.name` as a computable map on programs.

## Construction

Fix the program `i`. The stages are `s = ⟪x, z⟫`. Input `x` receives its value at the first stage
`⟪x, z⟫` at which some index *acts*, or at which `i` halts on `x` within cost `z`. Index `e` is
*flagged* at stage `s` when some input `y ≤ s`, on which `i` halts within cost `s`, has
`φ_i y < Φ_e y` (program `e` does not halt on `y` within cost `φ_i y`), and `y` had not flagged
`e` already when `e` last acted. A *candidate* is a flagged index `e ≤ s` that does not halt on `x`
within `z`, such that every unflagged index of higher priority does. The candidate of highest
priority acts, and `x` receives the value `z`. If no index acts and `i` halts on `x` within exactly
`z`, then `x` receives `max z (φ_i x)`.

Priority is dynamic. An index that has never acted has key `2 e`; an index that last acted at stage
`a` has key `2 a + 1`. Smaller keys have higher priority, so an index that acts moves behind every
other index considered so far. The key replaces the source's explicit priority list, and the
flag condition replaces its marks; both are computed from the history of earlier stages.

The value at an action is `z`. The source takes `Φ_{e_x}(x) - 1` instead, where `e_x` is the
acting index. Both are below `Φ_{e_x}(x)` when the latter is defined, and both are at least `z`,
which is what item 1 uses. The value `z` is defined even when `Φ_{e_x}(x)` is not.

## Verification

Let `i` compute a total `t`, with name `t'`.

* If program `e` halts within `t` almost everywhere, it acts at only finitely many stages
  (each action uses one of the finitely many inputs where `e` exceeds `t`).
* If `e` acts at infinitely many stages, it exceeds `t'` infinitely often (the private lemma
  `frequently_not_halts`): each action at `⟪x, z⟫` gives `x` the value `z`, within which `e` does
  not halt on `x`.
* If `e` acts at only finitely many stages, then almost everywhere `e` halts within `t` exactly when
  it halts within `t'` (the private lemma `halts_iff`). The proof fixes the final key `K` of `e`.
  For each of the finitely many indices `e' ≤ K`, being unflagged with key at most `K` is eventually
  constant ("quiet-set stabilization").

Together these give `eventually_cost_le_name_iff` for every program, total or not, and hence
`C_{t'} = C_t`. The source verifies its requirements `H_e` (`C_t ⊆ C_{t'}`) and `L_e`
(`C_{t'} ⊆ C_t`) separately, by cases on whether `e` eventually keeps a mark. Here both directions
split on whether `e` acts at finitely many stages, so the `L_e` direction is proved by a different
argument (quiet-set stabilization).

## Main definitions

* `Cslib.BlumComplexity.BlumMeasure.name`: the name `Φ.name i` of the function computed by `i`.

## Main results

* `Cslib.BlumComplexity.BlumMeasure.partrec_name`: the names are uniformly partial recursive.
* `Cslib.BlumComplexity.BlumMeasure.computablePred_mem_name`: the graph of `Φ.name i` is
  decidable, uniformly in `i`.
* `Cslib.BlumComplexity.BlumMeasure.dom_name`: `Φ.name i x` is defined wherever `φ_i x` is.
* `Cslib.BlumComplexity.BlumMeasure.eventually_cost_le_name_iff`: for a total `φ_i = t` with name
  `t'`, every program halts within `t` almost everywhere if and only if it halts within `t'` almost
  everywhere.
* `Cslib.BlumComplexity.BlumMeasure.complexityClass_name`: `C_{t'} = C_t`.
* `Cslib.BlumComplexity.BlumMeasure.naming_theorem`: **the naming theorem**, items 1–3 above.

## References

* [P. Odifreddi, *Classical Recursion Theory, Volume II*][Odifreddi1999]
* [E. M. McCreight and A. R. Meyer, *Classes of computable functions defined by bounds on
  computation*][McCreightMeyer1969]
-/

public section

namespace Cslib.BlumComplexity.BlumMeasure

open Encodable Denumerable Filter Cancellation
open Nat.Partrec (Code)

variable (Φ : BlumMeasure)

namespace Naming

/-! ### Bounded halting -/

/-- Program `c` halts on `y` within cost `b`. -/
private def Halts (c : Code) (y b : ℕ) : Prop := ∃ m ∈ Φ.cost c y, m ≤ b

private theorem halts_mono {Φ : BlumMeasure} {c : Code} {y b b' : ℕ} (h : Halts Φ c y b)
    (hb : b ≤ b') : Halts Φ c y b' :=
  let ⟨m, hm, hmb⟩ := h
  ⟨m, hm, hmb.trans hb⟩

private theorem computablePred_halts {α : Type*} [Primcodable α] {c : α → Code} {y b : α → ℕ}
    (hc : Computable c) (hy : Computable y) (hb : Computable b) :
    ComputablePred fun a => Halts Φ (c a) (y a) (b a) :=
  Φ.computablePred_cost_le.comp ((hc.pair hy).pair hb)

private theorem dom_eval_of_halts {Φ : BlumMeasure} {c : Code} {y b : ℕ} (h : Halts Φ c y b) :
    (c.eval y).Dom := by
  obtain ⟨m, hm, -⟩ := h
  exact (Φ.dom_cost_iff c y).1 (Part.dom_iff_mem.2 ⟨m, hm⟩)

/-- The output of `c` on `y` if `c` halts on `y` within cost `b`, and `0` otherwise. -/
private noncomputable def gv (c : Code) (y b : ℕ) : ℕ :=
  @dite _ (Halts Φ c y b) (Classical.dec _) (fun h => (c.eval y).get (dom_eval_of_halts h))
    fun _ => 0

private theorem gv_mem {Φ : BlumMeasure} {c : Code} {y b : ℕ} (h : Halts Φ c y b) :
    gv Φ c y b ∈ c.eval y := by
  simp only [gv, h, ↓reduceDIte]
  exact Part.get_mem _

private theorem gv_eq_of_mem {Φ : BlumMeasure} {c : Code} {y b v : ℕ} (h : Halts Φ c y b)
    (hv : v ∈ c.eval y) : gv Φ c y b = v :=
  Part.mem_unique (gv_mem h) hv

private theorem computable_gv' : Computable fun q : Code × ℕ × ℕ => gv Φ q.1 q.2.1 q.2.2 := by
  obtain ⟨f, hf, hfp⟩ := ComputablePred.computable_iff.1
    (computablePred_halts Φ Computable.fst (Computable.fst.comp Computable.snd)
      (Computable.snd.comp Computable.snd))
  have hp : Partrec fun q : Code × ℕ × ℕ => cond (f q) (q.1.eval q.2.1) (Part.some 0) :=
    Partrec.cond hf (Code.eval_part.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Partrec.const' (Part.some 0))
  refine hp.of_eq_tot fun q => ?_
  have hq : Halts Φ q.1 q.2.1 q.2.2 ↔ f q = true := by
    rw [show Halts Φ q.1 q.2.1 q.2.2 = (fun q : Code × ℕ × ℕ => Halts Φ q.1 q.2.1 q.2.2) q
      from rfl, hfp]
  cases hfq : f q with
  | true => exact gv_mem (hq.2 hfq)
  | false =>
    have hn : ¬Halts Φ q.1 q.2.1 q.2.2 := fun h => by
      have h' := hq.1 h
      rw [hfq] at h'
      exact Bool.false_ne_true h'
    simp only [gv, hn, ↓reduceDIte]
    exact Part.mem_some 0

private theorem computable_gv {α : Type*} [Primcodable α] {c : α → Code} {y b : α → ℕ}
    (hc : Computable c) (hy : Computable y) (hb : Computable b) :
    Computable fun a => gv Φ (c a) (y a) (b a) :=
  (computable_gv' Φ).comp (hc.pair (hy.pair hb))

/-! ### The construction

Fix the code `i` of the bound. The construction runs through the stages `s = ⟪x, z⟫`. At each
stage at most one index `e` *acts*, which defines the name at `x` with the value `z`. The
history of the stages `< s` is a list of `Option ℕ`. -/

/-- The index that acted at stage `a` of the history `l`, if any. -/
private def actAt (l : List (Option ℕ)) (a : ℕ) : Option ℕ := l.getD a none

/-- At stage `s`, input `y` triggers index `e`: `y ≤ s`, program `i` halts on
`y` within cost `s`, and program `e` does not halt on `y` within the value of `i` there. -/
private def Triggers (i : Code) (e y s : ℕ) : Prop :=
  y ≤ s ∧ Halts Φ i y s ∧ ¬Halts Φ (ofNat Code e) y (gv Φ i y s)

private theorem gv_mono {Φ : BlumMeasure} {i : Code} {y s s' : ℕ} (h : Halts Φ i y s)
    (hs : s ≤ s') : gv Φ i y s' = gv Φ i y s :=
  gv_eq_of_mem (halts_mono h hs) (gv_mem h)

private theorem triggers_mono {Φ : BlumMeasure} {i : Code} {e y s s' : ℕ} (h : Triggers Φ i e y s)
    (hs : s ≤ s') : Triggers Φ i e y s' := by
  obtain ⟨hy, hi, he⟩ := h
  refine ⟨hy.trans hs, halts_mono hi hs, ?_⟩
  rwa [gv_mono hi hs]

/-- The last stage `a < n` of `l` at which index `e` acted, if any. -/
private def lastAct (l : List (Option ℕ)) (e n : ℕ) : Option ℕ :=
  Nat.rec (motive := fun _ => Option ℕ) none
    (fun a r => if actAt l a = some e then some a else r) n

/-- The priority key of index `e` before stage `n`: `2 a + 1` if it last acted at stage `a`,
and `2 e` if it never acted. Smaller keys have higher priority. An index that acts moves to the
end of the priority list. -/
private def key (l : List (Option ℕ)) (e n : ℕ) : ℕ :=
  (lastAct l e n).elim (2 * e) fun a => 2 * a + 1

private theorem lastAct_eq_some {l : List (Option ℕ)} {e n a : ℕ} :
    lastAct l e n = some a ↔ a < n ∧ actAt l a = some e ∧
      ∀ b, a < b → b < n → actAt l b ≠ some e := by
  induction n with
  | zero => simp [lastAct]
  | succ n ih =>
    change (if actAt l n = some e then some n else lastAct l e n) = some a ↔ _
    split_ifs with h
    · constructor
      · rintro ⟨⟩
        exact ⟨Nat.lt_succ_self _, h, fun b hb hbn => by omega⟩
      · rintro ⟨ha, hae, hb⟩
        by_contra hne
        have han : a ≠ n := fun h' => hne (h' ▸ rfl)
        exact hb n (by omega) (Nat.lt_succ_self _) h
    · rw [ih]
      constructor
      · rintro ⟨ha, hae, hb⟩
        refine ⟨by omega, hae, fun b hab hbn => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hbn with hbn | rfl
        exacts [hb b hab hbn, h]
      · rintro ⟨ha, hae, hb⟩
        have han : a ≠ n := fun han => h (han ▸ hae)
        exact ⟨by omega, hae, fun b hab hbn => hb b hab (by omega)⟩

private theorem lastAct_eq_none {l : List (Option ℕ)} {e n : ℕ} :
    lastAct l e n = none ↔ ∀ a < n, actAt l a ≠ some e := by
  induction n with
  | zero => simp [lastAct]
  | succ n ih =>
    change (if actAt l n = some e then some n else lastAct l e n) = none ↔ _
    split_ifs with h
    · simp only [false_iff, not_forall]
      exact ⟨n, Nat.lt_succ_self _, fun h' => h' h⟩
    · rw [ih]
      constructor
      · intro hb a ha
        rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
        exacts [hb a ha, h]
      · exact fun hb a ha => hb a (by omega)

/-- Index `e` is flagged at stage `s`: some `y ≤ s` triggers `e` at `s` but had not triggered `e`
when `e` last acted. -/
private def Flagged (i : Code) (l : List (Option ℕ)) (e s : ℕ) : Prop :=
  ∃ y < s + 1, Triggers Φ i e y s ∧ ∀ a, lastAct l e s = some a → ¬Triggers Φ i e y a

/-- Index `e` is a candidate to act at stage `s` for input `x` and value `z`: `e ≤ s`, `e` is
flagged, `e` does not halt on `x` within `z`, and every unflagged index of higher priority halts on
`x` within `z`. -/
private def Cand (i : Code) (l : List (Option ℕ)) (x z e s : ℕ) : Prop :=
  e ≤ s ∧ Flagged Φ i l e s ∧ ¬Halts Φ (ofNat Code e) x z ∧
    ∀ e' < key l e s, key l e' s < key l e s → ¬Flagged Φ i l e' s →
      Halts Φ (ofNat Code e') x z

/-- The candidate of least key at stage `s` (the least index among candidates of least key). -/
private noncomputable def actor (i : Code) (l : List (Option ℕ)) (x z s : ℕ) : Option ℕ :=
  bfind (fun e => @decide (Cand Φ i l x z e s ∧ ∀ e' < s + 1, Cand Φ i l x z e' s →
    key l e s ≤ key l e' s) (Classical.dec _)) 0 (s + 1)

/-- Before value `z`, input `x` received no value: `i` does not halt on `x` within any `z' < z`
and no index acted at a stage `⟪x, z'⟫`. -/
private def UndefBefore (i : Code) (l : List (Option ℕ)) (x z : ℕ) : Prop :=
  ∀ z' < z, ¬Halts Φ i x z' ∧ actAt l (Nat.pair x z') = none

/-- One stage `s = ⟪x, z⟫`, given the history `l` of the stages `< s`. -/
private noncomputable def step (i : Code) (l : List (Option ℕ)) : Option ℕ :=
  @ite _ (UndefBefore Φ i l (Nat.unpair l.length).1 (Nat.unpair l.length).2) (Classical.dec _)
    (actor Φ i l (Nat.unpair l.length).1 (Nat.unpair l.length).2 l.length) none

/-- The history of the stages `< n`. -/
private noncomputable def hist (i : Code) : ℕ → List (Option ℕ)
  | 0 => []
  | n + 1 => hist i n ++ [step Φ i (hist i n)]

/-- The index that acts at stage `s`, if any. -/
private noncomputable def act (i : Code) (s : ℕ) : Option ℕ := step Φ i (hist Φ i s)

/-- Input `x` receives its value at stage `⟪x, z⟫`: no earlier stage `⟪x, z'⟫` did, and at stage
`⟪x, z⟫` either an index acts or `i` halts on `x` within `z`. -/
private def Defd (i : Code) (x z : ℕ) : Prop :=
  (∀ z' < z, ¬Halts Φ i x z' ∧ act Φ i (Nat.pair x z') = none) ∧
    (act Φ i (Nat.pair x z) ≠ none ∨ Halts Φ i x z)

/-- The value given to `x` at stage `⟪x, z⟫`: `z` if an index acts there, and otherwise
`max z (φ_i x)`. -/
private noncomputable def val (i : Code) (x z : ℕ) : ℕ :=
  (act Φ i (Nat.pair x z)).elim (max z (gv Φ i x z)) fun _ => z

/-! ### Computability -/

private theorem computable_actAt {α : Type*} [Primcodable α] {l : α → List (Option ℕ)}
    {a : α → ℕ} (hl : Computable l) (ha : Computable a) :
    Computable fun x => actAt (l x) (a x) :=
  (Primrec.list_getD none).to_comp.comp hl ha

private theorem computablePred_eq {α σ : Type*} [Primcodable α] [Primcodable σ]
    {f g : α → σ} (hf : Computable f) (hg : Computable g) : ComputablePred fun a => f a = g a := by
  classical
  exact (Primrec.eq.decide.to_comp.comp hf hg).computablePred

private theorem computablePred_triggers {α : Type*} [Primcodable α] {i : α → Code}
    {e y s : α → ℕ} (hi : Computable i) (he : Computable e) (hy : Computable y)
    (hs : Computable s) : ComputablePred fun a => Triggers Φ (i a) (e a) (y a) (s a) :=
  (ComputablePred.nat_le hy hs).and ((computablePred_halts Φ hi hy hs).and
    (computablePred_halts Φ ((Computable.ofNat Code).comp he) hy
      (computable_gv Φ hi hy hs)).not)

private theorem primrec_lastAct :
    Primrec fun q : List (Option ℕ) × ℕ × ℕ => lastAct q.1 q.2.1 q.2.2 := by
  have h : Primrec₂ fun (a : List (Option ℕ) × ℕ) (n : ℕ) => Nat.rec (motive := fun _ => Option ℕ)
      none (fun k r => if actAt a.1 k = some a.2 then some k else r) n :=
    Primrec.nat_rec (Primrec.const none) (Primrec.ite
      (Primrec.eq.comp ((Primrec.list_getD none).comp (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd)) (Primrec.option_some.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂
  exact (h.comp (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)).of_eq fun q => rfl

private theorem computable_lastAct {α : Type*} [Primcodable α] {l : α → List (Option ℕ)}
    {e n : α → ℕ} (hl : Computable l) (he : Computable e) (hn : Computable n) :
    Computable fun a => lastAct (l a) (e a) (n a) :=
  primrec_lastAct.to_comp.comp (hl.pair (he.pair hn))

private theorem computable_key {α : Type*} [Primcodable α] {l : α → List (Option ℕ)}
    {e n : α → ℕ} (hl : Computable l) (he : Computable e) (hn : Computable n) :
    Computable fun a => key (l a) (e a) (n a) := by
  refine (Computable.option_casesOn (computable_lastAct hl he hn)
    (Primrec.nat_double.to_comp.comp he)
    (Primrec.nat_double_succ.to_comp.comp Computable.snd).to₂).of_eq fun a => ?_
  unfold key
  cases lastAct (l a) (e a) (n a) <;> rfl

/-- `∀ b, o a = some b → p a b` is computable when `o` and `p` are. -/
private theorem computablePred_forall_option {α : Type*} [Primcodable α] {o : α → Option ℕ}
    {p : α → ℕ → Prop} (ho : Computable o) (hp : ComputablePred fun q : α × ℕ => p q.1 q.2) :
    ComputablePred fun a => ∀ b, o a = some b → p a b := by
  obtain ⟨f, hf, hfp⟩ := ComputablePred.computable_iff.1 hp
  refine ComputablePred.computable_iff.2 ⟨fun a => (o a).elim true fun b => f (a, b),
    (Computable.option_casesOn ho (Computable.const true) (hf.comp
      (Computable.fst.pair Computable.snd)).to₂).of_eq fun a => ?_, funext fun a => ?_⟩
  · cases o a <;> rfl
  · have hpq : ∀ b, p a b ↔ f (a, b) = true := fun b => by
      rw [show p a b = (fun q : α × ℕ => p q.1 q.2) (a, b) from rfl, hfp]
    dsimp only
    cases h : o a with
    | none => simp
    | some b => simpa using hpq b

private theorem computablePred_flagged {α : Type*} [Primcodable α] {i : α → Code}
    {l : α → List (Option ℕ)} {e s : α → ℕ} (hi : Computable i) (hl : Computable l)
    (he : Computable e) (hs : Computable s) :
    ComputablePred fun a => Flagged Φ (i a) (l a) (e a) (s a) := by
  refine ComputablePred.exists_lt (p := fun a y => Triggers Φ (i a) (e a) y (s a) ∧
    ∀ b, lastAct (l a) (e a) (s a) = some b → ¬Triggers Φ (i a) (e a) y b) ?_
    (Computable.succ.comp hs)
  have hi' := hi.comp (Computable.fst (α := α) (β := ℕ))
  have he' := he.comp (Computable.fst (α := α) (β := ℕ))
  have hs' := hs.comp (Computable.fst (α := α) (β := ℕ))
  refine (computablePred_triggers Φ hi' he' Computable.snd hs').and
    (computablePred_forall_option (computable_lastAct (hl.comp Computable.fst) he' hs') ?_)
  exact (computablePred_triggers Φ (hi.comp (Computable.fst.comp Computable.fst))
    (he.comp (Computable.fst.comp Computable.fst)) (Computable.snd.comp Computable.fst)
    Computable.snd).not

private theorem computablePred_cand {α : Type*} [Primcodable α] {i : α → Code}
    {l : α → List (Option ℕ)} {x z e s : α → ℕ} (hi : Computable i) (hl : Computable l)
    (hx : Computable x) (hz : Computable z) (he : Computable e) (hs : Computable s) :
    ComputablePred fun a => Cand Φ (i a) (l a) (x a) (z a) (e a) (s a) := by
  refine (ComputablePred.nat_le he hs).and ((computablePred_flagged Φ hi hl he hs).and
    ((computablePred_halts Φ ((Computable.ofNat Code).comp he) hx hz).not.and ?_))
  refine ComputablePred.forall_lt (p := fun a e' => key (l a) e' (s a) < key (l a) (e a) (s a) →
    ¬Flagged Φ (i a) (l a) e' (s a) → Halts Φ (ofNat Code e') (x a) (z a)) ?_
    (computable_key hl he hs)
  have hl' := hl.comp (Computable.fst (α := α) (β := ℕ))
  have hs' := hs.comp (Computable.fst (α := α) (β := ℕ))
  exact (ComputablePred.nat_lt (computable_key hl' Computable.snd hs')
    (computable_key hl' (he.comp Computable.fst) hs')).imp
    ((computablePred_flagged Φ (hi.comp Computable.fst) hl' Computable.snd hs').not.imp
      (computablePred_halts Φ ((Computable.ofNat Code).comp Computable.snd)
        (hx.comp Computable.fst) (hz.comp Computable.fst)))

private theorem computable_actor {α : Type*} [Primcodable α] {i : α → Code}
    {l : α → List (Option ℕ)} {x z s : α → ℕ} (hi : Computable i) (hl : Computable l)
    (hx : Computable x) (hz : Computable z) (hs : Computable s) :
    Computable fun a => actor Φ (i a) (l a) (x a) (z a) (s a) := by
  have hi' := hi.comp (Computable.fst (α := α) (β := ℕ))
  have hl' := hl.comp (Computable.fst (α := α) (β := ℕ))
  have hx' := hx.comp (Computable.fst (α := α) (β := ℕ))
  have hz' := hz.comp (Computable.fst (α := α) (β := ℕ))
  have hs' := hs.comp (Computable.fst (α := α) (β := ℕ))
  have hp : ComputablePred fun q : α × ℕ => Cand Φ (i q.1) (l q.1) (x q.1) (z q.1) q.2 (s q.1) ∧
      ∀ e' < s q.1 + 1, Cand Φ (i q.1) (l q.1) (x q.1) (z q.1) e' (s q.1) →
        key (l q.1) q.2 (s q.1) ≤ key (l q.1) e' (s q.1) := by
    refine (computablePred_cand Φ hi' hl' hx' hz' Computable.snd hs').and ?_
    refine ComputablePred.forall_lt (p := fun q e' =>
      Cand Φ (i q.1) (l q.1) (x q.1) (z q.1) e' (s q.1) →
        key (l q.1) q.2 (s q.1) ≤ key (l q.1) e' (s q.1)) ?_ (Computable.succ.comp hs')
    have hl'' := hl.comp (Computable.fst.comp (Computable.fst (α := α × ℕ) (β := ℕ)))
    have hs'' := hs.comp (Computable.fst.comp (Computable.fst (α := α × ℕ) (β := ℕ)))
    exact (computablePred_cand Φ (hi.comp (Computable.fst.comp Computable.fst)) hl''
      (hx.comp (Computable.fst.comp Computable.fst)) (hz.comp (Computable.fst.comp Computable.fst))
      Computable.snd hs'').imp (ComputablePred.nat_le
        (computable_key hl'' (Computable.snd.comp Computable.fst) hs'')
        (computable_key hl'' Computable.snd hs''))
  exact computable_bfind (@ComputablePred.decide _ _ _ (fun _ => Classical.dec _) hp).to₂
    (Computable.const 0) (Computable.succ.comp hs)

private theorem computablePred_undefBefore {α : Type*} [Primcodable α] {i : α → Code}
    {l : α → List (Option ℕ)} {x z : α → ℕ} (hi : Computable i) (hl : Computable l)
    (hx : Computable x) (hz : Computable z) :
    ComputablePred fun a => UndefBefore Φ (i a) (l a) (x a) (z a) := by
  refine ComputablePred.forall_lt (p := fun a z' => ¬Halts Φ (i a) (x a) z' ∧
    actAt (l a) (Nat.pair (x a) z') = none) ?_ hz
  have hx' := hx.comp (Computable.fst (α := α) (β := ℕ))
  exact (computablePred_halts Φ (hi.comp Computable.fst) hx' Computable.snd).not.and
    (computablePred_eq (computable_actAt (hl.comp Computable.fst)
      (Primrec₂.natPair.to_comp.comp hx' Computable.snd)) (Computable.const none))

private theorem computable_step : Computable fun q : Code × List (Option ℕ) => step Φ q.1 q.2 := by
  have hn : Computable fun q : Code × List (Option ℕ) => q.2.length :=
    Computable.list_length.comp Computable.snd
  have hx : Computable fun q : Code × List (Option ℕ) => (Nat.unpair q.2.length).1 :=
    Computable.fst.comp (Primrec.unpair.to_comp.comp hn)
  have hz : Computable fun q : Code × List (Option ℕ) => (Nat.unpair q.2.length).2 :=
    Computable.snd.comp (Primrec.unpair.to_comp.comp hn)
  have hu := computablePred_undefBefore Φ Computable.fst Computable.snd hx hz
  refine (Computable.cond (@ComputablePred.decide _ _ _ (fun _ => Classical.dec _) hu)
    (computable_actor Φ Computable.fst Computable.snd hx hz hn)
    (Computable.const none)).of_eq fun q => ?_
  unfold step
  exact @Bool.cond_decide _ _ (Classical.dec _) _ _

private theorem computable_hist : Computable fun q : Code × ℕ => hist Φ q.1 q.2 := by
  have h : Computable fun q : Code × ℕ => Nat.rec (motive := fun _ => List (Option ℕ)) []
      (fun _ (IH : List (Option ℕ)) => IH ++ [step Φ q.1 IH]) q.2 := by
    refine Computable.nat_rec (h := fun (q : Code × ℕ) (p : ℕ × List (Option ℕ)) =>
      p.2 ++ [step Φ q.1 p.2]) Computable.snd (Computable.const []) ?_
    exact (Computable.list_append.comp (Computable.snd.comp Computable.snd)
      (Computable.list_cons.comp ((computable_step Φ).comp ((Computable.fst.comp
        Computable.fst).pair (Computable.snd.comp Computable.snd))) (Computable.const []))).to₂
  refine h.of_eq fun q => ?_
  obtain ⟨i, n⟩ := q
  induction n with
  | zero => rfl
  | succ n ih => rw [hist, ← ih]

private theorem computable_act {α : Type*} [Primcodable α] {i : α → Code} {s : α → ℕ}
    (hi : Computable i) (hs : Computable s) : Computable fun a => act Φ (i a) (s a) :=
  ((computable_step Φ).comp (hi.pair ((computable_hist Φ).comp (hi.pair hs)))).of_eq
    fun _ => rfl

private theorem computablePred_defd {α : Type*} [Primcodable α] {i : α → Code} {x z : α → ℕ}
    (hi : Computable i) (hx : Computable x) (hz : Computable z) :
    ComputablePred fun a => Defd Φ (i a) (x a) (z a) := by
  refine (ComputablePred.forall_lt (p := fun a z' => ¬Halts Φ (i a) (x a) z' ∧
    act Φ (i a) (Nat.pair (x a) z') = none) ?_ hz).and ?_
  · have hx' := hx.comp (Computable.fst (α := α) (β := ℕ))
    exact (computablePred_halts Φ (hi.comp Computable.fst) hx' Computable.snd).not.and
      (computablePred_eq (computable_act Φ (hi.comp Computable.fst)
        (Primrec₂.natPair.to_comp.comp hx' Computable.snd)) (Computable.const none))
  · exact (computablePred_eq (computable_act Φ hi (Primrec₂.natPair.to_comp.comp hx hz))
      (Computable.const none)).not.or (computablePred_halts Φ hi hx hz)

private theorem computable_val {α : Type*} [Primcodable α] {i : α → Code} {x z : α → ℕ}
    (hi : Computable i) (hx : Computable x) (hz : Computable z) :
    Computable fun a => val Φ (i a) (x a) (z a) := by
  refine (Computable.option_casesOn (computable_act Φ hi (Primrec₂.natPair.to_comp.comp hx hz))
    (Primrec.nat_max.to_comp.comp hz (computable_gv Φ hi hx hz))
    (hz.comp Computable.fst).to₂).of_eq fun a => ?_
  unfold val
  cases act Φ (i a) (Nat.pair (x a) (z a)) <;> rfl

/-! ### The history -/

variable {Φ}

private theorem hist_eq (i : Code) (n : ℕ) : hist Φ i n = (List.range n).map (act Φ i) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [hist, List.range_succ, List.map_append, ← ih]; rfl

private theorem length_hist (i : Code) (n : ℕ) : (hist Φ i n).length = n := by
  rw [hist_eq, List.length_map, List.length_range]

private theorem actAt_hist (i : Code) {n a : ℕ} (h : a < n) :
    actAt (hist Φ i n) a = act Φ i a := by
  unfold actAt
  rw [hist_eq, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map,
    List.getElem_range]

private theorem lastAct_hist_eq_some {i : Code} {e n a : ℕ} :
    lastAct (hist Φ i n) e n = some a ↔
      a < n ∧ act Φ i a = some e ∧ ∀ b, a < b → b < n → act Φ i b ≠ some e := by
  rw [lastAct_eq_some]
  constructor
  · rintro ⟨ha, hae, hb⟩
    refine ⟨ha, (actAt_hist i ha).symm.trans hae, fun b hab hbn => ?_⟩
    rw [← actAt_hist i hbn]
    exact hb b hab hbn
  · rintro ⟨ha, hae, hb⟩
    refine ⟨ha, (actAt_hist i ha).trans hae, fun b hab hbn => ?_⟩
    rw [actAt_hist i hbn]
    exact hb b hab hbn

private theorem lastAct_hist_eq_none {i : Code} {e n : ℕ} :
    lastAct (hist Φ i n) e n = none ↔ ∀ a < n, act Φ i a ≠ some e := by
  rw [lastAct_eq_none]
  exact forall₂_congr fun a ha => by rw [actAt_hist i ha]

/-- If `e` does not act at the stages `[S, s)`, its last action before `s` is its last action
before `S`. -/
private theorem lastAct_hist_stable {i : Code} {e S s : ℕ} (hSs : S ≤ s)
    (h : ∀ b, S ≤ b → b < s → act Φ i b ≠ some e) :
    lastAct (hist Φ i s) e s = lastAct (hist Φ i S) e S := by
  cases hS : lastAct (hist Φ i S) e S with
  | none =>
    rw [lastAct_hist_eq_none] at hS ⊢
    intro a ha
    by_cases haS : a < S
    · exact hS a haS
    · exact h a (by omega) ha
  | some a =>
    obtain ⟨ha, hae, hb⟩ := lastAct_hist_eq_some.1 hS
    refine lastAct_hist_eq_some.2 ⟨by omega, hae, fun b hab hbs => ?_⟩
    by_cases hbS : b < S
    · exact hb b hab hbS
    · exact h b (by omega) hbs

private theorem key_hist_stable {i : Code} {e S s : ℕ} (hSs : S ≤ s)
    (h : ∀ b, S ≤ b → b < s → act Φ i b ≠ some e) :
    key (hist Φ i s) e s = key (hist Φ i S) e S := by
  unfold key
  rw [lastAct_hist_stable hSs h]

/-- If `e` acted at stage `a < s`, its last action before `s` is at least `a`. -/
private theorem le_lastAct_hist {i : Code} {e a s : ℕ} (ha : a < s)
    (hae : act Φ i a = some e) : ∃ a', lastAct (hist Φ i s) e s = some a' ∧ a ≤ a' := by
  cases h : lastAct (hist Φ i s) e s with
  | none => exact absurd hae (lastAct_hist_eq_none.1 h a ha)
  | some a' =>
    obtain ⟨-, -, hb⟩ := lastAct_hist_eq_some.1 h
    refine ⟨a', rfl, ?_⟩
    by_contra hlt
    exact hb a (by omega) ha hae

private theorem act_eq_some {i : Code} {s e : ℕ} :
    act Φ i s = some e ↔ UndefBefore Φ i (hist Φ i s) (Nat.unpair s).1 (Nat.unpair s).2 ∧
      actor Φ i (hist Φ i s) (Nat.unpair s).1 (Nat.unpair s).2 s = some e := by
  unfold act step
  rw [length_hist]
  split_ifs with h
  · exact ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩
  · exact ⟨fun h' => by simp at h', fun h' => absurd h'.1 h⟩

private theorem actor_eq_some {i : Code} {l : List (Option ℕ)} {x z s e : ℕ}
    (h : actor Φ i l x z s = some e) : Cand Φ i l x z e s ∧
      ∀ e' < s + 1, Cand Φ i l x z e' s → key l e s ≤ key l e' s := by
  obtain ⟨-, -, hb, -⟩ := bfind_eq_some.1 h
  exact @of_decide_eq_true _ (Classical.dec _) hb

/-- A candidate forces some index of no larger key to act. -/
private theorem actor_isSome {i : Code} {l : List (Option ℕ)} {x z s e : ℕ}
    (he : Cand Φ i l x z e s) : ∃ e'', actor Φ i l x z s = some e'' ∧ key l e'' s ≤ key l e s := by
  classical
  have hex : ∃ k, ∃ e' < s + 1, Cand Φ i l x z e' s ∧ key l e' s = k :=
    ⟨_, e, Nat.lt_succ_of_le he.1, he, rfl⟩
  obtain ⟨e₀, he₀s, he₀, hk₀⟩ := Nat.find_spec hex
  have hmin : ∀ e' < s + 1, Cand Φ i l x z e' s → key l e₀ s ≤ key l e' s :=
    fun e' he's he' => by
      rw [hk₀]
      exact Nat.find_min' hex ⟨e', he's, he', rfl⟩
  cases ha : actor Φ i l x z s with
  | none =>
    have h1 := bfind_eq_none.1 ha e₀ (Nat.zero_le _) (by omega)
    have h2 : Cand Φ i l x z e₀ s ∧ ∀ e' < s + 1, Cand Φ i l x z e' s →
        key l e₀ s ≤ key l e' s := ⟨he₀, hmin⟩
    exact absurd (@decide_eq_true _ (Classical.dec _) h2) (by rw [h1]; simp)
  | some e'' =>
    exact ⟨e'', rfl, (actor_eq_some ha).2 e (Nat.lt_succ_of_le he.1) he⟩

variable (Φ) in
/-- Before value `z`, input `x` received no value. -/
private def Unset (i : Code) (x z : ℕ) : Prop :=
  ∀ z' < z, ¬Halts Φ i x z' ∧ act Φ i (Nat.pair x z') = none

private theorem undefBefore_hist_iff {i : Code} {x z : ℕ} :
    UndefBefore Φ i (hist Φ i (Nat.pair x z)) x z ↔ Unset Φ i x z :=
  forall₂_congr fun z' hz' => by
    rw [actAt_hist i (Nat.pair_lt_pair_right x hz')]

private theorem act_pair_eq_some {i : Code} {x z e : ℕ}
    (h : act Φ i (Nat.pair x z) = some e) : Unset Φ i x z ∧
      Cand Φ i (hist Φ i (Nat.pair x z)) x z e (Nat.pair x z) ∧
      ∀ e' < Nat.pair x z + 1, Cand Φ i (hist Φ i (Nat.pair x z)) x z e' (Nat.pair x z) →
        key (hist Φ i (Nat.pair x z)) e (Nat.pair x z) ≤
          key (hist Φ i (Nat.pair x z)) e' (Nat.pair x z) := by
  rw [act_eq_some, Nat.unpair_pair] at h
  exact ⟨undefBefore_hist_iff.1 h.1, actor_eq_some h.2⟩

private theorem act_pair_exists {i : Code} {x z e : ℕ} (hu : Unset Φ i x z)
    (he : Cand Φ i (hist Φ i (Nat.pair x z)) x z e (Nat.pair x z)) :
    ∃ e'', act Φ i (Nat.pair x z) = some e'' ∧
      key (hist Φ i (Nat.pair x z)) e'' (Nat.pair x z) ≤
        key (hist Φ i (Nat.pair x z)) e (Nat.pair x z) := by
  obtain ⟨e'', h1, h2⟩ := actor_isSome he
  refine ⟨e'', ?_, h2⟩
  rw [act_eq_some, Nat.unpair_pair]
  exact ⟨undefBefore_hist_iff.2 hu, h1⟩

private theorem act_le {i : Code} {s e : ℕ} (h : act Φ i s = some e) : e ≤ s :=
  (actor_eq_some (act_eq_some.1 h).2).1.1

private theorem key_ge_of_act {i : Code} {e a s : ℕ} (ha : a < s) (hae : act Φ i a = some e) :
    2 * a + 1 ≤ key (hist Φ i s) e s := by
  obtain ⟨a', h, haa'⟩ := le_lastAct_hist ha hae
  unfold key
  rw [h]
  change 2 * a + 1 ≤ 2 * a' + 1
  omega

private theorem le_key_hist (i : Code) (e s : ℕ) : e ≤ key (hist Φ i s) e s := by
  unfold key
  cases h : lastAct (hist Φ i s) e s with
  | none => change e ≤ 2 * e; omega
  | some a =>
    have := act_le (lastAct_hist_eq_some.1 h).2.1
    change e ≤ 2 * a + 1
    omega

private theorem Defd.unique {i : Code} {x z₁ z₂ : ℕ} (h₁ : Defd Φ i x z₁) (h₂ : Defd Φ i x z₂) :
    z₁ = z₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨hh, ha⟩ := h₂.1 z₁ h
    exact h₁.2.elim (fun h' => h' ha) hh
  · obtain ⟨hh, ha⟩ := h₁.1 z₂ h
    exact h₂.2.elim (fun h' => h' ha) hh

private theorem exists_defd {i : Code} {x c : ℕ} (hc : Halts Φ i x c) : ∃ z, Defd Φ i x z := by
  classical
  have hH : ∃ b, Halts Φ i x b := ⟨c, hc⟩
  by_cases hact : ∃ z < Nat.find hH, act Φ i (Nat.pair x z) ≠ none
  · refine ⟨Nat.find hact, fun z' hz' => ⟨fun h => ?_, ?_⟩, Or.inl (Nat.find_spec hact).2⟩
    · exact Nat.find_min hH (hz'.trans (Nat.find_spec hact).1) h
    · by_contra hne
      exact Nat.find_min hact hz' ⟨hz'.trans (Nat.find_spec hact).1, hne⟩
  · push Not at hact
    exact ⟨Nat.find hH, fun z' hz' => ⟨Nat.find_min hH hz', hact z' hz'⟩,
      Or.inr (Nat.find_spec hH)⟩

private theorem le_val (i : Code) (x z : ℕ) : z ≤ val Φ i x z := by
  unfold val
  cases act Φ i (Nat.pair x z) with
  | none => exact le_max_left _ _
  | some _ => exact le_rfl

private theorem val_of_act {i : Code} {x z e : ℕ} (h : act Φ i (Nat.pair x z) = some e) :
    val Φ i x z = z := by
  unfold val
  rw [h]
  rfl

private theorem val_of_not_act {i : Code} {x z : ℕ} (h : act Φ i (Nat.pair x z) = none) :
    val Φ i x z = max z (gv Φ i x z) := by
  unfold val
  rw [h]
  rfl

end Naming

open Naming

/-- The **name** `Φ.name i` of the bound computed by program `i`, from the proof of the naming
theorem [Odifreddi1999, Theorem VII.3.6]: the value at `x` is assigned at the first stage
`⟪x, z⟫` at which input `x` receives a value in the priority construction. -/
noncomputable def name (i : Code) (x : ℕ) : Part ℕ :=
  (Nat.rfind fun z => Part.some (@decide (Defd Φ i x z) (Classical.dec _))).map (val Φ i x)

variable {Φ}

private theorem mem_name {i : Code} {x v : ℕ} :
    v ∈ Φ.name i x ↔ ∃ z, Defd Φ i x z ∧ val Φ i x z = v := by
  unfold name
  rw [Part.mem_map_iff]
  refine exists_congr fun z => and_congr_left fun _ => Nat.mem_rfind.trans ?_
  simp only [Part.mem_some_iff]
  constructor
  · rintro ⟨h, -⟩
    exact @of_decide_eq_true _ (Classical.dec _) h.symm
  · intro h
    refine ⟨(@decide_eq_true _ (Classical.dec _) h).symm, fun {m} hm => ?_⟩
    exact (@decide_eq_false _ (Classical.dec _) fun hm' => (Defd.unique hm' h ▸ hm).false).symm

variable (Φ)

/-- The names are uniformly partial recursive. -/
theorem partrec_name : Partrec₂ Φ.name := by
  have hd : Computable₂ fun (q : Code × ℕ) (z : ℕ) =>
      @decide (Defd Φ q.1 q.2 z) (Classical.dec _) :=
    (@ComputablePred.decide _ _ _ (fun _ => Classical.dec _)
      (computablePred_defd Φ (Computable.fst.comp Computable.fst)
        (Computable.snd.comp Computable.fst) Computable.snd)).to₂
  have hr : Partrec fun q : Code × ℕ =>
      Nat.rfind fun z => Part.some (@decide (Defd Φ q.1 q.2 z) (Classical.dec _)) :=
    Partrec.rfind hd.partrec₂
  exact hr.map (computable_val Φ (Computable.fst.comp Computable.fst)
    (Computable.snd.comp Computable.fst) Computable.snd).to₂

/-- The graph of each name is decidable, uniformly in the program: the set of names is
*measured*. -/
theorem computablePred_mem_name :
    ComputablePred fun q : Code × ℕ × ℕ => q.2.2 ∈ Φ.name q.1 q.2.1 := by
  have hp : ComputablePred fun p : (Code × ℕ × ℕ) × ℕ =>
      Defd Φ p.1.1 p.1.2.1 p.2 ∧ val Φ p.1.1 p.1.2.1 p.2 = p.1.2.2 :=
    (computablePred_defd Φ (Computable.fst.comp Computable.fst)
      (Computable.fst.comp (Computable.snd.comp Computable.fst)) Computable.snd).and
      (computablePred_eq (computable_val Φ (Computable.fst.comp Computable.fst)
        (Computable.fst.comp (Computable.snd.comp Computable.fst)) Computable.snd)
        (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  refine (ComputablePred.exists_lt (p := fun (q : Code × ℕ × ℕ) z =>
    Defd Φ q.1 q.2.1 z ∧ val Φ q.1 q.2.1 z = q.2.2) hp
    (Computable.succ.comp (Computable.snd.comp Computable.snd))).of_eq fun q => ?_
  rw [mem_name]
  constructor
  · rintro ⟨z, -, hz⟩
    exact ⟨z, hz⟩
  · rintro ⟨z, hd, hv⟩
    have := le_val (Φ := Φ) q.1 q.2.1 z
    exact ⟨z, by omega, hd, hv⟩

variable {Φ}

/-- A name is defined wherever the program it names halts. -/
theorem dom_name {i : Code} {x : ℕ} (h : (i.eval x).Dom) : (Φ.name i x).Dom := by
  obtain ⟨c, hc⟩ := Part.dom_iff_mem.1 ((Φ.dom_cost_iff i x).2 h)
  obtain ⟨z, hz⟩ := exists_defd (show Halts Φ i x c from ⟨c, hc, le_rfl⟩)
  exact Part.dom_iff_mem.2 ⟨_, mem_name.2 ⟨z, hz, rfl⟩⟩

namespace Naming

/-! ### Comparison with the bound

Fix a program `i` computing a total `t`, and the name `t'` of `i`. -/

private theorem gv_eq {i : Code} {t : ℕ → ℕ} (ht : ∀ n, t n ∈ i.eval n) {y b : ℕ}
    (h : Halts Φ i y b) : gv Φ i y b = t y :=
  gv_eq_of_mem h (ht y)

private theorem exists_halts {i : Code} {t : ℕ → ℕ} (ht : ∀ n, t n ∈ i.eval n) (y : ℕ) :
    ∃ c, Halts Φ i y c := by
  obtain ⟨c, hc⟩ := Part.dom_iff_mem.1 (Φ.dom_cost_of_total ht y)
  exact ⟨c, c, hc, le_rfl⟩

private theorem eventually_triggers {i : Code} {t : ℕ → ℕ} (ht : ∀ n, t n ∈ i.eval n) {e y : ℕ}
    (hy : ¬Halts Φ (ofNat Code e) y (t y)) : ∀ᶠ s in atTop, Triggers Φ i e y s := by
  obtain ⟨c, hc⟩ := exists_halts ht y
  filter_upwards [eventually_ge_atTop (y + c)] with s hs
  have hcs : Halts Φ i y s := halts_mono hc (by omega)
  exact ⟨by omega, hcs, by rwa [gv_eq ht hcs]⟩

private theorem not_halts_of_triggers {i : Code} {t : ℕ → ℕ} (ht : ∀ n, t n ∈ i.eval n)
    {e y s : ℕ} (h : Triggers Φ i e y s) : ¬Halts Φ (ofNat Code e) y (t y) := by
  have := h.2.2
  rwa [gv_eq ht h.2.1] at this

/-- (A) If program `e` halts within `t` almost everywhere, then `e` acts at only finitely many
stages: each action uses up one of the finitely many inputs where `e` exceeds `t`. -/
private theorem eventually_act_ne {i : Code} {t : ℕ → ℕ} (ht : ∀ n, t n ∈ i.eval n) {e : ℕ}
    (he : ∀ᶠ y in atTop, Halts Φ (ofNat Code e) y (t y)) :
    ∃ S, ∀ s, S ≤ s → act Φ i s ≠ some e := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  have hfin : ∀ᶠ s in atTop, ∀ y ∈ {y | y < N}, ¬Halts Φ (ofNat Code e) y (t y) →
      Triggers Φ i e y s :=
    (Set.finite_lt_nat N).eventually_all.2 fun y _ => by
      by_cases hy : Halts Φ (ofNat Code e) y (t y)
      · exact Eventually.of_forall fun _ h => absurd hy h
      · filter_upwards [eventually_triggers ht hy] with s hs _ using hs
  obtain ⟨S₁, hS₁⟩ := eventually_atTop.1 hfin
  by_cases hex : ∃ a, S₁ ≤ a ∧ act Φ i a = some e
  · obtain ⟨a, ha, hae⟩ := hex
    refine ⟨a + 1, fun s hs hse => ?_⟩
    obtain ⟨-, hfl, -⟩ := (actor_eq_some (act_eq_some.1 hse).2).1
    obtain ⟨y, -, hy, hy'⟩ := hfl
    obtain ⟨a', ha', haa'⟩ := le_lastAct_hist (show a < s by omega) hae
    have hyN : y < N := by
      by_contra hyN
      exact not_halts_of_triggers ht hy (hN y (by omega))
    exact hy' a' ha' (triggers_mono (hS₁ a ha y hyN (not_halts_of_triggers ht hy)) haa')
  · push Not at hex
    exact ⟨S₁, fun s hs => hex s hs⟩

private theorem name_eq_val {i : Code} {t' : ℕ → ℕ} (ht' : ∀ n, t' n ∈ Φ.name i n) {x z : ℕ}
    (hd : Defd Φ i x z) : t' x = val Φ i x z := by
  obtain ⟨z', hz', hv⟩ := mem_name.1 (ht' x)
  rw [← hv, Defd.unique hz' hd]

/-- (B) If program `e` acts at infinitely many stages, then `e` exceeds the name infinitely often:
each action at `⟪x, z⟫` gives `x` the value `z`, within which `e` does not halt on `x`. -/
private theorem frequently_not_halts {i : Code} {t' : ℕ → ℕ} (ht' : ∀ n, t' n ∈ Φ.name i n)
    {e : ℕ} (he : ∃ᶠ s in atTop, act Φ i s = some e) :
    ∃ᶠ x in atTop, ¬Halts Φ (ofNat Code e) x (t' x) := by
  rw [frequently_atTop]
  intro N
  have hfin : ∀ᶠ s in atTop, ∀ x ∈ {x | x < N}, ∀ z, Defd Φ i x z → s ≠ Nat.pair x z :=
    (Set.finite_lt_nat N).eventually_all.2 fun x _ => by
      by_cases hz : ∃ z, Defd Φ i x z
      · obtain ⟨z, hz⟩ := hz
        filter_upwards [eventually_gt_atTop (Nat.pair x z)] with s hs z' hz'
        rw [Defd.unique hz' hz]
        exact hs.ne'
      · exact Eventually.of_forall fun _ z hz' => absurd ⟨z, hz'⟩ hz
  obtain ⟨B, hB⟩ := eventually_atTop.1 hfin
  obtain ⟨s, hs, hse⟩ := frequently_atTop.1 he B
  obtain ⟨x, z, rfl⟩ : ∃ x z, Nat.pair x z = s := ⟨_, _, Nat.pair_unpair s⟩
  obtain ⟨hu, hc, -⟩ := act_pair_eq_some hse
  have hd : Defd Φ i x z := ⟨hu, Or.inl (by simp [hse])⟩
  refine ⟨x, ?_, ?_⟩
  · by_contra hx
    exact hB _ hs x (by simpa using hx) z hd rfl
  · rw [name_eq_val ht' hd, val_of_act hse]
    exact hc.2.2.1

/-- Eventually every acting index has key above `K`: each of the finitely many indices `≤ K`
moves above `K` once it acts at a stage `≥ K`. -/
private theorem eventually_lt_key_of_act (i : Code) (K : ℕ) :
    ∀ᶠ s in atTop, ∀ e'', act Φ i s = some e'' → K < key (hist Φ i s) e'' s := by
  have hfin : ∀ᶠ s in atTop, ∀ e'' ∈ {e'' | e'' < K + 1}, act Φ i s = some e'' →
      K < key (hist Φ i s) e'' s :=
    (Set.finite_lt_nat (K + 1)).eventually_all.2 fun e'' _ => by
      by_cases hex : ∃ a, K ≤ a ∧ act Φ i a = some e''
      · obtain ⟨a, ha, hae⟩ := hex
        filter_upwards [eventually_gt_atTop a] with s hs _
        have := key_ge_of_act hs hae
        omega
      · push Not at hex
        filter_upwards [eventually_ge_atTop K] with s hs h
        exact absurd h (hex s hs)
  filter_upwards [hfin] with s hs e'' he''
  by_cases hlt : e'' < K + 1
  · exact hs e'' hlt he''
  · have := le_key_hist (Φ := Φ) i e'' s
    omega

variable (Φ) in
/-- Index `e'` has key at most `K` and is not flagged at stage `s`. -/
private def Quiet (i : Code) (K e' s : ℕ) : Prop :=
  key (hist Φ i s) e' s ≤ K ∧ ¬Flagged Φ i (hist Φ i s) e' s

private theorem flagged_mono {i : Code} {l l' : List (Option ℕ)} {e s s' : ℕ}
    (h : Flagged Φ i l e s) (hs : s ≤ s') (hl : lastAct l' e s' = lastAct l e s) :
    Flagged Φ i l' e s' := by
  obtain ⟨y, hy, hyt, hya⟩ := h
  exact ⟨y, by omega, triggers_mono hyt hs, fun a ha => hya a (hl ▸ ha)⟩

/-- Whether index `e'` is quiet is eventually constant. -/
private theorem quiet_eventually_const (i : Code) (K e' : ℕ) :
    (∀ᶠ s in atTop, Quiet Φ i K e' s) ∨ ∀ᶠ s in atTop, ¬Quiet Φ i K e' s := by
  by_cases hex : ∃ a, K ≤ a ∧ act Φ i a = some e'
  · obtain ⟨a, ha, hae⟩ := hex
    refine Or.inr ?_
    filter_upwards [eventually_gt_atTop a] with s hs hq
    have := key_ge_of_act hs hae
    exact absurd hq.1 (by omega)
  · push Not at hex
    have hst : ∀ s, K ≤ s → lastAct (hist Φ i s) e' s = lastAct (hist Φ i K) e' K :=
      fun s hs => lastAct_hist_stable hs fun b hb _ => hex b hb
    have hkst : ∀ s, K ≤ s → key (hist Φ i s) e' s = key (hist Φ i K) e' K :=
      fun s hs => key_hist_stable hs fun b hb _ => hex b hb
    by_cases hfl : ∃ s₀, K ≤ s₀ ∧ Flagged Φ i (hist Φ i s₀) e' s₀
    · obtain ⟨s₀, hs₀, hf⟩ := hfl
      refine Or.inr ?_
      filter_upwards [eventually_ge_atTop s₀] with s hs hq
      exact hq.2 (flagged_mono hf hs ((hst s (by omega)).trans (hst s₀ hs₀).symm))
    · push Not at hfl
      by_cases hk : key (hist Φ i K) e' K ≤ K
      · refine Or.inl ?_
        filter_upwards [eventually_ge_atTop K] with s hs
        exact ⟨(hkst s hs).trans_le hk, hfl s hs⟩
      · refine Or.inr ?_
        filter_upwards [eventually_ge_atTop K] with s hs hq
        exact hk ((hkst s hs).symm.trans_le hq.1)

/-- An index that is eventually always quiet halts within `t` almost everywhere: otherwise some
input would trigger it after its last action. -/
private theorem halts_of_eventually_quiet {i : Code} {t : ℕ → ℕ} (ht : ∀ n, t n ∈ i.eval n)
    {K e' : ℕ} (hq : ∀ᶠ s in atTop, Quiet Φ i K e' s) :
    ∀ᶠ y in atTop, Halts Φ (ofNat Code e') y (t y) := by
  obtain ⟨S₂, hS₂⟩ := eventually_atTop.1 hq
  have hna : ∀ s, S₂ ≤ s → act Φ i s ≠ some e' := fun s hs hse =>
    (hS₂ s hs).2 (actor_eq_some (act_eq_some.1 hse).2).1.2.1
  filter_upwards [eventually_ge_atTop S₂] with y hy
  by_contra hny
  obtain ⟨c, hc⟩ := exists_halts ht y
  have htr : Triggers Φ i e' y (S₂ + y + c) := by
    have hcs : Halts Φ i y (S₂ + y + c) := halts_mono hc (by omega)
    exact ⟨by omega, hcs, by rwa [gv_eq ht hcs]⟩
  refine (hS₂ (S₂ + y + c) (by omega)).2 ⟨y, by omega, htr, fun a ha hta => ?_⟩
  rw [lastAct_hist_stable (show S₂ ≤ S₂ + y + c by omega) fun b hb _ => hna b hb] at ha
  have := (lastAct_hist_eq_some.1 ha).1
  have := hta.1
  omega

/-- (C) If program `e` acts at only finitely many stages, then almost everywhere `e` halts within
`t` exactly when it halts within the name. -/
private theorem halts_iff {i : Code} {t t' : ℕ → ℕ} (ht : ∀ n, t n ∈ i.eval n)
    (ht' : ∀ n, t' n ∈ Φ.name i n) {e S₀ : ℕ} (hS₀ : ∀ s, S₀ ≤ s → act Φ i s ≠ some e) :
    ∀ᶠ x in atTop, (Halts Φ (ofNat Code e) x (t x) ↔ Halts Φ (ofNat Code e) x (t' x)) := by
  classical
  have heK₀ := le_key_hist (Φ := Φ) i e S₀
  generalize hK : key (hist Φ i S₀) e S₀ = K at heK₀
  have hkey : ∀ s, S₀ ≤ s → key (hist Φ i s) e s = K := fun s hs =>
    (key_hist_stable hs fun b hb _ => hS₀ b hb).trans hK
  have heK : e ≤ K := heK₀
  have hV : ∀ e', ∀ᶠ s in atTop, (Quiet Φ i K e' s ↔ ∀ᶠ s' in atTop, Quiet Φ i K e' s') := by
    intro e'
    rcases quiet_eventually_const (Φ := Φ) i K e' with h | h
    · filter_upwards [h] with s hs
      exact iff_of_true hs h
    · filter_upwards [h] with s hs
      exact iff_of_false hs fun h' => (h.and h').exists.elim fun _ hs' => hs'.1 hs'.2
  have hall : ∀ᶠ s in atTop, ∀ e' ∈ {e' | e' < K + 1},
      (Quiet Φ i K e' s ↔ ∀ᶠ s' in atTop, Quiet Φ i K e' s') :=
    (Set.finite_lt_nat (K + 1)).eventually_all.2 fun e' _ => hV e'
  have hH : ∀ᶠ y in atTop, ∀ e' ∈ {e' | e' < K + 1}, (∀ᶠ s' in atTop, Quiet Φ i K e' s') →
      Halts Φ (ofNat Code e') y (t y) :=
    (Set.finite_lt_nat (K + 1)).eventually_all.2 fun e' _ => by
      by_cases hq : ∀ᶠ s' in atTop, Quiet Φ i K e' s'
      · filter_upwards [halts_of_eventually_quiet ht hq] with y hy _ using hy
      · exact Eventually.of_forall fun _ h => absurd h hq
  obtain ⟨S, hS⟩ := eventually_atTop.1 ((eventually_lt_key_of_act (Φ := Φ) i K).and
    (hall.and (eventually_ge_atTop (S₀ + K))))
  filter_upwards [hH, eventually_ge_atTop S] with x hHx hxS
  have hP : ∃ b, ∀ e' < K + 1, (∀ᶠ s' in atTop, Quiet Φ i K e' s') →
      Halts Φ (ofNat Code e') x b := ⟨t x, hHx⟩
  obtain ⟨M, hM, hMt, hMmin⟩ : ∃ M, (∀ e' < K + 1, (∀ᶠ s' in atTop, Quiet Φ i K e' s') →
      Halts Φ (ofNat Code e') x M) ∧ M ≤ t x ∧ ∀ b < M, ¬∀ e' < K + 1,
        (∀ᶠ s' in atTop, Quiet Φ i K e' s') → Halts Φ (ofNat Code e') x b :=
    ⟨Nat.find hP, Nat.find_spec hP, Nat.find_min' hP hHx, fun b hb => Nat.find_min hP hb⟩
  obtain ⟨z₁, hz₁, hv⟩ := mem_name.1 (ht' x)
  rw [← hv]
  by_cases hMz : M ≤ z₁
  · have hSM : S ≤ Nat.pair x M := hxS.trans (Nat.left_le_pair x M)
    obtain ⟨hlate, hq, hSK⟩ := hS _ hSM
    have hkM := hkey _ (show S₀ ≤ Nat.pair x M by omega)
    have heM : Halts Φ (ofNat Code e) x M := by
      by_cases hve : ∀ᶠ s' in atTop, Quiet Φ i K e s'
      · exact hM e (by omega) hve
      · by_contra hne
        have hfl : Flagged Φ i (hist Φ i (Nat.pair x M)) e (Nat.pair x M) := by
          by_contra hnf
          exact hve ((hq e (show e < K + 1 by omega)).1 ⟨hkM.le, hnf⟩)
        have hcand : Cand Φ i (hist Φ i (Nat.pair x M)) x M e (Nat.pair x M) := by
          refine ⟨by omega, hfl, hne, fun e' _ hk hnf => ?_⟩
          have he'K := le_key_hist (Φ := Φ) i e' (Nat.pair x M)
          exact hM e' (by omega) ((hq e' (show e' < K + 1 by omega)).1 ⟨by omega, hnf⟩)
        have hun : Unset Φ i x M := fun z' hz' => hz₁.1 z' (by omega)
        obtain ⟨e'', he'', hk''⟩ := act_pair_exists hun hcand
        have := hlate e'' he''
        omega
    have := le_val (Φ := Φ) i x z₁
    exact ⟨fun _ => halts_mono heM (by omega), fun _ => halts_mono heM hMt⟩
  · push Not at hMz
    have hSz : S ≤ Nat.pair x z₁ := hxS.trans (Nat.left_le_pair x z₁)
    obtain ⟨hlate, hq, -⟩ := hS _ hSz
    have hna : act Φ i (Nat.pair x z₁) = none := by
      cases hc : act Φ i (Nat.pair x z₁) with
      | none => rfl
      | some e'' =>
        exfalso
        obtain ⟨-, hcand, -⟩ := act_pair_eq_some hc
        have hlt := hlate e'' hc
        refine hMmin z₁ hMz fun e' he' hve => ?_
        have hqe := (hq e' he').2 hve
        have hqk := hqe.1
        have he'' := le_key_hist (Φ := Φ) i e' (Nat.pair x z₁)
        exact hcand.2.2.2 e' (by omega) (by omega) hqe.2
    have hH₁ : Halts Φ i x z₁ := hz₁.2.resolve_left fun h => h hna
    rw [val_of_not_act hna, gv_eq ht hH₁, max_eq_right (by omega)]

/-- The naming property for every program, total or not. -/
private theorem eventually_halts_iff {i : Code} {t t' : ℕ → ℕ} (ht : ∀ n, t n ∈ i.eval n)
    (ht' : ∀ n, t' n ∈ Φ.name i n) (c : Code) :
    (∀ᶠ x in atTop, Halts Φ c x (t x)) ↔ ∀ᶠ x in atTop, Halts Φ c x (t' x) := by
  rw [← ofNat_encode c]
  constructor
  · intro h
    obtain ⟨S₀, hS₀⟩ := eventually_act_ne ht h
    filter_upwards [h, halts_iff ht ht' hS₀] with x hx hiff using hiff.1 hx
  · intro h
    by_cases hfin : ∃ S₀, ∀ s, S₀ ≤ s → act Φ i s ≠ some (encode c)
    · obtain ⟨S₀, hS₀⟩ := hfin
      filter_upwards [h, halts_iff ht ht' hS₀] with x hx hiff using hiff.2 hx
    · have hfr : ∃ᶠ s in atTop, act Φ i s = some (encode c) := by
        rw [frequently_atTop]
        intro a
        by_contra hne
        push Not at hne
        exact hfin ⟨a, hne⟩
      exact (((frequently_not_halts ht' hfr).and_eventually h).exists.elim
        fun _ hx => hx.1 hx.2).elim

end Naming

variable (Φ) in
/-- The name of a program that halts everywhere halts everywhere. -/
theorem exists_name_total {i : Code} {t : ℕ → ℕ} (ht : ∀ n, t n ∈ i.eval n) :
    ∃ t' : ℕ → ℕ, ∀ n, t' n ∈ Φ.name i n :=
  ⟨fun n => (Φ.name i n).get (dom_name (Part.dom_iff_mem.2 ⟨_, ht n⟩)),
    fun _ => Part.get_mem _⟩

/-- **The naming property, pointwise.** Let program `i` compute the total function `t`, with name
`t'`. Every program `c`, total or not, halts within `t` almost everywhere if and only if it halts
within `t'` almost everywhere. -/
theorem eventually_cost_le_name_iff {i : Code} {t t' : ℕ → ℕ} (ht : ∀ n, t n ∈ i.eval n)
    (ht' : ∀ n, t' n ∈ Φ.name i n) (c : Code) :
    (∀ᶠ n in atTop, ∃ m ∈ Φ.cost c n, m ≤ t n) ↔ ∀ᶠ n in atTop, ∃ m ∈ Φ.cost c n, m ≤ t' n :=
  eventually_halts_iff ht ht' c

/-- The name of a total program defines the same complexity class: `C_{t'} = C_t`. -/
theorem complexityClass_name {i : Code} {t t' : ℕ → ℕ} (ht : ∀ n, t n ∈ i.eval n)
    (ht' : ∀ n, t' n ∈ Φ.name i n) : Φ.complexityClass t' = Φ.complexityClass t := by
  ext f
  simp only [mem_complexityClass]
  refine exists_congr fun c => and_congr_right fun hc => ?_
  have h := eventually_cost_le_name_iff ht ht' c
  simp only [← Φ.forall_mem_cost_iff_exists_of_total hc] at h
  exact h.symm

variable (Φ) in
/-- **The naming theorem** [Odifreddi1999, Theorem VII.3.6]. There is a computable map `h` on
programs such that

1. the predicate `φ_{h i} x = y` is decidable, uniformly in `i`, `x` and `y`;
2. if `φ_i` is total, so is `φ_{h i}`;
3. if `φ_i` is total, then `C_{φ_{h i}} = C_{φ_i}`.

So the measured set `{φ_{h i}}` contains a name for every complexity class `C_t` of a computable
`t`. -/
theorem naming_theorem :
    ∃ h : Code → Code, Computable h ∧
      ComputablePred (fun q : Code × ℕ × ℕ => q.2.2 ∈ (h q.1).eval q.2.1) ∧
      ∀ i : Code, ∀ t : ℕ → ℕ, (∀ n, t n ∈ i.eval n) →
        ∃ t' : ℕ → ℕ, (∀ n, t' n ∈ (h i).eval n) ∧
          Φ.complexityClass t' = Φ.complexityClass t := by
  have hF : Nat.Partrec fun n => Φ.name (ofNat Code (Nat.unpair n).1) (Nat.unpair n).2 :=
    Partrec.nat_iff.1 ((Φ.partrec_name.comp ((Computable.ofNat Code).comp
      (Computable.fst.comp Computable.unpair)) (Computable.snd.comp Computable.unpair)).of_eq
        fun _ => rfl)
  obtain ⟨c, hc⟩ := Code.exists_code.1 hF
  have hh : ∀ i x, (Code.curry c (encode i)).eval x = Φ.name i x := fun i x => by
    rw [Code.eval_curry, hc]
    simp only [Nat.unpair_pair, ofNat_encode]
  refine ⟨fun i => Code.curry c (encode i), Code.primrec₂_curry.to_comp.comp
    (Computable.const c) Computable.encode, ?_, fun i t ht => ?_⟩
  · refine (Φ.computablePred_mem_name).of_eq fun q => ?_
    rw [hh]
  · obtain ⟨t', ht'⟩ := Φ.exists_name_total ht
    exact ⟨t', fun n => (hh i n).symm ▸ ht' n, complexityClass_name ht ht'⟩

end Cslib.BlumComplexity.BlumMeasure
