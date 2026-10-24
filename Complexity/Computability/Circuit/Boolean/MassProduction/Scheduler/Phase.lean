/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.MassProduction.Scheduler.Basic
public import Complexity.Computability.Circuit.Boolean.MassProduction.Scheduler.State

/-!
# One scheduler phase

A phase starts from a state whose first `a` records are accepted and whose last `2 ^ p` records
are pending, and tests a fixed menu of direction tuples for the pending requests. For every menu
entry `e`, pending request `i` and scalar index `c`, the candidate point is the target of `i`
plus `scalar c • menu e i`; its bits are the target bits plus a fixed offset. A candidate is
*occupied* when it lies on an accepted line, and a *duplicate* when another request's candidate
for the same entry is the same point. A request is clean for an entry when none of its candidates
is occupied or a duplicate; this is exactly `LineCode.IsClean` (`clean_iff`). An entry succeeds
when at least half of the requests are clean, and the first successful entry is chosen. The
pending records, with their candidate lines for the chosen entry and their clean flags, are
sorted with clean records first; the first `⌈2 ^ p / 2⌉` of them are accepted (`next`).

For a universal menu some entry succeeds, so every accepted record is clean, which keeps the
state good (`good_next`).

## Main definitions

* `Cslib.Circuits.Boolean.MassProduction.Scheduler.pending`,
  `Cslib.Circuits.Boolean.MassProduction.Scheduler.accepted`,
  `Cslib.Circuits.Boolean.MassProduction.Scheduler.acceptedLines`: positions and lines of pending
  and accepted requests.
* `Cslib.Circuits.Boolean.MassProduction.Scheduler.candidate`: the bits of a candidate point.
* `Cslib.Circuits.Boolean.MassProduction.Scheduler.occupied`,
  `Cslib.Circuits.Boolean.MassProduction.Scheduler.duplicate`,
  `Cslib.Circuits.Boolean.MassProduction.Scheduler.clean`: conflict and cleanliness predicates.
* `Cslib.Circuits.Boolean.MassProduction.Scheduler.success`,
  `Cslib.Circuits.Boolean.MassProduction.Scheduler.chosen`,
  `Cslib.Circuits.Boolean.MassProduction.Scheduler.flag`,
  `Cslib.Circuits.Boolean.MassProduction.Scheduler.newLine`: menu selection and selected candidate
  flags and lines.
* `Cslib.Circuits.Boolean.MassProduction.Scheduler.enriched`,
  `Cslib.Circuits.Boolean.MassProduction.Scheduler.flagKey`,
  `Cslib.Circuits.Boolean.MassProduction.Scheduler.sortedPending`,
  `Cslib.Circuits.Boolean.MassProduction.Scheduler.next`: sorting pending records by cleanliness
  and forming the state after the phase.

## Main results

* `Cslib.Circuits.Boolean.MassProduction.Scheduler.clean_iff`: clean flags are `IsClean`.
* `Cslib.Circuits.Boolean.MassProduction.Scheduler.good_next`: a phase keeps the state good.

## References

* Adapted from MassProduction/Nonuniform/MenuClean.lean,
  MassProduction/Nonuniform/MenuSelection.lean,
  MassProduction/Nonuniform/PointConflicts.lean,
  MassProduction/Nonuniform/BufferedPhase.lean and
  MassProduction/Nonuniform/BufferStepCorrectness.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction],
  using the sorting network of
  [K. E. Batcher, *Sorting Networks and Their Applications*][Batcher1968].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MassProduction.Scheduler

open Finset BitString LineCode BitonicSort

variable {K : Type*} [Field K] {ℓ b s D p a r : ℕ}

section Definitions

variable (hk : a + arity p = 2 ^ D)

/-- The position of pending request `i`. -/
def pending (i : Fin (arity p)) : Fin (2 ^ D) := Fin.cast hk (Fin.natAdd a i)

/-- The position of accepted request `m`. -/
def accepted (m : Fin a) : Fin (2 ^ D) := Fin.cast hk (Fin.castAdd (arity p) m)

variable (bits : K ≃+ BitString b) (scalar : Fin s ≃ {c : K // c ≠ 0})
  (menu : Fin r → Fin (arity p) → Fin ℓ → K) (x : BitString (2 ^ D * width D (ℓ * b) s))

/-- The bits of candidate point `c` of request `i` for menu entry `e`: the target bits plus the
fixed bits of `scalar c • menu e i`. -/
def candidate (e : Fin r) (i : Fin (arity p)) (c : Fin s) : BitString (ℓ * b) :=
  target x (pending hk i) + pointBits bits ((scalar c : K) • menu e i)

/-- A candidate lies on an accepted line. -/
def occupied (e : Fin r) (i : Fin (arity p)) (c : Fin s) : Bool :=
  decide (∃ m : Fin a, ∃ c' : Fin s,
    line x (accepted hk m) c' = candidate hk bits scalar menu x e i c)

/-- Another candidate of the same menu entry is the same point. -/
def duplicate (e : Fin r) (i : Fin (arity p)) (c : Fin s) : Bool :=
  decide (∃ i' c', (i', c') ≠ (i, c) ∧
    candidate hk bits scalar menu x e i' c' = candidate hk bits scalar menu x e i c)

/-- No candidate of request `i` for entry `e` is occupied or a duplicate. -/
def clean (e : Fin r) (i : Fin (arity p)) : Bool :=
  decide (∀ c, occupied hk bits scalar menu x e i c = false ∧
    duplicate hk bits scalar menu x e i c = false)

/-- At least half of the pending requests are clean for entry `e`. -/
def success (e : Fin r) : Bool :=
  decide (arity p ≤ 2 * #{i | clean hk bits scalar menu x e i = true})

/-- Entry `e` is the first successful entry. -/
def chosen (e : Fin r) : Bool :=
  decide (success hk bits scalar menu x e = true ∧
    ∀ e' < e, success hk bits scalar menu x e' = false)

/-- Request `i` is clean for the chosen entry. -/
def flag (i : Fin (arity p)) : Bool :=
  decide (∃ e, chosen hk bits scalar menu x e = true ∧ clean hk bits scalar menu x e i = true)

/-- Bit `β` of candidate point `c` of request `i` for the chosen entry. -/
def newLine (i : Fin (arity p)) (c : Fin s) (β : Fin (ℓ * b)) : Bool :=
  decide (∃ e, chosen hk bits scalar menu x e = true ∧
    candidate hk bits scalar menu x e i c β = true)

/-- A pending record with its clean flag in front and its candidate line for the chosen entry. -/
def enriched (i : Fin (arity p)) : BitString (1 + width D (ℓ * b) s) :=
  Fin.append (fun _ => flag hk bits scalar menu x i)
    (Fin.append (label x (pending hk i)) (Fin.append (target x (pending hk i))
      fun q => newLine hk bits scalar menu x i (finProdFinEquiv.symm q).1
        (finProdFinEquiv.symm q).2))

/-- The flag key of an enriched record. -/
def flagKey : Fin 1 → Fin (1 + width D (ℓ * b) s) := Fin.castAdd _

/-- The enriched pending records, sorted with clean records first. -/
noncomputable def sortedPending : Fin (arity p) → BitString (1 + width D (ℓ * b) s) :=
  sort (fun record => toLex (record ∘ flagKey)) p false (enriched hk bits scalar menu x)

/-- The state after the phase: accepted records stay, and the sorted enriched pending records
follow without their flags. -/
noncomputable def next : BitString (2 ^ D * width D (ℓ * b) s) := fun q =>
  Fin.addCases (motive := fun _ => Bool)
    (fun m => x (finProdFinEquiv (accepted hk m, (finProdFinEquiv.symm q).2)))
    (fun j => sortedPending hk bits scalar menu x j (Fin.natAdd 1 (finProdFinEquiv.symm q).2))
    (Fin.cast hk.symm (finProdFinEquiv.symm q).1)

end Definitions

variable {hk : a + arity p = 2 ^ D}

/-- Pending request `i` sits `i` positions after the accepted block. -/
private theorem val_pending (i : Fin (arity p)) : (pending hk i).val = a + i.val := rfl

/-- Accepted request `m` sits at position `m`. -/
theorem val_accepted (m : Fin a) : (accepted (p := p) hk m).val = m.val := rfl

/-- Every position is accepted or pending. -/
theorem accepted_or_pending (m : Fin (2 ^ D)) :
    (∃ m', m = accepted hk m') ∨ ∃ i, m = pending hk i := by
  rcases Nat.lt_or_ge m.val a with h | h
  · exact Or.inl ⟨⟨m.val, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨m.val - a, by have := m.isLt; lia⟩,
      Fin.ext (by rw [val_pending]; dsimp only; lia)⟩

/-- A phase keeps the accepted records. -/
theorem next_accepted (bits : K ≃+ BitString b) (scalar : Fin s ≃ {c : K // c ≠ 0})
    (menu : Fin r → Fin (arity p) → Fin ℓ → K) (x : BitString (2 ^ D * width D (ℓ * b) s))
    (m : Fin a) (f : Fin (width D (ℓ * b) s)) :
    next hk bits scalar menu x (finProdFinEquiv (accepted hk m, f)) =
      x (finProdFinEquiv (accepted hk m, f)) := by
  simp only [next, Equiv.symm_apply_apply]
  rw [show Fin.cast hk.symm (accepted hk m) = Fin.castAdd (arity p) m from Fin.ext rfl,
    Fin.addCases_left]

/-- After a phase, the pending block holds the sorted enriched records without their flags. -/
theorem next_pending (bits : K ≃+ BitString b) (scalar : Fin s ≃ {c : K // c ≠ 0})
    (menu : Fin r → Fin (arity p) → Fin ℓ → K) (x : BitString (2 ^ D * width D (ℓ * b) s))
    (j : Fin (arity p)) (f : Fin (width D (ℓ * b) s)) :
    next hk bits scalar menu x (finProdFinEquiv (pending hk j, f)) =
      sortedPending hk bits scalar menu x j (Fin.natAdd 1 f) := by
  simp only [next, Equiv.symm_apply_apply]
  rw [show Fin.cast hk.symm (pending hk j) = Fin.natAdd a j from Fin.ext rfl, Fin.addCases_right]

section Correctness

variable [Fintype K] [DecidableEq K]
variable (bits : K ≃+ BitString b) (scalar : Fin s ≃ {c : K // c ≠ 0})
  (menu : Fin r → Fin (arity p) → Fin ℓ → K) {x : BitString (2 ^ D * width D (ℓ * b) s)}
  {T : Fin (2 ^ D) → Fin ℓ → K} {dirs : Fin (2 ^ D) → Fin ℓ → K}

/-- The accepted lines of a state, padded by unused slots. -/
def acceptedLines (a : ℕ) (T dirs : Fin (2 ^ D) → Fin ℓ → K) :
    Fin (2 ^ D) → Option ((Fin ℓ → K) × (Fin ℓ → K)) :=
  fun m => if m.val < a then some (T m, dirs m) else none

/-- The occupied points are the points of the accepted lines. -/
theorem mem_occupiedPoints_acceptedLines {w : Fin ℓ → K} :
    w ∈ occupiedPoints (acceptedLines a T dirs) ↔
      ∃ m : Fin (2 ^ D), m.val < a ∧ w ∈ puncturedLine (T m) (dirs m) := by
  simp only [occupiedPoints, mem_biUnion, mem_univ, true_and, acceptedLines]
  constructor
  · rintro ⟨m, hm⟩
    split_ifs at hm with h
    · exact ⟨m, h, hm⟩
    · exact absurd hm (Finset.notMem_empty w)
  · rintro ⟨m, h, hm⟩
    exact ⟨m, by simpa only [h, ↓reduceIte, Option.elim_some] using hm⟩

variable (htarget : ∀ m, target x m = pointBits bits (T m))
include htarget

omit [Fintype K] [DecidableEq K] in
/-- A candidate lists the bits of its point. -/
private theorem candidate_eq (e : Fin r) (i : Fin (arity p)) (c : Fin s) :
    candidate hk bits scalar menu x e i c =
      pointBits bits (T (pending hk i) + (scalar c : K) • menu e i) := by
  rw [candidate, htarget, pointBits_add]

variable (hline : ∀ m, m.val < a → dirs m ≠ 0 ∧
  ∀ c, line x m c = pointBits bits (T m + (scalar c : K) • dirs m))
include hline

/-- A candidate is occupied exactly when its point lies on an accepted line. -/
theorem occupied_iff (e : Fin r) (i : Fin (arity p)) (c : Fin s) :
    occupied hk bits scalar menu x e i c = true ↔
      T (pending hk i) + (scalar c : K) • menu e i ∈ occupiedPoints (acceptedLines a T dirs) := by
  rw [occupied, decide_eq_true_iff, mem_occupiedPoints_acceptedLines]
  constructor
  · rintro ⟨m, c', h⟩
    rw [(hline _ m.isLt).2, candidate_eq bits scalar menu htarget] at h
    exact ⟨accepted hk m, m.isLt, (mem_puncturedLine_iff scalar).mpr
      ⟨c', pointBits_injective bits h⟩⟩
  · rintro ⟨m, hm, hw⟩
    obtain ⟨c', hc'⟩ := (mem_puncturedLine_iff scalar).mp hw
    refine ⟨⟨m.val, hm⟩, c', ?_⟩
    rw [show accepted hk ⟨m.val, hm⟩ = m from Fin.ext rfl, (hline m hm).2,
      candidate_eq bits scalar menu htarget, hc']

omit hline [Fintype K] [DecidableEq K] in
/-- A candidate is a duplicate exactly when another candidate of its entry is the same point. -/
theorem duplicate_iff (e : Fin r) (i : Fin (arity p)) (c : Fin s) :
    duplicate hk bits scalar menu x e i c = true ↔
      ∃ i' c', (i', c') ≠ (i, c) ∧ T (pending hk i') + (scalar c' : K) • menu e i' =
        T (pending hk i) + (scalar c : K) • menu e i := by
  simp only [duplicate, decide_eq_true_iff, candidate_eq bits scalar menu htarget,
    (pointBits_injective bits).eq_iff]

/-- The clean flags are exactly the clean requests of `LineCode.IsClean`, for nonzero menu
directions. -/
theorem clean_iff (hmenu : ∀ e i, menu e i ≠ 0) (e : Fin r) (i : Fin (arity p)) :
    clean hk bits scalar menu x e i = true ↔
      IsClean (occupiedPoints (acceptedLines a T dirs)) (fun i => T (pending hk i)) (menu e) i := by
  rw [clean, decide_eq_true_iff]
  constructor
  · intro h
    refine ⟨disjoint_left.mpr fun w hw hocc => ?_,
      fun j hji => disjoint_left.mpr fun w hw hw' => ?_⟩
    · obtain ⟨c, rfl⟩ := (mem_puncturedLine_iff scalar).mp hw
      have := (h c).1
      rw [← Bool.not_eq_true, occupied_iff bits scalar menu htarget hline] at this
      exact this hocc
    · obtain ⟨c, rfl⟩ := (mem_puncturedLine_iff scalar).mp hw
      obtain ⟨c', hc'⟩ := (mem_puncturedLine_iff scalar).mp hw'
      have := (h c).2
      rw [← Bool.not_eq_true, duplicate_iff bits scalar menu htarget] at this
      exact this ⟨j, c', fun h => hji (Prod.mk.inj h).1, hc'⟩
  · intro h c
    refine ⟨?_, ?_⟩
    · rw [← Bool.not_eq_true, occupied_iff bits scalar menu htarget hline]
      exact disjoint_left.mp h.1 ((mem_puncturedLine_iff scalar).mpr ⟨c, rfl⟩)
    · rw [← Bool.not_eq_true, duplicate_iff bits scalar menu htarget]
      rintro ⟨i', c', hne, heq⟩
      by_cases hi : i' = i
      · subst hi
        exact hne (by rw [add_smul_injective scalar (hmenu e i') heq])
      · exact disjoint_left.mp (h.2 i' hi) ((mem_puncturedLine_iff scalar).mpr ⟨c, rfl⟩)
          ((mem_puncturedLine_iff scalar).mpr ⟨c', heq⟩)

end Correctness

/-- A phase with a universal menu keeps the state good and accepts `⌈2 ^ p / 2⌉` more
requests. -/
theorem good_next [Fintype K] [DecidableEq K] (bits : K ≃+ BitString b)
    (scalar : Fin s ≃ {c : K // c ≠ 0})
    (menu : Fin r → Fin (arity p) → Fin ℓ → K) (hmenu : IsUniversalMenu (2 ^ D) menu)
    {targets : Fin (2 ^ D) → Fin ℓ → K} {x : BitString (2 ^ D * width D (ℓ * b) s)}
    (hx : Good bits scalar targets a x) :
    Good bits scalar targets (a + (arity p + 1) / 2) (next hk bits scalar menu x) := by
  obtain ⟨π, dirs, hlabel, htarget, hline, hdisj⟩ := hx
  set T := fun m => targets (π m) with hT
  set P := fun i => T (pending hk i) with hP
  have hclean := clean_iff (hk := hk) bits scalar menu (x := x) (T := T) (dirs := dirs)
    htarget hline hmenu.1
  -- Some entry succeeds, so there is a first successful entry.
  obtain ⟨e₀, C, hC, hCclean⟩ := hmenu.2 (acceptedLines a T dirs) P
  have hsucc₀ : success hk bits scalar menu x e₀ = true := by
    rw [success, decide_eq_true_iff]
    refine hC.trans (Nat.mul_le_mul_left 2 (card_le_card fun i hi => ?_))
    simp only [mem_filter, mem_univ, true_and]
    exact (hclean e₀ i).mpr (hCclean i hi)
  obtain ⟨e, he, hmin⟩ := exists_min_image ({e | success hk bits scalar menu x e = true} :
    Finset (Fin r)) id ⟨e₀, by simpa using hsucc₀⟩
  simp only [mem_filter, mem_univ, true_and, id] at he hmin
  have hchosen (e' : Fin r) : chosen hk bits scalar menu x e' = true ↔ e' = e := by
    rw [chosen, decide_eq_true_iff]
    constructor
    · rintro ⟨hs, hfirst⟩
      rcases lt_trichotomy e' e with h | h | h
      · exact absurd (hmin e' hs) (not_le.mpr h)
      · exact h
      · exact absurd he (by rw [hfirst e h]; decide)
    · rintro rfl
      refine ⟨he, fun e'' h'' => ?_⟩
      by_contra hn
      exact absurd (hmin e'' (by simpa using hn)) (not_le.mpr h'')
  have hflag (i : Fin (arity p)) :
      flag hk bits scalar menu x i = clean hk bits scalar menu x e i := by
    rw [Bool.eq_iff_iff, flag, decide_eq_true_iff]
    exact ⟨fun ⟨e', h₁, h₂⟩ => (hchosen e').mp h₁ ▸ h₂, fun h => ⟨e, (hchosen e).mpr rfl, h⟩⟩
  have hnew (i : Fin (arity p)) (c : Fin s) (β : Fin (ℓ * b)) :
      newLine hk bits scalar menu x i c β = candidate hk bits scalar menu x e i c β := by
    rw [Bool.eq_iff_iff, newLine, decide_eq_true_iff]
    exact ⟨fun ⟨e', h₁, h₂⟩ => (hchosen e').mp h₁ ▸ h₂, fun h => ⟨e, (hchosen e).mpr rfl, h⟩⟩
  -- Sorting permutes the pending records and puts the clean ones first.
  obtain ⟨σ, hσ⟩ := (sort_perm (fun record => toLex (record ∘ flagKey)) p false
    (enriched hk bits scalar menu x)).exists_equiv_ofFn
  have hsorted (j : Fin (arity p)) :
      sortedPending hk bits scalar menu x j = enriched hk bits scalar menu x (σ j) := hσ j
  have hflagbit (j : Fin (arity p)) : sortedPending hk bits scalar menu x j (Fin.castAdd _ 0) =
      clean hk bits scalar menu x e (σ j) := by
    rw [hsorted, enriched, Fin.append_left, hflag]
  have hfront (j : Fin (arity p)) (hj : j.val < (arity p + 1) / 2) :
      IsClean (occupiedPoints (acceptedLines a T dirs)) P (menu e) (σ j) := by
    refine (hclean e (σ j)).mp ?_
    rw [← hflagbit]
    refine (sort_flag_eq_true_iff (fun record => record ∘ flagKey) p
      (enriched hk bits scalar menu x) j).mpr ?_
    have hcount : #{i | (enriched hk bits scalar menu x i ∘ flagKey) 0 = true} =
        #{i | clean hk bits scalar menu x e i = true} := by
      simp only [Function.comp_apply, flagKey, enriched, Fin.append_left, hflag]
    rw [hcount]
    have := he
    rw [success, decide_eq_true_iff] at this
    lia
  -- The new state.
  let E : Fin a ⊕ Fin (arity p) ≃ Fin (2 ^ D) := finSumFinEquiv.trans (finCongr hk)
  have hEl (m : Fin a) : E (Sum.inl m) = accepted hk m := Fin.ext rfl
  have hEr (i : Fin (arity p)) : E (Sum.inr i) = pending hk i := Fin.ext rfl
  let τ : Equiv.Perm (Fin (2 ^ D)) :=
    E.symm.trans ((Equiv.sumCongr (Equiv.refl _) σ).trans E)
  have hτa (m : Fin a) : τ (accepted hk m) = accepted hk m := by
    simp only [τ, Equiv.trans_apply, ← hEl, Equiv.symm_apply_apply, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.refl_apply]
  have hτp (i : Fin (arity p)) : τ (pending hk i) = pending hk (σ i) := by
    simp only [τ, Equiv.trans_apply, ← hEr, Equiv.symm_apply_apply, Equiv.sumCongr_apply,
      Sum.map_inr]
  let dirs' : Fin (2 ^ D) → Fin ℓ → K :=
    fun m => Sum.elim (fun m' => dirs (accepted hk m')) (fun j => menu e (σ j)) (E.symm m)
  have hda (m : Fin a) : dirs' (accepted hk m) = dirs (accepted hk m) := by
    simp only [dirs', ← hEl, Equiv.symm_apply_apply, Sum.elim_inl]
  have hdp (i : Fin (arity p)) : dirs' (pending hk i) = menu e (σ i) := by
    simp only [dirs', ← hEr, Equiv.symm_apply_apply, Sum.elim_inr]
  -- Accepted positions after the phase.
  have hnew_acc (m : Fin (2 ^ D)) (hm : m.val < a + (arity p + 1) / 2) :
      (∃ m', m = accepted hk m') ∨
        ∃ j, m = pending hk j ∧ j.val < (arity p + 1) / 2 := by
    rcases accepted_or_pending (hk := hk) m with ⟨m', rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl ⟨m', rfl⟩
    · exact Or.inr ⟨j, rfl, by rw [val_pending] at hm; lia⟩
  have hsub (m : Fin a) : puncturedLine (T (accepted hk m)) (dirs (accepted hk m)) ⊆
      occupiedPoints (acceptedLines a T dirs) := fun w hw =>
    mem_occupiedPoints_acceptedLines.mpr ⟨accepted hk m, m.isLt, hw⟩
  refine ⟨τ.trans π, dirs', fun m => ?_, fun m => ?_, fun m hm => ?_, fun m m' hm hm' hne => ?_⟩
  · funext jj
    rcases accepted_or_pending (hk := hk) m with ⟨m', rfl⟩ | ⟨j, rfl⟩
    · simp only [label, next_accepted, Equiv.trans_apply, hτa]
      exact congrFun (hlabel _) jj
    · simp only [label, next_pending, Equiv.trans_apply, hτp, hsorted, enriched, labelBit]
      rw [show Fin.natAdd 1 (Fin.castAdd (ℓ * b + s * (ℓ * b)) jj) =
          Fin.natAdd 1 (Fin.castAdd (ℓ * b + s * (ℓ * b)) jj) from rfl, Fin.append_right,
        Fin.append_left]
      exact congrFun (hlabel _) jj
  · funext β
    rcases accepted_or_pending (hk := hk) m with ⟨m', rfl⟩ | ⟨j, rfl⟩
    · simp only [target, next_accepted, Equiv.trans_apply, hτa]
      exact congrFun (htarget _) β
    · simp only [target, next_pending, Equiv.trans_apply, hτp, hsorted, enriched, targetBit]
      rw [Fin.append_right, Fin.append_right, Fin.append_left]
      exact congrFun (htarget _) β
  · rcases hnew_acc m hm with ⟨m', rfl⟩ | ⟨j, rfl, hj⟩
    · rw [hda]
      refine ⟨(hline _ m'.isLt).1, fun c => ?_⟩
      funext β
      simp only [line, next_accepted, Equiv.trans_apply, hτa]
      exact congrFun ((hline _ m'.isLt).2 c) β
    · rw [hdp]
      refine ⟨hmenu.1 e (σ j), fun c => ?_⟩
      funext β
      simp only [line, next_pending, Equiv.trans_apply, hτp, hsorted, enriched, lineBit]
      rw [Fin.append_right, Fin.append_right, Fin.append_right, Equiv.symm_apply_apply, hnew,
        candidate_eq bits scalar menu htarget]
  · simp only [Equiv.trans_apply]
    rcases hnew_acc m hm with ⟨m₁, rfl⟩ | ⟨j, rfl, hj⟩ <;>
      rcases hnew_acc m' hm' with ⟨m₂, rfl⟩ | ⟨j', rfl, hj'⟩
    · rw [hτa, hτa, hda, hda]
      exact hdisj _ _ m₁.isLt m₂.isLt hne
    · rw [hτa, hτp, hda, hdp]
      exact ((hfront j' hj').1.mono_right (hsub m₁)).symm
    · rw [hτp, hτa, hdp, hda]
      exact (hfront j hj).1.mono_right (hsub m₂)
    · rw [hτp, hτp, hdp, hdp]
      exact (hfront j hj).2 (σ j') fun h => hne (by rw [σ.injective h])

end Cslib.Circuits.Boolean.MassProduction.Scheduler
