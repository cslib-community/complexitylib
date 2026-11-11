/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.State
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperserCore.Operations

/-!
# Zero-locus operations for `4n - 10d` gate elimination

Specialization of the shared state operations (`Cslib.Circuits.Boolean.AffineDisperserCore`)
to `4n - 10d` states with zero-locus pairs:

* restrictions `(UF)` and `(PF)` preserving `Z(P)` (`State.RestrictOK`, `State.Valid.restrict`);
* pair creation `(PC)` preserving `Z(P)` and lowering potential by `8`
  (`State.Valid.addPair`, `State.Valid.addPair_W_eq`);
* affine reparameterisation `(AR)` preserving `Z(P)` and nonincreasing potential
  (`State.Valid.swap`, `State.Valid.swap_W_le`).

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser4n.State.RestrictOK`: hypotheses for restrictions
  `(UF)` and `(PF)`.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.restrict`: `(UF)` and `(PF)` preserve
  validity.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.addPair`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.addPair_W_eq`: `(PC)` validity and
  potential change.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.swap`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.swap_W_le`: `(AR)` validity and
  potential change.
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Finset SemiCircuit AffineDisperserCore

namespace State

open AffineDisperserCore.State

variable {n : ℕ} {f : BooleanFunction n}

/-! ### Restrictions (UF) and (PF) -/

/-- The hypotheses of a restriction: `x` is a parameter, `ℓ` reads at most another parameter,
kept pairs avoid `x`, and every dropped pair is satisfied on the substituted assignment. -/
structure RestrictOK (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset ZeroPair) : Prop where
  /-- `x` is a parameter of `S`. -/
  mem : x ∈ S.params
  /-- Every variable read by `ℓ` is a parameter other than `x`. -/
  reads : ∀ y, ℓ.Reads y → y ∈ S.params ∧ y ≠ x
  /-- Kept pairs come from `S.pairs`. -/
  subset : P ⊆ S.pairs
  /-- Kept pairs do not contain `x`. -/
  avoid : ∀ pr ∈ P, ¬ pr.Contains x
  /-- Dropped pairs hold after substituting `x := ℓ`. -/
  drop : ∀ pr ∈ S.pairs, pr ∉ P → ∀ val, pr.Holds (Function.update val x (ℓ.eval val))

/-- Restrictions `(UF)` and `(PF)` preserve validity on `Z(P)`. -/
theorem Valid.restrict {S : State n} (hS : S.Valid f) {x : ℕ} {ℓ : Lit} {P : Finset ZeroPair}
    (h : S.RestrictOK x ℓ P) : (S.restrict x ℓ P).Valid f :=
  Valid.restrict_of hS h.mem h.reads h.subset h.avoid
    (hS.phi_affine.comp (isAffine_update isAffine_id x (isAffine_lit_eval isAffine_id ℓ)))
    fun val hlocus pr hpr => by
      by_cases hprP : pr ∈ P
      · have hav := h.avoid pr hprP
        have h1 : pr.fst ≠ x := fun he => hav (Or.inl he)
        have h2 : pr.snd ≠ x := fun he => hav (Or.inr he)
        exact (ZeroPair.holds_congr (Function.update_of_ne h1 (ℓ.eval val) val)
          (Function.update_of_ne h2 (ℓ.eval val) val)).2 (hlocus pr hprP)
      · exact h.drop pr hpr hprP val

/-! ### Pair creation (PC) -/

/-- Pair creation `(PC)` preserves validity on `Z(P)`. -/
theorem Valid.addPair {S : State n} (hS : S.Valid f) {pr : ZeroPair} (h : S.AddPairOK pr) :
    (S.addPair pr).Valid f :=
  Valid.addPair_of hS h hS.phi_affine fun _ hlocus pr' hpr' =>
    hlocus pr' (Finset.mem_insert_of_mem hpr')

/-- Pair creation `(PC)` on two used unpaired parameters lowers `W` by `8`. -/
theorem Valid.addPair_W_eq {S : State n} (_hS : S.Valid f) {pr : ZeroPair}
    (h : S.AddPairOK pr) (h1 : 1 ≤ S.deg pr.fst) (h2 : 1 ≤ S.deg pr.snd) :
    (S.addPair pr).W + 8 = S.W := by
  let S₁ := S.addPair pr
  let loss : ℕ → ℕ := fun u => (if u = pr.fst then 6 else 0) + (if u = pr.snd then 6 else 0)
  have hsum : ∑ u ∈ S.params, loss u = 12 := by
    rw [Finset.sum_add_distrib,
      Finset.sum_eq_single_of_mem pr.fst (mem_unpaired.1 h.fst_unpaired).1
        (fun _ _ hf => ite_eq_right hf),
      Finset.sum_eq_single_of_mem pr.snd (mem_unpaired.1 h.snd_unpaired).1
        (fun _ _ hf => ite_eq_right hf),
      ite_eq_left rfl, ite_eq_left rfl]
  have hwt_same : ∀ u ∈ S.params, u ≠ pr.fst → u ≠ pr.snd → S₁.wt u = S.wt u :=
    fun u hu hu1 hu2 => by
      by_cases hup : S.Paired u
      · obtain ⟨pr', hpr', hcu⟩ := hup
        have hup1 : S₁.Paired u := ⟨pr', Finset.mem_insert_of_mem hpr', hcu⟩
        have hup0 : S.Paired u := ⟨pr', hpr', hcu⟩
        rw [wt_of_paired hup1, wt_of_paired hup0]
      · have hup1 : ¬ S₁.Paired u := by
          rintro ⟨pr', hpr', hcu⟩
          rcases Finset.mem_insert.1 hpr' with rfl | hpr'
          · rcases hcu with he | he <;> [exact hu1 he.symm; exact hu2 he.symm]
          · exact hup ⟨pr', hpr', hcu⟩
        have hu1m : u ∈ S₁.unpaired := mem_unpaired.2 ⟨by rw [addPair_params]; exact hu, hup1⟩
        have hu0m : u ∈ S.unpaired := mem_unpaired.2 ⟨hu, hup⟩
        rw [wt_of_mem hu1m, wt_of_mem hu0m, SemiCircuit.deg, SemiCircuit.deg, addPair_children]
  have hle1 := W_add_le (S := S) (S' := S₁) (N := S.params) le_rfl (by rw [addPair_params])
    loss (fun _ => 0) fun u hu => by
      simp only [add_zero]
      by_cases hu1 : u = pr.fst
      · subst hu1
        have hp1 : S₁.Paired pr.fst := ⟨pr, Finset.mem_insert_self _ _, Or.inl rfl⟩
        dsimp only [loss]
        rw [wt_of_paired hp1, wt_of_mem h.fst_unpaired,
          show config.weight (S.deg pr.fst) = weight (S.deg pr.fst) from rfl,
          weight_of_one_le h1, ite_eq_left rfl, ite_eq_right h.ne]
      · by_cases hu2 : u = pr.snd
        · subst hu2
          have hp2 : S₁.Paired pr.snd := ⟨pr, Finset.mem_insert_self _ _, Or.inr rfl⟩
          dsimp only [loss]
          rw [wt_of_paired hp2, wt_of_mem h.snd_unpaired,
            show config.weight (S.deg pr.snd) = weight (S.deg pr.snd) from rfl,
            weight_of_one_le h2, ite_eq_right hu1, ite_eq_left rfl]
        · dsimp only [loss]
          rw [ite_eq_right hu1, ite_eq_right hu2, add_zero, hwt_same u hu hu1 hu2, add_zero]
  have hle2 := W_add_le (S := S₁) (S' := S) (N := S.params) (by rw [addPair_params]) le_rfl
    (fun _ => 0) loss fun u hu => by
      simp only [add_zero]
      by_cases hu1 : u = pr.fst
      · subst hu1
        dsimp only [loss]
        rw [wt_of_mem h.fst_unpaired,
          show config.weight (S.deg pr.fst) = weight (S.deg pr.fst) from rfl,
          weight_of_one_le h1, ite_eq_left rfl, ite_eq_right h.ne]
        omega
      · by_cases hu2 : u = pr.snd
        · subst hu2
          dsimp only [loss]
          rw [wt_of_mem h.snd_unpaired,
            show config.weight (S.deg pr.snd) = weight (S.deg pr.snd) from rfl,
            weight_of_one_le h2, ite_eq_right hu1, ite_eq_left rfl]
          omega
        · dsimp only [loss]
          rw [ite_eq_right hu1, ite_eq_right hu2, add_zero, hwt_same u hu hu1 hu2, add_zero]
  have hs1 : S₁.s = S.s := addPair_size S pr
  have hq1 : S₁.q = S.q + 1 := addPair_q h
  dsimp only [S₁] at hle1 hle2 hs1 hq1
  rw [hsum, Finset.sum_const_zero, hs1, hq1] at hle1 hle2
  omega

/-! ### Affine reparameterisation (AR) -/

/-- The affine reparameterisation `(AR)` preserves validity on `Z(P)`. -/
theorem Valid.swap {S : State n} (hS : S.Valid f) {x Q : ℕ} {c : Bool} {T : Finset ℕ}
    (h : S.SwapOK x Q c T) : (S.swap x Q c T).Valid f :=
  Valid.swap_of hS h
    (hS.phi_affine.comp (isAffine_update isAffine_id x (isAffine_add_add_sum isAffine_id Q c _)))

/-- An affine reparameterisation `(AR)` on a used parameter does not increase the potential `W`. -/
theorem Valid.swap_W_le {S : State n} (hS : S.Valid f) {x Q : ℕ} {c : Bool} {T : Finset ℕ}
    (h : S.SwapOK x Q c T) (hdeg : 1 ≤ S.deg x) : (S.swap x Q c T).W ≤ S.W := by
  have hloss : 6 ≤ S.wt x := by
    rw [wt_of_mem (mem_unpaired.2 ⟨h.mem, h.unpaired⟩),
      show config.weight (S.deg x) = weight (S.deg x) from rfl, weight_of_one_le hdeg]
  have hgain : (S.swap x Q c T).wt Q ≤ 6 := (S.swap x Q c T).wt_le_bound Q
  have hW := Valid.swap_W_le_of hS h hloss hgain
  omega

end State

end Cslib.Circuits.Boolean.AffineDisperser4n
