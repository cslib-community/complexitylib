/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Raw.Primrec

/-!
# One relation symbol suffices

Every raw formula can be rewritten with a single relation symbol, preserving finite
satisfiability. `Cslib.Logic.FO.RawFormula.uniformize B φ` replaces each atom `R_r(x̄)` by
`R_0(x̄, x_B, …, x_B)`, padded to the length `pair r |x̄| + 1`. The length codes the
pair `(r, |x̄|)` injectively, so a structure for `φ` and a structure for `uniformize B φ` determine
each other (`Cslib.Logic.FO.RawFormula.finSat_uniformize`). Every atom of `uniformize B φ` is the
symbol `0` at a positive arity (`Cslib.Logic.FO.RawFormula.atoms_uniformize`).

## Main definitions

* `Cslib.Logic.FO.RawFormula.uniformize`: the rewriting.

## Main results

* `Cslib.Logic.FO.RawFormula.finSat_uniformize`: preservation of finite satisfiability.
* `Cslib.Logic.FO.RawFormula.primrec₂_uniformize`: the rewriting is primitive recursive.
-/

public section

namespace Cslib.Logic.FO

namespace RawFormula

/-- The padded length coding symbol `r` with `k` arguments. -/
private def padLen (r k : ℕ) : ℕ := Nat.pair r k + 1

/-- Replace every atom `R_r(x̄)` by `R_0(x̄, x_B, …, x_B)`, padded to length `pair r |x̄| + 1`. -/
def uniformize (B : ℕ) : RawFormula → RawFormula
  | falsum => falsum
  | equal x y => equal x y
  | rel r args => rel 0 (args ++ List.replicate (padLen r args.length - args.length) B)
  | imp φ ψ => imp (uniformize B φ) (uniformize B ψ)
  | all x φ => all x (uniformize B φ)

/-- The interpretation of the original symbols induced by an interpretation `J` of the symbol `0`
and the padding element `b`. -/
private def uniformInterp {M : Type*} (J : ℕ → List M → Prop) (b : M) : ℕ → List M → Prop :=
  fun r as => J 0 (as ++ List.replicate (padLen r as.length - as.length) b)

private theorem realize_uniformize {M : Type*} (B : ℕ) (J : ℕ → List M → Prop) :
    ∀ (φ : RawFormula) (v : ℕ → M), φ.varBound ≤ B →
      ((uniformize B φ).Realize J v ↔ φ.Realize (uniformInterp J (v B)) v)
  | falsum, _, _ => Iff.rfl
  | equal _ _, _, _ => Iff.rfl
  | rel r args, v, _ => by
    simp only [uniformize, realize_rel, uniformInterp, List.map_append, List.map_replicate,
      List.length_map]
  | imp φ ψ, v, hB => by
    simp only [varBound, max_le_iff] at hB
    simp only [uniformize, realize_imp, realize_uniformize B J φ v hB.1,
      realize_uniformize B J ψ v hB.2]
  | all x φ, v, hB => by
    simp only [varBound, max_le_iff] at hB
    simp only [uniformize, realize_all]
    refine forall_congr' fun m => ?_
    rw [realize_uniformize B J φ _ hB.2, Function.update_of_ne (by omega)]

/-- **One relation symbol suffices**: `uniformize` preserves finite satisfiability. -/
theorem finSat_uniformize (φ : RawFormula) : FinSat (uniformize φ.varBound φ) ↔ FinSat φ := by
  constructor
  · rintro ⟨M, hf, hn, J, v, h⟩
    exact ⟨M, hf, hn, _, v, (realize_uniformize _ J φ v le_rfl).1 h⟩
  · rintro ⟨M, hf, hn, I, v, h⟩
    let J : ℕ → List M → Prop := fun _ as =>
      I (Nat.unpair (as.length - 1)).1 (as.take (Nat.unpair (as.length - 1)).2)
    refine ⟨M, hf, hn, J, v, (realize_uniformize _ J φ v le_rfl).2 ?_⟩
    refine (realize_congr_rel φ v fun r as _ => ?_).1 h
    have hk : as.length ≤ padLen r as.length := by
      have := Nat.right_le_pair r as.length
      simp only [padLen]
      omega
    have hl : (as ++ List.replicate (padLen r as.length - as.length) (v φ.varBound)).length - 1 =
        Nat.pair r as.length := by
      simp only [List.length_append, List.length_replicate, padLen] at hk ⊢
      omega
    simp only [uniformInterp, J, hl, Nat.unpair_pair, List.take_left]

theorem atoms_uniformize (B : ℕ) :
    ∀ φ : RawFormula, ∀ a ∈ (uniformize B φ).atoms, a.1 = 0 ∧ 0 < a.2
  | falsum, _, h => by simp [uniformize, atoms] at h
  | equal _ _, _, h => by simp [uniformize, atoms] at h
  | rel r args, a, h => by
    simp only [uniformize, atoms, List.mem_singleton] at h
    subst h
    simp only [List.length_append, List.length_replicate, padLen, true_and]
    omega
  | imp φ ψ, a, h => by
    simp only [uniformize, atoms, List.mem_append] at h
    exact h.elim (atoms_uniformize B φ a) (atoms_uniformize B ψ a)
  | all _ φ, a, h => atoms_uniformize B φ a h

section Primrec

open Primrec

private theorem primrec₂_replicate {α : Type*} [Primcodable α] :
    Primrec₂ fun (n : ℕ) (a : α) => List.replicate n a :=
  (list_map (list_range.comp fst) (snd.comp fst).to₂).of_eq fun p => by
    simp [List.map_const']

theorem primrec₂_uniformize : Primrec₂ uniformize := by
  refine primrec₂_of_rec (α := ℕ) (σ := RawFormula) uniformize (const falsum)
    (e := fun _ p => equal p.1 p.2) (primrec_equal (fst.comp snd) (snd.comp snd)).to₂
    (r := fun B p => rel 0 (p.2 ++ List.replicate (padLen p.1 p.2.length - p.2.length) B))
    ?_
    (i := fun _ p => imp p.2.1 p.2.2)
    (primrec_imp (fst.comp (snd.comp snd)) (snd.comp (snd.comp snd))).to₂
    (l := fun _ p => all p.1.1 p.2)
    (primrec_all (fst.comp (fst.comp snd)) (snd.comp snd)).to₂
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  have hlen : Primrec fun p : ℕ × ℕ × List ℕ => p.2.2.length := list_length.comp (snd.comp snd)
  have hpad : Primrec fun p : ℕ × ℕ × List ℕ => padLen p.2.1 p.2.2.length :=
    succ.comp (Primrec₂.natPair.comp (fst.comp snd) hlen)
  exact (primrec_rel (const 0) (list_append.comp (snd.comp snd)
    (primrec₂_replicate.comp (nat_sub.comp hpad hlen) fst))).to₂

end Primrec

end RawFormula

end Cslib.Logic.FO
