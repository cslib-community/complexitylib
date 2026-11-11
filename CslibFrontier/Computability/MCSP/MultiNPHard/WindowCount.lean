/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.MCSP.MultiNPHard.Window
import CslibFrontier.Computability.Circuit.FanIn
import Cslib.Computability.Circuit.Counting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.CardIntervalMod

/-!
# Window templates: the soundness count

If no set of at most `ℓ + 1` windows comes close to covering the inputs, then for most tables `T`
the template followed by `T` costs more than the template's distinct non-input gate functions plus
`ℓ`. This is the soundness half of the reduction of Ilango, Loff and Oliveira
[IlangoLoffOliveira2020, §4.2, pp. 22:20–22:21].

**Library route.** The source proves soundness by compression [IlangoLoffOliveira2020, Lemma 16
and its proof, pp. 22:22–22:23], using that the sets have bounded size. This file proves it
instead with a union bound over small circuits, which needs no bound on the sets but asks for
`2^p` large compared with the windows' number. If the cost were at most the count plus `ℓ`, then
by inputization (`card_nonInputComponents_add_ecomplexityGiven_le`) some function `F` of the input
and the gate values, computed with at most `ℓ` gates, recovers `T`. Such a circuit reads at most
`ℓ + 1` input wires (`Circuit.card_inputSupport_le_cost`), hence at most `ℓ + 1` windows; some set
`P` of at least `d` inputs avoids those windows, and by locality (`Window.value_congr`) `F` and the
entries of `T` outside `P` determine `T`. So at most `2^(2^p - d)` tables are consistent with each
`F`, and there are few `F` (`card_computableFunctions_mul_factorial_le_of_arity_le`). The arithmetic
is uniform over De Morgan bases through their bound of five operations.

`lift` supplies the windows of the reduction: a set of residues modulo `N`, lifted to the inputs
`0, …, 2^p - 1`. Covers of the residues lift to covers of the inputs, and a residue outside some
sets gives about `2^p / N` inputs outside their lifts.

## Main definitions

* `Cslib.MultiMCSP.Window.lift`: residues modulo `N`, lifted to the inputs.

## Main results

* `Cslib.MultiMCSP.Window.three_mul_card_cheap_le`: soundness, as a count of the cheap tables.
* `Cslib.MultiMCSP.Window.lift_cover`, `Cslib.MultiMCSP.Window.three_mul_card_cheap_lift_le`:
  completeness and soundness hypotheses for lifted windows.

## References

* [R. Ilango, B. Loff, I. C. Oliveira, *NP-Hardness of Circuit Minimization for Multi-Output
  Functions*][IlangoLoffOliveira2020]
-/

public section

namespace Cslib.MultiMCSP.Window

open Circuits Finset

universe v

variable {p t : ℕ} {σ : Signature.{v}} {I : Interpretation σ Bool} [Boolean.DeMorganBasis I]

/-- The arithmetic of the union bound: with `X = 2^p ≥ 64` and fewer than `3 X^2` wires, the
functions computable with `ℓ ≤ X` gates number at most `X^(5ℓ + 5) / 3`. -/
private theorem three_mul_le_pow {K ℓ M c X : ℕ} (hX : 64 ≤ X) (hℓ : ℓ ≤ X) (hM : M + 1 ≤ 3 * X ^ 2)
    (hc : c ≤ 5) (hK : K * ℓ.factorial ≤ (ℓ + 1) * (max ℓ (c * (M + 1) ^ 2)) ^ ℓ * M) :
    3 * K ≤ X ^ (5 * ℓ + 5) := by
  have hstep (k : ℕ) : 64 * X ^ k ≤ X ^ (k + 1) := by
    rw [pow_succ, Nat.mul_comm 64]
    exact Nat.mul_le_mul_left _ hX
  have hX3 : 64 * X ^ 2 ≤ X ^ 3 := hstep 2
  have hX4 : 64 * X ^ 3 ≤ X ^ 4 := hstep 3
  have hX5 : 64 * X ^ 4 ≤ X ^ 5 := hstep 4
  -- The maximum is at most `X^5`.
  have hsq : (M + 1) ^ 2 ≤ 9 * X ^ 4 := by
    calc (M + 1) ^ 2 ≤ (3 * X ^ 2) ^ 2 := Nat.pow_le_pow_left hM 2
      _ = 9 * X ^ 4 := by ring
  have hmax : max ℓ (c * (M + 1) ^ 2) ≤ X ^ 5 := by
    refine max_le (hℓ.trans (Nat.le_self_pow (by norm_num) X)) ?_
    calc c * (M + 1) ^ 2 ≤ 5 * (9 * X ^ 4) := Nat.mul_le_mul hc hsq
      _ ≤ X ^ 5 := by omega
  have hK' : K ≤ (ℓ + 1) * X ^ (5 * ℓ) * M := by
    calc K ≤ K * ℓ.factorial := Nat.le_mul_of_pos_right K (Nat.factorial_pos ℓ)
      _ ≤ (ℓ + 1) * (max ℓ (c * (M + 1) ^ 2)) ^ ℓ * M := hK
      _ ≤ (ℓ + 1) * (X ^ 5) ^ ℓ * M := by gcongr
      _ = (ℓ + 1) * X ^ (5 * ℓ) * M := by rw [← pow_mul]
  -- The remaining factor `3 (ℓ + 1) M` is at most `X^5`.
  have hrest : 3 * ((ℓ + 1) * M) ≤ X ^ 5 := by
    calc 3 * ((ℓ + 1) * M) ≤ 3 * ((X + 1) * (3 * X ^ 2)) :=
          Nat.mul_le_mul_left 3 (Nat.mul_le_mul (by omega) (by omega))
      _ = 9 * X ^ 3 + 9 * X ^ 2 := by ring
      _ ≤ X ^ 5 := by omega
  calc 3 * K ≤ 3 * ((ℓ + 1) * X ^ (5 * ℓ) * M) := Nat.mul_le_mul_left 3 hK'
    _ = X ^ (5 * ℓ) * (3 * ((ℓ + 1) * M)) := by ring
    _ ≤ X ^ (5 * ℓ) * X ^ 5 := Nat.mul_le_mul_left _ hrest
    _ = X ^ (5 * ℓ + 5) := by rw [pow_add]

/-- The windows met by a set of input wires of the template's inputs followed by its gates. -/
private noncomputable def windowsOf (S : Finset (Fin (p + gateCount p t))) : Finset (Fin t) :=
  S.biUnion fun z =>
    Fin.addCases (fun _ => ∅) (fun j => ((Gate.equivFin p t).symm j).set.toFinset) z

private theorem card_windowsOf_le (S : Finset (Fin (p + gateCount p t))) :
    #(windowsOf S) ≤ #S := by
  classical
  refine (card_biUnion_le_card_mul S _ 1 fun z _ => ?_).trans_eq (Nat.mul_one _)
  refine Fin.addCases (fun i => ?_) (fun j => ?_) z
  · simp
  · rw [Fin.addCases_right, Option.card_toFinset]
    cases ((Gate.equivFin p t).symm j).set <;> simp

private theorem mem_windowsOf {S : Finset (Fin (p + gateCount p t))} {j : Fin (gateCount p t)}
    (hj : Fin.natAdd p j ∈ S) {i : Fin t} (hi : ((Gate.equivFin p t).symm j).set = some i) :
    i ∈ windowsOf S := by
  classical
  refine mem_biUnion.mpr ⟨_, hj, ?_⟩
  rw [Fin.addCases_right, hi]
  exact Option.mem_toFinset.mpr rfl

/-- **Soundness, as a count** (library route). Suppose every set of at most `ℓ + 1` windows misses a
common set of at least `d` inputs, with `d ≥ p (5ℓ + 5)`, `ℓ ≤ t ≤ 2^p` and `2^p ≥ 64`. Then for at
most a third of the tables `T` does the template followed by `T` cost at most the template's
distinct non-input gate functions plus `ℓ`, over any De Morgan basis. This replaces the compression
argument of [IlangoLoffOliveira2020, Lemma 16, pp. 22:22–22:23] by a union bound over small
circuits. -/
theorem three_mul_card_cheap_le (A : Fin t → Finset (Fin (2 ^ p))) (ℓ d : ℕ)
    (hcover : ∀ B : Finset (Fin t), #B ≤ ℓ + 1 →
      ∃ P : Finset (Fin (2 ^ p)), d ≤ #P ∧ ∀ i ∈ B, Disjoint (A i) P)
    (ht : t ≤ 2 ^ p) (hℓ : ℓ ≤ t) (hX : 64 ≤ 2 ^ p) (hd : p * (5 * ℓ + 5) ≤ d) :
    3 * #{T : Fin (2 ^ p) → Bool |
      ecomplexity I (fun x => Fin.append (template A T x) (single (tableFun T) x)) ≤
        ((#(nonInputComponents (template A T)) + ℓ : ℕ) : ℕ∞)} ≤ 2 ^ (2 ^ p) := by
  classical
  have := Boolean.DeMorganBasis.finite_op (I := I)
  -- The tables a function of the input and the gate values recovers.
  let Cons (F : (Fin (p + gateCount p t) → Bool) → Bool) : Finset (Fin (2 ^ p) → Bool) :=
    {T | ∀ x, F (Fin.append x (template A T x)) = tableFun T x}
  -- Step 1: a cheap table is recovered by a function computed with `ℓ` gates.
  have hsub : ({T : Fin (2 ^ p) → Bool |
      ecomplexity I (fun x => Fin.append (template A T x) (single (tableFun T) x)) ≤
        ((#(nonInputComponents (template A T)) + ℓ : ℕ) : ℕ∞)} : Finset _) ⊆
      (computableFunctions I (p + gateCount p t) ℓ).biUnion Cons := by
    intro T hT
    rw [mem_filter] at hT
    have hle := (card_nonInputComponents_add_ecomplexityGiven_le I (template A T)
      (single (tableFun T))).trans hT.2
    rw [Nat.cast_add] at hle
    have hgiven : ecomplexityGiven I (single (tableFun T)) (template A T) ≤ (ℓ : ℕ∞) :=
      (ENat.add_le_add_iff_left (ENat.natCast_ne_top _)).mp hle
    obtain ⟨c, hc, hsize⟩ := (ecomplexityGiven_le_iff _ _).mp hgiven
    refine mem_biUnion.mpr ⟨fun z => c.eval I z 0, ?_, ?_⟩
    · exact mem_computableFunctions.mpr ⟨c, fun z => funext fun o => by
        rw [Subsingleton.elim o 0, single_apply], hsize⟩
    · simp only [Cons, mem_filter, mem_univ, true_and]
      intro x
      rw [hc x, single_apply]
  -- Step 2: few tables are recovered by each such function.
  have hfiber : ∀ F ∈ computableFunctions I (p + gateCount p t) ℓ,
      #(Cons F) ≤ 2 ^ (2 ^ p - d) := by
    intro F hF
    obtain ⟨c, hc, hsize⟩ := mem_computableFunctions.mp hF
    have hFc : ∀ z, F z = c.eval I z 0 := fun z => (congrFun (hc z) 0).symm
    have hsupp : #c.inputSupport ≤ ℓ + 1 := by
      have h := c.card_inputSupport_le_cost (fun _ => 1) fun op =>
        Boolean.DeMorganBasis.arity_le_two I op
      rw [Program.cost_const, one_mul] at h
      omega
    obtain ⟨P, hP, hdisj⟩ := hcover (windowsOf c.inputSupport)
      ((card_windowsOf_le _).trans hsupp)
    -- Tables recovered by `F` that agree outside `P` are equal.
    have hinj : Set.InjOn (fun T : Fin (2 ^ p) → Bool => {y ∈ Pᶜ | T y = true})
        (Cons F : Set (Fin (2 ^ p) → Bool)) := by
      intro T hT T' hT' heq
      rw [mem_coe] at hT hT'
      simp only [Cons, mem_filter, mem_univ, true_and] at hT hT'
      have hout : ∀ y ∉ P, T y = T' y := fun y hy => by
        have := congrArg (y ∈ ·) heq
        simp only [mem_filter, mem_compl, hy, not_false_eq_true, true_and, eq_iff_iff] at this
        exact Bool.eq_iff_iff.mpr this
      funext y
      obtain ⟨x, rfl⟩ := (BitString.equivFin p).surjective y
      have hT1 := hT x
      have hT2 := hT' x
      simp only [tableFun_apply] at hT1 hT2
      rw [← hT1, ← hT2, hFc, hFc]
      refine congrFun (c.dependsOn_eval I fun z hz => ?_) 0
      refine Fin.addCases (fun i hz => ?_) (fun j hz => ?_) z hz
      · simp only [Fin.append_left]
      · simp only [Fin.append_right, template_apply]
        refine congrFun (value_congr A _ fun i hi y hy => hout y fun hyP => ?_) x
        exact disjoint_left.mp (hdisj i (mem_windowsOf hz hi)) hy hyP
    calc #(Cons F) ≤ #(Pᶜ.powerset) := card_le_card_of_injOn _
          (fun T _ => mem_powerset.mpr (filter_subset _ _)) hinj
      _ = 2 ^ (2 ^ p - #P) := by rw [card_powerset, card_compl, Fintype.card_fin]
      _ ≤ 2 ^ (2 ^ p - d) := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- Step 3: the union bound.
  have hcount : 3 * #(computableFunctions I (p + gateCount p t) ℓ) ≤ 2 ^ d := by
    have hpX := @Nat.lt_two_pow_self p
    have hM : p + gateCount p t + ℓ + 1 ≤ 3 * (2 ^ p) ^ 2 := by
      have h1 : 2 ^ p * p ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul_left _ hpX.le
      have h2 : t * 2 ^ p ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul_right _ ht
      have h3 : 64 * 2 ^ p ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul_right _ hX
      rw [gateCount_eq, sq]
      omega
    have h := three_mul_le_pow hX (hℓ.trans ht) hM (Boolean.DeMorganBasis.card_op_le I)
      (card_computableFunctions_mul_factorial_le_of_arity_le I (p + gateCount p t) ℓ 2
        (Boolean.DeMorganBasis.arity_le_two I))
    calc 3 * #(computableFunctions I (p + gateCount p t) ℓ) ≤ (2 ^ p) ^ (5 * ℓ + 5) := h
      _ = 2 ^ (p * (5 * ℓ + 5)) := by rw [← pow_mul]
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  have hdle : d ≤ 2 ^ p := by
    obtain ⟨P, hP, -⟩ := hcover ∅ (by simp)
    exact hP.trans ((card_le_univ P).trans_eq (Fintype.card_fin _))
  calc 3 * #{T : Fin (2 ^ p) → Bool |
        ecomplexity I (fun x => Fin.append (template A T x) (single (tableFun T) x)) ≤
          ((#(nonInputComponents (template A T)) + ℓ : ℕ) : ℕ∞)}
      ≤ 3 * #((computableFunctions I (p + gateCount p t) ℓ).biUnion Cons) :=
        Nat.mul_le_mul_left 3 (card_le_card hsub)
    _ ≤ 3 * (#(computableFunctions I (p + gateCount p t) ℓ) * 2 ^ (2 ^ p - d)) :=
        Nat.mul_le_mul_left 3 (card_biUnion_le_card_mul _ _ _ hfiber)
    _ = 3 * #(computableFunctions I (p + gateCount p t) ℓ) * 2 ^ (2 ^ p - d) := by ring
    _ ≤ 2 ^ d * 2 ^ (2 ^ p - d) := Nat.mul_le_mul_right _ hcount
    _ = 2 ^ (2 ^ p) := by rw [← pow_add, Nat.add_sub_cancel' hdle]

/-! ### Lifted windows -/

/-- The inputs `y < 2^p` whose residue modulo `N` lies in `S`. -/
def lift (p N : ℕ) (S : Finset ℕ) : Finset (Fin (2 ^ p)) :=
  {y | (y : ℕ) % N ∈ S}

@[simp] theorem mem_lift {N : ℕ} {S : Finset ℕ} {y : Fin (2 ^ p)} :
    y ∈ lift p N S ↔ (y : ℕ) % N ∈ S := by
  simp [lift]

/-- **Covers lift.** Sets covering the residues `0, …, N - 1` lift to sets covering the inputs. -/
theorem lift_cover {N : ℕ} (hN : 0 < N) (S : Fin t → Finset ℕ) (C : Finset (Fin t))
    (hC : ∀ u < N, ∃ i ∈ C, u ∈ S i) (y : Fin (2 ^ p)) : ∃ i ∈ C, y ∈ lift p N (S i) := by
  obtain ⟨i, hi, hu⟩ := hC _ (Nat.mod_lt _ hN)
  exact ⟨i, hi, mem_lift.mpr hu⟩

/-- At least `2^p / N` inputs `y < 2^p` have residue `u < N` (`Nat.count_modEq_card`). -/
private theorem le_card_residue {N u : ℕ} (hN : 0 < N) (hu : u < N) :
    2 ^ p / N ≤ #{y : Fin (2 ^ p) | (y : ℕ) % N = u} := by
  have hc := Nat.count_modEq_card (2 ^ p) hN u
  rw [Nat.count_eq_card_filter_range] at hc
  have hmap : #{y : Fin (2 ^ p) | (y : ℕ) % N = u} = #{x ∈ range (2 ^ p) | x ≡ u [MOD N]} := by
    rw [← card_map Fin.valEmbedding]
    congr 1
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range,
      Nat.ModEq, Nat.mod_eq_of_lt hu]
    exact ⟨fun ⟨y, hy, hx⟩ => hx ▸ ⟨y.isLt, hy⟩, fun ⟨hx, hy⟩ => ⟨⟨x, hx⟩, hy, rfl⟩⟩
  rw [hmap, hc]
  exact Nat.le_add_right _ _

/-- **Soundness for lifted windows** (library route). Suppose every set of at most `ℓ + 1` of the
sets `S i` misses some common residue `u < N`, with `ℓ ≤ t ≤ 2^p`, `2^p ≥ 64` and
`p (5ℓ + 5) ≤ 2^p / N`. Then for at most a third of the tables `T` does the template of the lifted
windows followed by `T` cost at most its distinct non-input gate functions plus `ℓ`, over any De
Morgan basis. -/
theorem three_mul_card_cheap_lift_le {N : ℕ} (hN : 0 < N) (S : Fin t → Finset ℕ) (ℓ : ℕ)
    (hmiss : ∀ B : Finset (Fin t), #B ≤ ℓ + 1 → ∃ u < N, ∀ i ∈ B, u ∉ S i)
    (ht : t ≤ 2 ^ p) (hℓ : ℓ ≤ t) (hX : 64 ≤ 2 ^ p) (hd : p * (5 * ℓ + 5) ≤ 2 ^ p / N) :
    3 * #{T : Fin (2 ^ p) → Bool |
      ecomplexity I (fun x => Fin.append (template (fun i => lift p N (S i)) T x)
          (single (tableFun T) x)) ≤
        ((#(nonInputComponents (template (fun i => lift p N (S i)) T)) + ℓ : ℕ) : ℕ∞)} ≤
      2 ^ (2 ^ p) := by
  refine three_mul_card_cheap_le _ ℓ (2 ^ p / N) (fun B hB => ?_) ht hℓ hX hd
  obtain ⟨u, hu, hmissB⟩ := hmiss B hB
  refine ⟨({y | (y : ℕ) % N = u} : Finset (Fin (2 ^ p))), le_card_residue hN hu, fun i hi => ?_⟩
  refine disjoint_left.mpr fun y hy hyP => hmissB i hi ?_
  rw [mem_lift] at hy
  rw [mem_filter] at hyP
  exact hyP.2 ▸ hy

end Cslib.MultiMCSP.Window
