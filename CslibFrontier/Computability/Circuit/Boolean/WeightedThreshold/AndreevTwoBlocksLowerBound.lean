/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.AndreevSignCoherent
public import CslibFrontier.Foundations.Combinatorics.CornerCutting

/-!
# Sign-coherent depth-two circuits for Andreev's function with two address blocks

For two address blocks (`b = 2`) the sign-coherent lower bound is linear in `m`: every circuit of
depth at most two computing `andreev 2 m` whose bottom gates are sign-coherent
(`IsSignCoherent (andreevBlockVar 2 m)`) has at least `m - 1` bottom gates read by its output gate
(`sub_one_le_card_outputBottomGates_andreev_two`, and
`sub_one_le_of_depthTwoInputs_andreev_two` for `depthTwoInputs` circuits).

## Proof

Fix the table `x_c = c₀ ⊕ c₁` (`andreevXorTable`). On the unit square `(i, j)` of block counts (the
cube restriction `andreevCubePoint_add` of `AndreevSignCoherent`), Andreev's function is the XOR
of the two live bits or its negation. Restricted to the square, the circuit is an upper level set
of its live form (`isUpperLevelSet_eval_embedUpdate`). If no bottom gate had a nonzero mixed
difference there, i.e. none cut a corner of the square (`Cslib.Combinatorics.CutsCorner`), the
live form would have zero mixed difference (`circuitLiveForm_mixed_eq`), and no upper level set of
such a form is XOR. So some gate read by the output cuts a corner of every square
(`exists_cutsCorner_andreevGateGrid`).

With the table fixed, a sign-coherent gate is a threshold of `F₀ (s₀) + F₁ (s₁)` with each block
form monotone or antitone (`andreevGateGrid_orientation`), so by the ring lemma
`Cslib.Combinatorics.card_filter_cutsCorner_gridBorder_le` it cuts a corner of at most `4` of the
`4 (m - 1)` border squares of the grid. Hence `4 (m - 1) ≤ 4 G`.

## Correspondence with the unpublished draft (not publicly verifiable)

The statement is part (a) of the remark "Two address blocks" (`prop:k2`) of C. Reitwiessner,
*Depth-Two Threshold Circuits for Andreev's Function* (unpublished draft, not publicly
accessible). The draft's sketch is expanded here: "cuts off a corner" is formalized as a nonzero
mixed difference, the output gate's direct input wires are absorbed into its separable live
form, and the draft's "at most four turns on the border", which it checks numerically for
`m ≤ 11`, is proved for all `m` via two chains of border squares.

## References

* [cslib-frontier#4640](https://github.com/cslib-community/cslib-frontier/issues/4640):
  original AI-assisted work, milestone M4.
-/

public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open BitString Finset Cslib.Combinatorics

variable {m : ℕ}

/-! ### The XOR table -/

/-- The table `x_c = c₀ ⊕ c₁` on two address blocks. -/
def andreevXorTable : BitString (2 ^ 2) :=
  fun idx => (BitString.equivFin 2).symm idx 0 ^^ (BitString.equivFin 2).symm idx 1

/-- With the XOR table, Andreev's function at a cube point is the XOR of the block-count
parities. -/
theorem andreev_andreevCubePoint_xorTable {s : Fin 2 → ℕ} (hs : ∀ j, s j ≤ m) :
    andreev 2 m (andreevCubePoint 2 m andreevXorTable s) =
      (decide (s 0 % 2 = 1) ^^ decide (s 1 % 2 = 1)) := by
  rw [andreev_andreevCubePoint _ hs, andreevXorTable, Equiv.symm_apply_apply]

/-! ### Gates on the grid of block counts -/

/-- The value of the gate `k` of `c` at the cube point with table `x` and block counts `(i, j)`. -/
noncomputable def andreevGateGrid (c : Circuit signature (2 ^ 2 + 2 * m) 1) (k : Fin c.size)
    (x : BitString (2 ^ 2)) (i j : ℕ) : Bool :=
  ltfEval (inputWeight c.program k) (c.program.lines k).op.threshold
    (andreevCubePoint 2 m x ![i, j])

private theorem monotone_decide_le {f : ℕ → ℝ} (θ : ℝ) (hf : Monotone f) :
    Monotone fun i => decide (θ ≤ f i) := fun _ _ h => by
  simp only [Bool.le_iff_imp, decide_eq_true_eq]
  exact fun hi => hi.trans (hf h)

private theorem antitone_decide_le {f : ℕ → ℝ} (θ : ℝ) (hf : Antitone f) :
    Antitone fun i => decide (θ ≤ f i) := fun _ _ h => by
  simp only [Bool.le_iff_imp, decide_eq_true_eq]
  exact fun hi => hi.trans (hf h)

/-- **Orientation**: with the table fixed, a sign-coherent gate is monotone or antitone in each
block count, uniformly in the other one. -/
theorem andreevGateGrid_orientation {c : Circuit signature (2 ^ 2 + 2 * m) 1} {k : Fin c.size}
    (hk : IsSignCoherent (andreevBlockVar 2 m) (inputWeight c.program k)) (x : BitString (2 ^ 2)) :
    ((∀ j, Monotone fun i => andreevGateGrid c k x i j) ∨
        ∀ j, Antitone fun i => andreevGateGrid c k x i j) ∧
      ((∀ i, Monotone (andreevGateGrid c k x i)) ∨ ∀ i, Antitone (andreevGateGrid c k x i)) := by
  have hval (i j : ℕ) : andreevGateGrid c k x i j = decide ((c.program.lines k).op.threshold ≤
      (∑ idx, inputWeight c.program k (andreevTableIndex 2 m idx) * (x idx).toNat) +
        ((∑ t : Fin m, if (t : ℕ) < i then inputWeight c.program k (andreevBlockVar 2 m 0 t)
          else 0) +
          ∑ t : Fin m, if (t : ℕ) < j then inputWeight c.program k (andreevBlockVar 2 m 1 t)
            else 0)) := by
    rw [andreevGateGrid, ltfEval, sum_mul_andreevCubePoint, Fin.sum_univ_two]
    rfl
  refine ⟨?_, ?_⟩
  · rcases monotone_or_antitone_blockForm hk 0 with h | h
    · exact Or.inl fun j => (funext fun i => hval i j) ▸
        monotone_decide_le _ ((h.add_const _).const_add _)
    · exact Or.inr fun j => (funext fun i => hval i j) ▸
        antitone_decide_le _ ((h.add_const _).const_add _)
  · rcases monotone_or_antitone_blockForm hk 1 with h | h
    · exact Or.inl fun i => (funext (hval i)) ▸
        monotone_decide_le _ ((h.const_add _).const_add _)
    · exact Or.inr fun i => (funext (hval i)) ▸
        antitone_decide_le _ ((h.const_add _).const_add _)

/-! ### Every square needs a corner-cutting gate -/

/-- **Every square needs a corner-cutting gate**: for every circuit of depth at most two computing
`andreev 2 m` and every unit square `(i, j)` of block counts, some bottom gate read by the output
cuts a corner of the square when the table is `andreevXorTable`. No sign condition is needed. -/
theorem exists_cutsCorner_andreevGateGrid (c : Circuit signature (2 ^ 2 + 2 * m) 1)
    (hd : c.depth ≤ 2) (hcomp : c.Computes interpretation (single (andreev 2 m))) {i j : ℕ}
    (hi : i < m) (hj : j < m) :
    ∃ k ∈ outputBottomGates c 0, CutsCorner (andreevGateGrid c k andreevXorTable) i j := by
  classical
  by_contra hno
  push Not at hno
  let q : Fin 2 → Fin m := ![⟨i, hi⟩, ⟨j, hj⟩]
  obtain ⟨τ, hτ⟩ := isUpperLevelSet_eval_embedUpdate c hd 0 (andreevLiveVar_injective 2 m q)
    (andreevCubePoint 2 m andreevXorTable fun l => q l)
  set F := circuitLiveForm c 0 (andreevLiveVar 2 m q)
    (circuitSplitGates c 0 (univ.image (andreevLiveVar 2 m q))
      (andreevCubePoint 2 m andreevXorTable fun l => q l)) fun k u =>
      ltfEval (inputWeight c.program k) (c.program.lines k).op.threshold
        (embedUpdate (andreevLiveVar 2 m q) (andreevCubePoint 2 m andreevXorTable fun l => q l) u)
  have hpt (u : Fin 2 → Bool) :
      (fun l => (q l : ℕ) + (u l).toNat) = ![i + (u 0).toNat, j + (u 1).toNat] := by
    funext l; fin_cases l <;> rfl
  have hgate (k : Fin c.size) (u : Fin 2 → Bool) :
      ltfEval (inputWeight c.program k) (c.program.lines k).op.threshold
          (embedUpdate (andreevLiveVar 2 m q)
            (andreevCubePoint 2 m andreevXorTable fun l => q l) u) =
        andreevGateGrid c k andreevXorTable (i + (u 0).toNat) (j + (u 1).toNat) := by
    rw [← andreevCubePoint_add, hpt, andreevGateGrid]
  have heval (u : Fin 2 → Bool) : decide (τ ≤ F u) =
      (decide ((i + (u 0).toNat) % 2 = 1) ^^ decide ((j + (u 1).toNat) % 2 = 1)) := by
    have hs (l : Fin 2) : (q l : ℕ) + (u l).toNat ≤ m := by
      have := (q l).isLt; have := Bool.toNat_le (u l); omega
    rw [← hτ u]
    dsimp only
    rw [← andreevCubePoint_add, congrFun (hcomp _) 0]
    exact andreev_andreevCubePoint_xorTable hs
  have hmix : F ![false, false] + F ![true, true] = F ![true, false] + F ![false, true] := by
    refine circuitLiveForm_mixed_eq c 0 _ _ _ fun k hk => ?_
    have := hno k (circuitSplitGates_subset c 0 _ _ hk)
    rw [CutsCorner, not_not] at this
    simpa only [hgate, Matrix.cons_val_zero, Matrix.cons_val_one, Bool.toNat_false,
      Bool.toNat_true, add_zero] using this
  have h00 := heval ![false, false]
  have h11 := heval ![true, true]
  have h10 := heval ![true, false]
  have h01 := heval ![false, true]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Bool.toNat_false, Bool.toNat_true,
    add_zero] at h00 h11 h10 h01
  rcases Nat.mod_two_eq_zero_or_one i with hi2 | hi2 <;>
    rcases Nat.mod_two_eq_zero_or_one j with hj2 | hj2 <;>
    simp [hi2, hj2, Nat.add_mod] at h00 h11 h10 h01 <;> linarith

/-! ### The lower bound -/

/-- **Two address blocks, lower bound** (draft remark "Two address blocks", part (a)): a circuit of
depth at most two computing `andreev 2 m` whose bottom gates read by the output are sign-coherent
has at least `m - 1` of them. -/
theorem sub_one_le_card_outputBottomGates_andreev_two (c : Circuit signature (2 ^ 2 + 2 * m) 1)
    (hd : c.depth ≤ 2) (hcomp : c.Computes interpretation (single (andreev 2 m)))
    (hcoh : ∀ k ∈ outputBottomGates c 0,
      IsSignCoherent (andreevBlockVar 2 m) (inputWeight c.program k)) :
    m - 1 ≤ #(outputBottomGates c 0) := by
  classical
  have hcover : gridBorder m ⊆ (outputBottomGates c 0).biUnion fun k =>
      (gridBorder m).filter fun p => CutsCorner (andreevGateGrid c k andreevXorTable) p.1 p.2 := by
    intro p hp
    obtain ⟨hp1, hp2, -⟩ := mem_gridBorder.mp hp
    obtain ⟨k, hk, hcut⟩ := exists_cutsCorner_andreevGateGrid c hd hcomp hp1 hp2
    exact mem_biUnion.mpr ⟨k, hk, mem_filter.mpr ⟨hp, hcut⟩⟩
  have hring : ∑ k ∈ outputBottomGates c 0,
      #((gridBorder m).filter fun p => CutsCorner (andreevGateGrid c k andreevXorTable) p.1 p.2) ≤
        ∑ _k ∈ outputBottomGates c 0, 4 := sum_le_sum fun k hk => by
    obtain ⟨h₁, h₂⟩ := andreevGateGrid_orientation (hcoh k hk) andreevXorTable
    exact card_filter_cutsCorner_gridBorder_le h₁ h₂ m
  rw [sum_const, smul_eq_mul] at hring
  have := (card_le_card hcover).trans card_biUnion_le
  have := le_card_gridBorder m
  omega

/-- **Two address blocks, lower bound for `depthTwoInputs`**: if a sign-coherent circuit
`depthTwoInputs bottom args u v θ` with `G` bottom gates computes `andreev 2 m`, then
`m - 1 ≤ G`. -/
theorem sub_one_le_of_depthTwoInputs_andreev_two {G : ℕ} (bottom : Fin G → Op)
    (args : ∀ j, Fin (bottom j).arity → Fin (2 ^ 2 + 2 * m)) (u : Fin G → ℝ)
    (v : Fin (2 ^ 2 + 2 * m) → ℝ) (θ : ℝ)
    (hcomp : (depthTwoInputs bottom args u v θ).Computes interpretation (single (andreev 2 m)))
    (hcoh : ∀ j, IsSignCoherent (andreevBlockVar 2 m) (argWeight (bottom j) (args j))) :
    m - 1 ≤ G := by
  set c := depthTwoInputs bottom args u v θ
  obtain ⟨top, htop⟩ : ∃ top, c.outputs 0 = .gate top := ⟨_, rfl⟩
  have hB : #(outputBottomGates c 0) ≤ G := by
    have := card_outputBottomGates_lt_size htop
    have hs : c.size = G + 1 := size_depthTwoInputs ..
    omega
  exact (sub_one_le_card_outputBottomGates_andreev_two c (depth_depthTwoInputs_le ..) hcomp
    fun k hk => isSignCoherent_inputWeight_depthTwoInputs bottom args u v θ hcoh htop
      (by rwa [outputBottomGates_of_gate htop] at hk)).trans hB

end Cslib.Circuits.Boolean.WeightedThreshold
