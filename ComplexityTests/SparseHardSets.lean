/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Sparse
import Complexity.Computability.Complexity.Classes.Sparse.Fortune
import Complexity.Computability.Complexity.Classes.Sparse.Mahaney

/-!
# Sparse problems and the procedures of Fortune and Mahaney

Sparse and non-sparse problems; the pruning rules and the searches of the self-reduction tree on
concrete inputs, including a bound too small for Fortune's procedure to be correct; and both
procedures as exponential-time deciders for `SAT`, which satisfy the hypotheses of
`Cslib.Complexity.Fortune.accepts_iff` and `Cslib.Complexity.Mahaney.accepts_iff` with the
identity reductions of `UNSAT` and `SAT` to the encodings of their members and an exponential
bound.
-/

namespace ComplexityTests.SparseHardSets

open Cslib Cslib.Complexity Cslib.Complexity.Fortune Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Sparse problems -/

/-- Words of even length consisting only of `true`s. -/
private def evenOnes : Set (List Bool) := {w | Even w.length ∧ ∀ b ∈ w, b = true}

example : evenOnes ∈ SPARSE encBits ∧ (evenOnes : Language Bool) ∈ Circuits.Boolean.PPoly :=
  ⟨mem_SPARSE_of_unary fun _ hw => hw.2,
    Circuits.Boolean.PPoly.of_mem_SPARSE (mem_SPARSE_of_unary fun _ hw => hw.2)⟩

/-- A finite problem over an infinite type with any encoding, and its subsets. -/
example (enc : ℕ ↪ List Bool) : ({0, 5, 7} : Set ℕ) ∈ SPARSE enc ∧ ({5} : Set ℕ) ∈ SPARSE enc :=
  let h : ({0, 5, 7} : Set ℕ) ∈ SPARSE enc := (Set.toFinite _).mem_SPARSE
  ⟨h, mem_SPARSE_of_subset (by simp) h⟩

/-- All words are not sparse, so neither are all formulas through their encodings. -/
example : (Set.univ : Set (List Bool)) ∉ SPARSE encBits ∧
    (Set.univ : Set (List Bool)) ∉ SPARSE (Function.Embedding.refl _) := by
  refine ⟨univ_notMem_SPARSE, fun h => univ_notMem_SPARSE ?_⟩
  simpa using image_mem_SPARSE_encBits_iff.mpr h

/-! ### Pruning and search on concrete inputs -/

/-- The first entry with each label is kept, then at most `c + 1` of them. -/
example : prune (· % 3) 5 [1, 3, 4, 2, 1, 5] = [1, 3, 2] ∧
    prune (· % 3) 1 [1, 3, 4, 2, 1, 5] = [1, 3] ∧ prune id 0 [7, 7, 8] = [7] := by
  decide

example : expand 4 [[], [(1, false)]] =
    [[(4, true)], [(4, false)], [(1, false), (4, true)], [(1, false), (4, false)]] := by
  decide

/-- With the encodings of the formulas as labels, no two nodes share a label, so a bound larger
than the tree keeps every node and the procedure is a brute-force search. -/
example : accepts encCNF 8 [[(0, true), (1, false)], [(1, true)]] = true ∧
    accepts encCNF 8 [[(0, true)], [(0, false)]] = false ∧
    accepts encCNF 8 [[(0, true)], [(1, true)], [(0, false), (1, false)]] = false := by
  decide

/-- A bound too small breaks the procedure: with `c = 0` only the first child, which sets the
variable to `true`, survives the first level, so the satisfiable formula `¬x₀` is rejected. -/
example : search (fun a => encCNF (SAT.units a ++ [[(0, false)]])) 0 [[(0, false)]] =
      [[(0, true)]] ∧
    accepts encCNF 0 [[(0, false)]] = false ∧ [[(0, false)]] ∈ SAT :=
  ⟨by decide, by decide, ⟨fun _ => false, rfl⟩⟩

/-! ### Fortune's procedure with an exponential bound -/

/-- At most `(M + 1) 2 ^ M` words have length at most `M`. -/
private theorem card_le_of_length_le {M : ℕ} (s : Finset (List Bool))
    (hs : ∀ w ∈ s, w.length ≤ M) : s.card ≤ (M + 1) * 2 ^ M := by
  classical
  have hsub : s ⊆ (Finset.range (M + 1)).biUnion fun n =>
      (Finset.univ : Finset (Fin n → Bool)).image List.ofFn := by
    intro w hw
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨w.length, Nat.lt_succ_of_le (hs w hw), fun i => w[i], List.ofFn_getElem⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  refine (Finset.sum_le_card_nsmul _ _ (2 ^ M) fun n hn => ?_).trans (by simp)
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  exact Nat.pow_le_pow_right two_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))

/-- The hypotheses of `accepts_iff` are satisfiable: the encoding reduces `UNSAT` to the encodings
of unsatisfiable formulas, and the number of words of bounded length bounds the census. So
Fortune's procedure with an exponential bound decides `SAT`. -/
example (φ : CNF ℕ) :
    let L := (encCNF φ).length
    let M := L + L * (8 * L + 11)
    accepts encCNF ((M + 1) * 2 ^ M) φ = true ↔ φ ∈ SAT := by
  intro L M
  refine accepts_iff (K := encCNF '' UNSAT) (M := M) (fun ψ => ?_) (fun a ha hlen => ?_)
    (fun s hs => card_le_of_length_le s fun w hw => (hs w hw).2)
  · rw [encCNF.injective.mem_set_image]
    rfl
  · have hunits := SAT.length_encCNF_units_le ha
    have hvars := SAT.length_vars_le φ
    dsimp only [M, L]
    rw [SAT.length_encCNF_append]
    nlinarith

/-! ### Mahaney's theorem -/

/-- A stage keeps the first node and the first node with each label `(a + b) % 3` after it, and
drops the first node when more than `t` others remain; pruning repeats it. -/
example : Mahaney.stage (fun a b : ℕ => (a + b) % 3) 1 [0, 1, 4, 2] = [1, 2] ∧
    Mahaney.stage (fun a b : ℕ => (a + b) % 3) 2 [0, 1, 4, 2] = [0, 1, 2] ∧
    Mahaney.prune (fun a b : ℕ => (a + b) % 3) 1 [0, 1, 4, 2] = [1, 2] ∧
    Mahaney.prune (fun a b : ℕ => (a + b) % 3) 0 [0, 1, 4, 2] = [2] := by
  decide

/-- The disjunction of the nodes fixing `x₀` to `true` and to `false` in `x₀ ∧ ¬x₀` is
unsatisfiable, while in `x₁` it is satisfiable. -/
example : Mahaney.disj [[(0, true)], [(0, false)]] [(0, true)] [(0, false)] ∉ SAT ∧
    Mahaney.disj [[(1, true)]] [(0, true)] [(0, false)] ∈ SAT := by
  rw [Mahaney.disj_mem_SAT_iff, Mahaney.disj_mem_SAT_iff]
  refine ⟨fun h => ?_, .inl ⟨fun _ => true, rfl⟩⟩
  rcases h with ⟨σ, hσ⟩ | ⟨σ, hσ⟩ <;> cases h0 : σ 0 <;> simp [SAT.units, CNF.eval, h0] at hσ

example : Mahaney.accepts encCNF 8 [[(0, true), (1, false)], [(1, true)]] = true ∧
    Mahaney.accepts encCNF 8 [[(0, true)], [(0, false)]] = false := by
  decide

/-- The hypotheses of `Mahaney.accepts_iff` are satisfiable: the encoding reduces `SAT` to the
encodings of satisfiable formulas, and the number of words of bounded length bounds the census. -/
example (φ : CNF ℕ) :
    let L := (encCNF φ).length
    let M := L * L * (16 * L + 21) + L
    Mahaney.accepts encCNF ((M + 1) * 2 ^ M) φ = true ↔ φ ∈ SAT := by
  intro L M
  refine Mahaney.accepts_iff (K := encCNF '' SAT) (M := M) (fun ψ => ?_)
    (fun a b ha hb hla hlb => ?_) (fun s hs => card_le_of_length_le s fun w hw => (hs w hw).2)
  · rw [encCNF.injective.mem_set_image]
  · have hvars := SAT.length_vars_le φ
    have hla' : a.length ≤ L := hla.trans hvars
    have hlb' : b.length ≤ L := hlb.trans hvars
    refine (Mahaney.length_encCNF_disj_le ha hb).trans ?_
    dsimp only [M]
    gcongr

end ComplexityTests.SparseHardSets
