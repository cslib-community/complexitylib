/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.BranchingProgram.PolyLength
public import Complexity.Computability.Circuit.Boolean.Barrington
public import Complexity.Computability.Circuit.Boolean.DepthClasses
import Complexity.Computability.Circuit.Boolean.NegationNormalForm
import Complexity.Computability.Circuit.Unfolding
import Complexity.Foundations.Data.Nat.PolynomialBound.Log
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Tactic.Ring

/-!
# Barrington's theorem as a class equality

**NC¹ is logarithmic formula depth**: a language is in NC¹ exactly when its slice at length `n`
has a De Morgan formula with `O(log n)` AND and OR gates on every path
(`Boolean.mem_NC_one_iff_formulaDepth_le`). A circuit unfolds into formulas of its depth
(`Circuit.toFormula`); conversely, a formula with `d` AND and OR gates on every path has a
negation normal form of depth at most `d + 1` (`Formula.nnf`), which is a circuit with fewer than
`2 ^ (d + 1)` gates.

**Barrington's theorem** [Barrington1989], [Jukna, Section 15.4][Jukna2012]: NC¹ is the class of
languages decided by permutation branching programs of width `5` and polynomial length
(`Boolean.NC_one_eq_polyLength_perm_five`). A formula of depth `O(log n)` becomes a program of
length `4 ^ O(log n)`, a polynomial (`Boolean.exists_four_pow_formulaDepth_le_of_mem_NC_one`), that
`σ`-computes it for any `5`-cycle `σ`
(`Boolean.exists_monoidProgram_alternatingGroup_computes_of_mem_NC_one`,
`Boolean.exists_monoidProgram_computes_of_mem_NC_one`). Conversely, a program over a finite
monoid `M` is a branching program of width `|M|`, through the action of `M` on itself by left
multiplication, and so a formula of depth logarithmic in its length [BarringtonTherien1988]: the
languages of polynomial-length programs over a finite monoid are in NC¹
(`Boolean.polyLength_subset_NC_one`). Five-cycles are even, so the programs of Barrington's
theorem are programs over the alternating group `A₅`
(`Boolean.NC_one_eq_polyLength_alternatingGroup`), and NC¹ is the class of languages of
polynomial-length programs over any finite monoid into which `A₅` embeds
(`Boolean.NC_one_eq_polyLength_of_injective`), for instance of polynomial-length permutation
branching programs, and of polynomial-length branching programs, of any fixed width `w ≥ 5`
(`Boolean.NC_one_eq_polyLength_perm`, `Boolean.NC_one_eq_polyLength_end`). The classes of
programs here are those of languages over `Bool`, `PolyLength Bool M`, and all these classes are
nonuniform.

## Main results

* `Cslib.Circuits.Boolean.mem_NC_one_iff_formulaDepth_le`: NC¹ is logarithmic formula depth.
* `Cslib.Circuits.Boolean.exists_monoidProgram_alternatingGroup_computes_of_mem_NC_one`,
  `Cslib.Circuits.Boolean.exists_monoidProgram_computes_of_mem_NC_one`: Barrington's theorem for
  the languages of NC¹, over `A₅` and over `S₅`.
* `Cslib.Circuits.Boolean.NC_one_subset_polyLength_alternatingGroup`,
  `Cslib.Circuits.Boolean.NC_one_subset_polyLength`,
  `Cslib.Circuits.Boolean.polyLength_subset_NC_one`: the inclusions.
* `Cslib.Circuits.Boolean.NC_one_eq_polyLength_perm_five`,
  `Cslib.Circuits.Boolean.NC_one_eq_polyLength_alternatingGroup`: Barrington's theorem as a class
  equality, over `S₅` and over `A₅`.
* `Cslib.Circuits.Boolean.NC_one_eq_polyLength_perm`,
  `Cslib.Circuits.Boolean.NC_one_eq_polyLength_end`: bounded-width branching programs of
  polynomial length decide exactly the languages of NC¹.

## References

* [D. A. Barrington, *Bounded-width polynomial-size branching programs recognize exactly those
  languages in NC¹*][Barrington1989]
* [D. A. Mix Barrington, D. Thérien, *Finite monoids and the fine structure of
  NC¹*][BarringtonTherien1988]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Equiv Equiv.Perm Cslib.BranchingPrograms

variable {L : Language Bool}

/-! ### NC¹ as logarithmic formula depth -/

/-- **NC¹ is logarithmic formula depth.** A language is in NC¹ exactly when, for a constant `c`,
its slice at every length `n` has formula depth at most `c (⌊log₂ n⌋ + 1)`: a De Morgan formula
with at most that many AND and OR gates on every path. -/
theorem mem_NC_one_iff_formulaDepth_le :
    L ∈ NC 1 ↔ ∃ c, ∀ n, formulaDepth (L.slice n) ≤ c * (Nat.log 2 n + 1) := by
  simp only [NC, PolylogDepth, DepthClass, pow_one, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨c, s, -, hC⟩
    refine ⟨c, fun n => ?_⟩
    obtain ⟨C, hCc, hCd, -⟩ := hC n
    calc formulaDepth (L.slice n) ≤ (C.toFormula 0).depthWith binaryCost :=
          formulaDepth_le (hCc.toFormula 0)
      _ ≤ (C.toFormula 0).depth := (C.toFormula 0).depthWith_le_depth binaryCost_le_one
      _ ≤ C.depth := C.depth_toFormula_le 0
      _ ≤ c * (Nat.log 2 n + 1) := hCd
  · rintro ⟨c, hc⟩
    refine ⟨c + 1, fun n => 2 ^ ((c + 1) * (Nat.log 2 n + 1)),
      polynomiallyBounded_two_pow_mul_log _, fun n => ?_⟩
    obtain ⟨F, hF, hd⟩ := exists_computes_depth_le_formulaDepth_add_one (L.slice n)
    have hd' : F.depth ≤ (c + 1) * (Nat.log 2 n + 1) := by
      have := hc n
      rw [add_mul, one_mul]
      omega
    refine ⟨F.toCircuit, hF.toCircuit, F.depth_toCircuit_le.trans hd', ?_⟩
    rw [F.size_toCircuit]
    exact (F.size_lt_pow_depth Boolean.arity_le_two le_rfl).le.trans
      (Nat.pow_le_pow_right two_pos hd')

/-! ### Barrington's theorem -/

/-- On a language in NC¹, `4` to the power of the formula depth is polynomially bounded. -/
theorem exists_four_pow_formulaDepth_le_of_mem_NC_one (hL : L ∈ NC 1) :
    ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧ ∀ n, 4 ^ formulaDepth (L.slice n) ≤ s n := by
  obtain ⟨c, hc⟩ := mem_NC_one_iff_formulaDepth_le.1 hL
  refine ⟨fun n => 2 ^ (2 * c * (Nat.log 2 n + 1)), polynomiallyBounded_two_pow_mul_log _,
    fun n => ?_⟩
  calc 4 ^ formulaDepth (L.slice n) ≤ 4 ^ (c * (Nat.log 2 n + 1)) :=
        Nat.pow_le_pow_right (by decide) (hc n)
    _ = 2 ^ (2 * c * (Nat.log 2 n + 1)) := by rw [mul_assoc, pow_mul 2 2]; rfl

/-- **Barrington's theorem for NC¹ over `A₅`.** For a language in NC¹ there is a polynomially
bounded `s` such that, at every length `n ≠ 0` and for every `5`-cycle `σ`, a program over the
alternating group `A₅` of length at most `s n` `σ`-computes the slice of the language at `n`. -/
theorem exists_monoidProgram_alternatingGroup_computes_of_mem_NC_one (hL : L ∈ NC 1) :
    ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧ ∀ (n : ℕ) [NeZero n] (σ : alternatingGroup (Fin 5)),
      IsFiveCycle (σ : Perm (Fin 5)) → ∃ P : MonoidProgram (Fin n) Bool (alternatingGroup (Fin 5)),
        P.toList.length ≤ s n ∧ P.Computes σ (L.slice n) := by
  obtain ⟨s, hs, hle⟩ := exists_four_pow_formulaDepth_le_of_mem_NC_one hL
  refine ⟨s, hs, fun n _ σ hσ => ?_⟩
  obtain ⟨P, hlen, hP⟩ :=
    exists_monoidProgram_alternatingGroup_computes_of_formulaDepth (L.slice n) hσ
  exact ⟨P, hlen.trans (hle n), hP⟩

/-- **Barrington's theorem for NC¹.** For a language in NC¹ there is a polynomially bounded `s`
such that, at every length `n ≠ 0` and for every `5`-cycle `σ`, a permutation branching program
of width `5` and length at most `s n` `σ`-computes the slice of the language at `n`. -/
theorem exists_monoidProgram_computes_of_mem_NC_one (hL : L ∈ NC 1) :
    ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧ ∀ (n : ℕ) [NeZero n] (σ : Perm (Fin 5)), IsFiveCycle σ →
      ∃ P : MonoidProgram (Fin n) Bool (Perm (Fin 5)),
        P.toList.length ≤ s n ∧ P.Computes σ (L.slice n) := by
  obtain ⟨s, hs, h⟩ := exists_monoidProgram_alternatingGroup_computes_of_mem_NC_one hL
  refine ⟨s, hs, fun n _ σ hσ => ?_⟩
  obtain ⟨P, hlen, hP⟩ := h n ⟨σ, hσ.mem_alternatingGroup⟩ hσ
  exact ⟨P.map (alternatingGroup (Fin 5)).subtype, (MonoidProgram.length_map _ P).trans_le hlen,
    hP.map _⟩

/-- **NC¹ is decided by polynomial-length programs over the alternating group `A₅`.** -/
theorem NC_one_subset_polyLength_alternatingGroup :
    NC 1 ⊆ PolyLength Bool (alternatingGroup (Fin 5)) := by
  intro L hL
  obtain ⟨s, hs, h⟩ := exists_monoidProgram_alternatingGroup_computes_of_mem_NC_one hL
  have hσ : IsFiveCycle ([0, 1, 2, 3, 4] : List (Fin 5)).formPerm :=
    isFiveCycle_formPerm (by decide) rfl
  refine ⟨s, hs, fun n => ?_⟩
  rcases n with _ | n
  · exact ⟨1, _, MonoidProgram.decides_one _, by simp⟩
  · obtain ⟨P, hlen, hPc⟩ := h (n + 1) ⟨_, hσ.mem_alternatingGroup⟩ hσ
    exact ⟨P, _, hPc.decides fun h => hσ.ne_one (congrArg Subtype.val h), hlen⟩

/-- **NC¹ is decided by polynomial-length permutation branching programs of width `5`.** -/
theorem NC_one_subset_polyLength : NC 1 ⊆ PolyLength Bool (Perm (Fin 5)) :=
  NC_one_subset_polyLength_alternatingGroup.trans
    (PolyLength.subset_of_injective (alternatingGroup (Fin 5)).subtype_injective)

/-- Left multiplication of a monoid on itself, transported to `Fin k` along a bijection. -/
private def leftMulEnd {M : Type*} [Monoid M] {k : ℕ} (e : M ≃ Fin k) :
    M →* Function.End (Fin k) where
  toFun m i := e (m * e.symm i)
  map_one' := funext fun i => show e (1 * e.symm i) = i by simp
  map_mul' m m' := funext fun i =>
    show e (m * m' * e.symm i) = e (m * e.symm (e (m' * e.symm i))) by simp [mul_assoc]

private theorem leftMulEnd_apply {M : Type*} [Monoid M] {k : ℕ} (e : M ≃ Fin k) (m : M)
    (i : Fin k) : leftMulEnd e m i = e (m * e.symm i) :=
  rfl

/-- **Polynomial-length programs over a finite monoid decide languages in NC¹**
[BarringtonTherien1988]: by left multiplication, a program over a finite monoid is a branching
program of width its cardinality, which is a formula of depth logarithmic in its length. -/
theorem polyLength_subset_NC_one (M : Type*) [Monoid M] [Finite M] : PolyLength Bool M ⊆ NC 1 := by
  classical
  rintro L ⟨s, hs, hP⟩
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin M
  obtain ⟨a, ha⟩ := hs.exists_clog_le_mul_log
  refine mem_NC_one_iff_formulaDepth_le.2 ⟨(Nat.clog 2 k + 1) * a + Nat.clog 2 k, fun n => ?_⟩
  obtain ⟨P, S, hPS, hlen⟩ := hP n
  obtain ⟨F, hF, hd, -⟩ := (P.map (leftMulEnd e)).exists_formula (e 1)
    (Finset.univ.filter fun i => e.symm i ∈ S)
  have hFc : F.Computes interpretation (L.slice n) := fun x => by
    rw [hF x, Bool.eq_iff_iff, decide_eq_true_iff, hPS x]
    simp [leftMulEnd_apply]
  calc formulaDepth (L.slice n) ≤ F.depthWith binaryCost := formulaDepth_le hFc
    _ ≤ (Nat.clog 2 k + 1) * Nat.clog 2 P.toList.length + Nat.clog 2 k := by
        simpa only [MonoidProgram.length_map] using hd
    _ ≤ (Nat.clog 2 k + 1) * (a * (Nat.log 2 n + 1)) + Nat.clog 2 k * (Nat.log 2 n + 1) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ ((Nat.clog_mono_right 2 hlen).trans (ha n)))
          (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
    _ = ((Nat.clog 2 k + 1) * a + Nat.clog 2 k) * (Nat.log 2 n + 1) := by ring

/-- **Barrington's theorem** [Barrington1989]: NC¹ is the class of languages decided by
permutation branching programs of width `5` and polynomial length. -/
theorem NC_one_eq_polyLength_perm_five : NC 1 = PolyLength Bool (Perm (Fin 5)) :=
  NC_one_subset_polyLength.antisymm (polyLength_subset_NC_one _)

/-- NC¹ is the class of languages decided by polynomial-length programs over any finite monoid
into which the alternating group `A₅` embeds. -/
theorem NC_one_eq_polyLength_of_injective {M : Type*} [Monoid M] [Finite M]
    {φ : alternatingGroup (Fin 5) →* M} (hφ : Function.Injective φ) : NC 1 = PolyLength Bool M :=
  (NC_one_subset_polyLength_alternatingGroup.trans (PolyLength.subset_of_injective hφ)).antisymm
    (polyLength_subset_NC_one M)

/-- **Barrington's theorem over `A₅`** [Barrington1989]: NC¹ is the class of languages decided by
polynomial-length programs over the alternating group `A₅`. -/
theorem NC_one_eq_polyLength_alternatingGroup :
    NC 1 = PolyLength Bool (alternatingGroup (Fin 5)) :=
  NC_one_eq_polyLength_of_injective (φ := MonoidHom.id _) Function.injective_id

/-- For every `w ≥ 5`, NC¹ is the class of languages decided by permutation branching programs of
width `w` and polynomial length, the programs over `Equiv.Perm (Fin w)`. -/
theorem NC_one_eq_polyLength_perm {w : ℕ} (hw : 5 ≤ w) : NC 1 = PolyLength Bool (Perm (Fin w)) :=
  NC_one_eq_polyLength_of_injective
    (φ := (viaEmbeddingHom (Fin.castLEEmb hw)).comp (alternatingGroup (Fin 5)).subtype)
    ((viaEmbeddingHom_injective _).comp (alternatingGroup (Fin 5)).subtype_injective)

/-- **Bounded-width branching programs of polynomial length decide exactly the languages of NC¹**
[Barrington1989]: for every `w ≥ 5`, NC¹ is the class of languages decided by branching programs
of width `w` and polynomial length, the programs over `Function.End (Fin w)`. -/
theorem NC_one_eq_polyLength_end {w : ℕ} (hw : 5 ≤ w) :
    NC 1 = PolyLength Bool (Function.End (Fin w)) := by
  have : Finite (Function.End (Fin w)) := inferInstanceAs (Finite (Fin w → Fin w))
  have hφ : Function.Injective (MulAction.toEndHom (M := Perm (Fin w)) (α := Fin w)) :=
    fun σ τ h => Equiv.ext fun i => congrFun h i
  exact NC_one_eq_polyLength_of_injective (φ := (MulAction.toEndHom.comp
    (viaEmbeddingHom (Fin.castLEEmb hw))).comp (alternatingGroup (Fin 5)).subtype)
    ((hφ.comp (viaEmbeddingHom_injective _)).comp (alternatingGroup (Fin 5)).subtype_injective)

end Cslib.Circuits.Boolean
