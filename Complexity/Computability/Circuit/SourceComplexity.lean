/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Computability.Circuit.RelativeComplexity
public import Cslib.Computability.Circuit.Simulation
import Complexity.Computability.Circuit.Simulation

/-!
# Weighted circuit complexity from supplied values

A source family `sources : X → Fin n → U` supplies exactly the inputs available to a circuit
computing `target : X → Fin m → U`. The common domain may be arbitrary. No coordinates of `X`
are implicitly available, and supplying the sources has no cost. The minimum of `Program.cost`
over implementing circuits is recorded in `ℕ∞`, with `⊤` when no circuit exists.

Operation costs may be zero. Consequently, zero weighted complexity need not mean that the
target is obtained by wiring. Even with an empty common domain, a syntactic circuit must exist;
vacuous correctness alone does not provide outputs from zero inputs over an empty signature.

Unit costs recover native support complexity by taking the support subtype as the common domain.
Supplying both raw inputs and helper values recovers native `ecomplexityGiven`. These bridges
require no chosen extension of the target outside the range of the sources.

The model allows arbitrary finite gate arities and natural-number weights. Every output must
be wired; constants must be supplied or implemented by gates. In particular, the syntax does
not use Boyack's convention assigning zero to disconnected vertices.

## Main definitions

* `Cslib.Circuits.Circuit.ComputesFrom`: computation from exactly the supplied source family.
* `Cslib.Circuits.ecomplexityFrom`: minimum weighted cost of such a computation.

## Main results

* `Cslib.Circuits.ecomplexityFrom_le_iff`: every finite budget has a circuit witness.
* `Cslib.Circuits.ecomplexityFrom_comp_le`: composition through an intermediate supplied family.
* `Cslib.Circuits.ecomplexityFrom_map_le`: homomorphisms cannot increase source complexity;
  `ecomplexityFrom_map_eq` gives equality for injective homomorphisms.
* `Cslib.Circuits.ecomplexityFrom_unit_subtype`,
  `Cslib.Circuits.ecomplexityFrom_unit_append`: bridges to native circuit complexity.

## References

* Ported from Complexity/Relative.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
  Homomorphism transport adapts LowerBound/Fusion/Comap.lean from the same development.
* [S. W. Boyack, *The Robustness of Combinatorial Measures of Boolean Matrix
  Complexity*][Boyack1985], Definition 2.1 and Proposition 2.2, pp. 29–30, for computation
  relative to supplied functions and its composition inequality.
-/

@[expose] public section

namespace Cslib.Circuits

universe v u w z

variable {σ : Signature.{v}} {U : Type u} {X : Type w} {n m p : ℕ}

/-- Compute the target family from exactly the supplied values, without implicit raw inputs. -/
def Circuit.ComputesFrom (c : Circuit σ n m) (I : Interpretation σ U)
    (target : X → Fin m → U) (sources : X → Fin n → U) : Prop :=
  ∀ x, c.eval I (sources x) = target x

variable {I : Interpretation σ U} {cost cost' : σ.Op → ℕ}
  {target : X → Fin m → U} {sources : X → Fin n → U}
  {V : Type z} {J : Interpretation σ V}

/-- The same circuit computes the homomorphic image of the supplied-source problem. -/
theorem Circuit.ComputesFrom.map {c : Circuit σ n m}
    (hc : c.ComputesFrom I target sources) (h : Homomorphism I J) :
    c.ComputesFrom J (fun x => h.map ∘ target x) (fun x => h.map ∘ sources x) := by
  intro x
  rw [← c.map_eval h, hc x]

/-- An injective homomorphism also reflects computation of the supplied-source problem. -/
theorem Circuit.computesFrom_map_iff (c : Circuit σ n m) (h : Homomorphism I J)
    (hinj : Function.Injective h.map) :
    c.ComputesFrom J (fun x => h.map ∘ target x) (fun x => h.map ∘ sources x) ↔
      c.ComputesFrom I target sources := by
  refine ⟨fun hc x => funext fun i => hinj ?_, fun hc => hc.map h⟩
  exact congrFun ((c.map_eval h (sources x)).trans (hc x)) i

/-- Equal supplied values must give equal target values. -/
theorem Circuit.ComputesFrom.agrees_on_fibers {c : Circuit σ n m}
    (hc : c.ComputesFrom I target sources) {x y : X} (h : sources x = sources y) :
    target x = target y := by
  rw [← hc x, ← hc y, h]

/-- Compose computations through an intermediate supplied family. -/
theorem Circuit.ComputesFrom.comp {c : Circuit σ n m} {d : Circuit σ m p}
    {f : X → Fin m → U} {g : X → Fin p → U}
    (hc : c.ComputesFrom I f sources) (hd : d.ComputesFrom I g f) :
    (d.comp c).ComputesFrom I g sources := fun x => by
  rw [Circuit.eval_comp, hc x, hd x]

/-- Compute two target families from the same supplied values. -/
theorem Circuit.ComputesFrom.append {c : Circuit σ n m} {d : Circuit σ n p}
    {f : X → Fin m → U} {g : X → Fin p → U}
    (hc : c.ComputesFrom I f sources) (hd : d.ComputesFrom I g sources) :
    (c.append d).ComputesFrom I (fun x => Fin.append (f x) (g x)) sources := fun x => by
  rw [Circuit.eval_append, hc x, hd x]

/-- Computing from the inclusion `Subtype.val` of a subset `S` is equivalent to
`c.ComputesOn I S f`. -/
@[simp] theorem Circuit.computesFrom_subtype_iff (c : Circuit σ n m)
    (S : Set (Fin n → U)) (f : (Fin n → U) → Fin m → U) :
    c.ComputesFrom I (fun x : S => f x) Subtype.val ↔ c.ComputesOn I S f := by
  simp only [ComputesFrom, ComputesOn, Set.EqOn, Subtype.forall]

/-- An explicitly supplied extension identifies source computation with computation on its range. -/
theorem Circuit.computesFrom_iff_computesOn_range (c : Circuit σ n m)
    (f : (Fin n → U) → Fin m → U) (hf : ∀ x, f (sources x) = target x) :
    c.ComputesFrom I target sources ↔ c.ComputesOn I (Set.range sources) f := by
  simp only [ComputesFrom, ComputesOn, Set.EqOn, Set.forall_mem_range, hf]

/-- Minimum weighted cost of computing a target from the supplied values, or `⊤` if no circuit
does so. Every operation has finite natural-number cost; supplying the sources is free. -/
noncomputable def ecomplexityFrom (I : Interpretation σ U) (cost : σ.Op → ℕ)
    (target : X → Fin m → U) (sources : X → Fin n → U) : ℕ∞ :=
  ⨅ c : {c : Circuit σ n m // c.ComputesFrom I target sources}, (c.1.program.cost cost : ℕ∞)

/-- Every circuit computing `target` from `sources` bounds `ecomplexityFrom` by its weighted
cost. -/
theorem ecomplexityFrom_le_of_computesFrom (c : Circuit σ n m)
    (hc : c.ComputesFrom I target sources) :
    ecomplexityFrom I cost target sources ≤ c.program.cost cost :=
  iInf_le (fun c : {c // c.ComputesFrom I target sources} => (c.1.program.cost cost : ℕ∞)) ⟨c, hc⟩

/-- `ecomplexityFrom` is finite (`≠ ⊤`) if and only if some circuit computes `target` from
`sources`. -/
theorem ecomplexityFrom_ne_top_iff :
    ecomplexityFrom I cost target sources ≠ ⊤ ↔
      ∃ c : Circuit σ n m, c.ComputesFrom I target sources := by
  rw [ecomplexityFrom, ENat.iInf_natCast_ne_top, nonempty_subtype]

/-- `ecomplexityFrom` is `⊤` if and only if no circuit computes `target` from `sources`. -/
@[simp] theorem ecomplexityFrom_eq_top_iff :
    ecomplexityFrom I cost target sources = ⊤ ↔
      ¬ ∃ c : Circuit σ n m, c.ComputesFrom I target sources := by
  simpa using not_congr (ecomplexityFrom_ne_top_iff (I := I) (cost := cost)
    (target := target) (sources := sources))

/-- A representable target has a circuit attaining its minimum weighted cost. -/
theorem exists_computesFrom_cost_eq_ecomplexityFrom
    (h : ∃ c : Circuit σ n m, c.ComputesFrom I target sources) :
    ∃ c : Circuit σ n m, c.ComputesFrom I target sources ∧
      (c.program.cost cost : ℕ∞) = ecomplexityFrom I cost target sources := by
  have : Nonempty {c : Circuit σ n m // c.ComputesFrom I target sources} := nonempty_subtype.mpr h
  obtain ⟨⟨c, hc⟩, hmin⟩ := ENat.exists_eq_iInf
    (fun c : {c : Circuit σ n m // c.ComputesFrom I target sources} =>
      (c.1.program.cost cost : ℕ∞))
  exact ⟨c, hc, hmin⟩

/-- Every finite weighted budget is witnessed by a circuit. -/
theorem ecomplexityFrom_le_iff {k : ℕ} :
    ecomplexityFrom I cost target sources ≤ k ↔
      ∃ c : Circuit σ n m, c.ComputesFrom I target sources ∧ c.program.cost cost ≤ k := by
  constructor
  · intro h
    have hne := ne_top_of_le_ne_top (ENat.natCast_ne_top k) h
    obtain ⟨c, hc, hcost⟩ :=
      exists_computesFrom_cost_eq_ecomplexityFrom (ecomplexityFrom_ne_top_iff.mp hne)
    exact ⟨c, hc, by exact_mod_cast hcost.trans_le h⟩
  · rintro ⟨c, hc, hk⟩
    exact (ecomplexityFrom_le_of_computesFrom c hc).trans (by exact_mod_cast hk)

/-- A lower bound holds exactly when it holds for every implementing circuit. -/
theorem le_ecomplexityFrom_iff {k : ℕ∞} :
    k ≤ ecomplexityFrom I cost target sources ↔
      ∀ c : Circuit σ n m, c.ComputesFrom I target sources → k ≤ c.program.cost cost := by
  simp only [ecomplexityFrom, le_iInf_iff, Subtype.forall]

/-- Applying a homomorphism to every supplied and target value cannot increase complexity.
The operation weights and implementing circuit are unchanged; the map need not be injective. -/
theorem ecomplexityFrom_map_le (h : Homomorphism I J) (weight : σ.Op → ℕ)
    (target : X → Fin m → U) (sources : X → Fin n → U) :
    ecomplexityFrom J weight (fun x => h.map ∘ target x) (fun x => h.map ∘ sources x) ≤
      ecomplexityFrom I weight target sources :=
  le_ecomplexityFrom_iff.mpr fun c hc => ecomplexityFrom_le_of_computesFrom c (hc.map h)

/-- An injective homomorphism preserves supplied-source complexity, including infinity. -/
theorem ecomplexityFrom_map_eq (h : Homomorphism I J) (hinj : Function.Injective h.map)
    (weight : σ.Op → ℕ) (target : X → Fin m → U) (sources : X → Fin n → U) :
    ecomplexityFrom J weight (fun x => h.map ∘ target x) (fun x => h.map ∘ sources x) =
      ecomplexityFrom I weight target sources := by
  simp only [ecomplexityFrom, iInf_subtype, Circuit.computesFrom_map_iff _ h hinj]

/-- `ecomplexityFrom` is monotone in the operation cost weights. -/
theorem ecomplexityFrom_mono_cost (h : ∀ op, cost op ≤ cost' op) :
    ecomplexityFrom I cost target sources ≤ ecomplexityFrom I cost' target sources :=
  le_ecomplexityFrom_iff.mpr fun c hc =>
    (ecomplexityFrom_le_of_computesFrom c hc).trans (by exact_mod_cast c.program.cost_mono h)

/-- Selecting, permuting or duplicating supplied values is free. -/
@[simp] theorem ecomplexityFrom_wiring (sources : X → Fin n → U) (select : Fin m → Fin n) :
    ecomplexityFrom I cost (fun x => sources x ∘ select) sources = 0 := by
  apply nonpos_iff_eq_zero.mp
  exact ecomplexityFrom_le_of_computesFrom (Circuit.wiring σ select) (fun _ => rfl)

/-- Computing `sources` from `sources` itself has weighted complexity `0`. -/
@[simp] theorem ecomplexityFrom_self (sources : X → Fin n → U) :
    ecomplexityFrom I cost sources sources = 0 :=
  ecomplexityFrom_wiring sources id

/-- If the sources identify two points distinguished by the target, no implementation exists. -/
theorem ecomplexityFrom_eq_top_of_fiber_collision {x y : X} (h : sources x = sources y)
    (hne : target x ≠ target y) : ecomplexityFrom I cost target sources = ⊤ := by
  rw [ecomplexityFrom_eq_top_iff]
  rintro ⟨c, hc⟩
  exact hne (hc.agrees_on_fibers h)

/-- Computing through an intermediate family adds at most the two weighted complexities. -/
theorem ecomplexityFrom_comp_le (f : X → Fin m → U) (g : X → Fin p → U)
    (sources : X → Fin n → U) :
    ecomplexityFrom I cost g sources ≤
      ecomplexityFrom I cost f sources + ecomplexityFrom I cost g f := by
  conv_rhs => simp only [ecomplexityFrom, ENat.iInf_add, ENat.add_iInf]
  refine le_iInf fun d => le_iInf fun c => ?_
  exact (ecomplexityFrom_le_of_computesFrom (cost := cost) (d.1.comp c.1) (c.2.comp d.2)).trans_eq
    (by rw [Circuit.cost_program_comp, Nat.cast_add])

/-- Computing two families from the same sources costs at most the sum of their complexities. -/
theorem ecomplexityFrom_append_le (f : X → Fin m → U) (g : X → Fin p → U)
    (sources : X → Fin n → U) :
    ecomplexityFrom I cost (fun x => Fin.append (f x) (g x)) sources ≤
      ecomplexityFrom I cost f sources + ecomplexityFrom I cost g sources := by
  conv_rhs => simp only [ecomplexityFrom, ENat.iInf_add, ENat.add_iInf]
  refine le_iInf fun d => le_iInf fun c => ?_
  exact (ecomplexityFrom_le_of_computesFrom (cost := cost) (c.1.append d.1)
    (c.2.append d.2)).trans_eq
    (by rw [Circuit.cost_program_append, Nat.cast_add])

/-- Unit weights and the support subtype recover native support complexity. -/
theorem ecomplexityFrom_unit_subtype (S : Set (Fin n → U))
    (f : (Fin n → U) → Fin m → U) :
    ecomplexityFrom I (fun _ => 1) (fun x : S => f x) Subtype.val = ecomplexityOn I S f := by
  simp only [ecomplexityFrom, ecomplexityOn, iInf_subtype, Circuit.computesFrom_subtype_iff,
    Program.cost_const, one_mul]

/-- Unit weights with raw inputs and helpers recover native relative complexity. -/
theorem ecomplexityFrom_unit_append {k : ℕ} (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin k → U) :
    ecomplexityFrom I (fun _ => 1) f (fun x => Fin.append x (g x)) = ecomplexityGiven I f g := by
  simp only [ecomplexityFrom, ecomplexityGiven, ecomplexityOn, iInf_subtype, Circuit.ComputesFrom,
    Circuit.computesOn_graph_iff, Program.cost_const, one_mul]

end Cslib.Circuits
