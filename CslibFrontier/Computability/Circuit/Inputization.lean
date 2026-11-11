/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Normalization
public import Cslib.Computability.Circuit.RelativeComplexity
import Mathlib.Algebra.BigOperators.Fin

/-!
# Gate inputization and projection-aware deduplication

For a multi-output function `g : (Fin n → U) → Fin k → U`, the *non-input components*
`nonInputComponents g` are the distinct functions `fun x => g x j` that are not input projections
`fun x => x i`. Their number is the exact complexity of `g` whenever `g` lists the wire
functions of a program, and it is the price of computing `g` alongside any other function `f`:

* every circuit computing `g` (alongside `f`) has a distinct gate for each non-input component,
  because an output computing such a component cannot be an input wire and distinct functions are
  computed by distinct gates;
* turning those gates into extra inputs, which carry the values `g x`, leaves a circuit computing
  `f` from `x` and `g x`. So computing `g` and `f` together costs at least
  `#(nonInputComponents g) + C(f | g)`;
* conversely, a program whose gate functions are components of `g` can be rebuilt with one gate
  per distinct non-projection gate function (`Program.exists_irredundant_noInput`), which bounds
  the complexity of `g` from above.

Repeated components are counted once and components that are input projections are not counted,
since an output wire may be an input wire and designating outputs is free.

## Main definitions

* `Cslib.Circuits.nonInputComponents`: the distinct components of `g` that are not input
  projections.
* `Cslib.Circuits.Program.componentGates`: the gates of a program computing a component of `g`.

## Main results

* `Cslib.Circuits.Circuit.card_nonInputComponents_le_card_componentGates`: a circuit whose outputs
  include `g` has a distinct gate computing each non-input component of `g`.
* `Cslib.Circuits.Circuit.card_nonInputComponents_add_ecomplexityGiven_le`,
  `Cslib.Circuits.card_nonInputComponents_add_ecomplexityGiven_le`: inputization,
  `#(nonInputComponents g) + C(f | g) ≤ C(g, f)`.
* `Cslib.Circuits.card_nonInputComponents_le_ecomplexity`: the lower bound
  `#(nonInputComponents g) ≤ C(g)`.
* `Cslib.Circuits.Program.exists_irredundant_noInput`: a program can be rebuilt with pairwise
  distinct gate functions, none an input projection, each computed by a gate of the original.
* `Cslib.Circuits.ecomplexity_le_card_nonInputComponents`,
  `Cslib.Circuits.ecomplexity_eq_card_nonInputComponents`,
  `Cslib.Circuits.ecomplexity_eval_eq_card_nonInputComponents`: when `g` lists wire functions of
  a program covering its gates, `C(g) = #(nonInputComponents g)`.
* `Cslib.Circuits.ecomplexity_append_eq_card_nonInputComponents_add_ecomplexityGiven`: then
  `C(g, f) = #(nonInputComponents g) + C(f | g)` for every `f`.
* `Cslib.Circuits.card_nonInputComponents_eq`: pairwise distinct components, none a projection,
  are all counted.

## References

These are library generalizations, to arbitrary signatures and interpretations, of
[Ilango, Loff and Oliveira][IlangoLoffOliveira2020], Proposition 14 (pp. 22:21–22:22), where `g`
lists the gates of De Morgan formulas, and of its use in Section 4.2, where the gap between the
complexities of `T • g` and of `g` measures the cost of computing `T` from the components of `g`.

* [R. Ilango, B. Loff and I. C. Oliveira, *NP-Hardness of Circuit Minimization for Multi-Output
  Functions*][IlangoLoffOliveira2020]
-/

public section

namespace Cslib.Circuits

open Finset

universe v u
variable {σ : Signature.{v}} {U : Type u} {n m k : ℕ}

open Classical in
/-- The distinct components `fun x => g x j` of `g` that are not input projections
`fun x => x i`. Repeated components are counted once. -/
noncomputable def nonInputComponents (g : (Fin n → U) → Fin k → U) :
    Finset ((Fin n → U) → U) :=
  (univ.image fun j x => g x j).filter fun h => ∀ i, h ≠ fun x => x i

theorem mem_nonInputComponents {g : (Fin n → U) → Fin k → U} {h : (Fin n → U) → U} :
    h ∈ nonInputComponents g ↔ (∃ j, (fun x => g x j) = h) ∧ ∀ i, h ≠ fun x => x i := by
  classical
  simp [nonInputComponents]

/-- There are at most as many non-input components as components. -/
theorem card_nonInputComponents_le (g : (Fin n → U) → Fin k → U) :
    #(nonInputComponents g) ≤ k := by
  classical
  refine (card_filter_le _ _).trans ?_
  simpa using card_image_le (s := univ) (f := fun j x => g x j)

/-- When the components of `g` are pairwise distinct and none is an input projection, all `k` of
them are counted. -/
theorem card_nonInputComponents_eq {g : (Fin n → U) → Fin k → U}
    (hinj : Function.Injective fun j x => g x j) (hproj : ∀ j i, (fun x => g x j) ≠ fun x => x i) :
    #(nonInputComponents g) = k := by
  classical
  have hfilter : nonInputComponents g = univ.image fun j x => g x j := by
    unfold nonInputComponents
    refine filter_true_of_mem fun h hh => ?_
    obtain ⟨j, -, rfl⟩ := mem_image.mp hh
    exact hproj j
  rw [hfilter, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]

open Classical in
/-- The gates of `p` computing a component of `g`. -/
noncomputable def Program.componentGates {s : ℕ} (p : Program σ n s) (I : Interpretation σ U)
    (g : (Fin n → U) → Fin k → U) : Finset (Fin s) :=
  univ.filter fun t => ∃ j, p.gateFunction I t = fun x => g x j

theorem Program.mem_componentGates {s : ℕ} {p : Program σ n s} {I : Interpretation σ U}
    {g : (Fin n → U) → Fin k → U} {t : Fin s} :
    t ∈ p.componentGates I g ↔ ∃ j, p.gateFunction I t = fun x => g x j := by
  classical
  simp [Program.componentGates]

/-! ### Inputization -/

/-- Read a wire of a program on `n` inputs as a wire on `n + k` inputs, sending gates through
`gates`. -/
private def liftWire {s s' : ℕ} (gates : Fin s → Wire (n + k) s') : Wire n s → Wire (n + k) s' :=
  Wire.elim (fun i => Wire.input (Fin.castAdd k i)) gates

/-- **Inputization.** Every gate of `p` computing a component of `g` can be replaced by the extra
input carrying that component. The remaining program reads `x` followed by `g x`, has one gate
for each other gate of `p`, and reproduces every wire value. -/
private theorem Program.exists_inputize (I : Interpretation σ U) (g : (Fin n → U) → Fin k → U) :
    ∀ {s : ℕ} (p : Program σ n s), ∃ s', ∃ q : Program σ (n + k) s',
      ∃ gates : Fin s → Wire (n + k) s',
        (∀ x t, q.trace I (Fin.append x (g x)) (gates t) = p.gateFunction I t x) ∧
          s' + #(p.componentGates I g) = s
  | _, .empty => ⟨0, .empty, Fin.elim0, fun _ t => t.elim0, by simp [Program.componentGates]⟩
  | s + 1, .gate p line => by
      classical
      obtain ⟨s', q, gates, hgates, hcount⟩ := Program.exists_inputize I g p
      have hwire (x : Fin n → U) (w : Wire n s) :
          q.trace I (Fin.append x (g x)) (liftWire gates w) = p.trace I x w := by
        cases w with
        | input i => simp [liftWire]
        | gate t => exact hgates x t
      let l := line.mapWires (liftWire gates)
      have hl (x : Fin n → U) :
          l.eval I (Fin.append x (g x)) (q.eval I (Fin.append x (g x))) =
            line.eval I x (p.eval I x) :=
        line.eval_mapWires _ I x _ _ _ (hwire x)
      have hsplit : #((p.gate line).componentGates I g) = #(p.componentGates I g) +
          if ∃ j, (p.gate line).gateFunction I (Fin.last s) = fun x => g x j then 1 else 0 := by
        simp only [Program.componentGates, card_filter, Fin.sum_univ_castSucc,
          Program.gateFunction_gate_castSucc]
      by_cases hlast : ∃ j, (p.gate line).gateFunction I (Fin.last s) = fun x => g x j
      · obtain ⟨j, hj⟩ := hlast
        refine ⟨s', q, Fin.lastCases (Wire.input (Fin.natAdd n j)) gates, fun x t => ?_, ?_⟩
        · refine Fin.lastCases ?_ (fun t => ?_) t
          · simpa using (congrFun hj x).symm
          · simpa using hgates x t
        · rw [hsplit, ite_eq_left ⟨j, hj⟩]
          omega
      · refine ⟨s' + 1, q.gate l,
          Fin.lastCases (Wire.gate (Fin.last s')) fun t => (gates t).castSucc, fun x t => ?_, ?_⟩
        · refine Fin.lastCases ?_ (fun t => ?_) t
          · simpa [Program.trace] using hl x
          · simpa using hgates x t
        · rw [hsplit, ite_eq_right hlast]
          omega

/-- **Inputization** (generalizing [Ilango, Loff and Oliveira][IlangoLoffOliveira2020],
Proposition 14 and Section 4.2). A circuit computing `g` followed by `f` has a distinct gate for
each non-input component of `g`, and its remaining gates compute `f` from `x` and `g x`. -/
theorem Circuit.card_nonInputComponents_add_ecomplexityGiven_le {I : Interpretation σ U}
    {g : (Fin n → U) → Fin k → U} {f : (Fin n → U) → Fin m → U} (c : Circuit σ n (k + m))
    (hc : c.Computes I fun x => Fin.append (g x) (f x)) :
    #(nonInputComponents g) + ecomplexityGiven I f g ≤ c.size := by
  classical
  obtain ⟨s', q, gates, hgates, hcount⟩ := c.program.exists_inputize I g
  have hwire (x : Fin n → U) (w : Wire n c.size) :
      q.trace I (Fin.append x (g x)) (liftWire gates w) = c.program.trace I x w := by
    cases w with
    | input i => simp [liftWire]
    | gate t => exact hgates x t
  have hout (x : Fin n → U) (o : Fin (k + m)) :
      c.program.trace I x (c.outputs o) = Fin.append (g x) (f x) o :=
    congrFun (hc x) o
  -- The remaining gates compute `f` from `x` and `g x`.
  have hf : ecomplexityGiven I f g ≤ s' := by
    refine ecomplexityGiven_le_of_eval f g
      ⟨q, fun o => liftWire gates (c.outputs (Fin.natAdd k o))⟩ fun x => funext fun o => ?_
    simpa [Circuit.eval] using (hwire x _).trans (hout x (Fin.natAdd k o))
  -- Every non-input component of `g` is computed by a gate of `c`.
  have hsub : nonInputComponents g ⊆ (c.program.componentGates I g).image
      (c.program.gateFunction I) := by
    intro h hh
    obtain ⟨⟨j, rfl⟩, hproj⟩ := mem_nonInputComponents.mp hh
    have hj (x : Fin n → U) : c.program.trace I x (c.outputs (Fin.castAdd m j)) = g x j := by
      simpa using hout x (Fin.castAdd m j)
    cases hw : c.outputs (Fin.castAdd m j) with
    | input i =>
        exact absurd (funext fun x => by simpa [hw] using (hj x).symm) (hproj i)
    | gate t =>
        have ht : c.program.gateFunction I t = fun x => g x j :=
          funext fun x => by simpa [hw] using hj x
        exact mem_image.mpr ⟨t, Program.mem_componentGates.mpr ⟨j, ht⟩, ht⟩
  have hcard := (card_le_card hsub).trans card_image_le
  calc (#(nonInputComponents g) : ℕ∞) + ecomplexityGiven I f g
      ≤ #(c.program.componentGates I g) + s' := add_le_add (by exact_mod_cast hcard) hf
    _ = c.size := by norm_cast; omega

/-- **Inputization.** Computing `g` followed by `f` costs at least one gate for each non-input
component of `g`, plus the complexity of `f` given `g`. -/
theorem card_nonInputComponents_add_ecomplexityGiven_le (I : Interpretation σ U)
    (g : (Fin n → U) → Fin k → U) (f : (Fin n → U) → Fin m → U) :
    #(nonInputComponents g) + ecomplexityGiven I f g ≤
      ecomplexity I fun x => Fin.append (g x) (f x) :=
  le_ecomplexity_iff.mpr fun c hc => c.card_nonInputComponents_add_ecomplexityGiven_le hc

/-- A circuit whose outputs include the components of `g` has a distinct gate computing each
non-input component of `g` ([Ilango, Loff and Oliveira][IlangoLoffOliveira2020], Proposition 14,
first statement). -/
theorem Circuit.card_nonInputComponents_le_card_componentGates {I : Interpretation σ U}
    {g : (Fin n → U) → Fin k → U} (c : Circuit σ n m)
    (hg : ∀ j, ∃ o, ∀ x, c.eval I x o = g x j) :
    #(nonInputComponents g) ≤ #(c.program.componentGates I g) := by
  classical
  refine (card_le_card fun h hh => ?_).trans (card_image_le (f := c.program.gateFunction I))
  obtain ⟨⟨j, rfl⟩, hproj⟩ := mem_nonInputComponents.mp hh
  obtain ⟨o, ho⟩ := hg j
  cases hw : c.outputs o with
  | input i =>
      exact absurd (funext fun x => by simpa [Circuit.eval, hw] using (ho x).symm) (hproj i)
  | gate t =>
      have ht : c.program.gateFunction I t = fun x => g x j :=
        funext fun x => by simpa [Circuit.eval, hw] using ho x
      exact mem_image.mpr ⟨t, Program.mem_componentGates.mpr ⟨j, ht⟩, ht⟩

/-- Computing `g` costs at least one gate for each non-input component of `g`. -/
theorem card_nonInputComponents_le_ecomplexity (I : Interpretation σ U)
    (g : (Fin n → U) → Fin k → U) : #(nonInputComponents g) ≤ ecomplexity I g :=
  le_ecomplexity_iff.mpr fun c hc => by
    have h := c.card_nonInputComponents_le_card_componentGates (I := I) (g := g)
      fun j => ⟨j, fun x => congrFun (hc x) j⟩
    exact_mod_cast h.trans (card_le_univ _ |>.trans_eq (Fintype.card_fin _))

/-! ### Projection-aware deduplication -/

/-- **Projection-aware deduplication.** A program can be rebuilt so that its gates compute pairwise
distinct functions, none of which is an input projection, while every wire keeps its value. Each
new gate computes the function of some gate of the original program. -/
theorem Program.exists_irredundant_noInput {s : ℕ} (p : Program σ n s) (I : Interpretation σ U) :
    ∃ s' ≤ s, ∃ q : Program σ n s', ∃ ρ : Wire.Renaming n s s',
      (∀ x w, q.trace I x (ρ w) = p.trace I x w) ∧ q.Irredundant I ∧
        (∀ t i, q.gateFunction I t ≠ fun x => x i) ∧ ∀ t, ∃ t₀, ρ.gates t₀ = Wire.gate t := by
  induction p with
  | empty =>
      exact ⟨0, le_rfl, .empty, .id, by simp, fun t => t.elim0, fun t => t.elim0,
        fun t => t.elim0⟩
  | @gate s p line ih =>
      obtain ⟨s', hs', q, ρ, hρ, hq, hqin, hρsurj⟩ := ih
      let l := line.mapWires ρ
      have hl (x) : l.eval I x (q.eval I x) = line.eval I x (p.eval I x) :=
        line.eval_mapWires ρ I x x (p.eval I x) (q.eval I x) (hρ x)
      -- A gate computing an input projection, or a function already computed, is skipped.
      have hskip (w : Wire n s') (hw : ∀ x, q.trace I x w = l.eval I x (q.eval I x)) :
          ∃ s'' ≤ s + 1, ∃ q' : Program σ n s'', ∃ ρ' : Wire.Renaming n (s + 1) s'',
            (∀ x w, q'.trace I x (ρ' w) = (p.gate line).trace I x w) ∧ q'.Irredundant I ∧
              (∀ t i, q'.gateFunction I t ≠ fun x => x i) ∧
                ∀ t, ∃ t₀, ρ'.gates t₀ = Wire.gate t := by
        refine ⟨s', by omega, q, ρ.skipLast w, fun x v => ?_, hq, hqin, fun t => ?_⟩
        · refine Wire.lastCases ?_ (fun v => ?_) v
          · simpa [Program.trace] using (hw x).trans (hl x)
          · simpa using hρ x v
        · obtain ⟨t₀, ht₀⟩ := hρsurj t
          exact ⟨t₀.castSucc, by simpa [Wire.Renaming.skipLast] using ht₀⟩
      by_cases hin : ∃ i, (fun x => l.eval I x (q.eval I x)) = fun x => x i
      · obtain ⟨i, hi⟩ := hin
        exact hskip (Wire.input i) fun x => (congrFun hi x).symm
      by_cases hdup : ∃ t, q.gateFunction I t = fun x => l.eval I x (q.eval I x)
      · obtain ⟨t, ht⟩ := hdup
        exact hskip (Wire.gate t) fun x => congrFun ht x
      refine ⟨s' + 1, by omega, q.gate l, ρ.appendLast, fun x v => ?_, ?_, fun t => ?_,
        fun t => ?_⟩
      · refine Wire.lastCases ?_ (fun v => ?_) v
        · simpa [Program.trace] using hl x
        · simpa using hρ x v
      · change Function.Injective ((q.gate l).gateFunction I)
        convert Fin.snoc_injective_of_injective hq hdup using 1
        ext t x
        refine Fin.lastCases ?_ (fun t => ?_) t <;> simp
      · refine Fin.lastCases ?_ (fun t => ?_) t
        · intro i hi
          exact hin ⟨i, by simpa using hi⟩
        · simpa using hqin t
      · refine Fin.lastCases ⟨Fin.last s, by simp [Wire.Renaming.appendLast]⟩ (fun t => ?_) t
        obtain ⟨t₀, ht₀⟩ := hρsurj t
        exact ⟨t₀.castSucc, by simp [Wire.Renaming.appendLast, ht₀]⟩

/-- When every component of `g` is a wire function of `p` and every gate of `p` that is not an
input projection computes a component of `g`, computing `g` costs at most one gate per non-input
component ([Ilango, Loff and Oliveira][IlangoLoffOliveira2020], Proposition 14, second
statement). -/
theorem ecomplexity_le_card_nonInputComponents {s : ℕ} (I : Interpretation σ U)
    (p : Program σ n s) (g : (Fin n → U) → Fin k → U)
    (hwires : ∀ j, ∃ w, p.wireFunction I w = fun x => g x j)
    (hgates : ∀ t, (∀ i, p.gateFunction I t ≠ fun x => x i) →
      ∃ j, p.gateFunction I t = fun x => g x j) :
    ecomplexity I g ≤ #(nonInputComponents g) := by
  classical
  obtain ⟨s', -, q, ρ, hρ, hq, hqin, hρsurj⟩ := p.exists_irredundant_noInput I
  choose w hw using hwires
  refine (ecomplexity_le_of_computes ⟨q, fun j => ρ (w j)⟩ fun x => funext fun j => ?_).trans ?_
  · simpa [Circuit.eval] using (hρ x (w j)).trans (congrFun (hw j) x)
  -- Each gate of `q` computes a distinct non-input component of `g`.
  have hsub : univ.image (q.gateFunction I) ⊆ nonInputComponents g := by
    intro h hh
    obtain ⟨t, -, rfl⟩ := mem_image.mp hh
    obtain ⟨t₀, ht₀⟩ := hρsurj t
    have heq : q.gateFunction I t = p.gateFunction I t₀ :=
      funext fun x => by simpa [ht₀] using hρ x (Wire.gate t₀)
    obtain ⟨j, hj⟩ := hgates t₀ fun i => heq ▸ hqin t i
    exact mem_nonInputComponents.mpr ⟨⟨j, (heq.trans hj).symm⟩, hqin t⟩
  have hcard := card_le_card hsub
  rw [card_image_of_injective _ hq, card_univ, Fintype.card_fin] at hcard
  exact_mod_cast hcard

/-- When `g` lists wire functions of `p` covering every gate of `p` that is not an input
projection, the complexity of `g` is its number of non-input components
([Ilango, Loff and Oliveira][IlangoLoffOliveira2020], Proposition 14). -/
theorem ecomplexity_eq_card_nonInputComponents {s : ℕ} (I : Interpretation σ U)
    (p : Program σ n s) (g : (Fin n → U) → Fin k → U)
    (hwires : ∀ j, ∃ w, p.wireFunction I w = fun x => g x j)
    (hgates : ∀ t, (∀ i, p.gateFunction I t ≠ fun x => x i) →
      ∃ j, p.gateFunction I t = fun x => g x j) :
    ecomplexity I g = #(nonInputComponents g) :=
  le_antisymm (ecomplexity_le_card_nonInputComponents I p g hwires hgates)
    (card_nonInputComponents_le_ecomplexity I g)

/-- Computing all gates of a program costs one gate per distinct gate function that is not an
input projection. -/
theorem ecomplexity_eval_eq_card_nonInputComponents {s : ℕ} (I : Interpretation σ U)
    (p : Program σ n s) : ecomplexity I (p.eval I) = #(nonInputComponents (p.eval I)) :=
  ecomplexity_eq_card_nonInputComponents I p _ (fun t => ⟨Wire.gate t, rfl⟩)
    fun t _ => ⟨t, rfl⟩

/-- When computing `g` costs only its non-input components, computing `g` followed by `f` costs
exactly those components plus the complexity of `f` given `g`. -/
theorem ecomplexity_append_eq_card_nonInputComponents_add_ecomplexityGiven
    (I : Interpretation σ U) {g : (Fin n → U) → Fin k → U} (f : (Fin n → U) → Fin m → U)
    (hg : ecomplexity I g ≤ #(nonInputComponents g)) :
    ecomplexity I (fun x => Fin.append (g x) (f x)) =
      #(nonInputComponents g) + ecomplexityGiven I f g :=
  le_antisymm ((ecomplexity_append_le_add_ecomplexityGiven g f).trans (add_le_add hg le_rfl))
    (card_nonInputComponents_add_ecomplexityGiven_le I g f)

end Cslib.Circuits
