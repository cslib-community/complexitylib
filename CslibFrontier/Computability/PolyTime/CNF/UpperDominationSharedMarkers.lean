/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.UpperDominationUnique
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Logics.Propositional.DNF.ModelCount

/-!
# Shared parity-marker blocks for upper domination

The local writer of [ChenJiangZhu2027], Appendix D.3 (PDF p.35), uses one marker for an entire
pair-or-mark predicate. Added predicates are suffix path edges, so the left port is a variable;
only the final right port can be the fixed boundary. Every term shares the same marker index.
The full graph query assembly/count transport and source budget remain separate obligations.

## Main results

* `block_eval`: exact parity and activated-term semantics.
* `extension_unique`: proved local parsimonious marker extension under fresh-index hypotheses.
* `block_width`, `block_length`: width three and at most four linking clauses plus one per term.
* `block_polytime`: actual binary clause/literal writing cost.
-/

public section

namespace Cslib.Logic.PL.UpperDomination.Unique.SharedMarkers

open Turing.MultiTapeTM

/-- Binary port/marker indices, final-edge flag, boundary bit and explicit predicate terms. -/
structure Context where
  /-- Left path variable (suffix edges never have the initial constant port). -/
  left : ℕ
  /-- Right path variable, ignored at the final edge. -/
  right : ℕ
  /-- One shared fresh variable for the whole predicate. -/
  marker : ℕ
  /-- Whether the right port is the fixed boundary. -/
  last : Bool
  /-- Right endpoint value in the final-edge case. -/
  boundary : Bool
  /-- Explicit signed terms; the source pair-or-mark terms have width at most two. -/
  terms : DNF ℕ

/-- Fields in declaration order: binary indices, flags, then the signed predicate.
Each non-final field is framed; the final list uses the existing signed-CNF framing. -/
enc_structure encContext : Context where
  left : encNat, right : encNat, marker : encNat, last : encBool, boundary : encBool,
  terms : VCOne.encSignedCNF

/-- Force the shared marker to the parity of its ports, substituting a final constant directly.
The constant case needs two binary clauses; the interior case has four ternary clauses. -/
@[expose] def parity (c : Context) : CNF ℕ :=
  if c.last then
    if c.boundary then
      [[(c.left, true), (c.marker, true)], [(c.left, false), (c.marker, false)]]
    else [[(c.left, false), (c.marker, true)], [(c.left, true), (c.marker, false)]]
  else [[(c.left, true), (c.right, true), (c.marker, false)],
    [(c.left, true), (c.right, false), (c.marker, true)],
    [(c.left, false), (c.right, true), (c.marker, true)],
    [(c.left, false), (c.right, false), (c.marker, false)]]

/-- One activated false-marker clause per term, reusing the same marker even for repeated terms. -/
@[expose] def block (c : Context) : CNF ℕ :=
  parity c ++ c.terms.map (fun t => t.negate ++ [(c.marker, false)])

/-- Exact truth-table semantics of the linking clauses, including fixed right boundaries. -/
theorem parity_eval (c : Context) (σ : ℕ → Bool) :
    (parity c).eval σ = true ↔
      σ c.marker = (σ c.left ^^ (if c.last then c.boundary else σ c.right)) := by
  cases hl : σ c.left <;> cases hr : σ c.right <;> cases hm : σ c.marker <;>
    cases ht : c.last <;> cases hb : c.boundary <;>
      simp [parity, CNF.eval, Clause.eval, Literal.eval, hl, hr, hm, ht, hb]

/-- The block makes a true predicate force equal path endpoints, while its marker is always
functionally determined by the ports. No marker is introduced for an individual term. -/
theorem block_eval (c : Context) (σ : ℕ → Bool) :
    (block c).eval σ = true ↔
      σ c.marker = (σ c.left ^^ (if c.last then c.boundary else σ c.right)) ∧
        (DNF.eval σ c.terms = true → σ c.marker = false) := by
  have hc (t : Term ℕ) :
      Clause.eval σ (t.negate ++ [(c.marker, false)]) =
        (!Term.eval σ t || !σ c.marker) := by
    rw [Clause.eval, List.any_append]
    change (Clause.eval σ t.negate || _) = _
    rw [Term.eval_negate]
    simp [Literal.eval]
  rw [block, CNF.eval_append, Bool.and_eq_true, parity_eval]
  apply and_congr_right
  intro _
  simp only [CNF.eval, List.all_map, List.all_eq_true]
  simp only [Function.comp_def, hc]
  cases σ c.marker <;> simp [DNF.eval_eq_true_iff]

/-- Substituting the shared marker leaves original inputs untouched when its index is fresh.
The unused right index need not be fresh on a final edge. -/
theorem extension_eval (c : Context) (σ : ℕ → Bool) (b : Bool)
    (hl : c.left ≠ c.marker) (hr : c.last = false → c.right ≠ c.marker)
    (hf : ∀ t ∈ c.terms, ∀ l ∈ t, l.1 ≠ c.marker) :
    (block c).eval (Function.update σ c.marker b) = true ↔
      b = (σ c.left ^^ (if c.last then c.boundary else σ c.right)) ∧
        (DNF.eval σ c.terms = true → b = false) := by
  have hp : DNF.eval (Function.update σ c.marker b) c.terms = DNF.eval σ c.terms := by
    apply DNF.eval_congr
    intro v hv
    obtain ⟨t, ht, sign, hlit⟩ := CNF.mem_vars.mp hv
    exact Function.update_of_ne (hf t ht (v, sign) hlit) _ _
  have hleft : Function.update σ c.marker b c.left = σ c.left :=
    Function.update_of_ne hl _ _
  have hright : (if c.last then c.boundary else Function.update σ c.marker b c.right) =
      (if c.last then c.boundary else σ c.right) := by
    cases ht : c.last with
    | false => simp only [Bool.false_eq_true, ite_false, Function.update_of_ne (hr ht)]
    | true => simp only [ite_true]
  rw [block_eval, hp, hleft, hright]
  simp

/-- Exactly one marker assignment extends a base assignment when the activated predicate
requires zero endpoint parity; otherwise there is no marker assignment. This is the local
parsimonious-extension property used by the source, without an assumed count contract. -/
theorem extension_unique (c : Context) (σ : ℕ → Bool)
    (hl : c.left ≠ c.marker) (hr : c.last = false → c.right ≠ c.marker)
    (hf : ∀ t ∈ c.terms, ∀ l ∈ t, l.1 ≠ c.marker) :
    (∃! b : Bool, (block c).eval (Function.update σ c.marker b) = true) ↔
      (DNF.eval σ c.terms = true →
        (σ c.left ^^ (if c.last then c.boundary else σ c.right)) = false) := by
  simp_rw [extension_eval c σ _ hl hr hf]
  constructor
  · rintro ⟨b, hb, _⟩
    simpa only [hb.1] using hb.2
  · intro h
    refine ⟨_, ⟨rfl, h⟩, ?_⟩
    intro b hb
    exact hb.1

/-- Exactly one clause per term is written in addition to at most four linking clauses. -/
theorem block_length (c : Context) : (block c).length ≤ c.terms.length + 4 := by
  cases ht : c.last <;> cases hb : c.boundary <;>
    simp [block, parity, ht, hb]

/-- Bounded pair-or-mark terms produce only ordinary width-three clauses. -/
theorem block_width (c : Context) (h : ∀ t ∈ c.terms, t.length ≤ 2) :
    ∀ cl ∈ block c, cl.length ≤ 3 := by
  intro cl hcl
  rcases List.mem_append.mp hcl with hp | ht
  · cases hl : c.last <;> cases hb : c.boundary <;>
      simp_all [parity] <;> grind
  · obtain ⟨t, hmem, he⟩ := List.mem_map.mp ht
    subst cl
    have := h t hmem
    simp only [List.length_append, Term.negate, List.length_map, List.length_singleton]
    omega

@[local fun_prop] private theorem left_polytime :
    ComputableInPolyTime Context.left encContext encNat :=
  encContext_left_inO.computableInPolyTime .self .self

@[local fun_prop] private theorem right_polytime :
    ComputableInPolyTime Context.right encContext encNat :=
  encContext_right_inO.computableInPolyTime .self .self

@[local fun_prop] private theorem marker_polytime :
    ComputableInPolyTime Context.marker encContext encNat :=
  encContext_marker_inO.computableInPolyTime .self .self

@[local fun_prop] private theorem last_polytime :
    ComputableInPolyTime Context.last encContext encBool :=
  encContext_last_inO.computableInPolyTime .self .self

@[local fun_prop] private theorem boundary_polytime :
    ComputableInPolyTime Context.boundary encContext encBool :=
  encContext_boundary_inO.computableInPolyTime .self .self

@[local fun_prop] private theorem terms_polytime :
    ComputableInPolyTime Context.terms encContext VCOne.encSignedCNF :=
  encContext_terms_inO.computableInPolyTime .self .self

private theorem parity_polytime : ComputableInPolyTime parity encContext VCOne.encSignedCNF := by
  unfold parity VCOne.encSignedCNF
  fun_prop

/-- All binary indices, tags and literal writes are charged by the existing list calculus. -/
theorem block_polytime : ComputableInPolyTime block encContext VCOne.encSignedCNF := by
  unfold block
  apply ComputableInPolyTime.listAppend' parity_polytime
  apply ComputableInPolyTime.mapWithInput (by fun_prop)
  unfold Term.negate
  fun_prop

end Cslib.Logic.PL.UpperDomination.Unique.SharedMarkers
