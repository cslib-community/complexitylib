/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Unbounded.Kleene
public import Complexity.Computability.Circuit.Weft
public import Complexity.Computability.Circuit.Encoding.Layer
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD

/-!
# Certificates for circuits of weft one

PLACEHOLDER
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Unbounded

open Turing.MultiTapeTM

namespace WeftOne

/-! ### Claims and their checks -/

/-- The gate of wire `w` of a gate list from `n` inputs, or a nullary negation when `w` is not a
gate. -/
def gateAt (n : ℕ) (gates : List (Op × List ℕ)) (w : ℕ) : Op × List ℕ :=
  gates.getD (w - n) (.not, [])

/-- The value that a gate can be claimed to have, on the strength of its arguments: a conjunction
can be claimed true and a disjunction false, when all their arguments have that value. -/
def claimable (g : Op × List ℕ) : Option Bool :=
  match g.1 with
  | .not => none
  | .and _ => some true
  | .or _ => some false

/-- Replace gate `j` by a nullary conjunction or disjunction when it is claimed to have the value
it can be claimed to have. -/
def overrideGate (n : ℕ) (claims : List (ℕ × Bool)) (g : Op × List ℕ) (j : ℕ) : Op × List ℕ :=
  if claimable g = some true ∧ (n + j, true) ∈ claims then (.and 0, [])
  else if claimable g = some false ∧ (n + j, false) ∈ claims then (.or 0, [])
  else g

/-- The gates with the claimed ones replaced by constants. -/
def overrideGates (n : ℕ) (claims : List (ℕ × Bool)) (gates : List (Op × List ℕ)) :
    List (Op × List ℕ) :=
  gates.zipIdx.map fun p => overrideGate n claims p.1 p.2

/-- The value claimed for input `i`, if any. -/
def claimInput (claims : List (ℕ × Bool)) (i : ℕ) : Option Bool :=
  if (i, true) ∈ claims then some true else if (i, false) ∈ claims then some false else none

/-- The claimed values of the `n` inputs. -/
def claimInputs (n : ℕ) (claims : List (ℕ × Bool)) : List (Option Bool) :=
  (List.range n).map (claimInput claims)

/-- The checks of a claim: a claimed input is checked itself, and a gate claimed to have the value
it can be claimed to have is checked through its arguments. -/
def claimChecks (n : ℕ) (gates : List (Op × List ℕ)) (c : ℕ × Bool) : List (ℕ × Bool) :=
  if c.1 < n then [c]
  else if claimable (gateAt n gates c.1) = some c.2 then (gateAt n gates c.1).2.map (·, c.2)
  else []

/-- The larger of the first two entries of a list. -/
def maxTwo (l : List ℕ) : ℕ :=
  max (l.getD 0 0) (l.getD 1 0)

/-- The small depth of a gate from those of its arguments, capped at `d + 1`: a gate with at most
two arguments is one deeper than they are, and a gate with more arguments has depth `d + 1`. -/
def smallDepthOp (d : ℕ) (_op : Op) (l : List ℕ) : ℕ :=
  if l.length ≤ 2 then min (d + 1) (maxTwo l + 1) else d + 1

/-- The small depths of the wires of a gate list from `n` inputs, capped at `d + 1`: the length of
a longest path of gates with at most two arguments ending at a wire, through such gates only. -/
def smallDepths (d n : ℕ) (gates : List (Op × List ℕ)) : List ℕ :=
  gates.foldl (fun sd g => sd ++ [smallDepthOp d g.1 (g.2.map (sd.getD · (d + 1)))])
    (List.replicate n 0)

/-- **The certificate check.** The claims are valid for output wire `o` of a gate list from `n`
inputs when Kleene evaluation of the gates with the claimed gates replaced by constants, from the
claimed inputs, finds `o` true, and every check of a claim is at small depth at most `d`. -/
def claimsValid (d n : ℕ) (gates : List (Op × List ℕ)) (o : ℕ) (claims : List (ℕ × Bool)) :
    Bool :=
  decide ((kleeneEval (claimInputs n claims) (overrideGates n claims gates)).getD o none =
      some true) &&
    (claims.flatMap (claimChecks n gates)).all fun e =>
      decide ((smallDepths d n gates).getD e.1 (d + 1) ≤ d)

/-! ### Basic facts -/

@[simp] theorem length_overrideGates (n : ℕ) (claims : List (ℕ × Bool))
    (gates : List (Op × List ℕ)) : (overrideGates n claims gates).length = gates.length := by
  simp [overrideGates]

theorem getElem?_overrideGates (n : ℕ) (claims : List (ℕ × Bool)) (gates : List (Op × List ℕ))
    (j : ℕ) : (overrideGates n claims gates)[j]? = gates[j]?.map (overrideGate n claims · j) := by
  simp only [overrideGates, List.getElem?_map, List.getElem?_zipIdx]
  cases gates[j]? <;> simp

theorem isCodeFrom_overrideGates {n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) (claims : List (ℕ × Bool)) :
    Program.IsCodeFrom signature n 0 (overrideGates n claims gates) := by
  refine Program.isCodeFrom_of_getElem fun j hj => ?_
  have hj' : j < gates.length := by simpa using hj
  have hg : (overrideGates n claims gates)[j] = overrideGate n claims gates[j] j := by
    have := getElem?_overrideGates n claims gates j
    rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj'] at this
    simpa using this
  rw [hg]
  obtain ⟨h₁, h₂⟩ := h.getElem j hj'
  unfold overrideGate
  split_ifs
  · exact ⟨rfl, by simp⟩
  · exact ⟨rfl, by simp⟩
  · exact ⟨h₁, h₂⟩

theorem gateAt_add {n : ℕ} {gates : List (Op × List ℕ)} {j : ℕ} {g : Op × List ℕ}
    (hg : gates[j]? = some g) : gateAt n gates (n + j) = g := by
  simp [gateAt, List.getD_eq_getElem?_getD, hg]

@[simp] theorem length_claimInputs (n : ℕ) (claims : List (ℕ × Bool)) :
    (claimInputs n claims).length = n := by
  simp [claimInputs]

theorem getD_claimInputs {n : ℕ} (claims : List (ℕ × Bool)) {i : ℕ} (hi : i < n) :
    (claimInputs n claims).getD i none = claimInput claims i := by
  simp [claimInputs, List.getD_eq_getElem?_getD, hi]

/-- The Kleene value of a gate after replacing the claimed gates. -/
theorem getD_kleeneEval_overrideGates {n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {ρ : List (Option Bool)} (hρ : ρ.length = n)
    (claims : List (ℕ × Bool)) {j : ℕ} {g : Op × List ℕ} (hg : gates[j]? = some g) :
    (kleeneEval ρ (overrideGates n claims gates)).getD (n + j) none =
      if claimable g = some true ∧ (n + j, true) ∈ claims then some true
      else if claimable g = some false ∧ (n + j, false) ∈ claims then some false
      else kleeneOp g.1 (g.2.map ((kleeneEval ρ (overrideGates n claims gates)).getD · none)) := by
  have hg' : (overrideGates n claims gates)[j]? = some (overrideGate n claims g j) := by
    rw [getElem?_overrideGates, hg, Option.map_some]
  rw [getD_kleeneEval_add hρ (isCodeFrom_overrideGates h claims) hg', overrideGate]
  split_ifs <;> simp [kleeneOp, kleeneAnd, kleeneOr]

/-- The Boolean value of a gate, for an input list of length `n`. -/
theorem getD_evalCode_add {n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {x : List Bool} (hx : x.length = n) {j : ℕ}
    {g : Op × List ℕ} (hg : gates[j]? = some g) :
    (evalCode interpretation false x gates).getD (n + j) false =
      interpretation g.1 fun a => g.2[a.val]?.elim false
        ((evalCode interpretation false x gates).getD · false) := by
  subst hx
  exact getD_evalCode interpretation false x h hg

theorem claimable_gateAt_add {n : ℕ} {gates : List (Op × List ℕ)} {j : ℕ} {g : Op × List ℕ}
    (hg : gates[j]? = some g) : claimable (gateAt n gates (n + j)) = claimable g := by
  rw [gateAt_add hg]

/-! ### Soundness -/

/-- **Replacing correctly claimed gates.** If every claim on an input, and every claim on a gate
of the value it can be claimed to have, is correct, then Kleene evaluation of the gates with the
claimed ones replaced, from the claimed inputs, approximates Boolean evaluation. -/
theorem approx_override {n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {x : List Bool} (hx : x.length = n)
    {claims : List (ℕ × Bool)}
    (hcl : ∀ c ∈ claims, (c.1 < n ∨ claimable (gateAt n gates c.1) = some c.2) →
      (evalCode interpretation false x gates).getD c.1 false = c.2) (w : ℕ) :
    Approx ((kleeneEval (claimInputs n claims) (overrideGates n claims gates)).getD w none)
      ((evalCode interpretation false x gates).getD w false) := by
  have hρ := length_claimInputs n claims
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w n with hw | hw
    · rw [getD_kleeneEval_of_lt _ _ (by rw [hρ]; exact hw), getD_claimInputs _ hw, claimInput]
      split_ifs with h₁ h₂
      · exact approx_some.2 (hcl _ h₁ (Or.inl hw)).symm
      · exact approx_some.2 (hcl _ h₂ (Or.inl hw)).symm
      · exact approx_none _
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hw
    rcases hg : gates[j]? with _ | g
    · have := List.getElem?_eq_none_iff.1 hg
      rw [List.getD_eq_default _ _ (by rw [length_kleeneEval, hρ, length_overrideGates]; omega)]
      exact approx_none _
    rw [getD_kleeneEval_overrideGates h hρ claims hg]
    split_ifs with h₁ h₂
    · exact approx_some.2 (hcl _ h₁.2 (Or.inr ((claimable_gateAt_add hg).trans h₁.1))).symm
    · exact approx_some.2 (hcl _ h₂.2 (Or.inr ((claimable_gateAt_add hg).trans h₂.1))).symm
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hg
    obtain ⟨harity, hlt⟩ := h.getElem j hj
    rw [getD_evalCode_add h hx hg, ← ofFn_elim_eq_map none _ _ harity]
    refine kleeneInterpretation_approx _ _ _ fun a => ?_
    rcases ha : gates[j].2[a.val]? with _ | i
    · exact approx_none _
    · exact ih i (by have := hlt i (List.mem_of_getElem? ha); omega)

/-- A claimable gate has the value it can be claimed to have exactly when all its arguments do. -/
theorem getD_evalCode_eq_iff_of_claimable {n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {x : List Bool} (hx : x.length = n) {j : ℕ}
    {g : Op × List ℕ} (hg : gates[j]? = some g) {b : Bool} (hb : claimable g = some b) :
    (evalCode interpretation false x gates).getD (n + j) false = b ↔
      ∀ c ∈ g.2, (evalCode interpretation false x gates).getD c false = b := by
  obtain ⟨hj, hgj⟩ := List.getElem?_eq_some_iff.1 hg
  have hlen := (h.getElem j hj).1
  rw [hgj] at hlen
  rw [getD_evalCode_add h hx hg]
  obtain ⟨op, args⟩ := g
  cases op with
  | not => simp [claimable] at hb
  | and m =>
    simp only [claimable, Option.some.injEq] at hb
    subst hb
    dsimp only at hlen ⊢
    rw [interpretation_and, decide_eq_true_iff]
    constructor
    · intro hall c hc
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
      have := hall ⟨i, by simp only [Op.arity] at hlen; omega⟩
      simpa [List.getElem?_eq_getElem hi] using this
    · intro hall i
      have hi : i.val < args.length := by simp only [Op.arity] at hlen; omega
      simpa [List.getElem?_eq_getElem hi] using hall _ (List.getElem_mem hi)
  | or m =>
    simp only [claimable, Option.some.injEq] at hb
    subst hb
    dsimp only at hlen ⊢
    rw [interpretation_or, decide_eq_false_iff_not, not_exists]
    constructor
    · intro hall c hc
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
      have := hall ⟨i, by simp only [Op.arity] at hlen; omega⟩
      simpa [List.getElem?_eq_getElem hi] using this
    · intro hall i
      have hi : i.val < args.length := by simp only [Op.arity] at hlen; omega
      simpa [List.getElem?_eq_getElem hi] using hall _ (List.getElem_mem hi)

/-- **Soundness of the certificate check.** If claims are valid for wire `o` and every check of a
claim holds on an input, the input makes wire `o` true. -/
theorem eval_of_claimsValid {d n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {o : ℕ} {claims : List (ℕ × Bool)}
    (hvalid : claimsValid d n gates o claims = true) {x : List Bool} (hx : x.length = n)
    (hchecks : ∀ e ∈ claims.flatMap (claimChecks n gates),
      (evalCode interpretation false x gates).getD e.1 false = e.2) :
    (evalCode interpretation false x gates).getD o false = true := by
  have hcl : ∀ c ∈ claims, (c.1 < n ∨ claimable (gateAt n gates c.1) = some c.2) →
      (evalCode interpretation false x gates).getD c.1 false = c.2 := by
    intro c hc hcases
    rcases Nat.lt_or_ge c.1 n with hlt | hge
    · exact hchecks c (List.mem_flatMap.2 ⟨c, hc, by simp [claimChecks, hlt]⟩)
    · have hb := hcases.resolve_left (by omega)
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hge
      rcases hg : gates[j]? with _ | g
      · simp [gateAt, hj, List.getD_eq_getElem?_getD, hg, claimable] at hb
      rw [hj, gateAt_add hg] at hb
      rw [hj, getD_evalCode_eq_iff_of_claimable h hx hg hb]
      intro c' hc'
      refine hchecks (c', c.2) (List.mem_flatMap.2 ⟨c, hc, ?_⟩)
      simp only [claimChecks, hj, gateAt_add hg, hb, show ¬n + j < n by omega, ↓reduceIte]
      exact List.mem_map.2 ⟨c', hc', rfl⟩
  have happrox := approx_override h hx hcl o
  simp only [claimsValid, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  rw [hvalid.1] at happrox
  exact (approx_some.1 happrox).symm

/-! ### Small depths and the inputs that determine a wire -/

theorem smallDepths_eq (d n : ℕ) {gates : List (Op × List ℕ)}
    (h : ∀ g ∈ gates, g.2.length = g.1.arity) :
    smallDepths d n gates = evalCode (σ := signature) (fun op a => smallDepthOp d op (List.ofFn a))
      (d + 1) (List.replicate n 0) gates :=
  foldl_eq_evalCode (σ := signature) (smallDepthOp d) (d + 1) _ h

theorem getD_smallDepths_add {d n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {j : ℕ} {g : Op × List ℕ}
    (hg : gates[j]? = some g) :
    (smallDepths d n gates).getD (n + j) (d + 1) =
      smallDepthOp d g.1 (g.2.map ((smallDepths d n gates).getD · (d + 1))) := by
  rw [smallDepths_eq d n (length_eq_arity_of_isCodeFrom h)]
  exact getD_evalCode_eq_map (σ := signature) (smallDepthOp d) (fun _ _ => rfl) (d + 1)
    List.length_replicate h hg

theorem getD_smallDepths_of_lt (d n : ℕ) (gates : List (Op × List ℕ)) {w : ℕ} (hw : w < n) :
    (smallDepths d n gates).getD w (d + 1) = 0 := by
  have hpre : List.replicate n 0 <+: smallDepths d n gates := by
    unfold smallDepths
    generalize List.replicate n 0 = x
    induction gates generalizing x with
    | nil => exact List.prefix_refl _
    | cons g gates ih => exact (List.prefix_append _ _).trans (ih _)
  obtain ⟨t, ht⟩ := hpre
  rw [← ht, List.getD_append _ _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem length_smallDepths (d n : ℕ) (gates : List (Op × List ℕ)) :
    (smallDepths d n gates).length = n + gates.length := by
  unfold smallDepths
  generalize hx : List.replicate n 0 = x
  have : x.length = n := by rw [← hx, List.length_replicate]
  rw [← this]
  clear hx this
  induction gates generalizing x with
  | nil => simp
  | cons g gates ih =>
    rw [List.foldl_cons, ih, List.length_append, List.length_singleton, List.length_cons]
    omega

theorem le_maxTwo {l : List ℕ} (hl : l.length ≤ 2) {v : ℕ} (hv : v ∈ l) : v ≤ maxTwo l := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  unfold maxTwo
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem maxTwo_le {l : List ℕ} {D : ℕ} (h : ∀ v ∈ l, v ≤ D) : maxTwo l ≤ D := by
  have key (i : ℕ) : l.getD i 0 ≤ D := by
    rw [List.getD_eq_getElem?_getD]
    rcases hi : l[i]? with _ | v
    · simp
    · exact h v (List.mem_of_getElem? hi)
  exact max_le (key 0) (key 1)

/-- **Wires of small depth are determined by few inputs.** A wire of small depth `D ≤ d` has a set
of at most `2 ^ D` inputs such that Kleene evaluation from partial inputs that agree with an
input `x` on that set knows the value of the wire on `x`. -/
theorem exists_determining {d n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {w D : ℕ}
    (hw : (smallDepths d n gates).getD w (d + 1) ≤ D) (hD : D ≤ d) :
    ∃ S : Finset ℕ, S.card ≤ 2 ^ D ∧ (∀ s ∈ S, s < n) ∧
      ∀ (x : List Bool) (ρ : List (Option Bool)), x.length = n → ρ.length = n →
        (∀ s ∈ S, ρ.getD s none = some (x.getD s false)) →
        (kleeneEval ρ gates).getD w none =
          some ((evalCode interpretation false x gates).getD w false) := by
  have harity := length_eq_arity_of_isCodeFrom h
  induction w using Nat.strong_induction_on generalizing D with
  | _ w ih =>
    rcases Nat.lt_or_ge w n with hwn | hwn
    · refine ⟨{w}, by simpa using Nat.one_le_two_pow, by simpa using hwn, fun x ρ hx hρ hS => ?_⟩
      rw [getD_kleeneEval_of_lt _ _ (by omega), getD_evalCode_of_lt _ _ _ _ (by omega)]
      exact hS w (Finset.mem_singleton_self w)
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hwn
    rcases hg : gates[j]? with _ | g
    · have := List.getElem?_eq_none_iff.1 hg
      rw [List.getD_eq_default _ _ (by rw [length_smallDepths]; omega)] at hw
      omega
    obtain ⟨hj, hgj⟩ := List.getElem?_eq_some_iff.1 hg
    obtain ⟨hlen, hlt⟩ := h.getElem j hj
    rw [hgj] at hlen hlt
    rw [getD_smallDepths_add h hg, smallDepthOp] at hw
    split_ifs at hw with h2
    · have h2' : g.2.length ≤ 2 := by simpa using h2
      have hchild : ∀ c ∈ g.2, (smallDepths d n gates).getD c (d + 1) ≤ D - 1 ∧ c < n + j := by
        intro c hc
        have := le_maxTwo h2 (List.mem_map_of_mem (f := ((smallDepths d n gates).getD · (d + 1))) hc)
        have hc' := hlt c hc
        refine ⟨?_, by omega⟩
        have hmin := min_le_iff.1 hw
        omega
      have hex : ∀ c ∈ g.2, ∃ S : Finset ℕ, S.card ≤ 2 ^ (D - 1) ∧ (∀ s ∈ S, s < n) ∧
          ∀ (x : List Bool) (ρ : List (Option Bool)), x.length = n → ρ.length = n →
            (∀ s ∈ S, ρ.getD s none = some (x.getD s false)) →
            (kleeneEval ρ gates).getD c none =
              some ((evalCode interpretation false x gates).getD c false) :=
        fun c hc => ih c (hchild c hc).2 (D := D - 1) (hchild c hc).1 (by omega)
      choose! S hScard hSlt hSdet using hex
      have hD1 : 1 ≤ D := by
        rcases min_le_iff.1 hw with h' | h' <;> omega
      refine ⟨g.2.toFinset.biUnion S, ?_, ?_, fun x ρ hx hρ hagree => ?_⟩
      · calc (g.2.toFinset.biUnion S).card ≤ ∑ c ∈ g.2.toFinset, (S c).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _c ∈ g.2.toFinset, 2 ^ (D - 1) :=
              Finset.sum_le_sum fun c hc => hScard c (List.mem_toFinset.1 hc)
          _ = g.2.toFinset.card * 2 ^ (D - 1) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ 2 * 2 ^ (D - 1) :=
              Nat.mul_le_mul_right _ ((List.toFinset_card_le _).trans h2')
          _ = 2 ^ D := by
              obtain ⟨D', rfl⟩ := Nat.exists_eq_add_of_le hD1
              rw [Nat.add_sub_cancel_left, Nat.add_comm 1 D', pow_succ']
      · intro s hs
        obtain ⟨c, hc, hs⟩ := Finset.mem_biUnion.1 hs
        exact hSlt c (List.mem_toFinset.1 hc) s hs
      · have hcs : ∀ c ∈ g.2, (kleeneEval ρ gates).getD c none =
            some ((evalCode interpretation false x gates).getD c false) := fun c hc =>
          hSdet c hc x ρ hx hρ fun s hs => hagree s
            (Finset.mem_biUnion.2 ⟨c, List.mem_toFinset.2 hc, hs⟩)
        have hmap : g.2.map (fun a => some ((evalCode interpretation false x gates).getD a false)) =
            (g.2.map ((evalCode interpretation false x gates).getD · false)).map some := by
          rw [List.map_map]
          rfl
        rw [getD_kleeneEval_add hρ h hg, getD_evalCode_add h hx hg, List.map_congr_left hcs, hmap,
          ← ofFn_elim_eq_map (σ := signature) false _ _ hlen, List.map_ofFn, ← kleeneInterpretation_some]
        rfl
    · omega

/-! ### Depth bounds -/

/-- In the depth interpretation, a gate is deeper than each of its arguments by its cost. -/
theorem getD_evalCode_depth_le {σ : Signature} (cost : σ.Op → ℕ) {n : ℕ}
    {gates : List (σ.Op × List ℕ)} (h : Program.IsCodeFrom σ n 0 gates) {j : ℕ}
    {g : σ.Op × List ℕ} (hg : gates[j]? = some g) {c : ℕ} (hc : c ∈ g.2) :
    (evalCode (depthInterpretation cost) 0 (List.replicate n 0) gates).getD c 0 + cost g.1 ≤
      (evalCode (depthInterpretation cost) 0 (List.replicate n 0) gates).getD (n + j) 0 := by
  have h' : Program.IsCodeFrom σ (List.replicate n 0).length 0 gates := by
    rwa [List.length_replicate]
  have hv := getD_evalCode (depthInterpretation cost) 0 (List.replicate n 0) h' hg
  rw [List.length_replicate] at hv
  rw [hv, depthInterpretation, Fin.foldl_max_eq_max_sup, Nat.zero_max]
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hg
  have hlen := (h.getElem j hj).1
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  refine Nat.add_le_add_right (le_trans ?_ (Finset.le_sup (Finset.mem_univ
    (⟨i, hlen ▸ hi⟩ : Fin (σ.Arity gates[j].1))))) _
  simp [List.getElem?_eq_getElem hi]

/-- In the depth interpretation, a gate is at least as deep as its cost. -/
theorem cost_le_getD_evalCode_depth {σ : Signature} (cost : σ.Op → ℕ) {n : ℕ}
    {gates : List (σ.Op × List ℕ)} (h : Program.IsCodeFrom σ n 0 gates) {j : ℕ}
    {g : σ.Op × List ℕ} (hg : gates[j]? = some g) :
    cost g.1 ≤ (evalCode (depthInterpretation cost) 0 (List.replicate n 0) gates).getD (n + j) 0 := by
  have h' : Program.IsCodeFrom σ (List.replicate n 0).length 0 gates := by
    rwa [List.length_replicate]
  have hv := getD_evalCode (depthInterpretation cost) 0 (List.replicate n 0) h' hg
  rw [List.length_replicate] at hv
  rw [hv, depthInterpretation]
  exact Nat.le_add_left _ _

/-- A wire of weft zero has small depth at most its depth. -/
theorem getD_smallDepths_le {d n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {w : ℕ} (hw : w < n + gates.length)
    (hwd : (evalCode (depthInterpretation (largeGateCost signature)) 0 (List.replicate n 0)
      gates).getD w 0 = 0) :
    (smallDepths d n gates).getD w (d + 1) ≤
      (evalCode (depthInterpretation (σ := signature) 1) 0 (List.replicate n 0) gates).getD w 0 := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w n with hwn | hwn
    · rw [getD_smallDepths_of_lt _ _ _ hwn]
      exact Nat.zero_le _
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hwn
    obtain ⟨g, hg⟩ : ∃ g, gates[j]? = some g := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨hj, hgj⟩ := List.getElem?_eq_some_iff.1 hg
    obtain ⟨hlen, hlt⟩ := h.getElem j hj
    rw [hgj] at hlen hlt
    have hcost := cost_le_getD_evalCode_depth (largeGateCost signature) h hg
    rw [hwd] at hcost
    have h2 : g.2.length ≤ 2 := by
      rw [hlen]
      unfold largeGateCost at hcost
      split_ifs at hcost with h'
      · omega
      · omega
    have hone := cost_le_getD_evalCode_depth 1 h hg
    simp only [Pi.one_apply] at hone
    simp only [getD_smallDepths_add h hg, smallDepthOp, List.length_map, h2, ↓reduceIte]
    refine (min_le_right _ _).trans ?_
    have hmax : maxTwo (g.2.map ((smallDepths d n gates).getD · (d + 1))) + 1 ≤
        (evalCode (depthInterpretation (σ := signature) 1) 0 (List.replicate n 0) gates).getD (n + j) 0 := by
      have : maxTwo (g.2.map ((smallDepths d n gates).getD · (d + 1))) ≤
          (evalCode (depthInterpretation (σ := signature) 1) 0 (List.replicate n 0) gates).getD (n + j) 0 - 1 := by
        refine maxTwo_le fun v hv => ?_
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hv
        have h1 := getD_evalCode_depth_le 1 h hg hc
        have h0 := getD_evalCode_depth_le (largeGateCost signature) h hg hc
        simp only [Pi.one_apply] at h1
        have := ih c (by have := hlt c hc; omega) (by have := hlt c hc; omega) (by omega)
        omega
      omega
    exact hmax

/-! ### Completeness -/

/-- Under correct claims, a known Kleene value is the Boolean value. -/
theorem eq_of_ne_none {n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {x : List Bool} (hx : x.length = n)
    {claims : List (ℕ × Bool)}
    (hcl : ∀ c ∈ claims, (evalCode interpretation false x gates).getD c.1 false = c.2) {w : ℕ}
    (hne : (kleeneEval (claimInputs n claims) (overrideGates n claims gates)).getD w none ≠ none) :
    (kleeneEval (claimInputs n claims) (overrideGates n claims gates)).getD w none =
      some ((evalCode interpretation false x gates).getD w false) := by
  have := approx_override h hx (fun c hc _ => hcl c hc) w
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hne
  rw [hb] at this ⊢
  rw [approx_some.1 this]

/-- A conjunction with a false argument, or a disjunction with a true one, is known. -/
theorem kleeneOp_of_claimable {g : Op × List ℕ} {b : Bool} (hb : claimable g = some b)
    {l : List (Option Bool)} (hl : some (!b) ∈ l) : kleeneOp g.1 l = some (!b) := by
  obtain ⟨op, args⟩ := g
  cases op with
  | not => simp [claimable] at hb
  | and m =>
    simp only [claimable, Option.some.injEq] at hb
    subst hb
    exact kleeneAnd_of_mem hl
  | or m =>
    simp only [claimable, Option.some.injEq] at hb
    subst hb
    exact kleeneOr_of_mem hl

/-- **Claims for a wire.** A wire of weft at most one and depth at most `d` has a list of at most
`2 ^ depth` correct claims whose checks are at small depth at most `d`, such that with any correct
claims including them, Kleene evaluation of the gates with the claimed ones replaced knows the
wire. -/
theorem exists_claims {d n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {x : List Bool} (hx : x.length = n) {w : ℕ}
    (hw : w < n + gates.length)
    (hwd : (evalCode (depthInterpretation (largeGateCost signature)) 0 (List.replicate n 0)
      gates).getD w 0 ≤ 1)
    (hdp : (evalCode (depthInterpretation (σ := signature) 1) 0 (List.replicate n 0) gates).getD w 0 ≤ d) :
    ∃ cl : List (ℕ × Bool),
      cl.length ≤ 2 ^ (evalCode (depthInterpretation (σ := signature) 1) 0 (List.replicate n 0) gates).getD w 0 ∧
      (∀ c ∈ cl, c.1 < n + gates.length ∧
        (evalCode interpretation false x gates).getD c.1 false = c.2) ∧
      (∀ e ∈ cl.flatMap (claimChecks n gates), (smallDepths d n gates).getD e.1 (d + 1) ≤ d) ∧
      ∀ claims : List (ℕ × Bool), cl ⊆ claims →
        (∀ c ∈ claims, (evalCode interpretation false x gates).getD c.1 false = c.2) →
        (kleeneEval (claimInputs n claims) (overrideGates n claims gates)).getD w none ≠ none := by
  have hρ (claims : List (ℕ × Bool)) := length_claimInputs n claims
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w n with hwn | hwn
    · refine ⟨[(w, (evalCode interpretation false x gates).getD w false)],
        by simpa using Nat.one_le_two_pow,
        fun c hc => ?_, fun e he => ?_, fun claims hsub _ => ?_⟩
      · rw [List.mem_singleton] at hc
        subst hc
        exact ⟨by omega, rfl⟩
      · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, claimChecks, hwn,
          ↓reduceIte, List.mem_singleton] at he
        subst he
        rw [getD_smallDepths_of_lt _ _ _ hwn]
        exact Nat.zero_le _
      · have hmem := hsub (List.mem_singleton_self _)
        rw [getD_kleeneEval_of_lt _ _ (by rw [hρ]; exact hwn), getD_claimInputs _ hwn,
          claimInput]
        split_ifs with h₁ h₂
        · simp
        · simp
        · cases hb : (evalCode interpretation false x gates).getD w false
          · exact absurd (hb ▸ hmem) h₂
          · exact absurd (hb ▸ hmem) h₁
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hwn
    have hj : j < gates.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gates[j]? = some g := ⟨_, List.getElem?_eq_getElem hj⟩
    have hgj : gates[j] = g := (List.getElem?_eq_some_iff.1 hg).2
    obtain ⟨hlen, hlt⟩ := h.getElem j hj
    rw [hgj] at hlen hlt
    have hwdc : ∀ c ∈ g.2, (evalCode (depthInterpretation (largeGateCost signature)) 0
        (List.replicate n 0) gates).getD c 0 + largeGateCost signature g.1 ≤ 1 :=
      fun c hc => (getD_evalCode_depth_le _ h hg hc).trans hwd
    have hdpc : ∀ c ∈ g.2, (evalCode (depthInterpretation (σ := signature) 1) 0 (List.replicate n 0)
        gates).getD c 0 + 1 ≤ (evalCode (depthInterpretation (σ := signature) 1) 0 (List.replicate n 0)
          gates).getD (n + j) 0 := fun c hc => getD_evalCode_depth_le 1 h hg hc
    have hcw : ∀ c ∈ g.2, c < n + j := fun c hc => by have := hlt c hc; omega
    set v := evalCode interpretation false x gates with hv_def
    by_cases hlarge : 2 < g.2.length
    · have hcost : largeGateCost signature g.1 = 1 := by
        have h2 : 2 < g.1.arity := by
          have : g.2.length = g.1.arity := hlen
          omega
        simp only [largeGateCost, h2, ↓reduceIte]
      have hsd : ∀ c ∈ g.2, (smallDepths d n gates).getD c (d + 1) ≤ d := fun c hc => by
        have h0 := hwdc c hc
        have h1 := hdpc c hc
        have := getD_smallDepths_le (d := d) h (show c < n + gates.length by
          have := hcw c hc; omega) (by omega)
        omega
      obtain ⟨b0, hb0⟩ : ∃ b0, claimable g = some b0 := by
        obtain ⟨op, args⟩ := g
        cases op with
        | not =>
          have h1 : args.length = 1 := hlen
          have h2 : 2 < args.length := hlarge
          omega
        | and m => exact ⟨true, rfl⟩
        | or m => exact ⟨false, rfl⟩
      by_cases hvb : v.getD (n + j) false = b0
      · refine ⟨[(n + j, b0)], ?_, fun c hc => ?_, fun e he => ?_, fun claims hsub _ => ?_⟩
        · simp only [List.length_singleton]
          exact Nat.one_le_two_pow
        · rw [List.mem_singleton] at hc
          subst hc
          exact ⟨hw, hvb⟩
        · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, claimChecks,
            show ¬n + j < n by omega, gateAt_add hg, hb0, ↓reduceIte, List.mem_map] at he
          obtain ⟨c, hc, rfl⟩ := he
          exact hsd c hc
        · have hmem := hsub (List.mem_singleton_self _)
          rw [getD_kleeneEval_overrideGates h (hρ claims) claims hg]
          cases b0 <;> simp_all
      · have hvb' : v.getD (n + j) false = !b0 := by
          cases b0 <;> simpa using hvb
        obtain ⟨c, hc, hvc⟩ : ∃ c ∈ g.2, v.getD c false = !b0 := by
          by_contra hcon
          simp only [not_exists, not_and] at hcon
          exact hvb ((getD_evalCode_eq_iff_of_claimable h hx hg hb0).2 fun c hc => by
            have := hcon c hc
            cases b0 <;> simpa using this)
        obtain ⟨cl, hcl_len, hcl_corr, hcl_chk, hcl_fin⟩ := ih c (hcw c hc)
          (by have := hcw c hc; omega) (by have := hwdc c hc; omega)
          (by have := hdpc c hc; omega)
        refine ⟨cl, ?_, hcl_corr, hcl_chk, fun claims hsub hcorr => ?_⟩
        · refine hcl_len.trans (Nat.pow_le_pow_right (by norm_num) ?_)
          have := hdpc c hc
          omega
        have hκc := eq_of_ne_none h hx hcorr (hcl_fin claims hsub hcorr)
        rw [getD_kleeneEval_overrideGates h (hρ claims) claims hg]
        split_ifs
        · simp
        · simp
        · rw [kleeneOp_of_claimable hb0 (List.mem_map.2 ⟨c, hc, hκc.trans (congrArg some hvc)⟩)]
          simp
    · rw [not_lt] at hlarge
      have hex : ∀ c ∈ g.2, ∃ cl : List (ℕ × Bool),
          cl.length ≤ 2 ^ (evalCode (depthInterpretation (σ := signature) 1) 0 (List.replicate n 0)
            gates).getD c 0 ∧
          (∀ c ∈ cl, c.1 < n + gates.length ∧ v.getD c.1 false = c.2) ∧
          (∀ e ∈ cl.flatMap (claimChecks n gates), (smallDepths d n gates).getD e.1 (d + 1) ≤ d) ∧
          ∀ claims : List (ℕ × Bool), cl ⊆ claims →
            (∀ c ∈ claims, v.getD c.1 false = c.2) →
            (kleeneEval (claimInputs n claims) (overrideGates n claims gates)).getD c none ≠
              none :=
        fun c hc => ih c (hcw c hc) (by have := hcw c hc; omega)
          (by have := hwdc c hc; omega) (by have := hdpc c hc; omega)
      choose! CL hCL_len hCL_corr hCL_chk hCL_fin using hex
      refine ⟨g.2.flatMap CL, ?_, ?_, ?_, fun claims hsub hcorr => ?_⟩
      · rw [List.length_flatMap]
        have hbound : ∀ c ∈ g.2, (CL c).length ≤
            2 ^ ((evalCode (depthInterpretation (σ := signature) 1) 0 (List.replicate n 0) gates).getD (n + j) 0
              - 1) := fun c hc =>
          (hCL_len c hc).trans (Nat.pow_le_pow_right (by norm_num) (by have := hdpc c hc; omega))
        calc (g.2.map fun c => (CL c).length).sum
            ≤ (g.2.map fun _ => 2 ^ ((evalCode (depthInterpretation (σ := signature) 1) 0 (List.replicate n 0)
                gates).getD (n + j) 0 - 1)).sum := List.sum_le_sum fun c hc => hbound c hc
          _ = g.2.length * 2 ^ ((evalCode (depthInterpretation (σ := signature) 1) 0 (List.replicate n 0)
                gates).getD (n + j) 0 - 1) := by
              rw [List.map_const', List.sum_replicate, smul_eq_mul]
          _ ≤ 2 ^ (evalCode (depthInterpretation (σ := signature) 1) 0 (List.replicate n 0) gates).getD
                (n + j) 0 := by
              rcases Nat.eq_zero_or_pos g.2.length with h0 | hpos
              · rw [h0, Nat.zero_mul]
                exact Nat.zero_le _
              · obtain ⟨c, hc⟩ := List.exists_mem_of_length_pos hpos
                have := hdpc c hc
                obtain ⟨D', hD'⟩ := Nat.exists_eq_add_of_le (show 1 ≤
                  (evalCode (depthInterpretation (σ := signature) 1) 0 (List.replicate n 0) gates).getD
                    (n + j) 0 by omega)
                rw [hD', Nat.add_sub_cancel_left, Nat.add_comm 1 D', pow_succ']
                exact Nat.mul_le_mul_right _ hlarge
      · intro c' hc'
        obtain ⟨c, hc, hc'⟩ := List.mem_flatMap.1 hc'
        exact hCL_corr c hc c' hc'
      · intro e he
        obtain ⟨c', hc', he⟩ := List.mem_flatMap.1 he
        obtain ⟨c, hc, hc'⟩ := List.mem_flatMap.1 hc'
        exact hCL_chk c hc e (List.mem_flatMap.2 ⟨c', hc', he⟩)
      · have hkc : ∀ c ∈ g.2, (kleeneEval (claimInputs n claims)
            (overrideGates n claims gates)).getD c none = some (v.getD c false) := fun c hc =>
          eq_of_ne_none h hx hcorr (hCL_fin c hc claims
            (fun c' hc' => hsub (List.mem_flatMap.2 ⟨c, hc, hc'⟩)) hcorr)
        rw [getD_kleeneEval_overrideGates h (hρ claims) claims hg]
        split_ifs
        · simp
        · simp
        · have hmap : g.2.map (fun a => some (v.getD a false)) =
              (g.2.map (v.getD · false)).map some := by
            rw [List.map_map]
            rfl
          rw [List.map_congr_left hkc, hmap]
          exact kleeneOp_map_some_ne_none g.1 (by rw [List.length_map]; exact hlen)

/-- Correct claims give correct checks. -/
theorem checks_correct {n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {x : List Bool} (hx : x.length = n)
    {claims : List (ℕ × Bool)}
    (hcl : ∀ c ∈ claims, (evalCode interpretation false x gates).getD c.1 false = c.2) :
    ∀ e ∈ claims.flatMap (claimChecks n gates),
      (evalCode interpretation false x gates).getD e.1 false = e.2 := by
  intro e he
  obtain ⟨c, hc, he⟩ := List.mem_flatMap.1 he
  unfold claimChecks at he
  split_ifs at he with h₁ h₂
  · rw [List.mem_singleton] at he
    rw [he]
    exact hcl c hc
  · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt h₁)
    rcases hg : gates[j]? with _ | g
    · simp [gateAt, hj, List.getD_eq_getElem?_getD, hg, claimable] at h₂
    rw [hj, gateAt_add hg] at h₂ he
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 he
    have := hcl c hc
    rw [hj, getD_evalCode_eq_iff_of_claimable h hx hg h₂] at this
    exact this c' hc'
  · simp at he

/-- **Completeness of the certificate check.** If wire `o`, of weft at most one and depth at most
`d`, is true on an input, then at most `2 ^ d` correct claims are valid for it. -/
theorem exists_claimsValid {d n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {x : List Bool} (hx : x.length = n) {o : ℕ}
    (ho : o < n + gates.length)
    (hwd : (evalCode (depthInterpretation (largeGateCost signature)) 0 (List.replicate n 0)
      gates).getD o 0 ≤ 1)
    (hdp : (evalCode (depthInterpretation (σ := signature) 1) 0 (List.replicate n 0) gates).getD o 0 ≤ d)
    (hv : (evalCode interpretation false x gates).getD o false = true) :
    ∃ claims : List (ℕ × Bool), claims.length ≤ 2 ^ d ∧
      (∀ c ∈ claims, c.1 < n + gates.length ∧
        (evalCode interpretation false x gates).getD c.1 false = c.2) ∧
      claimsValid d n gates o claims = true := by
  obtain ⟨cl, hlen, hcorr, hchk, hfin⟩ := exists_claims h hx ho hwd hdp
  refine ⟨cl, hlen.trans (Nat.pow_le_pow_right (by norm_num) hdp), hcorr, ?_⟩
  have hk := eq_of_ne_none h hx (fun c hc => (hcorr c hc).2)
    (hfin cl (List.Subset.refl _) fun c hc => (hcorr c hc).2)
  rw [hv] at hk
  simp only [claimsValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨hk, hchk⟩

/-! ### Polynomial time -/

section PolyTime

variable {γ : Type} {encIn : γ ↪ List Bool} {nf : γ → ℕ} {gf : γ → List (Op × List ℕ)}
  {of : γ → ℕ} {cf : γ → List (ℕ × Bool)}

/-- Whether an operation, by its number, can be claimed to have value `b`. -/
private def claimFlag (op : Op) (b : Bool) : Bool :=
  !(op.toNat == 0) && ((op.toNat % 2 == 1) == b)

private theorem claimFlag_eq (op : Op) (b : Bool) (g : List ℕ) :
    claimFlag op b = decide (claimable (op, g) = some b) := by
  cases op <;> cases b <;> simp [claimFlag, claimable, Op.toNat, Nat.add_mod]

private theorem claimInput_eq (claims : List (ℕ × Bool)) (i : ℕ) :
    claimInput claims i = if decide ((i, true) ∈ claims) then some true
      else if decide ((i, false) ∈ claims) then some false else none := by
  simp only [claimInput, decide_eq_true_eq]

private theorem computableInPolyTime_claimInputs
    (hn : ComputableInPolyTime nf encIn encUnary)
    (hc : ComputableInPolyTime cf encIn (encList (encPair encUnary encBool))) :
    ComputableInPolyTime (fun a => claimInputs (nf a) (cf a)) encIn
      (encList (encOption encBool)) := by
  unfold claimInputs
  refine ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hn) ?_
  simp only [claimInput_eq]
  have hp := ComputableInPolyTime.id' (encIn := encPair encIn encUnary)
  have hcl := hc.comp hp.fst'
  have ht := ComputableInPolyTime.decide_mem hcl (hp.snd'.prod (ComputableInPolyTime.const true))
  have hf := ComputableInPolyTime.decide_mem hcl (hp.snd'.prod (ComputableInPolyTime.const false))
  exact ComputableInPolyTime.ite' ht (ComputableInPolyTime.const _)
    (ComputableInPolyTime.ite' hf (ComputableInPolyTime.const _) (ComputableInPolyTime.const _))

private theorem computableInPolyTime_opNat :
    ComputableInPolyTime (fun g : Op × List ℕ => g.1.toNat) (Circuit.encGate encOp) encUnary :=
  (ComputableInPolyTime.id' (encIn := Circuit.encGate encOp)).fst'.of_enc_eq fun _ => rfl

private theorem computableInPolyTime_claimFlag {f : γ → Op × List ℕ} {b : γ → Bool}
    (hf : ComputableInPolyTime f encIn (Circuit.encGate encOp))
    (hb : ComputableInPolyTime b encIn encBool) :
    ComputableInPolyTime (fun a => claimFlag (f a).1 (b a)) encIn encBool := by
  have hop := computableInPolyTime_opNat.comp hf
  unfold claimFlag
  have h0 := ComputableInPolyTime.unary_beq' hop (ComputableInPolyTime.const 0)
  have h1 := ComputableInPolyTime.unary_beq' (ComputableInPolyTime.unary_mod.comp
    (hop.prod (ComputableInPolyTime.const 2))) (ComputableInPolyTime.const 1)
  fun_prop

private theorem overrideGate_eq (n : ℕ) (claims : List (ℕ × Bool)) (g : Op × List ℕ) (j : ℕ) :
    overrideGate n claims g j =
      if claimFlag g.1 true && decide ((n + j, true) ∈ claims) then (.and 0, [])
      else if claimFlag g.1 false && decide ((n + j, false) ∈ claims) then (.or 0, [])
      else g := by
  simp only [overrideGate, claimFlag_eq g.1 _ g.2, Bool.and_eq_true, decide_eq_true_eq]

private theorem computableInPolyTime_overrideGates
    (hn : ComputableInPolyTime nf encIn encUnary)
    (hg : ComputableInPolyTime gf encIn (encList (Circuit.encGate encOp)))
    (hc : ComputableInPolyTime cf encIn (encList (encPair encUnary encBool))) :
    ComputableInPolyTime (fun a => overrideGates (nf a) (cf a) (gf a)) encIn
      (encList (Circuit.encGate encOp)) := by
  simp only [overrideGates, overrideGate_eq]
  refine ComputableInPolyTime.mapWithInput
    ((ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.zipIdx _)).comp hg) ?_
  have hp := ComputableInPolyTime.id'
    (encIn := encPair encIn (encPair (Circuit.encGate encOp) encUnary))
  have hcl := hc.comp hp.fst'
  have hw := ComputableInPolyTime.unary_add' (hn.comp hp.fst') hp.snd'.snd'
  have ht := ComputableInPolyTime.bool_and'
    (computableInPolyTime_claimFlag hp.snd'.fst' (ComputableInPolyTime.const true))
    (ComputableInPolyTime.decide_mem hcl (hw.prod (ComputableInPolyTime.const true)))
  have hf := ComputableInPolyTime.bool_and'
    (computableInPolyTime_claimFlag hp.snd'.fst' (ComputableInPolyTime.const false))
    (ComputableInPolyTime.decide_mem hcl (hw.prod (ComputableInPolyTime.const false)))
  exact ComputableInPolyTime.ite' ht (ComputableInPolyTime.const _)
    (ComputableInPolyTime.ite' hf (ComputableInPolyTime.const _) hp.snd'.fst')

private theorem claimChecks_eq (n : ℕ) (gates : List (Op × List ℕ)) (c : ℕ × Bool) :
    claimChecks n gates c = if decide (c.1 < n) then [c]
      else if claimFlag (gateAt n gates c.1).1 c.2 then (gateAt n gates c.1).2.map (·, c.2)
      else [] := by
  simp only [claimChecks, claimFlag_eq _ _ (gateAt n gates c.1).2, decide_eq_true_eq]

private theorem computableInPolyTime_checks
    (hn : ComputableInPolyTime nf encIn encUnary)
    (hg : ComputableInPolyTime gf encIn (encList (Circuit.encGate encOp)))
    (hc : ComputableInPolyTime cf encIn (encList (encPair encUnary encBool))) :
    ComputableInPolyTime (fun a => (cf a).flatMap (claimChecks (nf a) (gf a))) encIn
      (encList (encPair encNat encBool)) := by
  refine ComputableInPolyTime.flatMapWithInput hc ?_
  simp only [claimChecks_eq]
  have hp := ComputableInPolyTime.id' (encIn := encPair encIn (encPair encUnary encBool))
  have hb := ComputableInPolyTime.unary_to_binary
  have hgate : ComputableInPolyTime (fun p : γ × (ℕ × Bool) => gateAt (nf p.1) (gf p.1) p.2.1)
      (encPair encIn (encPair encUnary encBool)) (Circuit.encGate encOp) := by
    unfold gateAt
    exact ComputableInPolyTime.listGetDWithInput (hg.comp hp.fst')
      (ComputableInPolyTime.unary_sub' hp.snd'.fst' (hn.comp hp.fst')) _
  have hlt := ComputableInPolyTime.unary_lt' hp.snd'.fst' (hn.comp hp.fst')
  have hself : ComputableInPolyTime (fun p : γ × (ℕ × Bool) => [p.2])
      (encPair encIn (encPair encUnary encBool)) (encList (encPair encNat encBool)) :=
    ComputableInPolyTime.cons' ((hb.comp hp.snd'.fst').prod hp.snd'.snd')
      (ComputableInPolyTime.const [])
  have hmap : ComputableInPolyTime
      (fun p : γ × (ℕ × Bool) => (gateAt (nf p.1) (gf p.1) p.2.1).2.map (·, p.2.2))
      (encPair encIn (encPair encUnary encBool)) (encList (encPair encNat encBool)) := by
    refine ComputableInPolyTime.mapWithInput hgate.snd' ?_
    have hq := ComputableInPolyTime.id'
      (encIn := encPair (encPair encIn (encPair encUnary encBool)) encNat)
    exact hq.snd'.prod hq.fst'.snd'.snd'
  exact ComputableInPolyTime.ite' hlt hself (ComputableInPolyTime.ite'
    (computableInPolyTime_claimFlag hgate hp.snd'.snd') hmap (ComputableInPolyTime.const []))

private theorem computableInPolyTime_smallDepthOp (d : ℕ) :
    ComputableInPolyTime (fun l : List ℕ => smallDepthOp d Op.not l) (encList encUnary)
      encUnary := by
  unfold smallDepthOp maxTwo
  fun_prop

theorem smallDepthOp_le (d : ℕ) (op : Op) (l : List ℕ) : smallDepthOp d op l ≤ d + 1 := by
  unfold smallDepthOp
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

private theorem computableInPolyTime_smallDepths (d : ℕ)
    (hn : ComputableInPolyTime nf encIn encUnary)
    (hg : ComputableInPolyTime gf encIn (encList (Circuit.encGate encOp))) :
    ComputableInPolyTime (fun a => smallDepths d (nf a) (gf a)) encIn (encList encUnary) := by
  have hstep : ComputableInPolyTime
      (fun p : List ℕ × (Op × List ℕ) =>
        p.1 ++ [smallDepthOp d p.2.1 (p.2.2.map (p.1.getD · (d + 1)))])
      (encPair (encList encUnary) (Circuit.encGate encOp)) (encList encUnary) := by
    have hp := ComputableInPolyTime.id' (encIn :=
      encPair (encList encUnary) (Circuit.encGate encOp))
    have hargs : ComputableInPolyTime
        (fun p : List ℕ × (Op × List ℕ) => p.2.2.map (p.1.getD · (d + 1)))
        (encPair (encList encUnary) (Circuit.encGate encOp)) (encList encUnary) := by
      refine ComputableInPolyTime.mapWithInput hp.snd'.snd' ?_
      have hq := ComputableInPolyTime.id' (encIn :=
        encPair (encPair (encList encUnary) (Circuit.encGate encOp)) encNat)
      exact ComputableInPolyTime.listGetD_binary (encA := encUnary) (d + 1) hq.fst'.fst' hq.snd'
    exact ComputableInPolyTime.listAppend' hp.fst' (ComputableInPolyTime.cons'
      ((computableInPolyTime_smallDepthOp d).comp hargs) (ComputableInPolyTime.const []))
  unfold smallDepths
  exact ComputableInPolyTime.foldl_of_bounded_growth hg
    (ComputableInPolyTime.replicate hn (ComputableInPolyTime.const 0)) hstep
    (growth := 2 * (d + 1) + 5) fun sd g => by
      have := smallDepthOp_le d g.1 (g.2.map (sd.getD · (d + 1)))
      simp only [encList_append, List.length_append, encList_cons, encList_nil, List.append_nil,
        length_frame, encUnary_apply, List.length_replicate]
      omega

/-- **The certificate check is polynomial-time**, for a fixed depth bound `d` and inputs, gates,
output and claims computed in polynomial time. -/
theorem computableInPolyTime_claimsValid (d : ℕ)
    (hn : ComputableInPolyTime nf encIn encUnary)
    (hg : ComputableInPolyTime gf encIn (encList (Circuit.encGate encOp)))
    (ho : ComputableInPolyTime of encIn encNat)
    (hc : ComputableInPolyTime cf encIn (encList (encPair encUnary encBool))) :
    ComputableInPolyTime (fun a => claimsValid d (nf a) (gf a) (of a) (cf a)) encIn encBool := by
  have hk := computableInPolyTime_kleeneEval (computableInPolyTime_claimInputs hn hc)
    (computableInPolyTime_overrideGates hn hg hc)
  have hval := ComputableInPolyTime.listGetD_binary (encA := encOption encBool) none hk ho
  have hfirst := ComputableInPolyTime.decide_eq' hval
    (ComputableInPolyTime.const (some true) (encOut := encOption encBool))
  have hsd := computableInPolyTime_smallDepths d hn hg
  have hall : ComputableInPolyTime
      (fun a => ((cf a).flatMap (claimChecks (nf a) (gf a))).all fun e =>
        decide ((smallDepths d (nf a) (gf a)).getD e.1 (d + 1) ≤ d)) encIn encBool := by
    refine ComputableInPolyTime.allWithInput (computableInPolyTime_checks hn hg hc) ?_
    have hp := ComputableInPolyTime.id' (encIn := encPair encIn (encPair encNat encBool))
    exact ComputableInPolyTime.unary_le'
      (ComputableInPolyTime.listGetD_binary (encA := encUnary) (d + 1) (hsd.comp hp.fst')
        hp.snd'.fst') (ComputableInPolyTime.const d)
  exact ComputableInPolyTime.bool_and' hfirst hall

end PolyTime

end WeftOne

end Cslib.Circuits.Boolean.Unbounded
