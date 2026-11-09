/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Edge.Defects

/-!
# The two actual ports of an edge variable

Two distinct original incidences naming the same variable exhaust its occurrences. This
packages the existing partner API for positional transports that already exhibit both ends.
-/

public section

namespace Cslib.Logic.PL.CSP.EdgeInstance

variable {Rel V : Type*} {F : CSP Rel V}

/-- Two distinct displayed ports exhaust every occurrence of their edge variable. -/
theorem eq_or_eq_of_two (h : EdgeInstance F) {o p q : Occurrence F}
    (hp : o.var = p.var) (hq : q.var = p.var) (hne : q ≠ p) : o = p ∨ o = q := by
  have hqp := (h.eq_or_eq_partner hq).resolve_left hne
  simpa only [← hqp] using h.eq_or_eq_partner hp

/-- A variable's defect is the disagreement of any displayed pair of its distinct ports. -/
theorem inconsistent_iff_of_two (h : EdgeInstance F) (l : OccurrenceLabeling F Bool)
    (p q : Occurrence F) (hv : q.var = p.var) (hn : q ≠ p) :
    Inconsistent l p.var ↔ l p ≠ l q := by
  have hq : q = h.partner p := (h.eq_or_eq_partner hv).resolve_left hn
  rw [h.inconsistent_iff, ← hq]

end Cslib.Logic.PL.CSP.EdgeInstance

namespace Cslib.Logic.PL.CSP

variable {Rel V : Type*} {F : CSP Rel V}

/-- Agreement at all actual ports of one variable preserves its exact defect status. -/
theorem inconsistent_congr {f g : OccurrenceLabeling F Bool} {v : V}
    (h : ∀ o : Occurrence F, o.var = v → f o = g o) :
    Inconsistent f v ↔ Inconsistent g v := by
  constructor
  · rintro ⟨o, p, ho, hp, hn⟩
    exact ⟨o, p, ho, hp, by rwa [← h o ho, ← h p hp]⟩
  · rintro ⟨o, p, ho, hp, hn⟩
    exact ⟨o, p, ho, hp, by rwa [h o ho, h p hp]⟩

/-- Agreement on a finite variable set preserves exactly the defects in that set. -/
theorem defects_inter_eq_of_eqOn [DecidableEq V] {f g : OccurrenceLabeling F Bool}
    (vs : Finset V) (h : ∀ o : Occurrence F, o.var ∈ vs → f o = g o) :
    defects f ∩ vs = defects g ∩ vs := by
  ext v
  simp only [Finset.mem_inter, mem_defects]
  by_cases hv : v ∈ vs
  · exact and_congr_left (fun _ => inconsistent_congr (fun o ho => h o (ho ▸ hv)))
  · simp only [hv, and_false]

end Cslib.Logic.PL.CSP
