/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.Horn

/-!
# Horn syntax under variable relabeling

Relabeling changes no literal polarities or occurrences, even when different variables become
identical. Consequently it preserves and reflects Horn and dual Horn syntax, without an
injectivity hypothesis.

## Main results

* `Cslib.Logic.PL.Clause.isHorn_relabel`: Horn clause syntax is invariant under relabeling.
* `Cslib.Logic.PL.CNF.isHorn_relabel`: Horn formula syntax is invariant under relabeling.
* `Cslib.Logic.PL.CNF.isDualHorn_relabel`: dual Horn syntax is invariant under relabeling.
-/

public section

namespace Cslib.Logic.PL

variable {V W : Type*}

/-- Relabeling preserves the number of occurrences of either polarity, including repetitions. -/
theorem Clause.length_filter_relabel (f : V → W) (c : Clause V) (b : Bool) :
    ((c.relabel f).filter fun l => l.2 == b).length =
      (c.filter fun l => l.2 == b).length := by
  simp [Clause.relabel, List.filter_map, Function.comp_def]

/-- Horn clause syntax is invariant under arbitrary, possibly noninjective relabeling. -/
@[simp] theorem Clause.isHorn_relabel (f : V → W) (c : Clause V) :
    (c.relabel f).IsHorn ↔ c.IsHorn := by
  simp [Clause.IsHorn, Clause.relabel, List.filter_map, Function.comp_def]

/-- Horn formula syntax is invariant under arbitrary relabeling. -/
@[simp] theorem CNF.isHorn_relabel (f : V → W) (φ : CNF V) :
    (φ.relabel f).IsHorn ↔ φ.IsHorn := by
  simp [CNF.IsHorn, CNF.relabel]

/-- Dual Horn clause syntax is invariant under arbitrary relabeling. -/
@[simp] theorem Clause.isDualHorn_relabel (f : V → W) (c : Clause V) :
    (c.relabel f).IsDualHorn ↔ c.IsDualHorn := by
  simp [Clause.isDualHorn_iff, Clause.relabel, List.filter_map, Function.comp_def]

/-- Dual Horn formula syntax is invariant under arbitrary relabeling. -/
@[simp] theorem CNF.isDualHorn_relabel (f : V → W) (φ : CNF V) :
    (φ.relabel f).IsDualHorn ↔ φ.IsDualHorn := by
  simp [CNF.isDualHorn_iff, CNF.relabel]

end Cslib.Logic.PL
