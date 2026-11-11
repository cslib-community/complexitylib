/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# The simp sets of `ram_eval`

The simp sets used by `ram_eval` and `ram_exact_eval` in
`CslibFrontier.Computability.WordRAM.Notation`. They are declared in a file of their own because
an attribute cannot be used in the file that declares it. A simp set is indexed once, when it is
filled, so a call that uses it does not index its lemmas again. These tactics run often, and with
the same lemmas every time.

`Notation.lean` and `ExactNotation.lean` fill the sets with `ram_eval_simp_set`, which adds exactly
the entries `simp only [ … ]` would build from the same list. The sets are internal: tagging a
lemma with either attribute changes what every later `ram_eval` call uses.

## Main definitions

* `ram_eval_simps`: the lemmas with which `ram_eval` runs the interpreter, standard basis.
* `ram_exact_eval_simps`: the same over the exact basis, for `ram_exact_eval`.
-/

public meta section

/-- The simp set `ram_eval_simps` runs the word-RAM interpreter `Cslib.WordRAM.Code.eval` on
structured code over the standard basis, for `ram_eval`. It is filled by `ram_eval_simp_set`; do not
tag lemmas with it. -/
register_simp_attr ram_eval_simps

/-- The simp set `ram_exact_eval_simps` runs the word-RAM interpreter `Cslib.WordRAM.Code.eval` on
structured code over the exact basis, for `ram_exact_eval`. It is filled by `ram_eval_simp_set`; do
not tag lemmas with it. -/
register_simp_attr ram_exact_eval_simps

end
