/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle.Exponential
public import Complexity.Computability.Complexity.Classes.Oracle.SelfReduction
import Complexity.Computability.Complexity.Classes.Oracle.Closure
import Complexity.Computability.Complexity.Classes.PH.Kannan
import Complexity.Computability.Complexity.Problems.SAT.PolyTime

/-!
# Witness bits in `E ^ NP`

The witness bit of a formula `φ` and a variable `v` (`Cslib.Complexity.SAT.witnessBit`) is the
value that the self-reduction of `φ` against the oracle `encCNF '' SAT` fixes for `v`, read as
`Cslib.Complexity.SAT.verifier` reads its certificate. It is polynomial time relative to that oracle
(`Cslib.Complexity.SAT.computableInPolyTimeWithOracle_witnessBit`), and when `φ` is satisfiable the
witness bits form a satisfying assignment of `φ` (`Cslib.Complexity.SAT.eval_witnessBit`).

After a preparation of the formula and the variable within time `O(2 ^ (d * n))`, the witness bits
of a family of formulas of size `2 ^ O(n)` form a problem in `E ^ NP`
(`Cslib.Complexity.preimage_witnessBit_mem_ENP`), by
`Cslib.Complexity.preimage_mem_EWithOracle`. This is the witness language in the folklore
lemma that circuits for `E ^ NP` give witness circuits for `NTIME (2 ^ n)`
[Williams, Lemma 3.2][Williams2010]. There the witness is the lexicographically smallest one,
found by binary search with `NP` queries; here it is the assignment found by the self-reduction.
Any witness that is canonical and computable with an `NP` oracle serves that argument.

## Main definitions

* `Cslib.Complexity.SAT.witnessBit`: the value the self-reduction fixes for a variable.

## Main results

* `Cslib.Complexity.SAT.computableInPolyTimeWithOracle_witnessBit`: the witness bit is in
  polynomial time relative to `encCNF '' SAT`.
* `Cslib.Complexity.SAT.eval_witnessBit`: the witness bits satisfy every satisfiable formula.
* `Cslib.Complexity.preimage_witnessBit_mem_ENP`: witness bits of exponentially prepared formulas
  form a problem in `E ^ NP`.

## References

* [R. Williams, *Improving exhaustive search implies superpolynomial lower bounds*][Williams2010]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

namespace SAT

open Classical in
/-- **The witness bit** of a formula `φ` and a variable `v`: the value that the self-reduction of
`φ` against the oracle `encCNF '' SAT` fixes for `v`, read at the first occurrence of `v` as
`Cslib.Complexity.SAT.verifier` reads its certificate. -/
noncomputable def witnessBit (p : CNF ℕ × ℕ) : Bool :=
  assignment p.1 (search (fun ψ => decide (encCNF ψ ∈ encCNF '' SAT)) p.1) p.2

/-- **The witness bits satisfy every satisfiable formula.** -/
theorem eval_witnessBit {φ : CNF ℕ} (hφ : φ ∈ SAT) : φ.eval (fun v => witnessBit (φ, v)) = true :=
  (verifier_search_image φ).mpr hφ

open Classical in
/-- **The witness bit is polynomial time relative to `encCNF '' SAT`**: run the self-reduction,
asking the oracle, and read the bit of the variable. -/
theorem computableInPolyTimeWithOracle_witnessBit :
    ComputableInPolyTimeWithOracle (encCNF '' SAT) witnessBit (encPair encCNF encNat) encBool := by
  have hsearch := (computableInPolyTimeWithOracle_search (encCNF '' SAT)).preprocess
    (ComputableInPolyTime.fst encCNF encNat)
  have hread : ComputableInPolyTime
      (fun q : (CNF ℕ × ℕ) × List Bool => assignment q.1.1 q.2 q.1.2)
      (encPair (encPair encCNF encNat) encBits) encBool :=
    computableInPolyTime_assignment.comp
      (((ComputableInPolyTime.fst (encPair encCNF encNat) encBits).fst').prod
        (ComputableInPolyTime.snd (encPair encCNF encNat) encBits) |>.prod
        ((ComputableInPolyTime.fst (encPair encCNF encNat) encBits).snd'))
  exact hsearch.map_with (g := fun p w => assignment p.1 w p.2) hread

end SAT

/-- **Witness bits of exponentially prepared formulas are in `E ^ NP`.** If `prepare` computes a
formula and a variable from an instance within time `O(2 ^ (d * n))`, then the instances whose
prepared variable has witness bit `true` form a problem in `E ^ NP`: prepare, then run the
self-reduction against the oracle `encCNF '' SAT`, which is in `NP`. -/
theorem preimage_witnessBit_mem_ENP {α : Type} {enc : α ↪ List Bool} {prepare : α → CNF ℕ × ℕ}
    {S : α → ℕ} {d : ℕ}
    (hprepare : ComputableInO prepare enc (encPair encCNF encNat)
      (fun a => 2 ^ (d * (enc a).length)) S) :
    {a | SAT.witnessBit (prepare a) = true} ∈ ENP enc :=
  mem_ENP.mpr ⟨encCNF '' SAT, image_SAT_mem_NP,
    preimage_mem_EWithOracle (M := {p | SAT.witnessBit p = true})
      ⟨SAT.witnessBit, SAT.computableInPolyTimeWithOracle_witnessBit, fun _ => Iff.rfl⟩
      hprepare⟩

end Cslib.Complexity
