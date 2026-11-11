/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.BlumComplexity.Basic
import Complexity.Computability.BlumComplexity.Cancellation
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Filter.Finite

/-!
# Blum's speedup theorem

For every Blum complexity measure `Φ` and every computable `r`, there is a computable
`0`/`1`-valued function `f` with no fastest program: every program `c` for `f` is beaten by
another program `c'` for `f` with `r n (Φ c' n) < Φ c n` for almost all `n`
[Blum, *A machine-independent theory of the complexity of recursive functions*][Blum1967].
Taking `r n m = 2 ^ m`, for instance, every program for `f` can be sped up exponentially, and the
speedup can be repeated forever.

## Construction

The proof is Blum's priority construction combined with the recursion theorem. For a program `e`,
parameters `u, d` and an input `x`, the version `vers e u d` runs the following *cancellation run*
(`Cslib.BlumComplexity.Cancellation.canc`). At stage `y`, the program numbered `i` is
*eligible* when `u ≤ i ≤ y` and, for some `d' ≤ y`, `Φ i y ≤ r y (Φ (vers e (i + 1) d') y)`.
The least eligible program not cancelled earlier is cancelled, and the version outputs
`1 - φ_i y` there, so that `φ_i` differs from it at `y`. Stages without a cancellation output `0`.
The data `d` encodes a finite table that fixes the output at some of the first stages; nothing is
cancelled at such a stage. By the recursion theorem (`Nat.Partrec.Code.fixed_point₂`), the
program `e` can run its own versions.

* Every version is total, by induction on `x - u`: deciding eligibility at stage `y ≤ x` only
  runs versions with a larger `u`.
* The version `vers e 0 d₀` with the empty table computes a function `f`. If `c` computes `f`,
  then `c` is never cancelled, since a cancellation of `c` at `y` would force `f y ≠ φ_c y`. So
  `c` is eligible only finitely often.
* For `u = encode c + 1`, the run of `vers e u d` skips the programs below `u`. Those are
  cancelled only finitely often. A table `d` recording `f` at those finitely many stages makes
  `vers e u d` compute `f` exactly.
* Eventually `c` is not eligible, and in particular
  `Φ c y > r y (Φ (vers e (encode c + 1) d) y)`.

## Strength

The conclusion `r n (Φ c' n) < Φ c n` is strict, so it implies the non-strict form
`r n (Φ c' n) ≤ Φ c n`. The function `r` takes the input `n` as an extra argument, as in Blum's
paper. The one-argument form `r (Φ c' n) < Φ c n` is the special case `fun _ m => r m`
(`speedup'`). The statement is not vacuous: `f` is computable, so it has a program, and every
program for `f` halts on every input, so both costs in the conclusion are defined everywhere
(`Cslib.BlumComplexity.BlumMeasure.dom_cost_of_total`).

## Main results

* `Cslib.BlumComplexity.BlumMeasure.speedup`: **Blum's speedup theorem**.
* `Cslib.BlumComplexity.BlumMeasure.speedup'`: the one-argument form.
* `Cslib.BlumComplexity.BlumMeasure.exists_no_fastest`: the function `f` has no program that is
  fastest up to `r`.

## References

* [M. Blum, *A machine-independent theory of the complexity of recursive functions*][Blum1967]
-/

public section

namespace Cslib.BlumComplexity.BlumMeasure

open Encodable Denumerable Filter Cancellation
open Nat.Partrec (Code)

variable (Φ : BlumMeasure)

/-! ### The construction -/

namespace Speedup

variable (r : ℕ → ℕ → ℕ)

/-- The version of the program `e` with parameters `u` and `d`. -/
private def vers (e : Code) (u d : ℕ) : Code := Code.curry e (Nat.pair u d)

/-- The program numbered `i` is eligible at stage `y`: for some `d ≤ y`, its cost is at most
`r y (Φ (vers e (i + 1) d) y)`. -/
private def Elig (e : Code) (i y : ℕ) : Prop :=
  ∃ d < y + 1, ∃ m ∈ Φ.cost (vers e (i + 1) d) y, ∃ m' ∈ Φ.cost (ofNat Code i) y, m' ≤ r y m

/-- Eligibility with the cost of the consulted version bounded by `B`. Unlike `Elig`, this is
decidable. -/
private def EligB (e : Code) (B i y : ℕ) : Prop :=
  ∃ d < y + 1, ∃ m < B + 1, m ∈ Φ.cost (vers e (i + 1) d) y ∧
    ∃ m' < r y m + 1, m' ∈ Φ.cost (ofNat Code i) y

/-- Every version consulted by the run of `vers e u ·` up to stage `x` halts with cost at most
`B`. -/
private def CostOK (e : Code) (u x B : ℕ) : Prop :=
  ∀ i < x + 1, ∀ y < x + 1, ∀ d < y + 1, u ≤ i → i ≤ y →
    ∃ m < B + 1, m ∈ Φ.cost (vers e (i + 1) d) y

/-- `Elig` as a Boolean, decided classically. -/
private noncomputable def elig (e : Code) (i y : ℕ) : Bool :=
  @decide (Elig Φ r e i y) (Classical.dec _)

/-- `EligB` as a Boolean, decided classically. It is computable by `computable_eligB`. -/
private noncomputable def eligB (e : Code) (B i y : ℕ) : Bool :=
  @decide (EligB Φ r e B i y) (Classical.dec _)

/-- `CostOK` as a Boolean, decided classically. It is computable by `computable_costOK`. -/
private noncomputable def costOK (e : Code) (u x B : ℕ) : Bool :=
  @decide (CostOK Φ e u x B) (Classical.dec _)

/-- The output stored for stage `y` by the table `d`, if any. -/
private def ovOf (d y : ℕ) : Option ℕ := ((ofNat (List (Option ℕ)) d)[y]?).bind id

/-- Whether the table `d` overrides stage `y`. -/
private def ovB (d y : ℕ) : Bool := (ovOf d y).isSome

/-- The program cancelled at stage `x`, or `Code.zero` if there is none. -/
private noncomputable def selCode (e : Code) (u d x B : ℕ) : Code :=
  ((canc (eligB Φ r e B) (ovB d) u x).map (ofNat Code)).getD Code.zero

/-- The output at stage `x`, given the output `w` of the cancelled program. -/
private noncomputable def post (e : Code) (u d x B w : ℕ) : ℕ :=
  (ovOf d x).getD (((canc (eligB Φ r e B) (ovB d) u x).map fun _ => 1 - w).getD 0)

/-- The version `vers e u d` on the input `x`, assuming that `e` runs its own versions. -/
private noncomputable def run (e : Code) (u d x : ℕ) : Part ℕ :=
  (Nat.rfind fun B => Part.some (costOK Φ e u x B)).bind fun B =>
    (selCode Φ r e u d x B).eval x |>.map (post Φ r e u d x B)

/-- All versions together, as a function of the program `e`. -/
private noncomputable def master (e : Code) (N : ℕ) : Part ℕ :=
  run Φ r e N.unpair.1.unpair.1 N.unpair.1.unpair.2 N.unpair.2

/-! ### Computability of the construction -/

private theorem computable_vers {α : Type*} [Primcodable α] {e : α → Code} {u d : α → ℕ}
    (he : Computable e) (hu : Computable u) (hd : Computable d) :
    Computable fun a => vers (e a) (u a) (d a) :=
  Code.primrec₂_curry.to_comp.comp he (Primrec₂.natPair.to_comp.comp hu hd)

private theorem computablePred_eligB (hr : Computable₂ r) :
    ComputablePred fun x : ((Code × ℕ) × ℕ) × ℕ => EligB Φ r x.1.1.1 x.1.1.2 x.1.2 x.2 := by
  -- x = (((e, B), i), y)
  have he : Computable fun x : ((Code × ℕ) × ℕ) × ℕ => x.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hB : Computable fun x : ((Code × ℕ) × ℕ) × ℕ => x.1.1.2 :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hi : Computable fun x : ((Code × ℕ) × ℕ) × ℕ => x.1.2 :=
    Computable.snd.comp Computable.fst
  have hy : Computable fun x : ((Code × ℕ) × ℕ) × ℕ => x.2 := Computable.snd
  refine ComputablePred.exists_lt (f := fun x : ((Code × ℕ) × ℕ) × ℕ => x.2 + 1)
    (p := fun x d => ∃ m < x.1.1.2 + 1, m ∈ Φ.cost (vers x.1.1.1 (x.1.2 + 1) d) x.2 ∧
      ∃ m' < r x.2 m + 1, m' ∈ Φ.cost (ofNat Code x.1.2) x.2) ?_ (Computable.succ.comp hy)
  refine ComputablePred.exists_lt
    (f := fun z : (((Code × ℕ) × ℕ) × ℕ) × ℕ => z.1.1.1.2 + 1)
    (p := fun z m => m ∈ Φ.cost (vers z.1.1.1.1 (z.1.1.2 + 1) z.2) z.1.2 ∧
      ∃ m' < r z.1.2 m + 1, m' ∈ Φ.cost (ofNat Code z.1.1.2) z.1.2) ?_
    (Computable.succ.comp (hB.comp Computable.fst))
  -- w = (((((e, B), i), y), d), m)
  have he' : Computable fun w : ((((Code × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => w.1.1.1.1.1 :=
    he.comp (Computable.fst.comp Computable.fst)
  have hi' : Computable fun w : ((((Code × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => w.1.1.1.2 :=
    hi.comp (Computable.fst.comp Computable.fst)
  have hy' : Computable fun w : ((((Code × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => w.1.1.2 :=
    hy.comp (Computable.fst.comp Computable.fst)
  have hd' : Computable fun w : ((((Code × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => w.1.2 :=
    Computable.snd.comp Computable.fst
  have hm' : Computable fun w : ((((Code × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => w.2 := Computable.snd
  refine ComputablePred.and ?_ ?_
  · exact Φ.computablePred_mem_cost_comp
      (computable_vers he' (Computable.succ.comp hi') hd') hy' hm'
  · refine ComputablePred.exists_lt
      (f := fun w : ((((Code × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => r w.1.1.2 w.2 + 1)
      (p := fun w m' => m' ∈ Φ.cost (ofNat Code w.1.1.1.2) w.1.1.2) ?_
      (Computable.succ.comp (hr.comp hy' hm'))
    exact Φ.computablePred_mem_cost_comp ((Computable.ofNat Code).comp
      (hi'.comp Computable.fst)) (hy'.comp Computable.fst) Computable.snd

private theorem computablePred_costOK :
    ComputablePred fun x : ((Code × ℕ) × ℕ) × ℕ => CostOK Φ x.1.1.1 x.1.1.2 x.1.2 x.2 := by
  -- x = (((e, u), x), B)
  have hx : Computable fun x : ((Code × ℕ) × ℕ) × ℕ => x.1.2 :=
    Computable.snd.comp Computable.fst
  refine ComputablePred.forall_lt (f := fun x : ((Code × ℕ) × ℕ) × ℕ => x.1.2 + 1)
    (p := fun x i => ∀ y < x.1.2 + 1, ∀ d < y + 1, x.1.1.2 ≤ i → i ≤ y →
      ∃ m < x.2 + 1, m ∈ Φ.cost (vers x.1.1.1 (i + 1) d) y) ?_ (Computable.succ.comp hx)
  -- z = ((((e, u), x), B), i)
  refine ComputablePred.forall_lt
    (f := fun z : (((Code × ℕ) × ℕ) × ℕ) × ℕ => z.1.1.2 + 1)
    (p := fun z y => ∀ d < y + 1, z.1.1.1.2 ≤ z.2 → z.2 ≤ y →
      ∃ m < z.1.2 + 1, m ∈ Φ.cost (vers z.1.1.1.1 (z.2 + 1) d) y) ?_
    (Computable.succ.comp (hx.comp Computable.fst))
  -- w = (((((e, u), x), B), i), y)
  refine ComputablePred.forall_lt
    (f := fun w : ((((Code × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => w.2 + 1)
    (p := fun w d => w.1.1.1.1.2 ≤ w.1.2 → w.1.2 ≤ w.2 →
      ∃ m < w.1.1.2 + 1, m ∈ Φ.cost (vers w.1.1.1.1.1 (w.1.2 + 1) d) w.2) ?_
    (Computable.succ.comp Computable.snd)
  -- v = ((((((e, u), x), B), i), y), d)
  have he : Computable fun v : (((((Code × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => v.1.1.1.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp
      (Computable.fst.comp Computable.fst))))
  have hu : Computable fun v : (((((Code × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => v.1.1.1.1.1.2 :=
    Computable.snd.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp
      (Computable.fst.comp Computable.fst))))
  have hB : Computable fun v : (((((Code × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => v.1.1.1.2 :=
    Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
  have hi : Computable fun v : (((((Code × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => v.1.1.2 :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hy : Computable fun v : (((((Code × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => v.1.2 :=
    Computable.snd.comp Computable.fst
  have hd : Computable fun v : (((((Code × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => v.2 := Computable.snd
  refine (ComputablePred.nat_le hu hi).imp ((ComputablePred.nat_le hi hy).imp ?_)
  refine ComputablePred.exists_lt
    (f := fun v : (((((Code × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => v.1.1.1.2 + 1)
    (p := fun v m => m ∈ Φ.cost (vers v.1.1.1.1.1.1 (v.1.1.2 + 1) v.2) v.1.2) ?_
    (Computable.succ.comp hB)
  exact Φ.computablePred_mem_cost_comp (computable_vers (he.comp Computable.fst)
    (Computable.succ.comp (hi.comp Computable.fst)) (hd.comp Computable.fst))
    (hy.comp Computable.fst) Computable.snd

private theorem primrec_ovOf : Primrec₂ ovOf := by
  unfold ovOf
  have h := Primrec.option_bind (Primrec.list_getElem?.comp
    ((Primrec.ofNat (List (Option ℕ))).comp Primrec.fst) Primrec.snd)
    (Primrec₂.right (α := ℕ × ℕ) (β := Option ℕ))
  exact h.of_eq fun _ => rfl

private theorem computable_costOK : Computable fun x : ((Code × ℕ) × ℕ) × ℕ =>
    costOK Φ x.1.1.1 x.1.1.2 x.1.2 x.2 :=
  @ComputablePred.decide _ _ _ (fun _ => Classical.dec _) (computablePred_costOK Φ)

private theorem computable_eligB (hr : Computable₂ r) :
    Computable fun x : ((Code × ℕ) × ℕ) × ℕ => eligB Φ r x.1.1.1 x.1.1.2 x.1.2 x.2 :=
  @ComputablePred.decide _ _ _ (fun _ => Classical.dec _) (computablePred_eligB Φ r hr)

/-- The run of `vers e u d` at stage `x` under the cost cap `B`, as a function of
`q = ((e, (u, (d, x))), B)`. -/
private theorem computable_canc_eligB (hr : Computable₂ r) :
    Computable fun q : (Code × ℕ × ℕ × ℕ) × ℕ =>
      canc (eligB Φ r q.1.1 q.2) (ovB q.1.2.2.1) q.1.2.1 q.1.2.2.2 := by
  refine computable_canc (E := fun q : (Code × ℕ × ℕ × ℕ) × ℕ => eligB Φ r q.1.1 q.2)
    (ov := fun q => ovB q.1.2.2.1) ?_ ?_ (Computable.fst.comp (Computable.snd.comp
      Computable.fst)) (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      Computable.fst)))
  · have h := (computable_eligB Φ r hr).comp (α := ((Code × ℕ × ℕ × ℕ) × ℕ) × ℕ × ℕ)
      (Computable.pair (Computable.pair (Computable.pair
      (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Computable.snd.comp Computable.fst)) (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd))
    exact h.of_eq fun _ => rfl
  · have h1 : Computable₂ ovB := (Primrec.option_isSome.comp primrec_ovOf).to_comp
    have hd : Computable fun p : ((Code × ℕ × ℕ × ℕ) × ℕ) × ℕ => p.1.1.2.2.1 :=
      Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
        (Computable.fst.comp Computable.fst)))
    exact (h1.comp hd Computable.snd :)

private theorem computable_selCode (hr : Computable₂ r) :
    Computable fun q : (Code × ℕ × ℕ × ℕ) × ℕ =>
      selCode Φ r q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2 := by
  unfold selCode
  exact Computable.option_getD (Computable.option_map (computable_canc_eligB Φ r hr)
    ((Computable.ofNat Code).comp Computable.snd).to₂) (Computable.const Code.zero)

private theorem computable_post (hr : Computable₂ r) :
    Computable fun q : ((Code × ℕ × ℕ × ℕ) × ℕ) × ℕ =>
      post Φ r q.1.1.1 q.1.1.2.1 q.1.1.2.2.1 q.1.1.2.2.2 q.1.2 q.2 := by
  unfold post
  have hov : Computable fun q : ((Code × ℕ × ℕ × ℕ) × ℕ) × ℕ =>
      ovOf q.1.1.2.2.1 q.1.1.2.2.2 :=
    primrec_ovOf.to_comp.comp
      (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
        (Computable.fst.comp Computable.fst))))
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
        (Computable.fst.comp Computable.fst))))
  exact Computable.option_getD hov (Computable.option_getD (Computable.option_map
    ((computable_canc_eligB Φ r hr).comp Computable.fst)
    (Primrec.nat_sub.to_comp.comp (Computable.const 1)
      (Computable.snd.comp Computable.fst)).to₂) (Computable.const 0))

private theorem partrec₂_master (hr : Computable₂ r) : Partrec₂ (master Φ r) := by
  -- the arguments `(e, (u, (d, x)))` decoded from `(e, N)`
  have hq : Computable fun p : Code × ℕ =>
      (p.1, p.2.unpair.1.unpair.1, p.2.unpair.1.unpair.2, p.2.unpair.2) := by
    refine Computable.pair Computable.fst (Computable.pair ?_ (Computable.pair ?_ ?_))
    · exact Computable.fst.comp (Computable.unpair.comp (Computable.fst.comp
        (Computable.unpair.comp Computable.snd)))
    · exact Computable.snd.comp (Computable.unpair.comp (Computable.fst.comp
        (Computable.unpair.comp Computable.snd)))
    · exact Computable.snd.comp (Computable.unpair.comp Computable.snd)
  have hcost : Computable₂ fun (p : Code × ℕ) (B : ℕ) =>
      costOK Φ p.1 p.2.unpair.1.unpair.1 p.2.unpair.2 B := by
    have h := (computable_costOK Φ).comp (α := (Code × ℕ) × ℕ)
      (Computable.pair (Computable.pair (Computable.pair
        (Computable.fst.comp (hq.comp Computable.fst))
        (Computable.fst.comp (Computable.snd.comp (hq.comp Computable.fst))))
        (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
          (hq.comp Computable.fst))))) Computable.snd)
    exact h.of_eq fun _ => rfl
  have hsel : Computable₂ fun (p : Code × ℕ) (B : ℕ) =>
      selCode Φ r p.1 p.2.unpair.1.unpair.1 p.2.unpair.1.unpair.2 p.2.unpair.2 B := by
    have h := (computable_selCode Φ r hr).comp (α := (Code × ℕ) × ℕ)
      (Computable.pair (hq.comp Computable.fst) Computable.snd)
    exact h.of_eq fun _ => rfl
  have hpost : Computable₂ fun (q : (Code × ℕ) × ℕ) (w : ℕ) =>
      post Φ r q.1.1 q.1.2.unpair.1.unpair.1 q.1.2.unpair.1.unpair.2 q.1.2.unpair.2 q.2 w := by
    have h := (computable_post Φ r hr).comp (α := ((Code × ℕ) × ℕ) × ℕ)
      (Computable.pair (Computable.pair (hq.comp (Computable.fst.comp Computable.fst))
        (Computable.snd.comp Computable.fst)) Computable.snd)
    exact h.of_eq fun _ => rfl
  have hx : Computable fun q : (Code × ℕ) × ℕ => q.1.2.unpair.2 :=
    Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.fst))
  have h := Partrec.bind (Partrec.rfind (hcost.partrec₂))
    (Partrec.map (Code.eval_part.comp hsel hx) hpost).to₂
  exact h.of_eq fun _ => rfl

/-! ### Semantics of the construction -/

variable {Φ r}

private theorem eval_vers {e : Code} (he : e.eval = master Φ r e) (u d x : ℕ) :
    (vers e u d).eval x = run Φ r e u d x := by
  rw [vers, Code.eval_curry, he]
  simp only [master, Nat.unpair_pair]

private theorem costOK_eq_true {e u x B} : costOK Φ e u x B = true ↔ CostOK Φ e u x B :=
  @decide_eq_true_iff _ (Classical.dec _)

private theorem elig_eq_true {e i y} : elig Φ r e i y = true ↔ Elig Φ r e i y :=
  @decide_eq_true_iff _ (Classical.dec _)

/-- Under the cost cap of `CostOK`, capped eligibility is eligibility. -/
private theorem eligB_eq {e u x B} (h : CostOK Φ e u x B) {i y} (hu : u ≤ i) (hiy : i ≤ y)
    (hy : y ≤ x) : eligB Φ r e B i y = elig Φ r e i y := by
  unfold eligB elig
  refine decide_eq_decide.2 ⟨?_, ?_⟩
  · rintro ⟨d, hd, m, -, hm, m', hm', hm'c⟩
    exact ⟨d, hd, m, hm, m', hm'c, by omega⟩
  · rintro ⟨d, hd, m, hm, m', hm'c, hle⟩
    obtain ⟨m₀, hm₀, hm₀c⟩ := h i (by omega) y (by omega) d hd hu hiy
    obtain rfl := Part.mem_unique hm hm₀c
    exact ⟨d, hd, m, hm₀, hm, m', Nat.lt_succ_of_le hle, hm'c⟩

private theorem canc_eligB_eq {e u d x B} (h : CostOK Φ e u x B) :
    canc (eligB Φ r e B) (ovB d) u x = canc (elig Φ r e) (ovB d) u x :=
  canc_congr (fun _ _ hu hiy hy => eligB_eq h hu hiy hy) x le_rfl

/-- The run of a version once a cost cap `B` has been found. -/
private theorem run_eq {e u d x B} (hB : B ∈ Nat.rfind fun B => Part.some (costOK Φ e u x B)) :
    run Φ r e u d x = Part.map (fun w => (ovOf d x).getD
      (((canc (elig Φ r e) (ovB d) u x).map fun _ => 1 - w).getD 0))
      (Code.eval (((canc (elig Φ r e) (ovB d) u x).map (ofNat Code)).getD Code.zero) x) := by
  have hok : CostOK Φ e u x B := costOK_eq_true.1 (Part.mem_some_iff.1 (Nat.rfind_spec hB)).symm
  rw [run, Part.bind_of_mem hB]
  unfold selCode post
  rw [canc_eligB_eq hok]

/-- If every version consulted up to stage `x` halts, some cost cap works. -/
private theorem exists_costOK {e u x}
    (h : ∀ i y d, u ≤ i → i ≤ y → y ≤ x → d ≤ y → (Φ.cost (vers e (i + 1) d) y).Dom) :
    ∃ B, CostOK Φ e u x B := by
  classical
  let g : (ℕ × ℕ) × ℕ → ℕ := fun t =>
    if hd : (Φ.cost (vers e (t.1.1 + 1) t.2) t.1.2).Dom then
      (Φ.cost (vers e (t.1.1 + 1) t.2) t.1.2).get hd else 0
  let S : Finset ((ℕ × ℕ) × ℕ) :=
    (Finset.range (x + 1) ×ˢ Finset.range (x + 1)) ×ˢ Finset.range (x + 1)
  refine ⟨S.sup g, fun i hi y hy d hd hui hiy => ?_⟩
  have hdom := h i y d hui hiy (by omega) (by omega)
  refine ⟨g ((i, y), d), Nat.lt_succ_of_le (Finset.le_sup ?_), ?_⟩
  · simp only [S, Finset.mem_product, Finset.mem_range]
    omega
  · simp only [g, hdom, ↓reduceDIte]
    exact Part.get_mem hdom

/-- Under a cost cap, the run halts. -/
private theorem dom_run_of_costOK {e u d x B} (hB : CostOK Φ e u x B) :
    (run Φ r e u d x).Dom := by
  have hrf : (Nat.rfind fun B => Part.some (costOK Φ e u x B)).Dom :=
    Nat.rfind_dom.2 ⟨B, Part.mem_some_iff.2 (costOK_eq_true.2 hB).symm,
      fun _ => Part.dom_iff_mem.2 ⟨_, Part.mem_some _⟩⟩
  rw [run_eq (Part.get_mem hrf)]
  change (Code.eval _ _).Dom
  cases hc : canc (elig Φ r e) (ovB d) u x with
  | none => exact trivial
  | some i =>
    obtain ⟨-, -, -, hE, -⟩ := canc_eq_some.1 hc
    obtain ⟨-, -, -, -, m', hm', -⟩ := elig_eq_true.1 hE
    exact (Φ.dom_cost_iff _ _).1 (Part.dom_iff_mem.2 ⟨m', hm'⟩)

/-- At the fixed point `e`, every version halts on every input, by induction on `x - u`. -/
private theorem costOK_of_fixed {e : Code} (he : e.eval = master Φ r e) :
    ∀ n u x, x + 1 - u ≤ n → ∃ B, CostOK Φ e u x B := by
  intro n
  induction n with
  | zero =>
    intro u x hn
    exact exists_costOK fun i y d hui hiy hyx _ => by omega
  | succ n ih =>
    intro u x hn
    refine exists_costOK fun i y d hui hiy hyx _ => ?_
    rw [Φ.dom_cost_iff, eval_vers he]
    obtain ⟨B, hB⟩ := ih (i + 1) y (by omega)
    exact dom_run_of_costOK hB

/-- At the fixed point, membership in the run is membership in the selected evaluation. -/
private theorem mem_run {e : Code} (he : e.eval = master Φ r e) {u d x w : ℕ}
    (hw : w ∈ (((canc (elig Φ r e) (ovB d) u x).map (ofNat Code)).getD Code.zero).eval x) :
    (ovOf d x).getD (((canc (elig Φ r e) (ovB d) u x).map fun _ => 1 - w).getD 0) ∈
      run Φ r e u d x := by
  obtain ⟨B, hB⟩ := costOK_of_fixed he _ u x le_rfl
  have hrf : (Nat.rfind fun B => Part.some (costOK Φ e u x B)).Dom :=
    Nat.rfind_dom.2 ⟨B, Part.mem_some_iff.2 (costOK_eq_true.2 hB).symm,
      fun _ => Part.dom_iff_mem.2 ⟨_, Part.mem_some _⟩⟩
  rw [run_eq (Part.get_mem hrf)]
  exact Part.mem_map _ hw

/-- A cancelled program halts at the stage where it is cancelled. -/
private theorem dom_eval_of_canc {e : Code} {ov : ℕ → Bool} {u x i : ℕ}
    (h : canc (elig Φ r e) ov u x = some i) : ((ofNat Code i).eval x).Dom := by
  obtain ⟨-, -, -, hE, -⟩ := canc_eq_some.1 h
  obtain ⟨-, -, -, -, m', hm', -⟩ := elig_eq_true.1 hE
  exact (Φ.dom_cost_iff _ _).1 (Part.dom_iff_mem.2 ⟨m', hm'⟩)

private theorem ovOf_encode_nil (y : ℕ) : ovOf (encode ([] : List (Option ℕ))) y = none := by
  simp [ovOf]

private theorem ovOf_encode_map (g : ℕ → Option ℕ) (N y : ℕ) :
    ovOf (encode ((List.range N).map g)) y = if y < N then g y else none := by
  unfold ovOf
  rw [ofNat_encode, List.getElem?_map]
  split_ifs with hy
  · rw [List.getElem?_range hy]
    rfl
  · rw [List.getElem?_eq_none (by simpa using hy)]
    rfl

end Speedup

open Speedup

/-- **Blum's speedup theorem** [Blum1967]. For every computable `r`, there is a computable
function `f` with values in `{0, 1}` such that every program `c` for `f` has another program `c'`
for `f` with `r n (Φ c' n) < Φ c n` for all sufficiently large `n`. -/
theorem speedup {r : ℕ → ℕ → ℕ} (hr : Computable₂ r) :
    ∃ f : ℕ → ℕ, Computable f ∧ (∀ n, f n ≤ 1) ∧
      ∀ c : Code, (∀ n, f n ∈ c.eval n) → ∃ c' : Code, (∀ n, f n ∈ c'.eval n) ∧
        ∀ᶠ n in atTop, ∀ m ∈ Φ.cost c' n, ∀ m' ∈ Φ.cost c n, r n m < m' := by
  obtain ⟨e, he⟩ := Code.fixed_point₂ (partrec₂_master Φ r hr)
  let d₀ := encode ([] : List (Option ℕ))
  have hovd₀ : ∀ y, ovOf d₀ y = none := ovOf_encode_nil
  have hov₀ : ovB d₀ = fun _ => false := funext fun y => by
    simp only [ovB, hovd₀, Option.isSome_none]
  -- the run from `0` without overrides
  let C₀ : ℕ → Option ℕ := canc (elig Φ r e) (fun _ => false) 0
  have hdom : ∀ x, (run Φ r e 0 d₀ x).Dom := fun x => by
    obtain ⟨B, hB⟩ := costOK_of_fixed he _ 0 x le_rfl
    exact dom_run_of_costOK hB
  let f : ℕ → ℕ := fun x => (run Φ r e 0 d₀ x).get (hdom x)
  have hfmem : ∀ x, f x ∈ run Φ r e 0 d₀ x := fun x => Part.get_mem (hdom x)
  -- the value of `f` at a stage with a cancellation, and at a stage without one
  have hfc : ∀ x i w, C₀ x = some i → w ∈ (ofNat Code i).eval x → f x = 1 - w := by
    intro x i w hc hw
    have hc' : canc (elig Φ r e) (ovB d₀) 0 x = some i := by rw [hov₀]; exact hc
    have h := mem_run he (u := 0) (d := d₀) (x := x) (w := w)
      (by rw [hc', Option.map_some, Option.getD_some]; exact hw)
    rw [hovd₀, Option.getD_none, hc', Option.map_some, Option.getD_some] at h
    exact Part.mem_unique (hfmem x) h
  have hf0 : ∀ x, C₀ x = none → f x = 0 := by
    intro x hc
    have hc' : canc (elig Φ r e) (ovB d₀) 0 x = none := by rw [hov₀]; exact hc
    have h := mem_run he (u := 0) (d := d₀) (x := x) (w := 0)
      (by rw [hc', Option.map_none, Option.getD_none]; exact Part.mem_some 0)
    rw [hovd₀, Option.getD_none, hc', Option.map_none, Option.getD_none] at h
    exact Part.mem_unique (hfmem x) h
  have hf1 : ∀ x, f x ≤ 1 := by
    intro x
    cases hc : C₀ x with
    | none => rw [hf0 x hc]; exact zero_le_one
    | some i =>
      obtain ⟨w, hw⟩ := Part.dom_iff_mem.1 (dom_eval_of_canc hc)
      rw [hfc x i w hc hw]
      omega
  have hfcomp : Computable f := by
    refine ((Code.eval_part.comp (Computable.const (vers e 0 d₀)) Computable.id).of_eq_tot
      fun x => ?_)
    rw [eval_vers he]
    exact hfmem x
  refine ⟨f, hfcomp, hf1, fun c hc => ?_⟩
  -- `c` is never cancelled, so eventually it is not eligible
  let i := encode c
  have hnc : ∀ y, C₀ y ≠ some i := by
    intro y hy
    have h := hfc y i (f y) hy (by simpa [i] using hc y)
    have := hf1 y
    omega
  have hne := eventually_not_eligible hnc
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_canc_ne (elig Φ r e) (fun _ => false) 0 (i + 1))
  -- the table recording `f` at the stages where a program below `i + 1` is cancelled
  classical
  let g : ℕ → Option ℕ := fun y => if ∃ j < i + 1, C₀ y = some j then some (f y) else none
  let D := encode ((List.range N).map g)
  have hovD : ∀ y, ovOf D y = g y := by
    intro y
    rw [ovOf_encode_map]
    split_ifs with hy
    · rfl
    · have : ¬∃ j < i + 1, C₀ y = some j := fun ⟨j, hj, hc⟩ => hN y (by omega) j hj hc
      simp only [g, this, ↓reduceIte]
  have hovB : ∀ y, ovB D y = true ↔ ∃ j < i + 1, C₀ y = some j := by
    intro y
    simp only [ovB, hovD, g]
    split_ifs with h <;> simp [h]
  have hsame := canc_override hovB
  -- the version `vers e (i + 1) D` computes `f`
  let c' := vers e (i + 1) D
  have hc' : ∀ y, f y ∈ c'.eval y := by
    intro y
    rw [eval_vers he]
    by_cases hlow : ∃ j < i + 1, C₀ y = some j
    · have hg : ovOf D y = some (f y) := by rw [hovD]; simp only [g, hlow, ↓reduceIte]
      cases hcy : canc (elig Φ r e) (ovB D) (i + 1) y with
      | none =>
        have h := mem_run he (u := i + 1) (d := D) (x := y) (w := 0)
          (by rw [hcy]; exact Part.mem_some 0)
        rwa [hg, Option.getD_some] at h
      | some k =>
        obtain ⟨w, hw⟩ := Part.dom_iff_mem.1 (dom_eval_of_canc hcy)
        have h := mem_run he (u := i + 1) (d := D) (x := y) (w := w)
          (by simpa [hcy] using hw)
        rwa [hg, Option.getD_some] at h
    · have hg : ovOf D y = none := by rw [hovD]; simp only [g, hlow, ↓reduceIte]
      cases hcy : C₀ y with
      | none =>
        have hcy' : canc (elig Φ r e) (ovB D) (i + 1) y = none := by
          cases h' : canc (elig Φ r e) (ovB D) (i + 1) y with
          | none => rfl
          | some k =>
            have := (hsame y k (canc_le h').1).1 h'
            exact absurd (this.symm.trans hcy) (Option.some_ne_none k)
        have h := mem_run he (u := i + 1) (d := D) (x := y) (w := 0)
          (by rw [hcy']; exact Part.mem_some 0)
        rw [hg, hcy', Option.map_none, Option.getD_none, Option.getD_none] at h
        rwa [hf0 y hcy]
      | some k =>
        have hk : i + 1 ≤ k := by
          by_contra hk
          exact hlow ⟨k, by omega, hcy⟩
        have hcy' : canc (elig Φ r e) (ovB D) (i + 1) y = some k := (hsame y k hk).2 hcy
        obtain ⟨w, hw⟩ := Part.dom_iff_mem.1 (dom_eval_of_canc hcy)
        have h := mem_run he (u := i + 1) (d := D) (x := y) (w := w)
          (by simpa [hcy'] using hw)
        rw [hfc y k w hcy hw]
        simpa [hg, hcy'] using h
  refine ⟨c', hc', ?_⟩
  -- eventually `c` is not eligible, which is the speedup
  filter_upwards [hne, eventually_ge_atTop D] with y hy hDy m hm m' hm'
  by_contra hlt
  push Not at hlt
  have : elig Φ r e i y = true :=
    elig_eq_true.2 ⟨D, Nat.lt_succ_of_le hDy, m, hm, m', by simpa [i] using hm', hlt⟩
  rw [hy] at this
  exact Bool.false_ne_true this

/-- **Blum's speedup theorem**, one-argument form: for every computable `r`, there is a
computable function `f` with values in `{0, 1}` such that every program `c` for `f` has another
program `c'` for `f` with `r (Φ c' n) < Φ c n` for all sufficiently large `n`. -/
theorem speedup' {r : ℕ → ℕ} (hr : Computable r) :
    ∃ f : ℕ → ℕ, Computable f ∧ (∀ n, f n ≤ 1) ∧
      ∀ c : Code, (∀ n, f n ∈ c.eval n) → ∃ c' : Code, (∀ n, f n ∈ c'.eval n) ∧
        ∀ᶠ n in atTop, ∀ m ∈ Φ.cost c' n, ∀ m' ∈ Φ.cost c n, r m < m' :=
  Φ.speedup (r := fun _ m => r m) (hr.comp Computable.snd).to₂

/-- The function of Blum's speedup theorem has no program that is fastest up to `r`: for each
program `c` for it, some program `c'` for it is faster than `c` by `r` almost everywhere, so `c`
is not within `r` of every other program. -/
theorem exists_no_fastest {r : ℕ → ℕ → ℕ} (hr : Computable₂ r) :
    ∃ f : ℕ → ℕ, Computable f ∧ (∀ n, f n ≤ 1) ∧
      ¬∃ c : Code, (∀ n, f n ∈ c.eval n) ∧ ∀ c' : Code, (∀ n, f n ∈ c'.eval n) →
        ∀ᶠ n in atTop, ∀ m ∈ Φ.cost c n, ∀ m' ∈ Φ.cost c' n, m ≤ r n m' := by
  obtain ⟨f, hf, hf1, hsp⟩ := Φ.speedup hr
  refine ⟨f, hf, hf1, fun ⟨c, hc, hfast⟩ => ?_⟩
  obtain ⟨c', hc', hev⟩ := hsp c hc
  obtain ⟨n, hn, hn'⟩ := ((hfast c' hc').and hev).exists
  obtain ⟨m, hm⟩ := Part.dom_iff_mem.1 (Φ.dom_cost_of_total hc n)
  obtain ⟨m', hm'⟩ := Part.dom_iff_mem.1 (Φ.dom_cost_of_total hc' n)
  have h1 := hn m hm m' hm'
  have h2 := hn' m' hm' m hm
  omega

end Cslib.BlumComplexity.BlumMeasure
