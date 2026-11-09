/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Computability.ComputablePred
public import Mathlib.Computability.PartrecCode
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Blum complexity measures

Blum's axioms describe a complexity measure without fixing a machine model
[Blum, *A machine-independent theory of the complexity of recursive functions*][Blum1967]. Fix an
acceptable numbering `φ` of the partial recursive functions; here it is Mathlib's
`Nat.Partrec.Code` with `Code.eval`. A *complexity measure* is a family `Φ` of partial functions,
one for each program, such that

1. `Φ c n` is defined exactly when `φ_c n` is defined, and
2. the predicate `Φ c n = m` is decidable, as a predicate of `(c, n, m)`.

Running time and space of Turing machines are the motivating examples.
`Cslib.BlumComplexity.fuelMeasure`, in `Complexity.Computability.BlumComplexity.Fuel`, is an
instance for Mathlib's evaluator `Code.evaln`.

The *complexity class* `Φ.complexityClass t` of a total bound `t` is the class of total functions
`f` that some program `c` computes with `Φ c n ≤ t n` for almost all `n`, that is, for all
sufficiently large `n`. This is the class `C_t` of Borodin
[Borodin, *Computational complexity and the existence of complexity gaps*][Borodin1972]. The
bound applies almost everywhere, not at every input. For each such `f`, finitely many inputs may
exceed the bound.

## Main definitions

* `Cslib.BlumComplexity.BlumMeasure`: a complexity measure satisfying Blum's axioms over
  `Nat.Partrec.Code`.
* `Cslib.BlumComplexity.BlumMeasure.complexityClass`: the class `C_t` of total functions computable
  with cost at most `t` almost everywhere.

## Main results

* `Cslib.BlumComplexity.BlumMeasure.partrec_cost`: every complexity measure is partial recursive.
* `Cslib.BlumComplexity.BlumMeasure.computablePred_cost_le`: the predicate `Φ c n ≤ b` is
  decidable. In particular, whether `φ_c n` halts within cost `b` is decidable.
* `Cslib.BlumComplexity.BlumMeasure.computable_of_mem_complexityClass`: complexity classes contain
  only computable functions.
* `Cslib.BlumComplexity.BlumMeasure.exists_computable_mem_complexityClass`: every computable
  function lies in `C_t` for some computable `t`.

## References

* [M. Blum, *A machine-independent theory of the complexity of recursive functions*][Blum1967]
* [A. Borodin, *Computational complexity and the existence of complexity gaps*][Borodin1972]
-/

public section

namespace Cslib.BlumComplexity

open Encodable Nat.Partrec Filter

/-- A **Blum complexity measure** [Blum1967] over the acceptable numbering `Nat.Partrec.Code`: a
cost `cost c n` for each program `c` and input `n`, defined exactly when `c` halts on `n`, such
that the predicate `m ∈ cost c n` (that is, `Φ c n = m`) is computable. -/
structure BlumMeasure where
  /-- The cost `Φ c n` of running the program `c` on the input `n`. -/
  cost : Code → ℕ →. ℕ
  /-- Blum's first axiom: the cost is defined exactly when the program halts. -/
  dom_cost_iff (c : Code) (n : ℕ) : (cost c n).Dom ↔ (c.eval n).Dom
  /-- Blum's second axiom: the predicate `Φ c n = m` is computable. -/
  computablePred_mem_cost :
    ComputablePred fun (((c, n), m) : (Code × ℕ) × ℕ) => m ∈ cost c n

namespace BlumMeasure

variable (Φ : BlumMeasure)

/-- Blum's second axiom, with computable functions substituted for the program, the input and the
cost. -/
theorem computablePred_mem_cost_comp {α : Type*} [Primcodable α] {f : α → Code} {g h : α → ℕ}
    (hf : Computable f) (hg : Computable g) (hh : Computable h) :
    ComputablePred fun a => h a ∈ Φ.cost (f a) (g a) :=
  Φ.computablePred_mem_cost.comp ((hf.pair hg).pair hh)

/-- A program that computes a total function has its cost defined on every input. -/
theorem dom_cost_of_total {f : ℕ → ℕ} {c : Code} (hc : ∀ n, f n ∈ c.eval n) (n : ℕ) :
    (Φ.cost c n).Dom :=
  (Φ.dom_cost_iff c n).2 (Part.dom_iff_mem.2 ⟨_, hc n⟩)

/-- For a program that computes a total function, a property holds of every value of its cost at
`n` exactly when it holds of some value: the cost is defined and single-valued. -/
theorem forall_mem_cost_iff_exists_of_total {f : ℕ → ℕ} {c : Code} (hc : ∀ n, f n ∈ c.eval n)
    {p : ℕ → Prop} (n : ℕ) : (∀ m ∈ Φ.cost c n, p m) ↔ ∃ m ∈ Φ.cost c n, p m := by
  obtain ⟨m, hm⟩ := Part.dom_iff_mem.1 (Φ.dom_cost_of_total hc n)
  exact ⟨fun h => ⟨m, hm, h m hm⟩, fun ⟨m', hm', h⟩ m'' hm'' => Part.mem_unique hm' hm'' ▸ h⟩

/-- Every complexity measure is partial recursive: the least `m` with `Φ c n = m` is found by
unbounded search. -/
theorem partrec_cost : Partrec₂ Φ.cost := by
  obtain ⟨b, hb, hpb⟩ := ComputablePred.computable_iff.1 Φ.computablePred_mem_cost
  have hp : Partrec₂ fun (x : Code × ℕ) (m : ℕ) => Part.some (b ((x.1, x.2), m)) :=
    (hb.comp ((Computable.fst.comp Computable.fst).pair (Computable.snd.comp Computable.fst)
      |>.pair Computable.snd)).partrec
  have hbm : ∀ c n m, b ((c, n), m) = true ↔ m ∈ Φ.cost c n := fun c n m => by
    rw [show (m ∈ Φ.cost c n) = (fun (((c, n), m) : (Code × ℕ) × ℕ) => m ∈ Φ.cost c n)
      ((c, n), m) from rfl, hpb]
  refine (Partrec.rfind hp).of_eq fun x => Part.ext fun k => Nat.mem_rfind.trans ?_
  simp only [Part.mem_some_iff]
  rw [eq_comm, hbm]
  refine ⟨fun h => h.1, fun h => ⟨h, fun {j} hj => ?_⟩⟩
  rw [eq_comm, Bool.eq_false_iff, ne_eq, hbm]
  exact fun hj' => absurd (Part.mem_unique hj' h) hj.ne

/-- The predicate `Φ c n ≤ b` is computable. In particular, whether `c` halts on `n` within cost
`b` is decidable. -/
theorem computablePred_cost_le :
    ComputablePred fun (((c, n), b) : (Code × ℕ) × ℕ) => ∃ m ∈ Φ.cost c n, m ≤ b := by
  refine (ComputablePred.exists_lt
    (p := fun (x : (Code × ℕ) × ℕ) m => m ∈ Φ.cost x.1.1 x.1.2)
    (Φ.computablePred_mem_cost_comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Computable.snd.comp (Computable.fst.comp Computable.fst)) Computable.snd)
    (Computable.succ.comp Computable.snd)).of_eq fun _ => ?_
  simp only [Nat.lt_succ_iff]
  exact ⟨fun ⟨m, hm, h⟩ => ⟨m, h, hm⟩, fun ⟨m, h, hm⟩ => ⟨m, hm, h⟩⟩

/-- The **complexity class** `C_t` of a bound `t`: total functions `f` computed by some program `c`
(`f n ∈ c.eval n` for every `n`) whose cost satisfies `Φ c n ≤ t n` for all sufficiently large `n`
[Borodin1972]. -/
def complexityClass (t : ℕ → ℕ) : Set (ℕ → ℕ) :=
  {f | ∃ c : Code, (∀ n, f n ∈ c.eval n) ∧ ∀ᶠ n in atTop, ∀ m ∈ Φ.cost c n, m ≤ t n}

variable {Φ}

theorem mem_complexityClass {t f : ℕ → ℕ} :
    f ∈ Φ.complexityClass t ↔
      ∃ c : Code, (∀ n, f n ∈ c.eval n) ∧ ∀ᶠ n in atTop, ∀ m ∈ Φ.cost c n, m ≤ t n :=
  Iff.rfl

/-- Complexity classes are monotone in the bound, compared almost everywhere. -/
theorem complexityClass_mono {t t' : ℕ → ℕ} (h : t ≤ᶠ[atTop] t') :
    Φ.complexityClass t ⊆ Φ.complexityClass t' := by
  rintro f ⟨c, hc, hev⟩
  refine ⟨c, hc, ?_⟩
  filter_upwards [hev, h] with n hn htn m hm
  exact (hn m hm).trans htn

/-- Complexity classes contain only computable functions. -/
theorem computable_of_mem_complexityClass {t f : ℕ → ℕ} (hf : f ∈ Φ.complexityClass t) :
    Computable f := by
  obtain ⟨c, hc, -⟩ := hf
  exact Partrec.nat_iff.2 (Code.exists_code.2 ⟨c, funext fun n => Part.eq_some_iff.2 (hc n)⟩)

/-- Every computable function lies in the complexity class of some computable bound: the cost of
any program computing it. -/
theorem exists_computable_mem_complexityClass {f : ℕ → ℕ} (hf : Computable f) :
    ∃ t : ℕ → ℕ, Computable t ∧ f ∈ Φ.complexityClass t := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hf)
  have hmem : ∀ n, f n ∈ c.eval n := fun n => by rw [hc]; exact Part.mem_some _
  have hdom : ∀ n, (Φ.cost c n).Dom := Φ.dom_cost_of_total hmem
  refine ⟨fun n => (Φ.cost c n).get (hdom n), ?_, c, hmem, Eventually.of_forall fun n m hm => ?_⟩
  · exact (Φ.partrec_cost.comp (Computable.const c) Computable.id).of_eq_tot fun n =>
      Part.get_mem (hdom n)
  · exact (Part.mem_unique hm (Part.get_mem (hdom n))).le

end BlumMeasure

end Cslib.BlumComplexity
