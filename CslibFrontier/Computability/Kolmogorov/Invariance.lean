/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.Basic
import Mathlib.Data.Set.Finite.List

/-!
# Invariance

A *simulation* of a description method `M` by a description method `N` compiles every `M`-program
`p` into an `N`-program of length at most `|p| + c` with the same output, and if `p` halts within
`t` steps, then the compiled program halts within `τ |p| t` steps. Then `N` is at most `c` worse
than `M`: `C_N(x) ≤ C_M(x) + c`, and a description of length `k` within time `t` under `M` gives a
description of length `k + c` within time `τ k t` under `N`, provided the overhead `τ` is monotone
in the program length. This is the invariance theorem of Kolmogorov complexity
[Li and Vitányi, Chapters 2 and 7][LiVitanyi2019], [Sipser, Section 6.4][Sipser2013], relative to
the simulation: a method of a class that simulates every method of the class with constant program
overhead is *additively optimal* for the class, and two additively optimal methods of the class
agree up to an additive constant.

For plain complexity only the outputs matter: a compiler that preserves outputs and adds at most
`c` bits is a simulation for *some* time overhead, because there are finitely many programs of
each length (`Cslib.Kolmogorov.DescriptionMethod.exists_simulation_of_produces`).

## Main definitions

* `Cslib.Kolmogorov.DescriptionMethod.Simulation`: a simulation of `M` by `N` with program
  overhead `c` and time overhead `τ`.
* `Cslib.Kolmogorov.DescriptionMethod.IsAdditivelyOptimal`: a method of a class that is at most a
  constant worse than every method of the class.

## Main results

* `Cslib.Kolmogorov.DescriptionMethod.Simulation.ecomplexity_le`: `C_N(x) ≤ C_M(x) + c`.
* `Cslib.Kolmogorov.DescriptionMethod.Simulation.etimeBoundedComplexity_le_of_le`: if
  `C_M^t(x) ≤ k` then `C_N^{τ k t}(x) ≤ k + c`, for a time overhead monotone in the program
  length.
* `Cslib.Kolmogorov.DescriptionMethod.Simulation.etimeBoundedComplexity_le`:
  `C_N^{σ t}(x) ≤ C_M^t(x) + c` for a time overhead `σ` independent of the program.
* `Cslib.Kolmogorov.DescriptionMethod.Simulation.etimeBoundedComplexity_le_of_polynomial`: the
  transfer under a polynomial time overhead.
* `Cslib.Kolmogorov.DescriptionMethod.exists_simulation_of_produces`: an output-preserving
  compiler is a simulation for some time overhead.
* `Cslib.Kolmogorov.DescriptionMethod.IsAdditivelyOptimal.invariance`: two additively optimal
  methods of a class have complexities within an additive constant of each other.

## References

* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Kolmogorov.DescriptionMethod

variable {α : Type*}

/-- A *simulation* of the description method `M` by the description method `N`, with program
overhead `c` and time overhead `τ`: a compiler from `M`-programs to `N`-programs that adds at most
`c` bits, such that a program halting with output `x` within `t` steps compiles to a program halting
with output `x` within `τ |p| t` steps. -/
structure Simulation (M N : DescriptionMethod α) (c : ℕ) (τ : ℕ → ℕ → ℕ) where
  /-- The compiler from `M`-programs to `N`-programs. -/
  compile : List Bool → List Bool
  /-- Compiling adds at most `c` bits. -/
  length_compile_le (p : List Bool) : (compile p).length ≤ p.length + c
  /-- A compiled program outputs what the original one does, within the time overhead. -/
  mem_runFor_compile {p : List Bool} {t : ℕ} {x : α} :
    x ∈ (M.run p).runFor t → x ∈ (N.run (compile p)).runFor (τ p.length t)

namespace Simulation

variable {M N P : DescriptionMethod α} {c d : ℕ} {τ σ : ℕ → ℕ → ℕ}

/-- Every description method simulates itself. -/
def refl (M : DescriptionMethod α) : Simulation M M 0 fun _ t => t where
  compile := id
  length_compile_le _ := le_rfl
  mem_runFor_compile h := h

/-- A simulation with larger overheads. -/
def mono (S : Simulation M N c τ) {c' : ℕ} {τ' : ℕ → ℕ → ℕ} (hc : c ≤ c')
    (hτ : ∀ n t, τ n t ≤ τ' n t) : Simulation M N c' τ' where
  compile := S.compile
  length_compile_le p := (S.length_compile_le p).trans (Nat.add_le_add_left hc _)
  mem_runFor_compile h := Computation.mem_runFor_of_le (hτ _ _) (S.mem_runFor_compile h)

/-- Simulations compose, provided the second time overhead is monotone in the program length. -/
def trans (S : Simulation M N c τ) (T : Simulation N P d σ) (hσ : ∀ t, Monotone (σ · t)) :
    Simulation M P (c + d) fun n t => σ (n + c) (τ n t) where
  compile p := T.compile (S.compile p)
  length_compile_le p := (T.length_compile_le _).trans <| by
    have := S.length_compile_le p
    omega
  mem_runFor_compile h := Computation.mem_runFor_of_le (hσ _ (S.length_compile_le _))
    (T.mem_runFor_compile (S.mem_runFor_compile h))

/-- Mapping a function over the outputs of a simulation. -/
def map {β : Type*} (f : α → β) (S : Simulation M N c τ) :
    Simulation (M.map f) (N.map f) c τ where
  compile := S.compile
  length_compile_le := S.length_compile_le
  mem_runFor_compile h := by
    obtain ⟨x, hx, rfl⟩ := mem_map_runFor_iff.mp h
    exact mem_map_runFor_iff.mpr ⟨x, S.mem_runFor_compile hx, rfl⟩

theorem produces_compile (S : Simulation M N c τ) {p : List Bool} {x : α} (h : M.Produces p x) :
    N.Produces (S.compile p) x :=
  let ⟨_, ht⟩ := produces_iff_exists_mem_runFor.mp h
  .of_mem_runFor (S.mem_runFor_compile ht)

/-- **Invariance.** A method that simulates `M` with program overhead `c` is at most `c` worse
than `M`. -/
theorem ecomplexity_le (S : Simulation M N c τ) (x : α) :
    N.ecomplexity x ≤ M.ecomplexity x + c := by
  by_cases h : M.ecomplexity x = ⊤
  · simp [h]
  obtain ⟨p, hp, hlen⟩ := exists_length_eq_ecomplexity h
  rw [← hlen]
  exact (ecomplexity_le_length (S.produces_compile hp)).trans (mod_cast S.length_compile_le p)

/-- **Time-bounded invariance.** If `M` describes `x` with at most `k` bits within `t` steps, then
`N` describes `x` with at most `k + c` bits within `τ k t` steps, for a time overhead `τ` monotone
in the program length. -/
theorem etimeBoundedComplexity_le_of_le (S : Simulation M N c τ) {t k : ℕ} {x : α}
    (hτ : Monotone (τ · t)) (h : M.etimeBoundedComplexity t x ≤ k) :
    N.etimeBoundedComplexity (τ k t) x ≤ (k + c : ℕ) := by
  obtain ⟨p, hp, hpx⟩ := etimeBoundedComplexity_le_natCast_iff.mp h
  exact etimeBoundedComplexity_le_natCast_iff.mpr
    ⟨S.compile p, (S.length_compile_le p).trans (Nat.add_le_add_right hp c),
      Computation.mem_runFor_of_le (hτ hp) (S.mem_runFor_compile hpx)⟩

/-- **Time-bounded invariance** for a time overhead `σ` that does not depend on the program:
`C_N^{σ t}(x) ≤ C_M^t(x) + c`. -/
theorem etimeBoundedComplexity_le {σ : ℕ → ℕ} (S : Simulation M N c fun _ t => σ t) (t : ℕ)
    (x : α) : N.etimeBoundedComplexity (σ t) x ≤ M.etimeBoundedComplexity t x + c := by
  by_cases h : M.etimeBoundedComplexity t x = ⊤
  · simp [h]
  obtain ⟨p, hp, hlen⟩ := exists_length_eq_etimeBoundedComplexity h
  rw [← hlen]
  exact (etimeBoundedComplexity_le_length (S.mem_runFor_compile hp)).trans
    (mod_cast S.length_compile_le p)

/-- **Time-bounded invariance under a polynomial time overhead.** If the compiled programs run in
time at most `a (|p| + t + 1) ^ e`, a description of `x` by `M` with at most `k` bits within `t`
steps gives one by `N` with at most `k + c` bits within `a (k + t + 1) ^ e` steps. -/
theorem etimeBoundedComplexity_le_of_polynomial (S : Simulation M N c τ) {a e : ℕ}
    (hτ : ∀ n t, τ n t ≤ a * (n + t + 1) ^ e) {t k : ℕ} {x : α}
    (h : M.etimeBoundedComplexity t x ≤ k) :
    N.etimeBoundedComplexity (a * (k + t + 1) ^ e) x ≤ (k + c : ℕ) :=
  (S.mono le_rfl hτ).etimeBoundedComplexity_le_of_le (τ := fun n t => a * (n + t + 1) ^ e)
    (fun _ _ hn => Nat.mul_le_mul_left a (Nat.pow_le_pow_left (by omega) e)) h

end Simulation

/-- A compiler that preserves outputs and adds at most `c` bits is a simulation for some time
overhead: there are finitely many programs of each length, so the halting times of the compiled
programs of a given length are bounded. The time overhead is not explicit, so this is useful for
plain complexity only. -/
theorem exists_simulation_of_produces {M N : DescriptionMethod α} {c : ℕ}
    (compile : List Bool → List Bool) (hlen : ∀ p, (compile p).length ≤ p.length + c)
    (h : ∀ {p x}, M.Produces p x → N.Produces (compile p) x) :
    ∃ τ : ℕ → ℕ → ℕ, Nonempty (Simulation M N c τ) := by
  classical
  let T (p : List Bool) : ℕ :=
    if hp : (N.run (compile p)).Terminates then (N.run (compile p)).length else 0
  refine ⟨fun n _ => (List.finite_length_eq Bool n).toFinset.sup T,
    ⟨{ compile, length_compile_le := hlen, mem_runFor_compile := fun {p t x} hx => ?_ }⟩⟩
  have hN : x ∈ N.run (compile p) := h (.of_mem_runFor hx)
  have hT : (N.run (compile p)).Terminates := Computation.terminates_of_mem hN
  refine Computation.mem_runFor_of_le ?_ (Computation.results_of_terminates' _ hN).mem_runFor
  calc (N.run (compile p)).length = T p := (dite_eq_left hT).symm
    _ ≤ _ := Finset.le_sup ((List.finite_length_eq Bool _).mem_toFinset.mpr rfl)

/-! ### Additive optimality -/

/-- The description method `U` is *additively optimal* for the class `𝓜` of description methods
[Li and Vitányi, Section 2.1][LiVitanyi2019]: `U` belongs to the class, and for every method `M`
of the class, `U` is at most a constant worse than `M`. -/
structure IsAdditivelyOptimal (U : DescriptionMethod α) (𝓜 : Set (DescriptionMethod α)) :
    Prop where
  /-- The optimal method belongs to the class. -/
  mem : U ∈ 𝓜
  /-- The optimal method is at most a constant worse than every method of the class. -/
  exists_ecomplexity_le : ∀ M ∈ 𝓜, ∃ c : ℕ, ∀ x, U.ecomplexity x ≤ M.ecomplexity x + c

/-- A method of a class that simulates every method of the class, each with a constant program
overhead, is additively optimal for the class. -/
theorem isAdditivelyOptimal_of_simulation {U : DescriptionMethod α}
    {𝓜 : Set (DescriptionMethod α)} (hU : U ∈ 𝓜)
    (h : ∀ M ∈ 𝓜, ∃ (c : ℕ) (τ : ℕ → ℕ → ℕ), Nonempty (Simulation M U c τ)) :
    U.IsAdditivelyOptimal 𝓜 where
  mem := hU
  exists_ecomplexity_le M hM :=
    let ⟨c, _, ⟨S⟩⟩ := h M hM
    ⟨c, S.ecomplexity_le⟩

/-- **Invariance theorem** [Li and Vitányi, Section 2.1][LiVitanyi2019]. Two additively optimal
methods of a class have complexities within an additive constant of each other. -/
theorem IsAdditivelyOptimal.invariance {U V : DescriptionMethod α}
    {𝓜 : Set (DescriptionMethod α)} (hU : U.IsAdditivelyOptimal 𝓜) (hV : V.IsAdditivelyOptimal 𝓜) :
    ∃ c : ℕ, ∀ x,
      U.ecomplexity x ≤ V.ecomplexity x + c ∧ V.ecomplexity x ≤ U.ecomplexity x + c := by
  obtain ⟨c, hc⟩ := hU.exists_ecomplexity_le V hV.mem
  obtain ⟨d, hd⟩ := hV.exists_ecomplexity_le U hU.mem
  refine ⟨max c d, fun x => ⟨(hc x).trans ?_, (hd x).trans ?_⟩⟩ <;>
    exact add_le_add_right (mod_cast (by omega)) _

end Cslib.Kolmogorov.DescriptionMethod
