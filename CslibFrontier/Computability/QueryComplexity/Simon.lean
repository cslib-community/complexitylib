/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Randomized
public import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Computability.DecisionTree.Composition

/-!
# Simon's problem: the classical randomized lower bound

**Simon's problem** [Simon][Simon1997], in the decision form of [de Wolf, §3.1, §3.3.2][deWolf2019]:
the input is a function `f : {0,1}^n → {0,1}^n` with the promise that for some `s ∈ {0,1}^n`,
`f(a) = f(b)` exactly when `b ∈ {a, a ⊕ s}` (`Cslib.QueryComplexity.SimonPromise f s`); the task is
to decide whether `s ≠ 0`. With `s = 0` the promise says that `f` is injective
(`Cslib.QueryComplexity.simonPromise_zero_iff`), and the hidden string is unique
(`Cslib.QueryComplexity.SimonPromise.eq`).

**The model.** We work with bit queries: the input is the truth table `X : Fin N → Bool` of the
`N = n · 2^n` output bits of `f`, with the positions identified with the pairs `(a, j)` (input `a`,
output bit `j`) by an equivalence `E : Fin N ≃ ({0,1}^n) × Fin n`, and
`Cslib.QueryComplexity.simonFun E X` is the function with `f(a)_j = X(E⁻¹(a, j))` (de Wolf §3.1
views the problem in the same way, as a function of `n 2^n` binary variables). The matching quantum
upper bound, in the same bit-query model, is in
`CslibFrontier/Computability/QueryComplexity/Quantum/Simon.lean`. Both sides count bit queries, so
the comparison is like for like. Simulating a value query `f(a)` by `n` bit queries transfers the
lower bound below to value queries only up to that factor (`q_v ≥ 2^{n/2} / n`); the coupling
argument, which uses only that `q` queries touch at most `q` inputs `a`, would give `2^n ≤ q_v²`
directly, but that is not formalized here.

**The lower bound.** A randomized decision tree that decides whether `s ≠ 0` with error `ε` on every
promise input has depth `q` with `2 (2^n - 1) (1 - 2ε) ≤ (q² - q)(1 - ε)`
(`Cslib.QueryComplexity.simon_randomized_lower_bound`); at `ε = 1/3` this gives `2^n ≤ q²`
(`Cslib.QueryComplexity.simon_two_pow_le_depth_sq`), so `q ≥ 2^{n/2}`. In terms of the input
length `N = n 2^n` this is `q ≥ (N / n)^{1/2} = N^{1/2 - o(1)}`.

**Search versions.** The search problem of [de Wolf, §3.1][deWolf2019] promises `s ≠ 0` and asks
for `s`. A randomized decision tree that finds `s` with error `1/3` on every promise input with
`s ≠ 0`, with no requirement when `s = 0`, has depth `q` with `2^n ≤ (q + 2n)²`
(`Cslib.QueryComplexity.simon_search_ne_zero_two_pow_le_sq`): appending to every leaf `s'` the `2n`
bit queries of `f(0)` and `f(s')` and answering whether `s' ≠ 0` and `f(0) = f(s')` decides Simon's
problem with no larger error, since it answers `false` on every injective input. The variant that
also requires the output `0` on injective inputs (`s = 0`) has the cleaner bound `2^n ≤ q²`
(`Cslib.QueryComplexity.simon_search_two_pow_le_depth_sq`), by answering whether the output is
nonzero; as a requirement on more inputs, that is a weaker lower bound.

The proof is the birthday argument of de Wolf §3.3.2, arranged as a coupling. The hard inputs are
`f = π ∘ rep_s` for a permutation `π` of `{0,1}^n` and `rep_s(a)` the representative of the pair
`{a, a ⊕ s}` (`Cslib.QueryComplexity.simonHard`); for `s = 0` these are the injective inputs. Fix a
deterministic tree `t` of depth at most `q` and a nonzero `s`. If the set `A` of inputs `a` that `t`
queries on `π ∘ rep_s` contains no pair `{a, a ⊕ s}`, then the involution that swaps `a` and `a ⊕ s`
exactly when `A` meets `{a, a ⊕ s}` in an element other than the representative turns `π` into a
permutation `ρ` with `π ∘ rep_s = ρ` on `A`; so `t` behaves identically on both inputs, and this is
a bijection. Since `|A| ≤ q`, at most `(q² - q)/2` nonzero strings `s` have a pair in `A`. Summing
over `s` and `π`, a tree that answers `false` on `c₀` injective hard inputs answers `false`
(wrongly) on at least `(2^n - 1 - (q² - q)/2) c₀` hard inputs with nonzero hidden strings.
Averaging over the trees of the randomized tree, the answer `false` has probability at least
`1 - ε` on each injective input and at most `ε` on each input with a nonzero hidden string, which
gives the inequality.

## Main definitions

* `Cslib.QueryComplexity.simonFun`: the function `{0,1}^n → {0,1}^n` with a given truth table.
* `Cslib.QueryComplexity.SimonPromise`: Simon's promise with hidden string `s`.
* `Cslib.QueryComplexity.simonInput`: the truth table of a function.
* `Cslib.QueryComplexity.simonHard`: the hard inputs `π ∘ rep_s`.

## Main results

* `Cslib.QueryComplexity.simonPromise_zero_iff`: the promise with `s = 0` is injectivity.
* `Cslib.QueryComplexity.SimonPromise.eq`: the hidden string is unique.
* `Cslib.QueryComplexity.simonPromise_simonHard`: the hard inputs satisfy the promise.
* `Cslib.QueryComplexity.simon_randomized_lower_bound`:
  `2 (2^n - 1) (1 - 2ε) ≤ (q² - q)(1 - ε)`.
* `Cslib.QueryComplexity.simon_randomized_lower_bound_third`: `2^n - 1 ≤ q² - q` at `ε = 1/3`.
* `Cslib.QueryComplexity.simon_two_pow_le_depth_sq`: `2^n ≤ q²` at `ε = 1/3`, for `n ≥ 1`.
* `Cslib.QueryComplexity.simon_two_pow_le_randomizedComplexity_sq`: `2^n ≤ R_{1/3}(F)²` for every
  total function `F` that answers Simon's problem on the promise inputs.
* `Cslib.QueryComplexity.simon_search_ne_zero_two_pow_le_sq`: `2^n ≤ (q + 2n)²` for the search
  problem with `s ≠ 0` at `ε = 1/3`, for `n ≥ 1`.
* `Cslib.QueryComplexity.simon_search_two_pow_le_depth_sq`: `2^n ≤ q²` at `ε = 1/3` for the search
  variant that also requires the output `0` when `s = 0`, for `n ≥ 1`.

## References

* [D. R. Simon, *On the Power of Quantum Computation*][Simon1997]
* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019], §3.1 and §3.3.2
-/

public section

namespace Cslib

open Finset

namespace QueryComplexity

variable {N n : ℕ}

/-- The Simon function whose truth table is `X`: `f(a)_j = X(E⁻¹(a, j))`. -/
@[expose] def simonFun (E : Fin N ≃ (Fin n → Bool) × Fin n) (X : Fin N → Bool)
    (a : Fin n → Bool) : Fin n → Bool := fun j => X (E.symm (a, j))

/-- Simon's promise with hidden string `s`: `f a = f b` exactly when `b ∈ {a, a + s}`, where `+`
is bitwise exclusive or. -/
@[expose] def SimonPromise (f : (Fin n → Bool) → Fin n → Bool) (s : Fin n → Bool) : Prop :=
  ∀ a b, f a = f b ↔ b = a ∨ b = a + s

/-- The truth table of `g`: position `i` holds the bit `g(a)_j` for `(a, j) = E i`. -/
def simonInput (E : Fin N ≃ (Fin n → Bool) × Fin n)
    (g : (Fin n → Bool) → Fin n → Bool) : Fin N → Bool := fun i => g (E i).1 (E i).2

@[simp] theorem simonFun_simonInput (E : Fin N ≃ (Fin n → Bool) × Fin n)
    (g : (Fin n → Bool) → Fin n → Bool) : simonFun E (simonInput E g) = g := by
  funext a j
  simp [simonFun, simonInput]

/-- Simon's promise with hidden string `0` says that `f` is injective. -/
theorem simonPromise_zero_iff (f : (Fin n → Bool) → Fin n → Bool) :
    SimonPromise f 0 ↔ Function.Injective f := by
  simp only [SimonPromise, add_zero, or_self]
  exact ⟨fun h a b hab => ((h a b).mp hab).symm, fun h a b => ⟨fun hab => (h hab).symm,
    fun hab => hab ▸ rfl⟩⟩

/-- The hidden string of Simon's promise is unique. -/
theorem SimonPromise.eq {f : (Fin n → Bool) → Fin n → Bool} {s s' : Fin n → Bool}
    (h : SimonPromise f s) (h' : SimonPromise f s') : s = s' := by
  have key : ∀ {s s' : Fin n → Bool}, SimonPromise f s → SimonPromise f s' → s' = 0 → s = 0 := by
    intro s s' h h' hs'
    subst hs'
    rcases (h' 0 s).mp ((h 0 s).mpr (Or.inr (zero_add s).symm)) with hs | hs
    · exact hs
    · simpa using hs
  by_cases hs : s = 0
  · exact hs.trans (key h' h hs).symm
  by_cases hs' : s' = 0
  · exact absurd (key h h' hs') hs
  rcases (h' 0 s).mp ((h 0 s).mpr (Or.inr (zero_add s).symm)) with h0 | h0
  · exact absurd h0 hs
  · simpa using h0

/-- The representative of `{a, a + s}`: the one that comes first in a fixed order. -/
private noncomputable def simonRep (s a : Fin n → Bool) : Fin n → Bool :=
  if Fintype.equivFin _ a ≤ Fintype.equivFin _ (a + s) then a else a + s

private theorem simonRep_add (s a : Fin n → Bool) : simonRep s (a + s) = simonRep s a := by
  unfold simonRep
  rw [BitString.add_cancel_right]
  split_ifs with h1 h2 h2
  · exact (Fintype.equivFin _).injective (le_antisymm h1 h2)
  · rfl
  · rfl
  · exact absurd (le_of_lt (not_le.mp h2)) h1

private theorem simonRep_mem (s a : Fin n → Bool) : simonRep s a = a ∨ simonRep s a = a + s := by
  unfold simonRep
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

@[simp] private theorem simonRep_zero : simonRep (0 : Fin n → Bool) = id := by
  funext a
  simp [simonRep]

private theorem simonRep_eq_iff (s a b : Fin n → Bool) :
    simonRep s a = simonRep s b ↔ b = a ∨ b = a + s := by
  constructor
  · intro h
    rcases simonRep_mem s a with ha | ha <;> rcases simonRep_mem s b with hb | hb <;>
      rw [ha, hb] at h
    · exact Or.inl h.symm
    · rw [h, BitString.add_cancel_right]
      exact Or.inr rfl
    · exact Or.inr h.symm
    · exact Or.inl (by rw [← BitString.add_cancel_right a s, h, BitString.add_cancel_right])
  · rintro (rfl | rfl)
    · rfl
    · exact (simonRep_add s a).symm

private theorem simonPromise_comp_simonRep (π : Equiv.Perm (Fin n → Bool)) (s : Fin n → Bool) :
    SimonPromise (fun a => π (simonRep s a)) s := by
  intro a b
  simp only [EmbeddingLike.apply_eq_iff_eq]
  exact simonRep_eq_iff s a b

/-- The hard input with permutation `π` and hidden string `s`: `f = π ∘ rep_s`. -/
noncomputable def simonHard (E : Fin N ≃ (Fin n → Bool) × Fin n) (π : Equiv.Perm (Fin n → Bool))
    (s : Fin n → Bool) : Fin N → Bool :=
  simonInput E fun a => π (simonRep s a)

theorem simonPromise_simonHard (E : Fin N ≃ (Fin n → Bool) × Fin n)
    (π : Equiv.Perm (Fin n → Bool)) (s : Fin n → Bool) :
    SimonPromise (simonFun E (simonHard E π s)) s := by
  rw [simonHard, simonFun_simonInput]
  exact simonPromise_comp_simonRep π s

/-- The inputs `a` of `f` some bit of whose value `f(a)` the tree queries on `X`. -/
private def queriedInputs (E : Fin N ≃ (Fin n → Bool) × Fin n) (t : DecisionTree (Fin N) Bool)
    (X : Fin N → Bool) : Finset (Fin n → Bool) :=
  (t.queries X).image fun i => (E i).1

private theorem card_queriedInputs_le (E : Fin N ≃ (Fin n → Bool) × Fin n)
    (t : DecisionTree (Fin N) Bool) (X : Fin N → Bool) : #(queriedInputs E t X) ≤ t.depth :=
  card_image_le.trans (t.card_queries_le_depth X)

private theorem simonInput_agree (E : Fin N ≃ (Fin n → Bool) × Fin n)
    (t : DecisionTree (Fin N) Bool) {g g' : (Fin n → Bool) → Fin n → Bool}
    (h : ∀ a ∈ queriedInputs E t (simonInput E g), g' a = g a) :
    ∀ i ∈ t.queries (simonInput E g), simonInput E g' i = simonInput E g i := fun i hi => by
  simp only [simonInput]
  rw [h _ (mem_image_of_mem _ hi)]

/-- `A` contains no pair `{a, a + s}`. -/
private abbrev PairFree (s : Fin n → Bool) (A : Finset (Fin n → Bool)) : Prop :=
  ∀ a ∈ A, a + s ∉ A

open Classical in
/-- An involution of the inputs that agrees with `rep_s` on `A` when `A` is `s`-free. -/
private noncomputable def simonFixFun (s : Fin n → Bool) (A : Finset (Fin n → Bool))
    (x : Fin n → Bool) : Fin n → Bool :=
  if (x ∈ A ∧ simonRep s x ≠ x) ∨ (x + s ∈ A ∧ simonRep s (x + s) ≠ x + s) then x + s else x

private theorem simonFixFun_involutive (s : Fin n → Bool) (A : Finset (Fin n → Bool)) :
    Function.Involutive (simonFixFun s A) := by
  classical
  intro x
  by_cases h : (x ∈ A ∧ simonRep s x ≠ x) ∨ (x + s ∈ A ∧ simonRep s (x + s) ≠ x + s)
  · have h' : (x + s ∈ A ∧ simonRep s (x + s) ≠ x + s) ∨
        (x + s + s ∈ A ∧ simonRep s (x + s + s) ≠ x + s + s) := by
      rw [BitString.add_cancel_right]
      tauto
    have h'' : (x + s ∈ A ∧ simonRep s (x + s) ≠ x + s) ∨ (x ∈ A ∧ simonRep s x ≠ x) := h.symm
    simp only [simonFixFun, h, h'', ite_true, BitString.add_cancel_right]
  · simp only [simonFixFun, h, ite_false]

/-- The permutation `simonFixFun s A`. -/
private noncomputable def simonFix (s : Fin n → Bool) (A : Finset (Fin n → Bool)) :
    Equiv.Perm (Fin n → Bool) :=
  (simonFixFun_involutive s A).toPerm

private theorem simonFix_apply_of_mem {s : Fin n → Bool} {A : Finset (Fin n → Bool)}
    (hA : PairFree s A) {a : Fin n → Bool} (ha : a ∈ A) : simonFix s A a = simonRep s a := by
  classical
  change simonFixFun s A a = _
  unfold simonFixFun
  rcases simonRep_mem s a with h | h
  · rw [h]
    have hn : ¬((a ∈ A ∧ a ≠ a) ∨ (a + s ∈ A ∧ simonRep s (a + s) ≠ a + s)) := by
      rintro (⟨_, hne⟩ | ⟨hmem, _⟩)
      · exact hne rfl
      · exact hA a ha hmem
    exact ite_eq_right hn
  · rw [h]
    have hy : (a ∈ A ∧ a + s ≠ a) ∨ (a + s ∈ A ∧ simonRep s (a + s) ≠ a + s) := by
      left
      refine ⟨ha, fun h' => ?_⟩
      have : s = 0 := add_left_cancel (h'.trans (add_zero a).symm)
      exact hA a ha (by rw [this, add_zero]; exact ha)
    exact ite_eq_left hy

private theorem simonFix_simonFix (s : Fin n → Bool) (A : Finset (Fin n → Bool)) :
    simonFix s A * simonFix s A = 1 :=
  Equiv.ext fun x => simonFixFun_involutive s A x

variable (E : Fin N ≃ (Fin n → Bool) × Fin n) (t : DecisionTree (Fin N) Bool)

/-- **The coupling**: on an `s`-free query set, the hard input `π ∘ rep_s` looks like the
injective input `π ∘ κ`. -/
private theorem simonHard_fix {π : Equiv.Perm (Fin n → Bool)} {s : Fin n → Bool}
    (hA : PairFree s (queriedInputs E t (simonHard E π s))) :
    t.eval (simonHard E (π * simonFix s (queriedInputs E t (simonHard E π s))) 0) =
      t.eval (simonHard E π s) ∧
    queriedInputs E t (simonHard E (π * simonFix s (queriedInputs E t (simonHard E π s))) 0) =
      queriedInputs E t (simonHard E π s) := by
  have hag := simonInput_agree E t (g := fun a => π (simonRep s a))
    (g' := fun a => (π * simonFix s (queriedInputs E t (simonHard E π s))) (simonRep 0 a))
    fun a ha => by
      simp only [simonRep_zero, id, Equiv.Perm.mul_apply]
      rw [simonFix_apply_of_mem hA ha]
  exact ⟨t.eval_eq_of_forall_mem_queries hag,
    congrArg (image fun i => (E i).1) (t.queries_eq_of_forall_mem_queries hag)⟩

/-- The inverse coupling. -/
private theorem simonHard_unfix {ρ : Equiv.Perm (Fin n → Bool)} {s : Fin n → Bool}
    (hA : PairFree s (queriedInputs E t (simonHard E ρ 0))) :
    t.eval (simonHard E (ρ * simonFix s (queriedInputs E t (simonHard E ρ 0))) s) =
      t.eval (simonHard E ρ 0) ∧
    queriedInputs E t (simonHard E (ρ * simonFix s (queriedInputs E t (simonHard E ρ 0))) s) =
      queriedInputs E t (simonHard E ρ 0) := by
  have hag := simonInput_agree E t (g := fun a => ρ (simonRep 0 a))
    (g' := fun a => (ρ * simonFix s (queriedInputs E t (simonHard E ρ 0))) (simonRep s a))
    fun a ha => by
      have ha' : simonFix s (queriedInputs E t (simonHard E ρ 0)) (simonRep s a) = a := by
        rw [← simonFix_apply_of_mem hA ha]
        exact simonFixFun_involutive s _ a
      simp only [simonRep_zero, id, Equiv.Perm.mul_apply, ha']
  exact ⟨t.eval_eq_of_forall_mem_queries hag,
    congrArg (image fun i => (E i).1) (t.queries_eq_of_forall_mem_queries hag)⟩

/-- **The coupling count**: as many permutations give output `b` with an `s`-free query set on the
hard inputs with hidden string `s` as on the injective inputs. -/
private theorem card_simonHard_eq (s : Fin n → Bool) (b : Bool) :
    #{π : Equiv.Perm (Fin n → Bool) | t.eval (simonHard E π s) = b ∧
      PairFree s (queriedInputs E t (simonHard E π s))} =
    #{ρ : Equiv.Perm (Fin n → Bool) | t.eval (simonHard E ρ 0) = b ∧
      PairFree s (queriedInputs E t (simonHard E ρ 0))} := by
  refine card_nbij' (fun π => π * simonFix s (queriedInputs E t (simonHard E π s)))
    (fun ρ => ρ * simonFix s (queriedInputs E t (simonHard E ρ 0))) ?_ ?_ ?_ ?_
  · intro π hπ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hπ ⊢
    obtain ⟨h1, h2⟩ := simonHard_fix E t hπ.2
    rw [h1, h2]
    exact hπ
  · intro ρ hρ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hρ ⊢
    obtain ⟨h1, h2⟩ := simonHard_unfix E t hρ.2
    rw [h1, h2]
    exact hρ
  · intro π hπ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hπ
    simp only
    rw [(simonHard_fix E t hπ.2).2, mul_assoc, simonFix_simonFix, mul_one]
  · intro ρ hρ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hρ
    simp only
    rw [(simonHard_unfix E t hρ.2).2, mul_assoc, simonFix_simonFix, mul_one]

/-- **Few hidden strings collide**: at most `(|A|² - |A|) / 2` nonzero `s` have `a, a + s ∈ A`. -/
private theorem two_mul_card_not_pairFree_le (A : Finset (Fin n → Bool)) :
    2 * #{s ∈ univ.erase (0 : Fin n → Bool) | ¬PairFree s A} ≤ #A * #A - #A := by
  classical
  rw [← offDiag_card]
  rw [card_eq_sum_card_fiberwise (f := fun p : (Fin n → Bool) × (Fin n → Bool) => p.1 + p.2)
    (t := univ) fun _ _ => mem_univ _]
  calc 2 * #{s ∈ univ.erase (0 : Fin n → Bool) | ¬PairFree s A}
      = ∑ s ∈ {s ∈ univ.erase (0 : Fin n → Bool) | ¬PairFree s A}, 2 := by
        rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ s ∈ {s ∈ univ.erase (0 : Fin n → Bool) | ¬PairFree s A},
        #{p ∈ A.offDiag | p.1 + p.2 = s} := by
        refine sum_le_sum fun s hs => ?_
        simp only [mem_filter, mem_erase, mem_univ, and_true, PairFree, not_forall, not_not] at hs
        obtain ⟨hs0, a, ha, has⟩ := hs
        have hne : a ≠ a + s := fun h => hs0 (add_left_cancel (h.symm.trans (add_zero a).symm))
        calc 2 = #{(a, a + s), (a + s, a)} := by
              rw [card_pair]
              intro h
              exact hne (Prod.ext_iff.mp h).1
          _ ≤ _ := by
              refine card_le_card fun p hp => ?_
              simp only [mem_insert, mem_singleton] at hp
              rcases hp with rfl | rfl
              · simp only [mem_filter, mem_offDiag]
                exact ⟨⟨ha, has, hne⟩, by rw [← add_assoc, BitString.add_self, zero_add]⟩
              · simp only [mem_filter, mem_offDiag]
                exact ⟨⟨has, ha, hne.symm⟩, by rw [add_comm a s, add_assoc, BitString.add_self,
                  add_zero]⟩
    _ ≤ ∑ s, #{p ∈ A.offDiag | p.1 + p.2 = s} :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.zero_le _

private theorem sum_card_filter_comm {α γ : Type*} (S : Finset α) (T : Finset γ) (P : γ → Prop)
    (Q : α → γ → Prop) [DecidablePred P] [∀ s ρ, Decidable (Q s ρ)] :
    ∑ s ∈ S, #{ρ ∈ T | P ρ ∧ Q s ρ} = ∑ ρ ∈ T with P ρ, #{s ∈ S | Q s ρ} := by
  simp only [card_filter]
  rw [sum_comm, sum_filter]
  refine sum_congr rfl fun ρ _ => ?_
  by_cases hP : P ρ <;> simp [hP]

/-- **The per-tree inequality**: a tree of depth at most `q` that answers `false` on `c₀` injective
hard inputs answers `false` (wrongly) on at least `(2^n - 1 - (q² - q)/2) c₀` hard inputs with
nonzero hidden strings. -/
private theorem card_simonHard_le {q : ℕ} (ht : t.depth ≤ q) :
    2 * (2 ^ n - 1) * #{ρ : Equiv.Perm (Fin n → Bool) | t.eval (simonHard E ρ 0) = false} ≤
      2 * ∑ s ∈ univ.erase (0 : Fin n → Bool),
          #{π : Equiv.Perm (Fin n → Bool) | t.eval (simonHard E π s) = false} +
        (q * q - q) * #{ρ : Equiv.Perm (Fin n → Bool) | t.eval (simonHard E ρ 0) = false} := by
  classical
  have h1 : ∑ s ∈ univ.erase (0 : Fin n → Bool),
      #{ρ : Equiv.Perm (Fin n → Bool) | t.eval (simonHard E ρ 0) = false ∧
        PairFree s (queriedInputs E t (simonHard E ρ 0))} ≤
      ∑ s ∈ univ.erase (0 : Fin n → Bool),
        #{π : Equiv.Perm (Fin n → Bool) | t.eval (simonHard E π s) = false} := by
    refine sum_le_sum fun s _ => ?_
    rw [← card_simonHard_eq E t s false]
    exact card_le_card fun π hπ => by
      simp only [mem_filter, mem_univ, true_and] at hπ ⊢
      exact hπ.1
  have hswap : ∑ s ∈ univ.erase (0 : Fin n → Bool),
      #{ρ : Equiv.Perm (Fin n → Bool) | t.eval (simonHard E ρ 0) = false ∧
        PairFree s (queriedInputs E t (simonHard E ρ 0))} =
      ∑ ρ ∈ (univ : Finset (Equiv.Perm (Fin n → Bool))) with t.eval (simonHard E ρ 0) = false,
        #{s ∈ univ.erase (0 : Fin n → Bool) | PairFree s (queriedInputs E t (simonHard E ρ 0))} :=
    sum_card_filter_comm _ _ (fun ρ => t.eval (simonHard E ρ 0) = false)
      (fun s ρ => PairFree s (queriedInputs E t (simonHard E ρ 0)))
  have h2 : ∀ ρ : Equiv.Perm (Fin n → Bool),
      2 * (2 ^ n - 1) ≤ 2 * #{s ∈ univ.erase (0 : Fin n → Bool) |
        PairFree s (queriedInputs E t (simonHard E ρ 0))} + (q * q - q) := by
    intro ρ
    have hsplit := card_filter_add_card_filter_not (s := univ.erase (0 : Fin n → Bool))
      (fun s => PairFree s (queriedInputs E t (simonHard E ρ 0)))
    have hbad := two_mul_card_not_pairFree_le (queriedInputs E t (simonHard E ρ 0))
    have hA : #(queriedInputs E t (simonHard E ρ 0)) ≤ q := (card_queriedInputs_le E t _).trans ht
    have hmono : #(queriedInputs E t (simonHard E ρ 0)) * #(queriedInputs E t (simonHard E ρ 0)) -
        #(queriedInputs E t (simonHard E ρ 0)) ≤ q * q - q := by
      rw [← Nat.mul_sub_one, ← Nat.mul_sub_one]
      exact Nat.mul_le_mul hA (Nat.sub_le_sub_right hA 1)
    have hcard : #(univ.erase (0 : Fin n → Bool)) = 2 ^ n - 1 := by
      rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin]
    generalize #(queriedInputs E t (simonHard E ρ 0)) * #(queriedInputs E t (simonHard E ρ 0)) -
      #(queriedInputs E t (simonHard E ρ 0)) = u at hbad hmono
    generalize q * q - q = v at hmono ⊢
    generalize 2 ^ n = w at hcard ⊢
    omega
  calc 2 * (2 ^ n - 1) * #{ρ : Equiv.Perm (Fin n → Bool) | t.eval (simonHard E ρ 0) = false}
      = ∑ ρ ∈ (univ : Finset (Equiv.Perm (Fin n → Bool))) with t.eval (simonHard E ρ 0) = false,
          2 * (2 ^ n - 1) := by
        rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ ρ ∈ (univ : Finset (Equiv.Perm (Fin n → Bool))) with t.eval (simonHard E ρ 0) = false,
          (2 * #{s ∈ univ.erase (0 : Fin n → Bool) |
            PairFree s (queriedInputs E t (simonHard E ρ 0))} + (q * q - q)) :=
        sum_le_sum fun ρ _ => h2 ρ
    _ = 2 * ∑ ρ ∈ (univ : Finset (Equiv.Perm (Fin n → Bool))) with
          t.eval (simonHard E ρ 0) = false,
          #{s ∈ univ.erase (0 : Fin n → Bool) | PairFree s (queriedInputs E t (simonHard E ρ 0))} +
        (q * q - q) * #{ρ : Equiv.Perm (Fin n → Bool) | t.eval (simonHard E ρ 0) = false} := by
        rw [sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul, mul_comm (#_)]
    _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hswap ▸ h1)) _

/-- The number of wrong answers (`false`) of `t` on the hard inputs with nonzero hidden strings. -/
private noncomputable def numFalse1 (t : DecisionTree (Fin N) Bool) : ℕ :=
  ∑ s ∈ univ.erase (0 : Fin n → Bool),
    #{π : Equiv.Perm (Fin n → Bool) | t.eval (simonHard E π s) = false}

/-- The number of `false` answers of `t` on the injective hard inputs; these answers are correct. -/
private noncomputable def numFalse0 (t : DecisionTree (Fin N) Bool) : ℕ :=
  #{ρ : Equiv.Perm (Fin n → Bool) | t.eval (simonHard E ρ 0) = false}

/-- **The classical randomized lower bound for Simon's problem**: a randomized decision tree that
decides whether the hidden string is nonzero with error `ε` on every promise input has depth `q`
with `2 (2^n - 1) (1 - 2ε) ≤ (q² - q)(1 - ε)`. -/
theorem simon_randomized_lower_bound (μ : RandomizedDecisionTree (Fin N) Bool)
    (F : (Fin N → Bool) → Bool) {ε : ℝ}
    (hF : ∀ X s, SimonPromise (simonFun E X) s → F X = decide (s ≠ 0))
    (hμ : ∀ X s, SimonPromise (simonFun E X) s → μ.errorProb F X ≤ ε) (hε : ε ≤ 1) :
    2 * (2 ^ n - 1) * (1 - 2 * ε) ≤ ((μ.depth * μ.depth - μ.depth : ℕ) : ℝ) * (1 - ε) := by
  classical
  have hM : ((2 ^ n - 1 : ℕ) : ℝ) = 2 ^ n - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    ring
  have hcardR : (#(univ.erase (0 : Fin n → Bool)) : ℝ) = 2 ^ n - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, hM]
  set K : ℝ := (Fintype.card (Equiv.Perm (Fin n → Bool)) : ℝ) with hKdef
  have hK : 0 < K := Nat.cast_pos.mpr Fintype.card_pos
  have hpt : ∀ t ∈ μ.weights.support, 2 * (2 ^ n - 1) * (numFalse0 E t : ℝ) ≤
      2 * (numFalse1 E t : ℝ) + ((μ.depth * μ.depth - μ.depth : ℕ) : ℝ) * (numFalse0 E t : ℝ) := by
    intro t ht
    have h := card_simonHard_le E t (RandomizedDecisionTree.depth_le_depth ht)
    rw [← hM]
    simp only [numFalse0, numFalse1]
    exact_mod_cast h
  have hnumFalse0 : ∀ t : DecisionTree (Fin N) Bool, (numFalse0 E t : ℝ) =
      ∑ ρ : Equiv.Perm (Fin n → Bool), if t.eval (simonHard E ρ 0) = false then 1 else 0 :=
    fun t => by rw [numFalse0, natCast_card_filter]
  have hnumFalse1 : ∀ t : DecisionTree (Fin N) Bool, (numFalse1 E t : ℝ) =
      ∑ s ∈ univ.erase (0 : Fin n → Bool), ∑ π : Equiv.Perm (Fin n → Bool),
        if t.eval (simonHard E π s) = false then 1 else 0 := fun t => by
    rw [numFalse1, Nat.cast_sum]
    exact sum_congr rfl fun s _ => natCast_card_filter _ _
  have hS1 : ∑ t ∈ μ.weights.support, μ.weights t * (numFalse1 E t : ℝ) ≤ (2 ^ n - 1) * K * ε := by
    calc ∑ t ∈ μ.weights.support, μ.weights t * (numFalse1 E t : ℝ)
        = ∑ s ∈ univ.erase (0 : Fin n → Bool), ∑ π : Equiv.Perm (Fin n → Bool),
            μ.errorProb F (simonHard E π s) := by
          simp only [hnumFalse1, mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun s hs => ?_
          rw [sum_comm]
          refine sum_congr rfl fun π _ => ?_
          have hFv : F (simonHard E π s) = true := by
            rw [hF _ s (simonPromise_simonHard E π s)]
            simpa using (mem_erase.mp hs).1
          rw [RandomizedDecisionTree.errorProb_eq_sum, Finsupp.sum, hFv]
          refine sum_congr rfl fun t _ => ?_
          cases t.eval (simonHard E π s) <;> simp
      _ ≤ ∑ s ∈ univ.erase (0 : Fin n → Bool), ∑ π : Equiv.Perm (Fin n → Bool), ε :=
          sum_le_sum fun s _ => sum_le_sum fun π _ => hμ _ _ (simonPromise_simonHard E π s)
      _ = (2 ^ n - 1) * K * ε := by
          rw [sum_const, sum_const, card_univ, nsmul_eq_mul, nsmul_eq_mul, hcardR, hKdef]
          ring
  have hS0 : K * (1 - ε) ≤ ∑ t ∈ μ.weights.support, μ.weights t * (numFalse0 E t : ℝ) := by
    have hw : ∑ t ∈ μ.weights.support, μ.weights t = 1 := μ.total
    have hρ : ∀ ρ, μ.errorProb F (simonHard E ρ 0) = 1 - ∑ t ∈ μ.weights.support,
        μ.weights t * if t.eval (simonHard E ρ 0) = false then 1 else 0 := by
      intro ρ
      have hFv : F (simonHard E ρ 0) = false := by
        rw [hF _ 0 (simonPromise_simonHard E ρ 0)]
        simp
      rw [RandomizedDecisionTree.errorProb_eq_sum, Finsupp.sum, hFv, eq_sub_iff_add_eq,
        ← sum_add_distrib]
      refine (sum_congr rfl fun t _ => ?_).trans hw
      cases t.eval (simonHard E ρ 0) <;> simp
    have hsum : ∑ ρ : Equiv.Perm (Fin n → Bool), μ.errorProb F (simonHard E ρ 0) =
        K - ∑ t ∈ μ.weights.support, μ.weights t * (numFalse0 E t : ℝ) := by
      simp only [hρ, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, hnumFalse0,
        mul_sum]
      rw [sum_comm]
    have hle : ∑ ρ : Equiv.Perm (Fin n → Bool), μ.errorProb F (simonHard E ρ 0) ≤ K * ε := by
      calc _ ≤ ∑ ρ : Equiv.Perm (Fin n → Bool), ε :=
            sum_le_sum fun ρ _ => hμ _ _ (simonPromise_simonHard E ρ 0)
        _ = K * ε := by rw [sum_const, card_univ, nsmul_eq_mul]
    linarith
  have hcomb : 2 * (2 ^ n - 1) * ∑ t ∈ μ.weights.support, μ.weights t * (numFalse0 E t : ℝ) ≤
      2 * ∑ t ∈ μ.weights.support, μ.weights t * (numFalse1 E t : ℝ) +
        ((μ.depth * μ.depth - μ.depth : ℕ) : ℝ) *
          ∑ t ∈ μ.weights.support, μ.weights t * (numFalse0 E t : ℝ) := by
    rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun t ht => ?_
    have := mul_le_mul_of_nonneg_left (hpt t ht) (μ.weights_nonneg t)
    linarith
  have hε0 : 0 ≤ ε :=
    RandomizedDecisionTree.errorProb_nonneg.trans (hμ _ _ (simonPromise_simonHard E 1 0))
  have hQ : (0 : ℝ) ≤ ((μ.depth * μ.depth - μ.depth : ℕ) : ℝ) := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ 2 ^ n - 1 := by
    have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    linarith
  generalize ((μ.depth * μ.depth - μ.depth : ℕ) : ℝ) = Q at hcomb hQ ⊢
  generalize ∑ t ∈ μ.weights.support, μ.weights t * (numFalse0 E t : ℝ) = W0 at hcomb hS0
  generalize ∑ t ∈ μ.weights.support, μ.weights t * (numFalse1 E t : ℝ) = W1 at hcomb hS1
  by_cases hsign : 2 * (2 ^ n - 1) - Q ≤ 0
  · have h1 : 0 ≤ (Q - 2 * (2 ^ n - 1)) * (1 - ε) := mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ (2 ^ n - 1) * ε := mul_nonneg hM0 hε0
    linarith
  · push Not at hsign
    have h3 := mul_le_mul_of_nonneg_left hS0 hsign.le
    have h4 : K * (2 * (2 ^ n - 1) * (1 - 2 * ε) - Q * (1 - ε)) ≤ K * 0 := by
      linarith
    have h5 := le_of_mul_le_mul_left h4 hK
    linarith

/-- **The classical lower bound at error `1/3`**: `2^n - 1 ≤ q² - q`. -/
theorem simon_randomized_lower_bound_third (μ : RandomizedDecisionTree (Fin N) Bool)
    (F : (Fin N → Bool) → Bool)
    (hF : ∀ X s, SimonPromise (simonFun E X) s → F X = decide (s ≠ 0))
    (hμ : ∀ X s, SimonPromise (simonFun E X) s → μ.errorProb F X ≤ 1 / 3) :
    2 ^ n - 1 ≤ μ.depth * μ.depth - μ.depth := by
  have h := simon_randomized_lower_bound E μ F hF hμ (by norm_num)
  have hR : ((2 ^ n - 1 : ℕ) : ℝ) ≤ ((μ.depth * μ.depth - μ.depth : ℕ) : ℝ) := by
    rw [Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    linarith
  exact_mod_cast hR

/-- **Exponential classical lower bound**: for `n ≥ 1`, a randomized decision tree that decides
Simon's problem with error `1/3` has depth `q` with `2^n ≤ q²`, so `q ≥ 2^{n/2}`. -/
theorem simon_two_pow_le_depth_sq (μ : RandomizedDecisionTree (Fin N) Bool)
    (F : (Fin N → Bool) → Bool)
    (hF : ∀ X s, SimonPromise (simonFun E X) s → F X = decide (s ≠ 0))
    (hμ : ∀ X s, SimonPromise (simonFun E X) s → μ.errorProb F X ≤ 1 / 3) (hn : 1 ≤ n) :
    2 ^ n ≤ μ.depth ^ 2 := by
  have h := simon_randomized_lower_bound_third E μ F hF hμ
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rcases Nat.eq_zero_or_pos μ.depth with hd | hd
  · rw [hd] at h
    simp only [mul_zero, Nat.sub_zero, nonpos_iff_eq_zero] at h
    omega
  · rw [sq]
    have hle := Nat.le_mul_self μ.depth
    generalize μ.depth * μ.depth = D at h hle ⊢
    generalize 2 ^ n = P at h h2 ⊢
    omega

/-- **Exponential classical lower bound, as a randomized query complexity**: for `n ≥ 1` and every
total function `F` that answers Simon's problem on the promise inputs, `2^n ≤ R_{1/3}(F)²`. -/
theorem simon_two_pow_le_randomizedComplexity_sq (F : (Fin N → Bool) → Bool)
    (hF : ∀ X s, SimonPromise (simonFun E X) s → F X = decide (s ≠ 0)) (hn : 1 ≤ n) :
    2 ^ n ≤ randomizedComplexity (1 / 3) F ^ 2 := by
  obtain ⟨μ, hμ, hd⟩ :=
    exists_computes_depth_eq_randomizedComplexity (ε := 1 / 3) (by norm_num) F
  rw [← hd]
  exact simon_two_pow_le_depth_sq E μ F hF (fun X _ _ => hμ X) hn

/-- **Exponential classical lower bound for the search variant including `s = 0`**: for `n ≥ 1`,
a randomized decision tree that finds the hidden string with error `1/3` on every promise input,
including the injective inputs, where it must output `0` (as the restriction to the promise inputs
of a total function `S`), has depth `q` with `2^n ≤ q²`. Answering whether its output is nonzero
decides Simon's problem with no further queries and no larger error
(`Cslib.RandomizedDecisionTree.errorProb_mapOutput_le`). This does not cover trees that only find
nonzero hidden strings, as in the search problem of [de Wolf, §3.1][deWolf2019]; for those see
`Cslib.QueryComplexity.simon_search_ne_zero_two_pow_le_sq`. -/
theorem simon_search_two_pow_le_depth_sq (μ : RandomizedDecisionTree (Fin N) (Fin n → Bool))
    (S : (Fin N → Bool) → Fin n → Bool)
    (hS : ∀ X s, SimonPromise (simonFun E X) s → S X = s)
    (hμ : ∀ X s, SimonPromise (simonFun E X) s → μ.errorProb S X ≤ 1 / 3) (hn : 1 ≤ n) :
    2 ^ n ≤ μ.depth ^ 2 := by
  set g : (Fin n → Bool) → Bool := fun s => decide (s ≠ 0) with hg
  have h := simon_two_pow_le_depth_sq E (RandomizedDecisionTree.mapOutput g μ) (g ∘ S)
    (fun X s hX => by rw [Function.comp_apply, hS X s hX])
    (fun X s hX => (RandomizedDecisionTree.errorProb_mapOutput_le g μ S X).trans (hμ X s hX)) hn
  exact h.trans (Nat.pow_le_pow_left (RandomizedDecisionTree.depth_mapOutput_le g μ) 2)

/-- The tree that reads `f(0)` and `f(s')` (`2n` bit queries) and answers whether `s' ≠ 0` and
`f(0) = f(s')`: on a promise input it answers `true` exactly when `s'` is the nonzero hidden
string. -/
private def simonCheck (E : Fin N ≃ (Fin n → Bool) × Fin n) (s' : Fin n → Bool) :
    DecisionTree (Fin N) Bool :=
  DecisionTree.queryAll (fun b => decide (s' ≠ 0 ∧ simonFun E b 0 = simonFun E b s'))
    (List.ofFn (fun j => E.symm (0, j)) ++ List.ofFn (fun j => E.symm (s', j))) fun _ => false

private theorem eval_simonCheck (E : Fin N ≃ (Fin n → Bool) × Fin n) (s' : Fin n → Bool)
    (X : Fin N → Bool) :
    (simonCheck E s').eval X = decide (s' ≠ 0 ∧ simonFun E X 0 = simonFun E X s') := by
  classical
  rw [simonCheck, DecisionTree.eval_queryAll]
  congr 3 <;> funext j <;> simp [simonFun]

private theorem depth_simonCheck_le (E : Fin N ≃ (Fin n → Bool) × Fin n) (s' : Fin n → Bool) :
    (simonCheck E s').depth ≤ 2 * n :=
  (DecisionTree.depth_queryAll_le _ _ _).trans_eq (by simp [two_mul])

/-- **Exponential classical lower bound for the search problem with a nonzero hidden string**, as
stated by [de Wolf, §3.1][deWolf2019]: for `n ≥ 1`, a randomized decision tree that finds the
hidden string with error `1/3` on every promise input with `s ≠ 0` (as the restriction of a total
function `S`) has depth `q` with `2^n ≤ (q + 2n)²`, so `q ≥ 2^{n/2} - 2n`. Nothing is required on
the inputs with `s = 0`. The proof appends to every leaf `s'` the `2n` bit queries of `f(0)` and
`f(s')` and answers whether `s' ≠ 0` and `f(0) = f(s')`
(`Cslib.RandomizedDecisionTree.mapTree`); this answers `false` on every injective input and is
correct whenever the output `s'` is, so it decides Simon's problem with error `1/3`. -/
theorem simon_search_ne_zero_two_pow_le_sq (μ : RandomizedDecisionTree (Fin N) (Fin n → Bool))
    (S : (Fin N → Bool) → Fin n → Bool)
    (hS : ∀ X s, SimonPromise (simonFun E X) s → s ≠ 0 → S X = s)
    (hμ : ∀ X s, SimonPromise (simonFun E X) s → s ≠ 0 → μ.errorProb S X ≤ 1 / 3)
    (hn : 1 ≤ n) : 2 ^ n ≤ (μ.depth + 2 * n) ^ 2 := by
  classical
  set φ : DecisionTree (Fin N) (Fin n → Bool) → DecisionTree (Fin N) Bool :=
    fun t => t.bind (simonCheck E) with hφ
  have heval : ∀ t X, (φ t).eval X = decide (t.eval X ≠ 0 ∧
      simonFun E X 0 = simonFun E X (t.eval X)) := fun t X => by
    rw [hφ, DecisionTree.eval_bind, eval_simonCheck]
  set F : (Fin N → Bool) → Bool :=
    fun X => decide (S X ≠ 0 ∧ simonFun E X 0 = simonFun E X (S X)) with hFdef
  have hF : ∀ X s, SimonPromise (simonFun E X) s → F X = decide (s ≠ 0) := by
    intro X s hX
    by_cases hs : s = 0
    · subst hs
      have hinj := (simonPromise_zero_iff _).mp hX
      simp only [hFdef, ne_eq, not_true_eq_false, decide_false, decide_eq_false_iff_not, not_and]
      exact fun h0 he => h0 (hinj he).symm
    · simp only [hFdef, hS X s hX hs, hs, ne_eq, not_false_eq_true, true_and, decide_true,
        decide_eq_true_eq]
      exact (hX 0 s).mpr (Or.inr (zero_add s).symm)
  have hμ' : ∀ X s, SimonPromise (simonFun E X) s →
      (RandomizedDecisionTree.mapTree φ μ).errorProb F X ≤ 1 / 3 := by
    intro X s hX
    by_cases hs : s = 0
    · subst hs
      have hinj := (simonPromise_zero_iff _).mp hX
      refine (RandomizedDecisionTree.errorProb_mapTree_eq_zero φ μ F X fun t => ?_).trans_le
        (by norm_num)
      rw [heval, hF X 0 hX]
      simp only [ne_eq, not_true_eq_false, decide_false, decide_eq_false_iff_not, not_and]
      exact fun h0 he => h0 (hinj he).symm
    · exact (RandomizedDecisionTree.errorProb_mapTree_le φ μ S F X fun t ht => by
        rw [heval, ht]).trans (hμ X s hX hs)
  have hd : (RandomizedDecisionTree.mapTree φ μ).depth ≤ μ.depth + 2 * n :=
    RandomizedDecisionTree.depth_mapTree_le φ μ fun t =>
      DecisionTree.depth_bind_le t _ (depth_simonCheck_le E)
  exact (simon_two_pow_le_depth_sq E _ F hF hμ' hn).trans (Nat.pow_le_pow_left hd 2)

end QueryComplexity

end Cslib
