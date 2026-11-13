/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Hierarchy
public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.ShortDesc
public import CslibFrontier.Computability.Complexity.Classes.Time
public import CslibFrontier.Foundations.Data.BitString.Enumeration
import CslibFrontier.Computability.Complexity.Classes.Time.Verifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run

/-!
# Lazy diagonalization against nondeterministic time

A diagonal for nondeterministic time cannot simply negate the answer of the machine it simulates:
that answer is an existential over certificates. Lazy diagonalization [Žák][Zak1983] negates it
only once per interval of lengths, where the input is long enough to try every certificate. This
module holds the construction and its lower bound, shared by the nondeterministic time hierarchies
(`Cslib.Complexity.lazyDiagonal`, `Cslib.Complexity.expLazyDiagonal`). It is parameterized by a
step budget `β`, a certificate length `L` and a horizon `H`.

An input carries a word `w` framed at its start, and `w` carries the description of a deterministic
verifier on pairs, followed by padding that gives each description infinitely many words `w`. The
interval of `w` runs from the length `P` of `frame w` to `2 ^ H P - 1`. Below its end, the verifier
`Cslib.Complexity.Diagonal.lazyVerifier β L H` runs the described verifier on the input one bit
longer for `β` steps with the universal function (`Cslib.Complexity.Diagonal.lazyAccepts`); at its
end, it accepts when the described verifier accepts no certificate of length `L P` on `frame w`.
The problem `Cslib.Complexity.Diagonal.lazyLanguage β L H` consists of the inputs `x` with an
accepted certificate of length `L (x.length + 1)`. A nondeterministic machine deciding it within
time `O(T)` has a deterministic verifier on pairs within linear time, accepting certificates of
every length at least `c * T n + c` (`Cslib.Complexity.exists_verifier_of_mem_NTIME`). When
certificates of length `L` and `β` simulated steps eventually suffice for it, the universal function
runs it exactly on the interval of a word `w` describing it with enough padding. Then each input of
the interval is in the problem exactly when the next one is, and the last exactly when the first is
not.

Arora and Barak enumerate nondeterministic machines and use one global sequence of intervals
[Arora and Barak, Theorem 3.3][AroraBarak07]; this construction gives each word `w` its own interval
instead, and diagonalizes against verifiers.

## Main definitions

* `Cslib.Complexity.Diagonal.lazyAccepts`: a run of a described verifier with the universal
  function.
* `Cslib.Complexity.Diagonal.lazyVerifier`: the verifier of the lazy diagonal.
* `Cslib.Complexity.Diagonal.lazyLanguage`: the lazy diagonal problem.

## Main results

* `Cslib.Complexity.Diagonal.lazyLanguage_notMem_NTIME`: the lazy diagonal is not in `NTIME T`
  when certificates of length `L` and `β` simulated steps eventually suffice for every verifier
  of a problem in `NTIME T`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft of January
  2007][AroraBarak07]
* [S. Žák, *A Turing machine time hierarchy*][Zak1983]
-/

public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

namespace Diagonal

/-- The machine described by `c`, run as a verifier on the pair `(y, v)` (encoded as
`frame y ++ v`) for `β y v` steps with the universal function, has halted with output
`[true]`. -/
@[expose]
def lazyAccepts (β : List Bool → List Bool → ℕ) (c y v : List Bool) : Bool :=
  !verdict (universal (decodeDesc c, (frame y ++ v).map eBit, β y v))

/-- **The verifier of the lazy diagonal** with step budget `β`, certificate length `L` and
horizon `H`, on an input `x` of length `n` and a certificate `v`. The input carries a word `w`
framed at its start, and `w` carries the description `unframe w` framed at its start. When the
description is short (`Cslib.Complexity.Diagonal.shortDesc w`), let `P = 2 * w.length + 1`; the
lengths from `P` to `2 ^ H P - 1` form the interval of `w`.

* If `n + 1 < 2 ^ H P`, below the end of the interval, accept when the described verifier
  accepts `v` on the input one bit longer.
* If `n + 1 = 2 ^ H P`, at the end of the interval, accept when the described verifier
  accepts no certificate of length `L P` on `frame w`, by trying them all.
* Otherwise, and when the description is not short, reject. -/
@[expose]
def lazyVerifier (β : List Bool → List Bool → ℕ) (L H : ℕ → ℕ) (p : List Bool × List Bool) :
    Bool :=
  if shortDesc (unframe p.1) then
    if Nat.size (p.1.length + 1) ≤ H (2 * (unframe p.1).length + 1) then
      lazyAccepts β (unframe (unframe p.1)) (p.1 ++ [false]) p.2
    else if Nat.size p.1.length ≤ H (2 * (unframe p.1).length + 1) then
      !(Cslib.BitString.enumList (L (2 * (unframe p.1).length + 1))).any
        (lazyAccepts β (unframe (unframe p.1)) (frame (unframe p.1)))
    else false
  else false

/-- **The lazy diagonal problem**: the words `x` with a certificate of length `L (x.length + 1)`
accepted by `Cslib.Complexity.Diagonal.lazyVerifier β L H`. -/
@[expose]
def lazyLanguage (β : List Bool → List Bool → ℕ) (L H : ℕ → ℕ) : Set (List Bool) :=
  {x | ∃ v : List Bool, v.length = L (x.length + 1) ∧ lazyVerifier β L H (x, v) = true}

/-- **The lazy diagonal is not decidable in nondeterministic time `O(T)`** once certificates of
length `L` (`hL`) and `β` simulated steps (`hβ`) eventually suffice for the linear-time verifiers
of `Cslib.Complexity.exists_verifier_of_mem_NTIME`, and every interval is nonempty (`hH`). -/
theorem lazyLanguage_notMem_NTIME {β : List Bool → List Bool → ℕ} {L H T : ℕ → ℕ}
    (hL : ∀ c, ∃ M, ∀ m, M ≤ m → c * T m + c ≤ L m)
    (hβ : ∀ c₂, ∃ M, ∀ y v : List Bool, M ≤ y.length → v.length = L y.length →
      c₂ * ((encPair encBits encBits (y, v)).length + 1) ≤ β y v)
    (hH : ∀ P, P + 1 < 2 ^ H P) :
    lazyLanguage β L H ∉ NTIME encBits T := by
  intro hD
  obtain ⟨V, c, hV, hmem⟩ := exists_verifier_of_mem_NTIME hD
  obtain ⟨c₂, ⟨k, State, hfin, tm, htm⟩, -⟩ := hV
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  set code := eDesc (desc eS eBit tm) with hcode
  obtain ⟨M₁, hM₁⟩ := hL c
  obtain ⟨M₂, hM₂⟩ := hβ c₂
  set M := M₁ + M₂ with hM
  -- the universal function runs the verifier exactly on long enough words
  have hsim (y v : List Bool) (hy : M ≤ y.length) (hv : v.length = L y.length) :
      lazyAccepts β code y v = V (y, v) := by
    obtain ⟨hhalt, hout⟩ := (htm (y, v)).runFrom_of_le (hM₂ y v (by omega) hv)
    simp only [encPair_apply, encBits_apply, encBool_apply] at hhalt hout
    rw [lazyAccepts, hcode, decodeDesc_eDesc, universal_desc, hout]
    simp only [List.map_cons, List.map_nil, Cfg.Halted] at hhalt ⊢
    rw [hhalt]
    cases V (y, v) <;> simp [verdict, eBit]
  -- on long enough words, membership is acceptance by the simulated verifier
  have hiff (y : List Bool) (hy : M ≤ y.length) : y ∈ lazyLanguage β L H ↔
      ∃ v : List Bool, v.length = L y.length ∧ lazyAccepts β code y v = true := by
    have h := hmem y (L y.length) (by simpa [encBits_apply] using hM₁ y.length (by omega))
    rw [h]
    exact exists_congr fun v => and_congr_right fun hv => by rw [hsim y v hy hv]
  -- the interval of `w`
  set w := frame code ++ List.replicate (2 ^ code.length + M) true with hw
  set P := 2 * w.length + 1 with hP
  set E := H P with hE
  set x : ℕ → List Bool := fun m => frame w ++ List.replicate (m - P) false with hx
  have hwlen : w.length = 2 * code.length + 1 + (2 ^ code.length + M) := by simp [w]
  have hMP : M ≤ P := by
    have := hwlen; generalize 2 ^ code.length = e at this; omega
  have hxlen (m : ℕ) (hm : P ≤ m) : (x m).length = m := by
    simp only [x, List.length_append, length_frame, List.length_replicate]; omega
  have hshort : shortDesc w = true := by
    rw [shortDesc, decide_eq_true_eq, unframe_frame_append, hwlen]; omega
  have hverifier (m : ℕ) (hm : P ≤ m) (v : List Bool) : lazyVerifier β L H (x m, v) =
      if Nat.size (m + 1) ≤ E then lazyAccepts β code (x m ++ [false]) v
      else if Nat.size m ≤ E then
        !(Cslib.BitString.enumList (L P)).any (lazyAccepts β code (frame w))
      else false := by
    have hu : unframe (x m) = w := unframe_frame_append _ _
    have hc : unframe w = code := unframe_frame_append _ _
    simp only [lazyVerifier, hu, hc, hshort, hxlen m hm, ← hP, ← hE, ↓reduceIte]
  have hPE : P + 1 < 2 ^ E := hH P
  set U := 2 ^ E - 1 with hU
  -- each word below the end of the interval is in the language exactly when the next one is
  have hstep (m : ℕ) (hm : P ≤ m) (hmU : m < U) :
      x m ∈ lazyLanguage β L H ↔ x (m + 1) ∈ lazyLanguage β L H := by
    have hsize : Nat.size (m + 1) ≤ E := Nat.size_le.mpr (by omega)
    have hnext : x m ++ [false] = x (m + 1) := by
      simp only [x, List.append_assoc, ← List.replicate_succ', show m - P + 1 = m + 1 - P by omega]
    rw [hiff (x (m + 1)) (by rw [hxlen _ (by omega)]; omega), lazyLanguage, Set.mem_ofPred_eq,
      hxlen (m + 1) (by omega), hxlen m hm]
    refine exists_congr fun v => and_congr_right fun _ => ?_
    simp only [hverifier m hm v, hsize, ↓reduceIte, hnext]
  -- the end of the interval is in the language exactly when its start is not
  have hend : x U ∈ lazyLanguage β L H ↔ x P ∉ lazyLanguage β L H := by
    have hUP : P ≤ U := by omega
    have hsize₁ : ¬Nat.size (U + 1) ≤ E := by
      rw [Nat.size_le, hU, Nat.sub_add_cancel Nat.one_le_two_pow]; exact lt_irrefl _
    have hsize₂ : Nat.size U ≤ E := Nat.size_le.mpr (by omega)
    have hbase : x P = frame w := by simp [x]
    rw [hiff (x P) (by rw [hxlen P le_rfl]; omega), hxlen P le_rfl, hbase, lazyLanguage,
      Set.mem_ofPred_eq]
    simp only [hverifier U hUP, hsize₁, hsize₂, ↓reduceIte, Bool.not_eq_true',
      List.any_eq_false, Cslib.BitString.mem_enumList, not_exists, not_and, Bool.not_eq_true]
    exact ⟨fun ⟨_, _, h⟩ v hv => h v hv,
      fun h => ⟨List.replicate _ false, List.length_replicate .., h⟩⟩
  -- the chain from the start of the interval to its end
  have hchain (j : ℕ) (hj : j ≤ U - P) :
      x (U - j) ∈ lazyLanguage β L H ↔ x U ∈ lazyLanguage β L H := by
    induction j with
    | zero => rfl
    | succ j ih =>
      have heq : U - j = U - (j + 1) + 1 := by omega
      rw [← ih (by omega), heq, ← hstep (U - (j + 1)) (by omega) (by omega)]
  have h := hchain (U - P) le_rfl
  rw [Nat.sub_sub_self (by omega), hend] at h
  exact iff_not_self h

end Diagonal

end Cslib.Complexity
