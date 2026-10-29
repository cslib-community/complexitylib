/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle
public import Complexity.Computability.Complexity.Classes.PP
public import Complexity.Computability.Complexity.Classes.SharpP
public import Complexity.Computability.Complexity.Classes.Toda
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Complexity.Computability.Complexity.Classes.Inclusions
import Complexity.Computability.Complexity.Classes.Oracle.Closure
import Complexity.Computability.Complexity.Classes.PP.Characterization
import Complexity.Computability.Complexity.Classes.SharpP.Closure
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Simulation
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Probabilistic.Oracle.Substitution
import Complexity.Languages.Probabilistic.Simulation
import Mathlib.Data.Nat.Bitwise
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# Polynomial time with a `PP` oracle

`P^PP` relative to the encoding `enc` of instances (`Cslib.Complexity.PWithPPOracle`) consists of
the problems `L` decided by one deterministic oracle program, strict oracle PPT as in
`Cslib.Complexity.ComputableInPolyTimeWithOracle`, that is correct against every oracle language
agreeing with some problem `B ∈ PP` on the encoded instances of `B`, for some encoded type of
instances of `B`. As for `Cslib.Complexity.PWithSharpPOracle`, the program is fixed before the
oracle and the answers on words that are not codes are arbitrary.

A bit of a value `f b` of a function `f ∈ #P` is computed in `P^PP` by binary search: the
problem `{(b, k) | k ≤ f b}` is in `PP`, by the characterisation through `GapP`
(`Cslib.Complexity.setOf_le_mem_PP`), and `N` queries `lo + 2 ^ (j - 1) ≤ f b`, for
`j = N, …, 1`, determine `f b < 2 ^ N` (`Cslib.Complexity.BinarySearch.fst_iterate_step`,
`Cslib.Complexity.BinarySearch.interpret_id_search`), within strict oracle PPT
(`Cslib.Complexity.BinarySearch.isOraclePPTOn_search`). Hence `P^#P ⊆ P^PP`
(`Cslib.Complexity.PWithSharpPOracle_subset_PWithPPOracle`): every request of a `P^#P` program
for bit `i` of `f b`, sent as the code `(b, i)`, is answered by a binary search
(`Cslib.Complexity.BinarySearch.bitQuery`), substituted into the program by open oracle
substitution (`Cslib.Probability.IsOraclePPTOn.run_interpret_preprocess_open`). The search reads
the code of `b` and the position `i` from the request without decoding `b`, and runs for
`r (n) + 1` rounds, for the length `n` of the request and `f b ≤ 2 ^ r (|b|)`.

With Toda's theorem `PH ⊆ P^#P` (`Cslib.Complexity.PH_subset_PWithSharpPOracle`), this gives
**Toda's theorem `PH ⊆ P^PP`** [Toda][Toda1991] (`Cslib.Complexity.PH_subset_PWithPPOracle`).
The classes do not count queries.

## Main definitions

* `Cslib.Complexity.PWithPPOracle`: polynomial time with a `PP` oracle.
* `Cslib.Complexity.BinarySearch.step`, `Cslib.Complexity.BinarySearch.search`: binary search, by
  itself and with an oracle.
* `Cslib.Complexity.BinarySearch.bitQuery`: answering a bit request to a `#P` function by binary
  search.

## Main results

* `Cslib.Complexity.P_subset_PWithPPOracle`, `Cslib.Complexity.PP_subset_PWithPPOracle`:
  `P ⊆ P^PP` and `PP ⊆ P^PP`.
* `Cslib.Complexity.PWithOracle_subset_PWithPPOracle`,
  `Cslib.Complexity.exists_mem_PP_mem_PWithOracle_image`: `P^A ⊆ P^PP` for `A ∈ PP`, and `P^PP`
  lies in `P` relative to the codes of a `PP` problem.
* `Cslib.Complexity.setOf_le_mem_PP`: comparing with a `#P` value is in `PP`.
* `Cslib.Complexity.BinarySearch.interpret_id_search`,
  `Cslib.Complexity.BinarySearch.isOraclePPTOn_search`: binary search with an oracle is correct
  and strict oracle PPT.
* `Cslib.Complexity.mem_PWithPPOracle_of_testBit`: one bit of a `#P` value is in `P^PP`.
* `Cslib.Complexity.PWithSharpPOracle_subset_PWithPPOracle`: `P^#P ⊆ P^PP`.
* `Cslib.Complexity.BPOp_ParityP_subset_PWithPPOracle`: `BP·⊕P ⊆ P^PP`.
* `Cslib.Complexity.PH_subset_PWithPPOracle`: **Toda's theorem, `PH ⊆ P^PP`**.

## References

* [S. Toda, *PP is as hard as the polynomial-time hierarchy*][Toda1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM

variable {α : Type}

open Classical in
/-- **`P^PP`**: the problems `L` such that, for some type `β` with encoding `encβ` and some
`B ∈ PP encβ`, one deterministic oracle program, strict oracle PPT on the encoding `enc` of
instances, decides `L` against every oracle language containing the code `encβ b` exactly when
`b ∈ B`. Answers on words that are not codes are arbitrary. -/
def PWithPPOracle (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ (β : Type) (encβ : β ↪ List Bool) (B : Set β), B ∈ PP encβ ∧
    PolyTimeOracleProgram enc encBool (fun A => ∀ b, encβ b ∈ A ↔ b ∈ B)
      (fun g => ∀ a, a ∈ L ↔ g a = true)}

variable {enc : α ↪ List Bool} {L : Set α}

/-- **`P ⊆ P^PP`**: a polynomial-time decider makes no query. -/
theorem P_subset_PWithPPOracle : P enc ⊆ PWithPPOracle enc := by
  rintro L ⟨g, hg, hL⟩
  have hempty : (∅ : Set α) ∈ PP enc :=
    BPP_subset_PP (P_subset_BPP ⟨fun _ => false, .const false, fun _ => by simp⟩)
  exact ⟨α, enc, ∅, hempty, .of_polyTime hg fun _ _ => hL⟩

/-- **`PP ⊆ P^PP`**: the program asks the oracle about its instance, with one query. -/
theorem PP_subset_PWithPPOracle : PP enc ⊆ PWithPPOracle enc := by
  classical
  intro L hL
  exact ⟨α, enc, L, hL, .of_query (.of_eq fun _ => rfl)
    fun A hA a => (hA a).symm.trans decide_eq_true_iff.symm⟩

/-- **`P^A ⊆ P^PP` for `A ∈ PP`**: a polynomial-time oracle program relative to a language in
`PP` over words encoded as themselves decides its problem against every oracle agreeing with that
language, since every word is a code. -/
theorem PWithOracle_subset_PWithPPOracle {A : Set (List Bool)} (hA : A ∈ PP encBits) :
    PWithOracle A enc ⊆ PWithPPOracle enc := by
  rintro L ⟨f, hf, hL⟩
  exact ⟨List Bool, encBits, A, hA,
    .of_computableInPolyTimeWithOracle hf fun A' hA' => ⟨Set.ext hA', hL⟩⟩

/-- **`P^PP` lies in polynomial time relative to the codes of a `PP` problem**: against the image
of its `PP` problem under the encoding, the program of a problem in `P^PP` decides it. -/
theorem exists_mem_PP_mem_PWithOracle_image (hL : L ∈ PWithPPOracle enc) :
    ∃ (β : Type) (encβ : β ↪ List Bool) (B : Set β), B ∈ PP encβ ∧
      L ∈ PWithOracle (encβ '' B) enc := by
  classical
  obtain ⟨β, encβ, B, hB, hL⟩ := hL
  exact ⟨β, encβ, B, hB,
    hL.exists_computableInPolyTimeWithOracle fun _ => encβ.injective.mem_set_image⟩

/-! ### Comparing with a `#P` value -/

/-- **Comparing with a `#P` value is in `PP`**: for `f ∈ #P`, the pairs `(a, k)` with `k ≤ f a`,
`k` in binary, are the instances where the `GapP` function `f a + 1 - k` is positive. -/
theorem setOf_le_mem_PP {f : α → ℕ} (hf : f ∈ SharpP enc) :
    {x : α × ℕ | x.2 ≤ f x.1} ∈ PP (encPair enc encNat) := by
  refine mem_PP_iff_exists_GapP.2 ⟨fun x => ((f x.1 + 1 : ℕ) : ℤ) - (x.2 : ℕ),
    ⟨_, SharpP.add_one_mem (SharpP.comp_mem hf (.fst enc encNat)), _,
      mem_SharpP_of_polyTime (.snd enc encNat), fun _ => rfl⟩,
    fun x => ?_⟩
  simp only [Set.mem_ofPred_eq, sub_pos, Nat.cast_lt]
  omega

/-! ### Binary search -/

namespace BinarySearch

/-- One round of binary search for a number `F`: in the state `(lo, j)` with `j > 0` bits left,
test whether `lo + 2 ^ (j - 1) ≤ F`, and keep the half containing `F`. -/
def step (F : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  if s.2 = 0 then s else (if s.1 + 2 ^ (s.2 - 1) ≤ F then s.1 + 2 ^ (s.2 - 1) else s.1, s.2 - 1)

/-- **Binary search finds `F < 2 ^ N` in `N` rounds.** -/
theorem fst_iterate_step {F N : ℕ} (hF : F < 2 ^ N) : ((step F)^[N] (0, N)).1 = F := by
  have key (t : ℕ) (ht : t ≤ N) : ∃ lo, (step F)^[t] (0, N) = (lo, N - t) ∧ lo ≤ F ∧
      F < lo + 2 ^ (N - t) := by
    induction t with
    | zero => exact ⟨0, rfl, Nat.zero_le _, by simpa using hF⟩
    | succ t ih =>
      obtain ⟨lo, hlo, hle, hlt⟩ := ih (by omega)
      rw [Function.iterate_succ_apply', hlo]
      obtain ⟨j, hj⟩ : ∃ j, N - t = j + 1 := ⟨N - t - 1, by omega⟩
      have hj' : N - (t + 1) = j := by omega
      rw [hj, pow_succ] at hlt
      unfold step
      simp only [hj, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, hj']
      split_ifs with h
      · exact ⟨_, rfl, h, by omega⟩
      · exact ⟨_, rfl, hle, by omega⟩
  obtain ⟨lo, hlo, hle, hlt⟩ := key N le_rfl
  rw [hlo]
  simp only [Nat.sub_self, pow_zero] at hlt
  dsimp only
  omega

/-! ### Binary search with an oracle -/

/-- One round of binary search with the oracle: in the state `(lo, j)` with `j > 0`, ask about the
code `encPair encBits encNat (u, lo + 2 ^ (j - 1))`, and keep the half selected by the reply. -/
def searchQuery (u : List Bool) (s : ℕ × ℕ) : WordQueryComp Unit (ℕ × ℕ) :=
  if s.2 = 0 then pure s else
    (fun reply => (if reply == [true] then s.1 + 2 ^ (s.2 - 1) else s.1, s.2 - 1)) <$>
      (List.take 1 <$> OracleComp.query ((), encPair encBits encNat (u, s.1 + 2 ^ (s.2 - 1))))

/-- Binary search in `N` rounds with the oracle, about the codes `encPair encBits encNat (u, k)`. -/
def search (u : List Bool) (N : ℕ) : WordQueryComp Unit ℕ :=
  Prod.fst <$> OracleComp.iterate N (searchQuery u) (0, N)

/-- A round of the search as a program with private coins and word queries. -/
private theorem interpret_searchQuery (u : List Bool) (s : ℕ × ℕ) :
    OracleComp.interpret ProbOracleComp.query (searchQuery u s) =
      if s.2 = 0 then pure s else
        (fun reply => (if reply == [true] then s.1 + 2 ^ (s.2 - 1) else s.1, s.2 - 1)) <$>
          (List.take 1 <$> ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
            ((), encPair encBits encNat (u, s.1 + 2 ^ (s.2 - 1)))) := by
  unfold searchQuery
  split <;> simp [OracleComp.interpret_map, OracleComp.interpret_query]

open Classical in
/-- Against an oracle containing the code of `(u, k)` exactly when `k ≤ F`, a round of the search
is `BinarySearch.step F`. -/
private theorem interpret_id_searchQuery {F : ℕ} {A : Set (List Bool)} {u : List Bool}
    (hA : ∀ k, encPair encBits encNat (u, k) ∈ A ↔ k ≤ F) (s : ℕ × ℕ) :
    OracleComp.interpret (m := Id) (languageOracle A) (searchQuery u s) =
      BinarySearch.step F s := by
  unfold searchQuery BinarySearch.step
  split
  · rfl
  · change (fun reply : List Bool =>
      (if reply == [true] then s.1 + 2 ^ (s.2 - 1) else s.1, s.2 - 1))
        (List.take 1 (languageOracle A ((), encPair encBits encNat (u, s.1 + 2 ^ (s.2 - 1))))) = _
    rw [languageOracle_apply]
    by_cases hm : encPair encBits encNat (u, s.1 + 2 ^ (s.2 - 1)) ∈ A
    · simp only [decide_eq_true hm, (hA _).1 hm, ↓reduceIte, List.take_succ_cons, List.take_zero,
        beq_self_eq_true]
    · have hle : ¬ s.1 + 2 ^ (s.2 - 1) ≤ F := fun h => hm ((hA _).2 h)
      simp only [decide_eq_false hm, hle, ↓reduceIte, List.take_succ_cons, List.take_zero]
      rfl

open Classical in
/-- **Binary search finds the number.** Against an oracle containing the code of `(u, k)` exactly
when `k ≤ F`, the search in `N` rounds returns `F < 2 ^ N`. -/
theorem interpret_id_search {F N : ℕ} {A : Set (List Bool)} {u : List Bool}
    (hA : ∀ k, encPair encBits encNat (u, k) ∈ A ↔ k ≤ F) (hF : F < 2 ^ N) :
    OracleComp.interpret (m := Id) (languageOracle A) (search u N) = F := by
  unfold search
  rw [OracleComp.interpret_map]
  change (OracleComp.interpret (m := Id) (languageOracle A)
    (OracleComp.iterate N (searchQuery u) (0, N))).1 = F
  rw [OracleComp.interpret_id_iterate]
  simp only [interpret_id_searchQuery hA]
  exact fst_iterate_step hF

private theorem cond_pt {β γ : Type} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {c : β → Bool} {yes no : β → γ}
    (hc : ComputableInPolyTime c encB encBool)
    (hyes : ComputableInPolyTime yes encB encC)
    (hno : ComputableInPolyTime no encB encC) :
    ComputableInPolyTime (fun x => if c x then yes x else no x) encB encC :=
  hc.ite hyes hno

attribute [local fun_prop] ComputableInPolyTime.fst' ComputableInPolyTime.snd' cond_pt in
/-- **Binary search is strict oracle PPT**: `N` rounds, with `N` computed in unary, each building
one request and reading one reply bit, on states of a binary number below `2 ^ N` and a unary
counter. -/
theorem isOraclePPTOn_search {input : α ↪ List Bool} {u : α → List Bool} {N : α → ℕ}
    (hu : ComputableInPolyTime u input encBits)
    (hN : ComputableInPolyTime N input encUnary) :
    IsOraclePPTOn input encNat
      (fun a => OracleComp.interpret ProbOracleComp.query (search (u a) (N a))) := by
  simp only [search, OracleComp.interpret_map, OracleComp.interpret_iterate]
  have hinit : ComputableInPolyTime (fun a => ((0 : ℕ), N a)) input
      (encPair encNat encUnary) :=
    (ComputableInPolyTime.const 0).prod hN
  have hstep₀ : IsOraclePPTOn (encPair encBits (encPair encNat encUnary))
      (encPair encNat encUnary) (fun pair : List Bool × (ℕ × ℕ) =>
        OracleComp.interpret ProbOracleComp.query (searchQuery pair.1 pair.2)) := by
    simp only [interpret_searchQuery]
    refine IsOraclePPTOn.ite' (by fun_prop)
      (ComputableInPolyTime.snd encBits (encPair encNat encUnary)).isOraclePPTOn ?_
    exact IsOraclePPTOn.map_with' (IsOraclePPTOn.query_take' () (by fun_prop) (by fun_prop))
      (by fun_prop)
  have hstep : IsOraclePPTOn (encPair input (encPair encNat encUnary)) (encPair encNat encUnary)
      (fun pair : α × (ℕ × ℕ) =>
        OracleComp.interpret ProbOracleComp.query (searchQuery (u pair.1) pair.2)) :=
    hstep₀.preprocess' (prepare := fun pair : α × (ℕ × ℕ) => (u pair.1, pair.2))
      ((hu.comp (ComputableInPolyTime.fst input (encPair encNat encUnary))).prod
        (ComputableInPolyTime.snd input (encPair encNat encUnary)))
  have hpreserve (a : α) (i : ℕ) (s : ℕ × ℕ) (hi : i < N a)
      (hinv : s.2 = N a - i ∧ s.1 + 2 ^ s.2 ≤ 2 ^ N a) (next : ℕ × ℕ)
      (hnext : next ∈ OracleComp.support
        (OracleComp.interpret ProbOracleComp.query (searchQuery (u a) s))) :
      next.2 = N a - (i + 1) ∧ next.1 + 2 ^ next.2 ≤ 2 ^ N a := by
    obtain ⟨hs, hlo⟩ := hinv
    have hs0 : s.2 ≠ 0 := by omega
    rw [interpret_searchQuery] at hnext
    simp only [hs0, ↓reduceIte, Functor.map_map] at hnext
    obtain ⟨reply, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
    obtain ⟨j, hj⟩ : ∃ j, s.2 = j + 1 := ⟨s.2 - 1, by omega⟩
    rw [hj, pow_succ] at hlo
    refine ⟨by simp only; omega, ?_⟩
    simp only [hj, Nat.add_sub_cancel]
    split_ifs <;> omega
  have hbound (a : α) (i : ℕ) (s : ℕ × ℕ) (_ : i ≤ N a)
      (hinv : s.2 = N a - i ∧ s.1 + 2 ^ s.2 ≤ 2 ^ N a) :
      (encPair encNat encUnary s).length ≤ 3 * N a + 1 := by
    obtain ⟨hs, hlo⟩ := hinv
    have hsize : s.1.size ≤ N a := Nat.size_le.2 (by
      have := Nat.one_le_two_pow (n := s.2)
      omega)
    rw [← Nat.size_eq_bits_len] at hsize
    simp only [length_encPair, encNat_apply, encUnary_apply, List.length_replicate]
    omega
  have hNpoly : PolyBounded (fun a => (input a).length) N :=
    hN.polyBounded_length.mono fun _ => by simp [encUnary_apply]
  exact (IsOraclePPTOn.iterateWith_spec'
    (step := fun a s => OracleComp.interpret ProbOracleComp.query (searchQuery (u a) s))
    hN hinit hstep (fun a i s => s.2 = N a - i ∧ s.1 + 2 ^ s.2 ≤ 2 ^ N a)
    (fun a => ⟨by simp, by simp⟩) hpreserve
    (((PolyBounded.const 3).mul hNpoly).add (.const 1)) hbound).1.map'
    (ComputableInPolyTime.fst encNat encUnary)

/-! ### Answering bit requests -/

/-- The handler answering a request for bit `i` of `f b`, sent as the code
`encPair encβ encNat (b, i)`, by binary search for `f b < 2 ^ N` with `N = r (n) + 1` rounds,
where `n` is the length of the request: the code of `b` is read from the request without decoding
`b`, and the position is read in binary and capped at `N`. -/
def bitQuery (r : Polynomial ℕ) (q : Unit × List Bool) : WordQueryComp Unit (List Bool) :=
  (fun lo => [lo.testBit (min (ofBits (dropFrame q.2)) (r.eval q.2.length + 1))]) <$>
    search (unframe q.2) (r.eval q.2.length + 1)

open Classical in
/-- Against an oracle agreeing with `{(b, k) | k ≤ f b}` on codes, `bitQuery` answers bit `i`
of `f b` to the code of `(b, i)`, when `f b ≤ 2 ^ r (|encβ b|)`. -/
private theorem interpret_id_bitQuery {β : Type} {encβ : β ↪ List Bool} {f : β → ℕ}
    {r : Polynomial ℕ}
    (hr : ∀ b, f b ≤ 2 ^ r.eval (encβ b).length) {A : Set (List Bool)}
    (hA : ∀ x : β × ℕ, encPair encβ encNat x ∈ A ↔ x.2 ≤ f x.1) (b : β) (i : ℕ) :
    OracleComp.interpret (m := Id) (languageOracle A) (bitQuery r ((), encPair encβ encNat (b, i)))
      = [(f b).testBit i] := by
  set N := r.eval (encPair encβ encNat (b, i)).length + 1 with hN
  have hfN : f b < 2 ^ N := by
    refine (hr b).trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_of_le ?_))
    exact Polynomial.eval_mono _ (by simp only [length_encPair]; omega)
  unfold bitQuery
  rw [OracleComp.interpret_map]
  change [(OracleComp.interpret (m := Id) (languageOracle A)
    (search (unframe (encPair encβ encNat (b, i))) N)).testBit
      (min (ofBits (dropFrame (encPair encβ encNat (b, i)))) N)] = _
  have hu : unframe (encPair encβ encNat (b, i)) = encβ b := unframe_frame_append _ _
  have hd : ofBits (dropFrame (encPair encβ encNat (b, i))) = i := by
    change ofBits (dropFrame (frame (encβ b) ++ encNat i)) = i
    rw [dropFrame_frame_append]
    exact Decoder.nat.decode_enc i
  rw [hu, hd, interpret_id_search (F := f b) (fun k => hA (b, k)) hfN]
  congr 1
  rcases le_total i N with hi | hi
  · rw [Nat.min_eq_left hi]
  · rw [Nat.min_eq_right hi, Nat.testBit_eq_false_of_lt hfN,
      Nat.testBit_eq_false_of_lt (hfN.trans_le (Nat.pow_le_pow_right (by norm_num) hi))]

end BinarySearch

/-! ### `P^#P ⊆ P^PP` -/

open BinarySearch in
attribute [local fun_prop] ComputableInPolyTime.fst' ComputableInPolyTime.snd' cond_pt in
/-- **`P^#P ⊆ P^PP`**: every request of a `P^#P` program for a bit of a `#P` value `f b` is
answered by binary search with queries `k ≤ f b` to the `PP` problem `{(b, k) | k ≤ f b}`. -/
theorem PWithSharpPOracle_subset_PWithPPOracle : PWithSharpPOracle enc ⊆ PWithPPOracle enc := by
  classical
  rintro L ⟨β, encβ, f, hf, program, hcert, hL⟩
  obtain ⟨r, hr⟩ := SharpP.exists_le_two_pow hf
  refine ⟨β × ℕ, encPair encβ encNat, {x | x.2 ≤ f x.1}, setOf_le_mem_PP hf,
    fun a => OracleComp.interpret (bitQuery r) (program a), ?_, fun A hA a => ?_⟩
  · -- substitute the binary search for every bit request
    have hindex : ComputableInPolyTime
        (fun pair : List Bool × ℕ => min (ofBits (dropFrame pair.1)) (r.eval pair.1.length + 1))
        (encPair encBits encNat) encUnary :=
      (ComputableInPolyTime.binary_min_unary' (by fun_prop) (by fun_prop)).of_enc_eq
        fun _ => congrArg encUnary (Nat.min_comm _ _)
    have hlast : ComputableInPolyTime (fun pair : List Bool × ℕ =>
        [pair.2.testBit (min (ofBits (dropFrame pair.1)) (r.eval pair.1.length + 1))])
        (encPair encBits encNat) encBits :=
      (ComputableInPolyTime.binary_testBit (ComputableInPolyTime.snd encBits encNat)
        hindex).of_enc_eq fun _ => (encBool_apply _).symm
    have hG : IsOraclePPTOn encBits encBits (fun w : List Bool =>
        OracleComp.interpret ProbOracleComp.query (bitQuery r ((), w))) := by
      simp only [bitQuery, OracleComp.interpret_map]
      exact (isOraclePPTOn_search (u := unframe) (N := fun w => r.eval w.length + 1)
        (by fun_prop) (by fun_prop)).map_with' hlast
    have hhandler : IsOraclePPTOn
        (encPair enc (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit)))
        (encPair encBits (encFinEnum Unit))
        (fun pair : α × (Unit × List Bool) × Unit => (fun reply => (reply, ())) <$>
          OracleComp.interpret ProbOracleComp.query (bitQuery r pair.2.1)) :=
      (hG.preprocess' (prepare := fun pair : α × (Unit × List Bool) × Unit => pair.2.1.2)
        (by fun_prop)).map' (by fun_prop)
    have hsub := hcert.run_interpret_preprocess_open' (State := Unit)
      (handler := fun _ q _ => (fun reply => (reply, ())) <$>
        OracleComp.interpret ProbOracleComp.query (bitQuery r q))
      (prepare := id) (initial := fun _ => ()) (resources := fun _ _ => 1)
      ComputableInPolyTime.id' hhandler (ComputableInPolyTime.const ())
      (fun _ _ => True) (fun _ => trivial) (ComputableInPolyTime.const 1)
      (fun a request state _ result hresult => by
        obtain ⟨reply, hreply, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
        rw [bitQuery, OracleComp.interpret_map] at hreply
        obtain ⟨lo, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
        exact ⟨trivial, by simp, Nat.le_add_right _ _⟩)
    refine (hsub.map' (ComputableInPolyTime.fst encBool (encFinEnum Unit))).congr
      fun a State oracle s => ?_
    congr 2
    rw [OracleComp.interpret_interpret, OracleComp.interpret_interpret]
    have hH : (fun q : Unit × List Bool => OracleComp.interpret (ProbOracleComp.handler
        (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
        (fun (q : Unit × List Bool) (_ : Unit) => (fun reply => (reply, ())) <$>
          OracleComp.interpret ProbOracleComp.query (bitQuery r q)))
        (ProbOracleComp.query q)) = fun q : Unit × List Bool =>
          StateT.lift (OracleComp.interpret ProbOracleComp.query (bitQuery r q)) := by
      funext q
      rw [ProbOracleComp.interpret_query]
      funext u
      simp [StateT.lift]
    rw [hH, OracleComp.run_interpret_lift, Functor.map_map]
    simp only [id_map', id]
  · -- the bits answered by the handler
    let A' : Set (List Bool) :=
      {w | OracleComp.interpret (m := Id) (languageOracle A) (bitQuery r ((), w)) = [true]}
    have hA' : AnswersBits encβ f A' := fun b i => by
      simp only [A', Set.mem_ofPred_eq, interpret_id_bitQuery hr (fun x => hA x) b i]
      exact ⟨fun h => (List.cons.inj h).1, fun h => by rw [h]⟩
    have hhandler : (fun q => OracleComp.interpret (m := Id) (languageOracle A) (bitQuery r q)) =
        languageOracle A' := by
      funext q
      have hsingle : ∀ w, ∃ bit, OracleComp.interpret (m := Id) (languageOracle A)
          (bitQuery r ((), w)) = [bit] := fun w => by
        unfold bitQuery
        rw [OracleComp.interpret_map]
        exact ⟨_, rfl⟩
      obtain ⟨bit, hbit⟩ := hsingle q.2
      rw [languageOracle_apply, show q = ((), q.2) from rfl, hbit]
      by_cases hq : q.2 ∈ A'
      · have hq' : [bit] = [true] := hbit.symm.trans hq
        rw [decide_eq_true hq, (List.cons.inj hq').1]
      · have hq' : [bit] ≠ [true] := fun h => hq (hbit.trans h)
        rw [decide_eq_false hq]
        cases bit
        · rfl
        · exact absurd rfl hq'
    dsimp only
    rw [hL A' hA' a, OracleComp.interpret_interpret, hhandler]

/-! ### Toda's theorem -/

/-- **One bit of a `#P` value is in `P^PP`**: a problem decided by the bit at a polynomial
position of a function `f ∈ #P` on its own instances is in `P^PP`, found by binary search with
queries `k ≤ f a` to the `PP` problem `{(a, k) | k ≤ f a}`. -/
theorem mem_PWithPPOracle_of_testBit {f : α → ℕ} (hf : f ∈ SharpP enc)
    {p : Polynomial ℕ} (h : ∀ a, a ∈ L ↔ (f a).testBit (p.eval (enc a).length)) :
    L ∈ PWithPPOracle enc :=
  PWithSharpPOracle_subset_PWithPPOracle (mem_PWithSharpPOracle_of_testBit hf h)

/-- **`BP·⊕P ⊆ P^PP`**: a problem decided with bounded error by a problem in `⊕P` about pairs of
an instance and a random string is decided by one bit of a function in `#P`, found by binary
search with a `PP` oracle. -/
theorem BPOp_ParityP_subset_PWithPPOracle :
    BPOp enc (ParityP (encPair enc encBits)) ⊆ PWithPPOracle enc :=
  BPOp_ParityP_subset_PWithSharpPOracle.trans PWithSharpPOracle_subset_PWithPPOracle

/-- **Toda's theorem: `PH ⊆ P^PP`** [Toda][Toda1991]. Every problem in the polynomial hierarchy is
decided by a polynomial-time oracle program against every oracle language agreeing with a problem
in `PP` on its encoded instances. -/
theorem PH_subset_PWithPPOracle : PH enc ⊆ PWithPPOracle enc :=
  PH_subset_PWithSharpPOracle.trans PWithSharpPOracle_subset_PWithPPOracle

end Cslib.Complexity
