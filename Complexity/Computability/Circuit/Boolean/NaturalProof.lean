/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.PolynomialTime
public import Complexity.Computability.MCSP.Basic
public import Complexity.Crypto.Primitives.PRG.Circuit
import Complexity.Computability.MCSP.Shannon
import Complexity.Crypto.Primitives.PRG.NisanWigderson.Sampling
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Natural proofs

A *property* of Boolean functions is a set `C n` of functions on `n` inputs for each `n`.
Razborov and Rudich call it *natural* when it contains a property `D` that is *large*, holding
for at least a `2 ^ (-O(n))` fraction of all functions on `n` inputs, and *constructive*, decided
from the truth table of length `2 ^ n` within some class `Γ` of languages, for instance by circuits
of size polynomial in `2 ^ n` (`Γ = P/poly`) [RazborovRudich1997]. It is *useful* against a class
`Λ` of languages when the slices of every language in `Λ` eventually lie outside it. A lower-bound
proof against `Λ` exhibits a property useful against `Λ`, and Razborov and Rudich observe that
the properties used by the known proofs are natural.

**The natural proofs barrier.** If a property holds for no function of a keyed family, the test
deciding it from truth tables never accepts the truth table of a member, but accepts that of a
uniformly random function with probability the density of the property
(`advantage_truthTableGenerator_truthTableTest`). A property decided by circuits with `t` gates
and useful against circuits with `s` gates therefore distinguishes every keyed family of functions
with `s` gates from uniformly random functions, by a circuit with `t` gates and with advantage its
density (`not_secure_truthTableGenerator`). Asymptotically, no `P/poly`-natural property is
useful against `P/poly` if some keyed family with members of polynomial circuit size is
*exponentially secure*, pseudorandom against circuits of size `2 ^ (c n)` with error `2 ^ (-c n)`
for every `c` (`Cslib.Crypto.PRG.IsExponentiallySecure`, `not_isUseful_PPoly_of_isNatural`).

Razborov and Rudich obtain such a family from a pseudorandom generator secure against circuits of
size `2 ^ (k ^ ε)` on seeds of length `k`, by the construction of Goldreich, Goldwasser and Micali
[GGM1986] with keys of length polynomial in `n`. That derivation, with its circuit-size analysis,
is `Cslib.Crypto.GGM.isExponentiallySecure_booleanFamily`, and the barrier from such a generator
is `Cslib.Circuits.Boolean.not_isUseful_PPoly_of_isNatural_of_generator`
(`Complexity.Computability.Circuit.Boolean.NaturalProof.Generator`).

Security is cslib's concrete security of generators (`Cslib.Crypto.PRG.Generator.Secure`), for the
generator mapping a key to the truth table of its function (`Cslib.Crypto.PRG.truthTableGenerator`),
against the deterministic tests computed by De Morgan circuits with at most `t` gates
(`Cslib.Crypto.PRG.IsCircuitTest`). These
tests read the whole truth table, that is they query the function at every input, as the
distinguisher of Razborov and Rudich does. Circuit sizes count every AND, OR, NOT and constant
gate.

The functions on `n` inputs that need more than `2 ^ n / (5 n)` gates form a property that is
large, by counting circuits, and useful against `P/poly` (`isLarge_setOf_lt_complexity`,
`isUseful_PPoly_setOf_lt_complexity`). Under the same hypothesis it is therefore not
`P/poly`-natural (`not_isNatural_PPoly_setOf_lt_complexity`), and not `P/poly`-constructive: its
truth tables, the no-instances of `GapMCSP` at threshold `2 ^ n / (5 n)`, do not form a language
in `P/poly` (`truthTableLanguage_setOf_lt_complexity_notMem_PPoly`) [KabanetsCai2000].

## Main definitions

* `Cslib.Circuits.Boolean.truthTableTest`: the test deciding a property from truth tables.
* `Cslib.Circuits.Boolean.truthTableLanguage`: the truth tables of a property, as a language.
* `Cslib.Circuits.Boolean.NaturalProof.IsLarge`, `Cslib.Circuits.Boolean.NaturalProof.IsNatural`,
  `Cslib.Circuits.Boolean.NaturalProof.IsUseful`: large, natural and useful properties.

## Main results

* `Cslib.Circuits.Boolean.isUseful_PPoly_iff`: usefulness against `P/poly` as a bound on the
  circuit complexity of every function with the property.
* `Cslib.Circuits.Boolean.NaturalProof.IsNatural.PPoly_of_P`: `P`-natural properties, decided
  in time polynomial in the length of the truth table, are `P/poly`-natural.
* `Cslib.Circuits.Boolean.advantage_truthTableGenerator_truthTableTest`: the advantage of the
  Razborov–Rudich distinguisher is the density of the property.
* `Cslib.Circuits.Boolean.not_secure_truthTableGenerator`: the barrier for one input length,
  with explicit sizes and advantage.
* `Cslib.Circuits.Boolean.not_isUseful_PPoly_of_isNatural`: the natural proofs barrier for
  `P/poly`, assuming an exponentially secure keyed family.
* `Cslib.Circuits.Boolean.isLarge_setOf_lt_complexity`,
  `Cslib.Circuits.Boolean.isUseful_PPoly_setOf_lt_complexity`: the functions needing more than
  `2 ^ n / (5 n)` gates form a large property useful against `P/poly`.
* `Cslib.Circuits.Boolean.not_isNatural_PPoly_setOf_lt_complexity`,
  `Cslib.Circuits.Boolean.truthTableLanguage_setOf_lt_complexity_notMem_PPoly`: under the same
  assumption, this property is not `P/poly`-natural, and the truth tables of these hard functions
  do not form a language in `P/poly`.

## References

* [A. A. Razborov, S. Rudich, *Natural proofs*][RazborovRudich1997]
* [O. Goldreich, S. Goldwasser, S. Micali, *How to construct random functions*][GGM1986]
* [V. Kabanets, J.-Y. Cai, *Circuit minimization problem*][KabanetsCai2000]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Filter MCSP
open Crypto.PRG (IsCircuitTest IsExponentiallySecure truthTableGenerator truthTableGenerator_apply)
open scoped NNReal Finset

variable {n : ℕ}

/-! ### Properties of Boolean functions -/

/-- The test that accepts the truth tables of the functions in `C`. Its circuit complexity is the
size of the smallest circuits deciding `C` from truth tables. -/
noncomputable def truthTableTest (C : Set (BooleanFunction n)) : BooleanFunction (2 ^ n) :=
  open scoped Classical in fun T => decide ((truthTable n).symm T ∈ C)

/-- `truthTableTest C` accepts a truth table `T` if and only if the function with truth table `T`
belongs to `C`. -/
@[simp] theorem truthTableTest_eq_true_iff {C : Set (BooleanFunction n)} {T : BitString (2 ^ n)} :
    truthTableTest C T = true ↔ (truthTable n).symm T ∈ C :=
  @decide_eq_true_iff _ (Classical.propDecidable _)

/-- `truthTableTest C` accepts the truth table of `f` if and only if `f ∈ C`. -/
theorem truthTableTest_truthTable_eq_true_iff {C : Set (BooleanFunction n)}
    {f : BooleanFunction n} : truthTableTest C (truthTable n f) = true ↔ f ∈ C := by
  rw [truthTableTest_eq_true_iff, Equiv.symm_apply_apply]

/-- The test deciding `C` accepts as many truth tables as there are functions in `C`. -/
private theorem card_filter_truthTableTest (C : Set (BooleanFunction n)) :
    #{T | truthTableTest C T = true} = C.ncard := by
  have h : ((({T | truthTableTest C T = true} : Finset (BitString (2 ^ n))) :
      Set (BitString (2 ^ n)))) = truthTable n '' C := by
    ext T
    obtain ⟨f, rfl⟩ := (truthTable n).surjective T
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      truthTableTest_truthTable_eq_true_iff, (truthTable n).injective.mem_set_image]
  rw [← Set.ncard_coe_finset, h, Set.ncard_image_of_injective _ (truthTable n).injective]

/-- The truth tables of a property, as a language [RazborovRudich1997]: a word of length `2 ^ n`
belongs to it when it is the truth table of a function in `C n`. Words whose length is not a power
of two do not belong to it. -/
def truthTableLanguage (C : ∀ n, Set (BooleanFunction n)) : Language Bool :=
  {w | ∃ n, ∃ h : w.length = 2 ^ n,
    (truthTable n).symm (fun i => w[(i : ℕ)]'(i.isLt.trans_eq h.symm)) ∈ C n}

/-- A `2 ^ n`-bit string `T`, viewed as a list via `List.ofFn`, belongs to `truthTableLanguage C`
if and only if its corresponding Boolean function lies in `C n`. -/
theorem ofFn_mem_truthTableLanguage {C : ∀ n, Set (BooleanFunction n)} {T : BitString (2 ^ n)} :
    List.ofFn T ∈ truthTableLanguage C ↔ (truthTable n).symm T ∈ C n := by
  constructor
  · rintro ⟨m, h, hm⟩
    obtain rfl : m = n :=
      Nat.pow_right_injective le_rfl (h.symm.trans (List.length_ofFn (f := T)))
    simpa only [List.getElem_ofFn] using hm
  · intro h
    exact ⟨n, List.length_ofFn, by simpa only [List.getElem_ofFn] using h⟩

/-- At length `2 ^ n`, the truth-table language of `C` is decided by the test for `C n`. -/
@[simp] theorem slice_truthTableLanguage (C : ∀ n, Set (BooleanFunction n)) (n : ℕ) :
    (truthTableLanguage C).slice (2 ^ n) = truthTableTest (C n) := by
  ext T
  rw [Bool.eq_iff_iff, Language.slice_eq_true_iff, ofFn_mem_truthTableLanguage,
    truthTableTest_eq_true_iff]

variable {Γ Γ' Λ Λ' : Set (Language Bool)} {C C' : ∀ n, Set (BooleanFunction n)}

namespace NaturalProof

/-- **Largeness** [RazborovRudich1997]: for some `c`, eventually at least a `2 ^ (-c n)` fraction
of the `2 ^ 2 ^ n` Boolean functions on `n` inputs lie in `C n`. -/
def IsLarge (C : ∀ n, Set (BooleanFunction n)) : Prop :=
  ∃ c, ∀ᶠ n in atTop, 2 ^ 2 ^ n ≤ 2 ^ (c * n) * (C n).ncard

/-- **Natural properties** [RazborovRudich1997]: `C` is `Γ`-natural when it contains a large
property whose truth tables form a language in `Γ`. For `Γ = PPoly` that property is decided by
circuits of size polynomial in the length `2 ^ n` of the truth table, that is of size
`2 ^ O(n)` (`exists_complexity_truthTableTest_le`). -/
def IsNatural (Γ : Set (Language Bool)) (C : ∀ n, Set (BooleanFunction n)) : Prop :=
  ∃ D : ∀ n, Set (BooleanFunction n), (∀ n, D n ⊆ C n) ∧ IsLarge D ∧ truthTableLanguage D ∈ Γ

/-- **Usefulness** [RazborovRudich1997]: `C` is useful against a class `Λ` of languages when the
slices of every language in `Λ` eventually lie outside `C`. Against `P/poly`, this says that for
every polynomial bound, eventually every function in `C n` needs more gates
(`isUseful_PPoly_iff`). -/
def IsUseful (Λ : Set (Language Bool)) (C : ∀ n, Set (BooleanFunction n)) : Prop :=
  ∀ L ∈ Λ, ∀ᶠ n in atTop, L.slice n ∉ C n

/-- Any property containing a large property at every input length is itself large. -/
theorem IsLarge.mono (hC : IsLarge C) (h : ∀ n, C n ⊆ C' n) : IsLarge C' := by
  obtain ⟨c, hc⟩ := hC
  exact ⟨c, hc.mono fun n hn => hn.trans (Nat.mul_le_mul_left _ (Set.ncard_le_ncard (h n)))⟩

/-- A larger class of deciders, or a larger property, keeps a property natural. -/
theorem IsNatural.mono (hC : IsNatural Γ C) (hΓ : Γ ⊆ Γ') (h : ∀ n, C n ⊆ C' n) :
    IsNatural Γ' C' := by
  obtain ⟨D, hDC, hlarge, hΓD⟩ := hC
  exact ⟨D, fun n => (hDC n).trans (h n), hlarge, hΓ hΓD⟩

/-- A smaller class, or a smaller property, keeps a property useful. -/
theorem IsUseful.anti (hC : IsUseful Λ C) (hΛ : Λ' ⊆ Λ) (h : ∀ n, C' n ⊆ C n) :
    IsUseful Λ' C' :=
  fun L hL => (hC L (hΛ hL)).mono fun _ hn hmem => hn (h _ hmem)

/-- If `Λ` contains `SIZE s`, with `s` positive, a property useful against `Λ` eventually holds
only for functions needing more than `s n` gates. -/
private theorem IsUseful.eventually_lt_complexity (hC : IsUseful Λ C) {s : ℕ → ℕ} (hΛ : SIZE s ⊆ Λ)
    (hs : ∀ n, 1 ≤ s n) :
    ∀ᶠ n in atTop, ∀ f ∈ C n, s n < complexity interpretation (single f) := by
  classical
  by_contra h
  rw [not_eventually] at h
  -- a language choosing, wherever possible, a function in `C n` with at most `s n` gates
  let g : ∀ n, BooleanFunction n := fun n =>
    if h : ∃ f ∈ C n, complexity interpretation (single f) ≤ s n then h.choose else fun _ => false
  have hg : Language.ofSlices g ∈ SIZE s := fun n => by
    rw [Language.slice_ofSlices]
    by_cases h : ∃ f ∈ C n, complexity interpretation (single f) ≤ s n
    · simpa only [g, dite_eq_left h] using h.choose_spec.2
    · simpa only [g, dite_eq_right h] using (Synthesis.const false).complexity_le.trans (hs n)
  obtain ⟨n, hn, hgn⟩ := (h.and_eventually (hC _ (hΛ hg))).exists
  have hex : ∃ f ∈ C n, complexity interpretation (single f) ≤ s n := by
    simpa only [not_forall, not_lt, exists_prop] using hn
  rw [Language.slice_ofSlices] at hgn
  exact hgn (by simpa only [g, dite_eq_left hex] using hex.choose_spec.1)

end NaturalProof

open NaturalProof

/-- **Usefulness against `P/poly`**, in the form of [RazborovRudich1997]: for every polynomially
bounded `s`, eventually every function in `C n` needs more than `s n` gates. -/
theorem isUseful_PPoly_iff :
    IsUseful PPoly C ↔ ∀ s : ℕ → ℕ, PolynomiallyBounded s →
      ∀ᶠ n in atTop, ∀ f ∈ C n, s n < complexity interpretation (single f) := by
  constructor
  · intro hC s hs
    filter_upwards [hC.eventually_lt_complexity (s := fun n => s n + 1)
      (fun L hL => (hs.add (PolynomiallyBounded.const 1)).mono_of_le hL)
      fun n => Nat.le_add_left _ _] with n hn f hf
    exact (Nat.lt_succ_self _).trans (hn f hf)
  · intro h L hL
    filter_upwards [h _ hL] with n hn hmem
    exact lt_irrefl _ (hn _ hmem)

/-- A `P/poly`-constructive property is decided by circuits of size `2 ^ O(n)`. -/
private theorem exists_complexity_truthTableTest_le (hC : truthTableLanguage C ∈ PPoly) :
    ∃ c, ∀ n, 1 ≤ n → complexity interpretation (single (truthTableTest (C n))) ≤ 2 ^ (c * n) := by
  obtain ⟨a, d, h⟩ := polynomiallyBounded_iff_le.1 hC
  refine ⟨a + 2 * d, fun n hn => ?_⟩
  have h1 := h (2 ^ n)
  rw [slice_truthTableLanguage] at h1
  refine h1.trans ?_
  calc a * (2 ^ n + 1) ^ d ≤ 2 ^ a * (2 ^ (n + 1)) ^ d := by
        gcongr
        · exact Nat.lt_two_pow_self.le
        · rw [pow_succ]
          have := Nat.one_le_two_pow (n := n)
          omega
    _ = 2 ^ (a + (n + 1) * d) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ ((a + 2 * d) * n) := Nat.pow_le_pow_right two_pos (by nlinarith)

/-- A property that is natural for the class `P`, applied to truth tables, is `P/poly`-natural:
a problem decided in time polynomial in the length of the truth table has circuits of polynomial
size (`PPoly.of_mem_P`). -/
theorem NaturalProof.IsNatural.PPoly_of_P
    (hC : IsNatural {L : Language Bool | (L : Set (List Bool)) ∈ Complexity.P
      Turing.MultiTapeTM.encBits} C) : IsNatural PPoly C :=
  hC.mono (fun _ hL => PPoly.of_mem_P hL) fun _ => le_rfl

/-! ### The Razborov–Rudich distinguisher -/

section Generator

variable {Key : Type*} [Fintype Key] [Nonempty Key]

/-- **The Razborov–Rudich distinguisher** [RazborovRudich1997, Section 4]. If no function of the
keyed family `F` lies in `C`, the test deciding `C` from truth tables never accepts the truth table
of `F key`, and accepts that of a uniformly random function with probability the density of `C`.
Its advantage is therefore exactly the density of `C`. -/
theorem advantage_truthTableGenerator_truthTableTest (F : Key → BooleanFunction n)
    {C : Set (BooleanFunction n)} (hF : ∀ key, F key ∉ C) :
    (truthTableGenerator F).advantage (fun T => PMF.pure (truthTableTest C T)) =
      C.ncard / 2 ^ 2 ^ n := by
  rw [Crypto.PRG.Generator.advantage, Crypto.PRG.Generator.toReal_realExperiment_pure,
    Crypto.PRG.Generator.toReal_idealExperiment_pure]
  have h0 : ({key | truthTableTest C (truthTableGenerator F key) = true} : Finset Key) = ∅ :=
    Finset.filter_false_of_mem fun key _ => by
      rw [truthTableGenerator_apply, truthTableTest_truthTable_eq_true_iff]
      exact hF key
  rw [h0, Finset.dens_empty, NNRat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (by positivity),
    Finset.dens_eq_card_div_card, card_filter_truthTableTest]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, NNRat.cast_div,
    NNRat.cast_natCast, NNRat.cast_pow, NNRat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat]

/-- **Natural properties break pseudorandom function families**, for one input length
[RazborovRudich1997, Section 4]. Let `C` be a property of functions on `n` inputs that is decided
from truth tables by circuits with at most `t` gates and holds for no function computable with at
most `s` gates. Then no keyed family of functions computable with at most `s` gates is
pseudorandom against circuits with at most `t` gates with error below the density of `C`. -/
theorem not_secure_truthTableGenerator {F : Key → BooleanFunction n} {C : Set (BooleanFunction n)}
    {s t : ℕ} {ε : ℝ≥0} (hconstructive : complexity interpretation (single (truthTableTest C)) ≤ t)
    (huseful : ∀ f ∈ C, s < complexity interpretation (single f))
    (hF : ∀ key, complexity interpretation (single (F key)) ≤ s)
    (hε : (ε : ℝ) < C.ncard / 2 ^ 2 ^ n) :
    ¬ (truthTableGenerator F).Secure (IsCircuitTest t) ε := by
  intro hsecure
  have h := hsecure _ ⟨_, hconstructive, rfl⟩
  rw [advantage_truthTableGenerator_truthTableTest F fun key hkey =>
    (huseful _ hkey).not_ge (hF key)] at h
  exact h.not_gt hε

end Generator

section Family

variable {Key : ℕ → Type*} [∀ n, Fintype (Key n)] [∀ n, Nonempty (Key n)]

/-- **The natural proofs barrier** for `P/poly` [RazborovRudich1997, Section 4]. Suppose that for
each `n` a keyed family `F n` of Boolean functions on `n` inputs has members with at most `s n`
gates, for a polynomially bounded `s`, and is exponentially secure: for every `c`, eventually no
circuit with at most `2 ^ (c n)` gates distinguishes the truth table of a member with a uniformly
random key from a uniformly random truth table with advantage more than `2 ^ (-c n)`. Then no
`P/poly`-natural property is useful against `P/poly`.

Razborov and Rudich derive such a family from a pseudorandom generator secure against circuits of
size `2 ^ (k ^ ε)` by the construction of Goldreich, Goldwasser and Micali with keys of length
polynomial in `n`: `Cslib.Circuits.Boolean.not_isUseful_PPoly_of_isNatural_of_generator`. -/
theorem not_isUseful_PPoly_of_isNatural {F : ∀ n, Key n → BooleanFunction n} {s : ℕ → ℕ}
    (hs : PolynomiallyBounded s) (hF : ∀ n key, complexity interpretation (single (F n key)) ≤ s n)
    (hsecure : IsExponentiallySecure F) (hC : IsNatural PPoly C) : ¬ IsUseful PPoly C := by
  intro huseful
  obtain ⟨D, hDC, ⟨a, ha⟩, hD⟩ := hC
  obtain ⟨b, hb⟩ := exists_complexity_truthTableTest_le hD
  obtain ⟨n, hn, hlarge, hn1, hsec⟩ := ((isUseful_PPoly_iff.1 (huseful.anti le_rfl hDC) s hs).and
    (ha.and ((eventually_ge_atTop 1).and (hsecure (a + b + 1))))).exists
  refine not_secure_truthTableGenerator ((hb n hn1).trans (Nat.pow_le_pow_right two_pos ?_)) hn
    (hF n) ?_ hsec
  · nlinarith
  -- the density of `D n` is at least `2 ^ (-a n)`, more than `2 ^ (-(a + b + 1) n)`
  have hdensity : ((2 : ℝ) ^ (a * n))⁻¹ ≤ (D n).ncard / 2 ^ 2 ^ n := by
    rw [le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
    exact_mod_cast hlarge
  refine lt_of_lt_of_le ?_ hdensity
  rw [NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_ofNat]
  exact (inv_lt_inv₀ (by positivity) (by positivity)).2
    (pow_lt_pow_right₀ one_lt_two (by nlinarith))

/-! ### Hard functions -/

/-- For `n ≥ 16`, at least half of the functions on `n` inputs need more than `2 ^ n / (5 n)`
gates, by counting circuits (`MCSP.ncard_setOf_mem_le`). -/
theorem two_pow_two_pow_le_two_mul_ncard_setOf_lt_complexity (hn : 16 ≤ n) :
    2 ^ 2 ^ n ≤ 2 * {f : BooleanFunction n |
      2 ^ n / (5 * n) < complexity interpretation (single f)}.ncard := by
  set s := 2 ^ n / (5 * n)
  have hyes : {T : BitString (2 ^ n) | ⟨n, T, s⟩ ∈ MCSP} =
      truthTable n '' {f | complexity interpretation (single f) ≤ s} := by
    ext T
    obtain ⟨f, rfl⟩ := (truthTable n).surjective T
    simp only [Set.mem_ofPred_eq, mk_truthTable_mem_iff, (truthTable n).injective.mem_set_image]
  have hle := ncard_setOf_mem_le (n := n) hn
  rw [hyes, Set.ncard_image_of_injective _ (truthTable n).injective] at hle
  have hsum := Set.ncard_add_ncard_compl {f : BooleanFunction n |
    complexity interpretation (single f) ≤ s}
  have hcompl : {f : BooleanFunction n | complexity interpretation (single f) ≤ s}ᶜ =
      {f | s < complexity interpretation (single f)} := by
    ext f
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  rw [hcompl, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin] at hsum
  have hquarter : 2 * 2 ^ (2 ^ n / 4) ≤ 2 ^ 2 ^ n := by
    rw [← pow_succ']
    refine Nat.pow_le_pow_right two_pos ?_
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right two_pos (by omega)
    omega
  linarith

/-- The functions on `n` inputs that need more than `2 ^ n / (5 n)` gates form a large property:
for `n ≥ 16` they are at least half of all functions. -/
theorem isLarge_setOf_lt_complexity :
    IsLarge fun n => {f : BooleanFunction n |
      2 ^ n / (5 * n) < complexity interpretation (single f)} := by
  refine ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop 16] with n hn
  refine (two_pow_two_pow_le_two_mul_ncard_setOf_lt_complexity hn).trans
    (Nat.mul_le_mul_right _ ?_)
  rw [one_mul]
  exact Nat.le_self_pow (by omega) 2

/-- Circuits of polynomial size eventually compute no function that needs more than
`2 ^ n / (5 n)` gates. -/
theorem isUseful_PPoly_setOf_lt_complexity :
    IsUseful PPoly fun n => {f : BooleanFunction n |
      2 ^ n / (5 * n) < complexity interpretation (single f)} := by
  refine isUseful_PPoly_iff.2 fun s hs => ?_
  have hpoly : PolynomiallyBounded fun n => 5 * n * (s n + 1) := by fun_prop
  filter_upwards [hpoly.eventually_lt_two_pow, eventually_ge_atTop 1] with n hn hn1 f hf
  have : s n < 2 ^ n / (5 * n) := by
    rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega), mul_comm]
    exact hn.le
  exact this.trans hf

/-- Under the hypothesis of `not_isUseful_PPoly_of_isNatural`, the truth tables of the functions
on `n` inputs that need more than `2 ^ n / (5 n)` gates, that is the no-instances
`GapMCSP.no (fun n => 2 ^ n / (5 * n)) n`, do not form a language in `P/poly`
[RazborovRudich1997], [KabanetsCai2000]. The property is large and useful against `P/poly`, so
it is not `P/poly`-constructive. -/
theorem truthTableLanguage_setOf_lt_complexity_notMem_PPoly {F : ∀ n, Key n → BooleanFunction n}
    {s : ℕ → ℕ} (hs : PolynomiallyBounded s)
    (hF : ∀ n key, complexity interpretation (single (F n key)) ≤ s n)
    (hsecure : IsExponentiallySecure F) :
    truthTableLanguage (fun n => {f : BooleanFunction n |
      2 ^ n / (5 * n) < complexity interpretation (single f)}) ∉ PPoly := fun hmem =>
  not_isUseful_PPoly_of_isNatural hs hF hsecure
    ⟨_, fun _ => le_rfl, isLarge_setOf_lt_complexity, hmem⟩ isUseful_PPoly_setOf_lt_complexity

/-- Under the hypothesis of `not_isUseful_PPoly_of_isNatural`, the property of needing more than
`2 ^ n / (5 n)` gates is not `P/poly`-natural: it is useful against `P/poly`
[RazborovRudich1997]. -/
theorem not_isNatural_PPoly_setOf_lt_complexity {F : ∀ n, Key n → BooleanFunction n}
    {s : ℕ → ℕ} (hs : PolynomiallyBounded s)
    (hF : ∀ n key, complexity interpretation (single (F n key)) ≤ s n)
    (hsecure : IsExponentiallySecure F) :
    ¬ IsNatural PPoly fun n => {f : BooleanFunction n |
      2 ^ n / (5 * n) < complexity interpretation (single f)} := fun hC =>
  not_isUseful_PPoly_of_isNatural hs hF hsecure hC isUseful_PPoly_setOf_lt_complexity

end Family

end Cslib.Circuits.Boolean
