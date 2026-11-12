/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.PIR.Cube

/-!
# Lower bound for two-server linear-summation schemes

A two-server scheme is of *linear-summation type* when each query is a set `q : ι → Bool`, each
server answers with the parity `x ⬝ᵥ q = ⊕_{j ∈ q} x j` of the database on its set, and the user
outputs the sum `b₀ + b₁` of the two answer bits (`Scheme.IsLinearSummation`). The basic scheme
`PIR.twoServer` is of this type (`PIR.isLinearSummation_twoServer`). For such schemes,
[Chor, Goldreich, Kushilevitz and Sudan, Section 5.2][ChorGoldreichKushilevitzSudan1998] shows that
privacy forces long queries: each server can receive at least `2 ^ (n - 1)` different sets.

* Correctness forces the two queries to add up to `eᵢ` (`IsLinearSummation.query_add_query`).
* With privacy, a set that the server `s` can receive becomes, after flipping one position, a set
  that the other server can receive (`IsLinearSummation.add_single_mem`). Hence every set at even
  (resp. odd) Hamming distance from a set possible for `s` is possible for `s` (resp. for the other
  server) (`IsLinearSummation.mem_support_add`). This is the Claim of Section 5.2.
* So each server can receive at least `2 ^ (n - 1)` sets
  (`IsLinearSummation.two_pow_le_ncard_support`), and any encoding of its queries by `ℓ`-bit
  strings that is injective on them needs `n - 1 ≤ ℓ` (`IsLinearSummation.card_sub_one_le`).

The bound is tight, as the note at the end of Section 5.2 observes. In the *even-set scheme*
`PIR.evenTwoServer`, the user draws a uniform set of even size, so each server receives one of the
`2 ^ (n - 1)` sets of a given parity (`PIR.ncard_support_evenTwoServer`). These sets have an
injective encoding by `n - 1` bits (`PIR.exists_injOn_evenTwoServer`).

The proofs use privacy only through supports: a set possible for the server `s` and the index `j`
is possible for `s` and every index `h`, as in observation 1 of the source.

Only linear-summation schemes are covered. Lower bounds for general two-server schemes are open in
the source and are not formalized here.

## Main definitions

* `Cslib.Crypto.Protocols.PIR.Scheme.IsLinearSummation`: two-server schemes of linear-summation
  type.
* `Cslib.Crypto.Protocols.PIR.evenTwoServer`: the even-set variant of the basic two-server scheme.

## Main results

* `Cslib.Crypto.Protocols.PIR.Scheme.IsLinearSummation.mem_support_add`: the Claim of Section 5.2.
* `Cslib.Crypto.Protocols.PIR.Scheme.IsLinearSummation.two_pow_le_ncard_support`,
  `Cslib.Crypto.Protocols.PIR.Scheme.IsLinearSummation.card_sub_one_le`: at least `2 ^ (n - 1)`
  queries, so `n - 1` bits, for each server.
* `Cslib.Crypto.Protocols.PIR.isCorrect_evenTwoServer`,
  `Cslib.Crypto.Protocols.PIR.isPrivate_evenTwoServer`,
  `Cslib.Crypto.Protocols.PIR.ncard_support_evenTwoServer`,
  `Cslib.Crypto.Protocols.PIR.exists_injOn_evenTwoServer`: the bound is attained.

## References

* [B. Chor, O. Goldreich, E. Kushilevitz, M. Sudan, *Private information
  retrieval*][ChorGoldreichKushilevitzSudan1998], Section 5.2; numbering of the authors' journal
  version of April 21, 1998
-/

public section

namespace Cslib.Crypto.Protocols.PIR

open Probability BitString Finset

namespace Scheme

variable {ι R : Type} [Fintype ι] [DecidableEq ι]

/-- A two-server scheme is of *linear-summation type*
[CGKS, Section 5.2][ChorGoldreichKushilevitzSudan1998] when the queries are sets `q : ι → Bool`,
each server answers with the parity `x ⬝ᵥ q` of the database on its set, and the user outputs the
sum of the two answer bits. -/
structure IsLinearSummation (P : Scheme ι Bool R (ι → Bool) Bool) : Prop where
  /-- Each server answers with the parity of the database on its set. -/
  answer_eq : ∀ s x q, P.answer s x q = x ⬝ᵥ q
  /-- The user adds the two answers. -/
  reconstruct_eq : ∀ i r a, P.reconstruct i r a = a false + a true

variable {P : Scheme ι Bool R (ι → Bool) Bool}

namespace IsLinearSummation

/-- A linear-summation scheme is correct exactly when the two queries always add up to `eᵢ`. -/
theorem isCorrect_iff (hP : P.IsLinearSummation) : P.IsCorrect ↔
    ∀ i r q, (r, q) ∈ (ProbComp.eval (P.query i)).support →
      q false + q true = Pi.single i true := by
  rw [P.isCorrect_iff]
  constructor
  · intro h i r q hrq
    funext j
    have := h (Pi.single j true) i r q hrq
    rw [hP.reconstruct_eq, hP.answer_eq, hP.answer_eq, ← dotProduct_add, single_dotProduct,
      Pi.single_apply] at this
    rw [Pi.single_apply]
    generalize (q false + q true) j = a at this ⊢
    by_cases hji : j = i
    · rw [ite_eq_left hji]
      rw [ite_eq_left hji.symm] at this
      revert this
      cases a <;> decide
    · rw [ite_eq_right hji]
      rw [ite_eq_right (Ne.symm hji)] at this
      revert this
      cases a <;> decide
  · intro h x i r q hrq
    rw [hP.reconstruct_eq, hP.answer_eq, hP.answer_eq, ← dotProduct_add, h i r q hrq]
    exact dotProduct_single_one x i

/-- In a correct linear-summation scheme, the two queries add up to `eᵢ`. -/
theorem query_add_query (hP : P.IsLinearSummation) (hcorrect : P.IsCorrect) {i : ι} {r : R}
    {q : Bool → ι → Bool} (hrq : (r, q) ∈ (ProbComp.eval (P.query i)).support) :
    q false + q true = Pi.single i true :=
  hP.isCorrect_iff.mp hcorrect i r q hrq

/-- Flipping one position of a set that the server `s` can receive gives a set that the other
server can receive [CGKS, Section 5.2][ChorGoldreichKushilevitzSudan1998]. By privacy, `v` can be
sent to `s` for the index `h`, and then the other query is `v + e_h`. -/
theorem add_single_mem (hP : P.IsLinearSummation) (hcorrect : P.IsCorrect)
    (hprivate : P.IsPrivate) {s : Bool} {i : ι} {v : ι → Bool}
    (hv : v ∈ (ProbComp.eval (P.serverQuery s i)).support) (h : ι) :
    v + Pi.single h true ∈ (ProbComp.eval (P.serverQuery (!s) i)).support := by
  rw [hprivate.eval_serverQuery_eq s i h, P.eval_serverQuery] at hv
  rw [hprivate.eval_serverQuery_eq (!s) i h, P.eval_serverQuery]
  obtain ⟨⟨r, q⟩, hrq, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hv
  refine (PMF.mem_support_map_iff _ _ _).2 ⟨(r, q), hrq, ?_⟩
  have hsum := hP.query_add_query hcorrect hrq
  funext j
  have hj := congrFun hsum j
  rw [Pi.add_apply] at hj
  change q (!s) j = q s j + (Pi.single h true : ι → Bool) j
  rw [← hj]
  cases s
  · change q true j = q false j + (q false j + q true j)
    rw [← add_assoc, BooleanRing.add_self, zero_add]
  · change q false j = q true j + (q false j + q true j)
    rw [add_comm (q false j), ← add_assoc, BooleanRing.add_self, zero_add]

omit [DecidableEq ι] in
/-- **The Claim of [CGKS, Section 5.2][ChorGoldreichKushilevitzSudan1998].** In a correct, private
linear-summation scheme, if the server `s` can receive `v`, then every set `w` can be received by
the server `s` if its Hamming distance to `v` is even and by the other server if it is odd: by the
server `s + ∑ h, (w h + v h)`. -/
theorem mem_support_add (hP : P.IsLinearSummation) (hcorrect : P.IsCorrect)
    (hprivate : P.IsPrivate) {s : Bool} {i : ι} {v : ι → Bool}
    (hv : v ∈ (ProbComp.eval (P.serverQuery s i)).support) (w : ι → Bool) :
    w ∈ (ProbComp.eval (P.serverQuery (s + ∑ h, (w h + v h)) i)).support := by
  classical
  -- Flip the positions of `D` where `w` and `v` differ, one at a time.
  have key (D : Finset ι) : v + ∑ h ∈ D, Pi.single h (w h + v h) ∈
      (ProbComp.eval (P.serverQuery (s + ∑ h ∈ D, (w h + v h)) i)).support := by
    induction D using Finset.induction_on with
    | empty => simpa only [sum_empty, add_zero] using hv
    | insert a D ha ih =>
      rw [sum_insert ha, sum_insert ha]
      rw [show v + (Pi.single a (w a + v a) + ∑ h ∈ D, Pi.single h (w h + v h)) =
          (v + ∑ h ∈ D, Pi.single h (w h + v h)) + Pi.single a (w a + v a) by abel,
        show s + (w a + v a + ∑ h ∈ D, (w h + v h)) =
          (s + ∑ h ∈ D, (w h + v h)) + (w a + v a) by abel]
      cases w a + v a
      · rw [show ∀ b : Bool, b + false = b from Bool.xor_false,
          show (Pi.single a false : ι → Bool) = 0 from Pi.single_zero a, add_zero]
        exact ih
      · rw [show ∀ b : Bool, b + true = !b from Bool.xor_true]
        exact hP.add_single_mem hcorrect hprivate ih a
  have h := key univ
  rwa [univ_sum_single (fun h => w h + v h),
    show v + (fun h => w h + v h) = w from funext fun h => by
      rw [Pi.add_apply, add_comm (w h), ← add_assoc, BooleanRing.add_self, zero_add]] at h

omit [DecidableEq ι] in
/-- In a correct, private linear-summation scheme, the server `s` can receive at least half of all
sets. -/
theorem two_pow_le_two_mul_ncard_support (hP : P.IsLinearSummation) (hcorrect : P.IsCorrect)
    (hprivate : P.IsPrivate) (s : Bool) (i : ι) :
    2 ^ Fintype.card ι ≤ 2 * (ProbComp.eval (P.serverQuery s i)).support.ncard := by
  classical
  let T : Bool → Set (ι → Bool) := fun t => (ProbComp.eval (P.serverQuery t i)).support
  change 2 ^ Fintype.card ι ≤ 2 * (T s).ncard
  obtain ⟨v, hv⟩ := (ProbComp.eval (P.serverQuery s i)).support_nonempty
  have hpos : 0 < (T s).ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨v, hv⟩
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨h₀⟩⟩
  · rw [Fintype.card_eq_zero, pow_zero]
    omega
  -- Every set can be received by `s` or by the other server.
  have hcover : (Set.univ : Set (ι → Bool)) ⊆ T s ∪ T (!s) := by
    intro w _
    have hw := hP.mem_support_add hcorrect hprivate hv w
    cases hsum : ∑ h, (w h + v h)
    · rw [hsum, show ∀ b : Bool, b + false = b from Bool.xor_false] at hw
      exact Or.inl hw
    · rw [hsum, show ∀ b : Bool, b + true = !b from Bool.xor_true] at hw
      exact Or.inr hw
  -- Flipping the position `h₀` maps the sets of the other server into those of `s`.
  have hflip : (T (!s)).ncard ≤ (T s).ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun w => w + Pi.single h₀ true) ?_ ?_
    · intro w hw
      have := hP.add_single_mem hcorrect hprivate hw h₀
      rwa [Bool.not_not] at this
    · intro w _ w' _ hww'
      exact add_right_cancel hww'
  have huniv := (Set.ncard_le_ncard hcover).trans (Set.ncard_union_le _ _)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool] at huniv
  omega

omit [DecidableEq ι] in
/-- **Each server of a correct, private linear-summation scheme can receive at least `2 ^ (n - 1)`
sets** [CGKS, Section 5.2][ChorGoldreichKushilevitzSudan1998]. -/
theorem two_pow_le_ncard_support (hP : P.IsLinearSummation) (hcorrect : P.IsCorrect)
    (hprivate : P.IsPrivate) (s : Bool) (i : ι) :
    2 ^ (Fintype.card ι - 1) ≤ (ProbComp.eval (P.serverQuery s i)).support.ncard := by
  have h := hP.two_pow_le_two_mul_ncard_support hcorrect hprivate s i
  have hn : Fintype.card ι - 1 + 1 = Fintype.card ι :=
    Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ⟨i⟩)
  rw [← hn, pow_succ] at h
  omega

omit [DecidableEq ι] in
/-- **The queries of each server of a correct, private linear-summation scheme need `n - 1`
bits** [CGKS, Section 5.2][ChorGoldreichKushilevitzSudan1998]: an encoding by `ℓ`-bit strings that
is injective on the sets the server can receive has `n - 1 ≤ ℓ`. -/
theorem card_sub_one_le (hP : P.IsLinearSummation) (hcorrect : P.IsCorrect)
    (hprivate : P.IsPrivate) (s : Bool) (i : ι) {ℓ : ℕ} {enc : (ι → Bool) → BitString ℓ}
    (henc : Set.InjOn enc (ProbComp.eval (P.serverQuery s i)).support) :
    Fintype.card ι - 1 ≤ ℓ := by
  have h := (hP.two_pow_le_ncard_support hcorrect hprivate s i).trans
    (Set.ncard_le_ncard_of_injOn enc (fun _ _ => Set.mem_univ _) henc)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h

end IsLinearSummation

end Scheme

section TwoServer

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The basic two-server scheme is of linear-summation type.** -/
theorem isLinearSummation_twoServer : (twoServer ι).IsLinearSummation where
  answer_eq σ x q := by rw [answer_twoServer, hadamardCode_apply]
  reconstruct_eq := reconstruct_twoServer

/-! ### The even-set scheme -/

variable (h₀ : ι)

/-- Make a set even by flipping the position `h₀` if needed. -/
private def makeEven (u : ι → Bool) : ι → Bool :=
  u + Pi.single h₀ (∑ h, u h)

private theorem sum_makeEven (u : ι → Bool) : ∑ h, makeEven h₀ u h = false := by
  simp only [makeEven, Pi.add_apply, sum_add_distrib, sum_pi_single', mem_univ, ite_true]
  exact BooleanRing.add_self _

private theorem makeEven_add_single (u : ι → Bool) (i : ι) (b : Bool) :
    makeEven h₀ (u + Pi.single i b) = makeEven h₀ u + Pi.single i b + Pi.single h₀ b := by
  have hsum : ∑ h, (u + Pi.single i b : ι → Bool) h = ∑ h, u h + b := by
    simp only [Pi.add_apply, sum_add_distrib, sum_pi_single', mem_univ, ite_true]
  rw [makeEven, makeEven, hsum, Pi.single_add]
  abel

/-- The even-set variant of the basic two-server scheme
[CGKS, Section 5.2][ChorGoldreichKushilevitzSudan1998]. The user draws a uniform set `t` of even
size (by making a uniform set even at `h₀`), sends `t` to the server `false` and `t + eᵢ` to the
server `true`, and adds the answers `x ⬝ᵥ t` and `x ⬝ᵥ (t + eᵢ)`. -/
noncomputable def evenTwoServer : Scheme ι Bool Unit (ι → Bool) Bool where
  query i := do
    let u ← ProbComp.uniform (ι → Bool)
    pure ((), fun σ => makeEven h₀ u + Pi.single i σ)
  answer _ x a := x ⬝ᵥ a
  reconstruct _ _ a := a false + a true

private theorem eval_serverQuery_evenTwoServer (σ : Bool) (i : ι) :
    ProbComp.eval ((evenTwoServer h₀).serverQuery σ i) =
      (PMF.uniformOfFintype (ι → Bool)).map fun u => makeEven h₀ u + Pi.single i σ := by
  rw [Scheme.eval_serverQuery, evenTwoServer]
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.map_bind,
    PMF.pure_map]
  rfl

theorem isLinearSummation_evenTwoServer : (evenTwoServer h₀).IsLinearSummation where
  answer_eq _ _ _ := rfl
  reconstruct_eq _ _ _ := rfl

/-- **The even-set scheme is correct**: the two queries add up to `eᵢ`. -/
theorem isCorrect_evenTwoServer : (evenTwoServer h₀).IsCorrect := by
  rw [(isLinearSummation_evenTwoServer h₀).isCorrect_iff]
  intro i r q hrq
  simp only [evenTwoServer, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hrq
  obtain ⟨u, -, -, rfl⟩ := hrq
  funext j
  change (makeEven h₀ u + (Pi.single i false : ι → Bool)) j +
      (makeEven h₀ u + (Pi.single i true : ι → Bool)) j = (Pi.single i true : ι → Bool) j
  rw [show (Pi.single i false : ι → Bool) = 0 from Pi.single_zero i, add_zero, Pi.add_apply,
    ← add_assoc, BooleanRing.add_self, zero_add]

/-- **The even-set scheme is private**: the server `σ` receives the uniform even set made odd at
`h₀` if `σ = true`, whatever the index. -/
theorem isPrivate_evenTwoServer : (evenTwoServer h₀).IsPrivate := by
  rw [Scheme.isPrivate_iff]
  -- Substituting `u + eᵢ • σ` for `u` removes the index.
  have key (σ : Bool) (i : ι) : ProbComp.eval ((evenTwoServer h₀).serverQuery σ i) =
      (PMF.uniformOfFintype (ι → Bool)).map fun u => makeEven h₀ u + Pi.single h₀ σ := by
    rw [eval_serverQuery_evenTwoServer]
    conv_lhs => rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv
      (Equiv.addRight (Pi.single i σ : ι → Bool)), PMF.map_comp]
    congr 1 with u : 1
    change makeEven h₀ (u + Pi.single i σ) + Pi.single i σ = makeEven h₀ u + Pi.single h₀ σ
    rw [makeEven_add_single]
    funext j
    simp only [Pi.add_apply]
    generalize makeEven h₀ u j = a
    generalize (Pi.single i σ : ι → Bool) j = b
    generalize (Pi.single h₀ σ : ι → Bool) j = c
    revert a b c
    decide
  intro σ i i'
  rw [key, key]

/-- The sets that the server `σ` of the even-set scheme receives have parity `σ`. -/
theorem sum_of_mem_support_evenTwoServer {σ : Bool} {i : ι} {v : ι → Bool}
    (hv : v ∈ (ProbComp.eval ((evenTwoServer h₀).serverQuery σ i)).support) : ∑ h, v h = σ := by
  rw [eval_serverQuery_evenTwoServer] at hv
  obtain ⟨u, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hv
  simp only [Pi.add_apply, sum_add_distrib, sum_makeEven, sum_pi_single', mem_univ, ite_true]
  exact zero_add σ

omit [DecidableEq ι] in
/-- Sets of the same parity that agree outside `h₀` are equal. -/
private theorem injOn_restrict_of_sum_eq (σ : Bool) :
    Set.InjOn (fun v : ι → Bool => fun h : {h // h ≠ h₀} => v h) {v | ∑ h, v h = σ} := by
  classical
  intro v hv w hw hvw
  funext h
  by_cases hh : h = h₀
  · subst hh
    have hv' : ∑ j, v j = σ := hv
    have hw' : ∑ j, w j = σ := hw
    rw [Fintype.sum_eq_add_sum_compl h] at hv' hw'
    have hrest : ∑ j ∈ {h}ᶜ, v j = ∑ j ∈ {h}ᶜ, w j := by
      refine sum_congr rfl fun j hj => ?_
      exact congrFun hvw ⟨j, by simpa only [mem_compl, mem_singleton] using hj⟩
    rw [hrest] at hv'
    exact add_right_cancel (hv'.trans hw'.symm)
  · exact congrFun hvw ⟨h, hh⟩

/-- **The lower bound is attained** [CGKS, Section 5.2][ChorGoldreichKushilevitzSudan1998]: each
server of the even-set scheme receives exactly `2 ^ (n - 1)` sets. -/
theorem ncard_support_evenTwoServer (σ : Bool) (i : ι) :
    (ProbComp.eval ((evenTwoServer h₀).serverQuery σ i)).support.ncard =
      2 ^ (Fintype.card ι - 1) := by
  refine le_antisymm ?_ ((isLinearSummation_evenTwoServer h₀).two_pow_le_ncard_support
    (isCorrect_evenTwoServer h₀) (isPrivate_evenTwoServer h₀) σ i)
  have h := Set.ncard_le_ncard_of_injOn
    (s := (ProbComp.eval ((evenTwoServer h₀).serverQuery σ i)).support) (t := Set.univ)
    (fun v : ι → Bool => fun h : {h // h ≠ h₀} => v h) (fun _ _ => Set.mem_univ _)
    ((injOn_restrict_of_sum_eq h₀ σ).mono fun v hv => sum_of_mem_support_evenTwoServer h₀ hv)
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq] at h

/-- `n - 1` bits encode the queries of each server of the even-set scheme: one encoding, for
every index. -/
theorem exists_injOn_evenTwoServer (σ : Bool) :
    ∃ enc : (ι → Bool) → BitString (Fintype.card ι - 1),
      ∀ i, Set.InjOn enc (ProbComp.eval ((evenTwoServer h₀).serverQuery σ i)).support := by
  have hcard : Fintype.card {h // h ≠ h₀} = Fintype.card ι - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨fun v k => v (e.symm k), fun i => ?_⟩
  intro v hv w hw hvw
  refine injOn_restrict_of_sum_eq h₀ σ (sum_of_mem_support_evenTwoServer h₀ hv)
    (sum_of_mem_support_evenTwoServer h₀ hw) (funext fun h => ?_)
  have := congrFun hvw (e h)
  simpa only [Equiv.symm_apply_apply] using this

end TwoServer

end Cslib.Crypto.Protocols.PIR
