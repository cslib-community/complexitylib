/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Demand
public import Complexity.Computability.Circuit.Frontier.Reduction
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Average-case frontier lower bounds

Let `S ⊆ U^n` have density within `b` of `1/2` on rectangles with both sides of size at least
`K` (`RectangleBias`). A circuit splits the inputs into those it accepts and those it rejects,
and each part is the accepted set of a constraint network whose branching program is
unambiguous. Peeling (`Cslib.Circuits.Frontier.Network.abs_signedCount_accepted_le`) shows that on
each part, too, the density of `S` is within `b` of `1/2`, up to a residual of `(K - 1) ^ 2` times
the size of the program. So the circuit agrees with `S` on at most a `1/2 + b` fraction of the
inputs plus the residual (`agreement_le_of_layout`). A circuit that leaves inputs carrying `K`
assignments unread is handled directly (`agreement_le_of_unread`).

Below `(1 + 1/A - ε) n` inner gates, the layout hypothesis `LayoutBound 3 A` makes the program
exponentially smaller than the `|U| ^ n` inputs (`eventually_add_lt_of_le`), so the residual is an
exponentially small fraction (`averageCaseBound_of_layoutBound`).

**The average-case claim** (`AverageCaseBound L`). For every `ε > 0` there is a `γ > 0`, uniform
over the alphabet and all admissible families, such that every circuit of fan-in at most two with
at most `(L - ε) n` gates of positive arity agrees with `S_n` on at most a
`1/2 + b_n + exp (-γ n)` fraction of inputs, whenever `S_n` has bias at most `b_n` on rectangles
with both sides of size at least `K_n` and `log K_n = o(n)`.

## Main definitions

* `Cslib.Circuits.Frontier.agreement S T`: the fraction of inputs on which membership in `S` and
  in `T` agree.
* `Cslib.Circuits.Frontier.correlation S T`: agreement minus disagreement.
* `Cslib.Circuits.Frontier.AverageCaseBound L`: the average-case claim with coefficient `L`.

## Main results

* `Cslib.Circuits.Frontier.correlation_eq_two_mul_agreement_sub_one`: on finite inputs over a
  nonempty alphabet, correlation is twice agreement minus one.
* `Cslib.Circuits.Frontier.correlation_mul_card_eq_sum`: correlation as a signed sum.
* `Cslib.Circuits.Frontier.agreement_le`: agreement from the bias on a set and its complement.
* `Cslib.Circuits.Frontier.agreement_le_of_layout`,
  `Cslib.Circuits.Frontier.agreement_le_of_unread`: the agreement of one circuit.
* `Cslib.Circuits.Frontier.averageCaseBound_of_layoutBound`: the average-case claim with
  coefficient `1 + 1/A` under the layout hypothesis `LayoutBound 3 A`.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set Filter Asymptotics
open scoped Finset

universe u v

/-- The *agreement* of two sets of inputs: the fraction of inputs on which membership in `S` and
membership in `T` agree. -/
noncomputable def agreement {ι U : Type*} (S T : Set (ι → U)) : ℝ :=
  ({x | x ∈ S ↔ x ∈ T}.ncard : ℝ) / Nat.card (ι → U)

section Correlation

variable {ι U : Type*}

/-! ### Correlation -/

/-- The *correlation* of two sets of inputs: the fraction of inputs on which membership in `S` and
membership in `T` agree, minus the fraction on which it differs. -/
noncomputable def correlation (S T : Set (ι → U)) : ℝ :=
  agreement S T - agreement S Tᶜ

/-- Complementing the second set negates the correlation. -/
@[simp]
theorem correlation_compl_right (S T : Set (ι → U)) : correlation S Tᶜ = -correlation S T := by
  rw [correlation, correlation, compl_compl, neg_sub]

section Finite

variable [Finite ι] [Finite U]

/-- Membership in `S` agrees with membership in `T` or with membership in `Tᶜ`. -/
private theorem agreement_add_agreement_compl [Nonempty U] (S T : Set (ι → U)) :
    agreement S T + agreement S Tᶜ = 1 := by
  have hN : (0 : ℝ) < Nat.card (ι → U) := by exact_mod_cast Nat.card_pos
  have hcompl : {x : ι → U | x ∈ S ↔ x ∈ Tᶜ} = {x | x ∈ S ↔ x ∈ T}ᶜ := by
    ext x
    simp only [mem_compl_iff, mem_ofPred_eq]
    tauto
  rw [agreement, agreement, hcompl, ← add_div, div_eq_one_iff_eq hN.ne']
  exact_mod_cast ncard_add_ncard_compl _

/-- **Correlation and agreement.** The correlation of `S` and `T` is `2 · agreement S T - 1`. -/
theorem correlation_eq_two_mul_agreement_sub_one [Nonempty U] (S T : Set (ι → U)) :
    correlation S T = 2 * agreement S T - 1 := by
  rw [correlation]
  linarith [agreement_add_agreement_compl S T]

/-- The correlation is at most one in absolute value. -/
theorem abs_correlation_le_one [Nonempty U] (S T : Set (ι → U)) : |correlation S T| ≤ 1 := by
  have h₁ : 0 ≤ agreement S T := by unfold agreement; positivity
  have h₂ : 0 ≤ agreement S Tᶜ := by unfold agreement; positivity
  rw [correlation, abs_le]
  constructor <;> linarith [agreement_add_agreement_compl S T]

/-- A correlation of absolute value at most `ε` is an agreement of at most `(1 + ε) / 2`. -/
theorem agreement_le_of_abs_correlation_le [Nonempty U] {S T : Set (ι → U)} {ε : ℝ}
    (h : |correlation S T| ≤ ε) : agreement S T ≤ 1 / 2 + ε / 2 := by
  rw [correlation_eq_two_mul_agreement_sub_one] at h
  linarith [le_abs_self (2 * agreement S T - 1)]

end Finite

/-- The correlation, scaled by the number of inputs, is the sum of `±1` over the inputs: `+1` where
membership in `S` and in `T` agree and `-1` where it differs. -/
theorem correlation_mul_card_eq_sum [Fintype ι] [Fintype U] [DecidableEq ι] [Nonempty U]
    (S T : Set (ι → U)) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] :
    correlation S T * Fintype.card (ι → U) =
      ∑ x, if (x ∈ S ↔ x ∈ T) then (1 : ℝ) else -1 := by
  have hN : (0 : ℝ) < Fintype.card (ι → U) := by exact_mod_cast Fintype.card_pos
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun x : ι → U => x ∈ S ↔ x ∈ T)
  rw [Finset.card_univ] at hsplit
  have hagree : agreement S T * Fintype.card (ι → U) =
      (Finset.univ.filter fun x : ι → U => x ∈ S ↔ x ∈ T).card := by
    rw [agreement, Nat.card_eq_fintype_card, div_mul_cancel₀ _ hN.ne', ncard_eq_toFinset_card',
      Set.toFinset_ofPred]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one,
    mul_neg_one, correlation_eq_two_mul_agreement_sub_one, sub_mul, mul_assoc, hagree]
  have : ((Finset.univ.filter fun x : ι → U => x ∈ S ↔ x ∈ T).card : ℝ) +
      (Finset.univ.filter fun x : ι → U => ¬(x ∈ S ↔ x ∈ T)).card = Fintype.card (ι → U) := by
    exact_mod_cast hsplit
  linarith

end Correlation

/-- **Agreement from bias.** If `S` has bias at most `β` on `T` and on its complement, up to the
residuals `R₁` and `R₂`, then membership in `S` and in `T` agree on at most a
`(1 + β)/2 + (R₁ + R₂)/(2 N)` fraction of the `N` inputs. -/
theorem agreement_le {ι U : Type*} [Finite ι] [Finite U] [Nonempty U] {S T : Set (ι → U)}
    {β R₁ R₂ : ℝ} (h₁ : |signedCount S T| ≤ β * T.ncard + R₁)
    (h₂ : |signedCount S Tᶜ| ≤ β * Tᶜ.ncard + R₂) :
    agreement S T ≤ (1 + β) / 2 + (R₁ + R₂) / (2 * Nat.card (ι → U)) := by
  have hN : (0 : ℝ) < Nat.card (ι → U) := by exact_mod_cast Nat.card_pos
  -- The agreeing inputs are those of `T` in `S` and those of `Tᶜ` outside `S`.
  have hagree : {x | x ∈ S ↔ x ∈ T} = (T ∩ S) ∪ (Tᶜ \ S) := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, Set.mem_sdiff, mem_compl_iff]
    tauto
  have hdisj : Disjoint (T ∩ S) (Tᶜ \ S) := disjoint_left.mpr fun x hx hx' => hx'.1 hx.1
  have hcard : ({x | x ∈ S ↔ x ∈ T}.ncard : ℝ) = (T ∩ S).ncard + (Tᶜ \ S).ncard := by
    rw [hagree, ncard_union_eq hdisj]
    push_cast
    ring
  have hT : ((T ∩ S).ncard : ℝ) + (T \ S).ncard = T.ncard := by
    exact_mod_cast ncard_inter_add_ncard_sdiff_eq_ncard T S
  have hTc : ((Tᶜ ∩ S).ncard : ℝ) + (Tᶜ \ S).ncard = Tᶜ.ncard := by
    exact_mod_cast ncard_inter_add_ncard_sdiff_eq_ncard Tᶜ S
  have htotal : (T.ncard : ℝ) + Tᶜ.ncard = Nat.card (ι → U) := by
    exact_mod_cast ncard_add_ncard_compl T
  have hs₁ := le_abs_self (signedCount S T)
  have hs₂ := neg_abs_le (signedCount S Tᶜ)
  have e₁ : signedCount S T = (T ∩ S).ncard - (T \ S).ncard := rfl
  have e₂ : signedCount S Tᶜ = (Tᶜ ∩ S).ncard - (Tᶜ \ S).ncard := rfl
  have hβ : β * T.ncard + β * Tᶜ.ncard = β * Nat.card (ι → U) := by rw [← htotal]; ring
  rw [agreement, div_le_iff₀ hN, hcard]
  have hRHS : ((1 + β) / 2 + (R₁ + R₂) / (2 * Nat.card (ι → U))) * Nat.card (ι → U) =
      (1 + β) / 2 * Nat.card (ι → U) + (R₁ + R₂) / 2 := by
    field_simp
  rw [hRHS]
  linarith

/-- A count whose base-`q` logarithm is at most `(1 - μ) n` is at most an
`exp (-μ log 2 · n)` fraction of `q ^ n`, for `q ≥ 2`. -/
private theorem div_pow_le_exp {q R μ : ℝ} {n : ℕ} (hq : 2 ≤ q) (hR : 0 < R) (hμ : 0 ≤ μ)
    (h : Real.logb q R ≤ (1 - μ) * n) : R / q ^ n ≤ Real.exp (-(μ * Real.log 2 * n)) := by
  have hq0 : 0 < q := by linarith
  have hlq : Real.log 2 ≤ Real.log q := Real.log_le_log two_pos hq
  have hlq0 : 0 < Real.log q := Real.log_pos (by linarith)
  have hlogR : Real.log R ≤ (1 - μ) * n * Real.log q := by
    rwa [Real.logb, div_le_iff₀ hlq0] at h
  have hexp : R / q ^ n = Real.exp (Real.log R - n * Real.log q) := by
    rw [Real.exp_sub, Real.exp_log hR, ← Real.log_pow, Real.exp_log (pow_pos hq0 n)]
  rw [hexp, Real.exp_le_exp]
  nlinarith [mul_nonneg hμ (Nat.cast_nonneg (α := ℝ) n)]

/-- `log_q (K ^ 3 (v + 1) q ^ (w + 4)) = w + 4 + 3 log_q K + log_q (v + 1)`. -/
private theorem logb_residual {q K v : ℝ} (hq : 1 < q) (hK : 0 < K) (hv : 0 ≤ v) (w : ℕ) :
    Real.logb q (K ^ 3 * (v + 1) * q ^ (w + 4)) =
      w + 4 + 3 * Real.logb q K + Real.logb q (v + 1) := by
  have hq0 : 0 < q := by linarith
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity)
    (by positivity), Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hq]
  push_cast
  ring

/-- Raising a threshold to at least two keeps its logarithm sublinear. -/
private theorem isLittleO_logb_max_two {K : ℕ → ℕ}
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ)) (q : ℝ) :
    (fun n => Real.logb q (max (K n) 2 : ℕ)) =o[atTop] fun n => (n : ℝ) := by
  have hK' : (fun n => Real.log (max (K n) 2 : ℕ)) =o[atTop] fun n => (n : ℝ) := by
    refine IsBigO.trans_isLittleO (g := fun n => ‖Real.log (K n)‖ + Real.log 2) ?_
      (hK.norm_left.add (isLittleO_const_id_atTop _).natCast_atTop)
    refine IsBigO.of_bound' (Eventually.of_forall fun n => ?_)
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
    have hK2 : (2 : ℝ) ≤ (max (K n) 2 : ℕ) := by exact_mod_cast le_max_right (K n) 2
    rw [Real.norm_of_nonneg (Real.log_nonneg (by linarith)),
      Real.norm_of_nonneg (by positivity)]
    rcases le_total (K n) 2 with h | h
    · rw [max_eq_right h]
      push_cast
      linarith [norm_nonneg (Real.log (K n))]
    · rw [max_eq_left h]
      linarith [Real.le_norm_self (Real.log (K n))]
  exact (hK'.const_mul_left (1 / Real.log q)).congr_left fun n => by
    simp only [Real.logb]
    ring

/-- If `1 + 2 log_q K ≤ n / 2`, then half of `n` coordinates carry at least `K` assignments:
`K ≤ q ^ ⌊n / 2⌋`. -/
private theorem le_pow_half_of_logb {q K n : ℕ} (hq : 1 < q) (hK : 0 < K)
    (h : 1 + 2 * Real.logb q K ≤ (1 - 1 / 2) * n) : K ≤ q ^ (n / 2) := by
  have hn2 : (n : ℝ) ≤ 2 * (n / 2 : ℕ) + 1 := by
    exact_mod_cast (show n ≤ 2 * (n / 2) + 1 by omega)
  have hlogb : Real.logb q K ≤ (n / 2 : ℕ) := by
    linarith [Nat.cast_nonneg (α := ℝ) (n / 2)]
  have := (Real.logb_le_iff_le_rpow (by exact_mod_cast hq) (by exact_mod_cast hK)).mp hlogb
  rw [Real.rpow_natCast] at this
  exact_mod_cast this

/-- There are `|U| ^ n` inputs. -/
private theorem card_input_eq {U : Type*} (n : ℕ) :
    (Nat.card (Fin n → U) : ℝ) = (Nat.card U : ℝ) ^ n := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
  push_cast
  rfl

section Circuit

variable {U : Type u} {σ : Signature.{v}} {n : ℕ} (I : Interpretation σ U) (Acc : Set U)
  (c : Circuit σ n 1)

/-- The inputs on which the output of a circuit lies in `Acc` are the accepted inputs of its
constraint network. -/
theorem accepted_network_eq_eval :
    (Compiler.network c I fun _ => Acc).accepted = {x | c.eval I x 0 ∈ Acc} :=
  accepted_network_of_decides fun _ => Iff.rfl

variable [Finite U] [Nontrivial U]

/-- **A circuit that leaves many inputs unread.** If the inputs a circuit does not read carry
at least `K ≥ 1` assignments, it agrees with a set `S` of bias at most `b ≥ 0` on large
rectangles on at most a `1/2 + b + |U| K ^ 2 / |U| ^ n` fraction of the inputs. -/
theorem agreement_le_of_unread {S : Set (Fin n → U)} {K : ℕ} {b : ℝ}
    (hS : RectangleBias S K b) (hb : 0 ≤ b) (hK : 1 ≤ K)
    (hu : K ≤ Nat.card U ^ (Compiler.network c I fun _ => Acc).readᶜ.ncard) :
    agreement S {x | c.eval I x 0 ∈ Acc} ≤
      1 / 2 + b + (Nat.card U * K ^ 2 : ℕ) / (Nat.card U : ℝ) ^ n := by
  have bound (A : Set U) := hS.abs_signedCount_le_of_dependsOn hb
    (Compiler.network c I fun _ => A).dependsOn_read hK hu
  have h₁ := bound Acc
  have h₂ := bound Accᶜ
  rw [accepted_network_eq_eval] at h₁ h₂
  have hN : (0 : ℝ) < (Nat.card U : ℝ) ^ n := by
    have : 0 < Nat.card U := Nat.card_pos
    positivity
  refine (agreement_le h₁ h₂).trans (le_of_eq ?_)
  rw [card_input_eq]
  field_simp
  ring

/-- **A circuit with a narrow layout.** Let the inputs a circuit of fan-in at most two does not
read carry fewer than `K` assignments, and let a layout of its graph have width at most `w`. Then
the circuit agrees with a set `S` of bias at most `b ≥ 0` on large rectangles on at most a
`1/2 + b + K ^ 3 (|V| + 1) |U| ^ (w + 4) / |U| ^ n` fraction of the inputs. -/
theorem agreement_le_of_layout {S : Set (Fin n → U)} {K : ℕ} {b : ℝ}
    (hS : RectangleBias S K b) (hb : 0 ≤ b) (hfan : c.FanInAtMost 2)
    (hu : Nat.card U ^ (Compiler.network c I fun _ => Acc).readᶜ.ncard < K)
    (π : Layout (Compiler.Vertex c)) {w : ℕ} (hw : (Compiler.graph c).width π ≤ w) :
    agreement S {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b +
      (K ^ 3 * (Nat.card (Compiler.Vertex c) + 1) * Nat.card U ^ (w + 4) : ℕ) /
        (Nat.card U : ℝ) ^ n := by
  set V := Nat.card (Compiler.Vertex c)
  set q := Nat.card U
  have bound (A : Set U) := (Compiler.network c I fun _ => A).abs_signedCount_accepted_le π
    (fun _ _ _ => Compiler.satisfies_unique) hb hS (w := w) (d := 3) (m := 1) hw
    (Compiler.maxDegreeLE le_rfl hfan) (Compiler.ncard_readAt_le I _)
  have h₁ := bound Acc
  have h₂ := bound Accᶜ
  rw [accepted_network_eq_eval] at h₁ h₂
  change _ ≤ _ + (((K - 1) ^ 2 * (V * q ^ (w + 3 + 1) +
    q ^ (Compiler.network c I fun _ => Acc).readᶜ.ncard) : ℕ) : ℝ) at h₂
  have h := agreement_le h₁ h₂
  -- The residual is at most `K ^ 3 (V + 1) q ^ (w + 4)`.
  have hres : (K - 1) ^ 2 * (V * q ^ (w + 3 + 1) +
      q ^ (Compiler.network c I fun _ => Acc).readᶜ.ncard) ≤ K ^ 3 * (V + 1) * q ^ (w + 4) := by
    have hq1 : 1 ≤ q ^ (w + 4) := Nat.one_le_pow _ _ Nat.card_pos
    calc _ ≤ K ^ 2 * (V * K * q ^ (w + 4) + K * q ^ (w + 4)) := by
          gcongr
          · omega
          · exact Nat.le_mul_of_pos_right _ (by omega)
          · exact hu.le.trans (Nat.le_mul_of_pos_right _ hq1)
      _ = K ^ 3 * (V + 1) * q ^ (w + 4) := by ring
  have hresR : (((K - 1) ^ 2 * (V * q ^ (w + 3 + 1) +
      q ^ (Compiler.network c I fun _ => Acc).readᶜ.ncard) : ℕ) : ℝ) ≤
      ((K ^ 3 * (V + 1) * q ^ (w + 4) : ℕ) : ℝ) := by exact_mod_cast hres
  have hq : 0 < q := Nat.card_pos
  have hN : (0 : ℝ) < (q : ℝ) ^ n := by positivity
  rw [card_input_eq] at h
  refine h.trans ?_
  have hhalf : ∀ R : ℝ, (R + R) / (2 * (q : ℝ) ^ n) = R / (q : ℝ) ^ n := fun R => by
    field_simp
    ring
  rw [hhalf]
  linarith [div_le_div_of_nonneg_right hresR hN.le]

/-- **A narrow layout of a circuit.** Suppose that connected, loopless multigraphs of maximum
degree three have layouts of width at most `(A + η) β₁ + η |V| + C`. If the inputs a circuit of
fan-in at most two does not read carry fewer than `K` assignments, its graph has a layout of
width at most `(A + η) (s - n + log_q K + 1) + η |V| + C` for `s` inner gates. -/
private theorem exists_layout_le {A η C : ℝ} (hAη : 0 ≤ A + η)
    (hC : ∀ (V E : Type) [Finite V] [Finite E] (G : Multigraph V E),
      G.toSimpleGraph.Connected → G.Loopless → G.MaxDegreeLE 3 →
        ∃ π : Layout V, (G.width π : ℝ) ≤ (A + η) * G.cycleRank + η * Nat.card V + C)
    (hfan : c.FanInAtMost 2) {K : ℕ}
    (hu : Nat.card U ^ (Compiler.network c I fun _ => Acc).readᶜ.ncard < K) :
    ∃ π : Layout (Compiler.Vertex c),
      ((Compiler.graph c).width π : ℝ) ≤
        (A + η) * (c.innerSize - n + Real.logb (Nat.card U) K + 1) +
          η * Nat.card (Compiler.Vertex c) + C := by
  have hrank : ((Compiler.graph c).cycleRank : ℝ) ≤
      c.innerSize - n + Real.logb (Nat.card U) K + 1 := by
    calc ((Compiler.graph c).cycleRank : ℝ)
        ≤ ((2 : ℕ) - 1) * c.innerSize - n + Real.logb (Nat.card U) K + 1 :=
          cycleRank_le (r := 2) hfan hu
      _ = c.innerSize - n + Real.logb (Nat.card U) K + 1 := by push_cast; ring
  obtain ⟨π, hπ⟩ := hC _ _ (Compiler.graph c) (Compiler.connected c) Compiler.loopless
    (Compiler.maxDegreeLE le_rfl hfan)
  exact ⟨π, hπ.trans (by gcongr)⟩

end Circuit

/-- **The average-case claim with coefficient `L`.** For every `ε > 0` there is a `γ > 0` such
that the following holds for every finite alphabet `U` with at least two symbols. Let
`S_n ⊆ U^n` have density within `b_n` of `1/2` on every rectangle with both sides of size at
least `K_n` (`RectangleBias`), where `log K_n = o(n)`. Then for all large `n`, every circuit of
fan-in at most two with at most `(L - ε) n` gates of positive arity, over any basis on `U` and
accepting any set of values, agrees with `S_n` on at most a `1/2 + b_n + exp (-γ n)` fraction of
the inputs.

The alphabet lives in the universe `u` and the basis in the universe `v`. -/
def AverageCaseBound (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ γ > 0, ∀ (U : Type u) [Finite U] [Nontrivial U] (S : ∀ n, Set (Fin n → U))
    (K : ℕ → ℕ) (b : ℕ → ℝ), (∀ᶠ n in atTop, RectangleBias (S n) (K n) (b n)) →
    (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → (c.innerSize : ℝ) ≤ (L - ε) * n →
        agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b n + Real.exp (-(γ * n))

/-- An average-case bound holds for every smaller coefficient. -/
theorem AverageCaseBound.mono {L L' : ℝ} (h : AverageCaseBound.{u, v} L) (hL : L' ≤ L) :
    AverageCaseBound.{u, v} L' := by
  intro ε hε
  obtain ⟨γ, hγ, H⟩ := h ε hε
  refine ⟨γ, hγ, fun U _ _ S K b hbias hK => ?_⟩
  filter_upwards [H U S K b hbias hK] with n hn
  intro σ I Acc c hfan hs
  exact hn σ I Acc c hfan
    (hs.trans (mul_le_mul_of_nonneg_right (sub_le_sub_right hL ε) (Nat.cast_nonneg n)))

/-- **The average-case frontier lower bound.** If subcubic graphs have layouts of width
`(A + o(1)) β₁ + o(|V|)` (`LayoutBound 3 A`), then the average-case claim holds with coefficient
`1 + 1/A`: below `(1 + 1/A - ε) n` inner gates, a circuit of fan-in at most two agrees with a set
of bias at most `b_n` on large rectangles on at most a `1/2 + b_n + exp (-γ n)` fraction of the
inputs. -/
theorem averageCaseBound_of_layoutBound {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound 3 A) :
    AverageCaseBound.{u, v} (1 + 1 / A) := by
  intro ε hε
  set μ := min (A * ε / 2) (1 / 2)
  have hμ : 0 < μ := lt_min (by positivity) (by norm_num)
  refine ⟨μ * Real.log 2, by positivity, ?_⟩
  intro U _ _ S K b hbias hK
  set q := Nat.card U
  have hq1 : 1 < q := Finite.one_lt_card
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq1
  -- Raise the thresholds to at least two.
  set K' : ℕ → ℕ := fun n => max (K n) 2
  have hlogb : (fun n => Real.logb q (K' n)) =o[atTop] fun n => (n : ℝ) :=
    isLittleO_logb_max_two hK q
  -- The error of the problem, `e(n) = 4 + 3 log_q K'(n)`, and the constant `κ`.
  set e : ℕ → ℝ := fun n => 4 + 3 * Real.logb q (K' n)
  have he : e =o[atTop] fun n => (n : ℝ) :=
    (isLittleO_const_id_atTop _).natCast_atTop.add (hlogb.const_mul_left 3)
  set κ : ℝ := 4 + 1 / Real.log 2
  have hκ4 : 4 ≤ κ := by simp only [κ]; linarith [show 0 ≤ 1 / Real.log 2 by positivity]
  obtain ⟨η, hη, H⟩ := eventually_add_lt_of_le hA (by linarith : 0 ≤ κ) hε
  obtain ⟨C, hC⟩ := hlayout η hη
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 + 2 * Real.logb q (K' n) ≤ (1 - 1 / 2) * n := by
    filter_upwards [((isLittleO_const_id_atTop (1 : ℝ)).natCast_atTop.add
      (hlogb.const_mul_left 2)).bound (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
    simp only [Real.norm_eq_abs, id, Nat.abs_cast] at hn
    linarith [le_abs_self (1 + 2 * Real.logb q (K' n))]
  filter_upwards [H C e he, hbias, hsmall] with n hn hbiasn hsmalln
  intro σ I Acc c hfan hsize
  have hK2 : 2 ≤ K' n := le_max_right _ _
  have hS : RectangleBias (S n) (K' n) (b n) := hbiasn.mono (le_max_left _ _)
  have hb : 0 ≤ b n := hS.nonneg (by
    rw [Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
    exact le_pow_half_of_logb hq1 (by omega) hsmalln)
  have hexp_mono : ∀ μ', μ ≤ μ' →
      Real.exp (-(μ' * Real.log 2 * n)) ≤ Real.exp (-(μ * Real.log 2 * n)) := fun μ' h =>
    Real.exp_le_exp.mpr (by
      nlinarith [mul_nonneg (Real.log_nonneg one_le_two) (Nat.cast_nonneg (α := ℝ) n)])
  have hq0 : 0 < q := Nat.card_pos
  by_cases hu : K' n ≤ q ^ (Compiler.network c I fun _ => Acc).readᶜ.ncard
  · -- Many unread inputs: the residual is `q K' ^ 2`.
    have hlog : Real.logb q ((q * K' n ^ 2 : ℕ) : ℝ) ≤ (1 - 1 / 2) * n := by
      push_cast
      rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
        Real.logb_self_eq_one (by linarith)]
      exact hsmalln
    linarith [agreement_le_of_unread I Acc c hS hb (by omega) hu,
      div_pow_le_exp hq2 (by positivity) (by norm_num) hlog, hexp_mono _ (min_le_right _ _)]
  · -- Few unread inputs: a narrow layout, whose residual is exponentially small.
    push Not at hu
    obtain ⟨π, hπ⟩ := exists_layout_le I Acc c (by linarith) hC hfan hu
    set V := Nat.card (Compiler.Vertex c)
    set w := (Compiler.graph c).width π
    have hlogK : 0 ≤ Real.logb q (K' n) :=
      Real.logb_nonneg (by linarith) (by exact_mod_cast (show 1 ≤ K' n by omega))
    have hsupply : (w : ℝ) ≤ (A + η) * (c.innerSize - n + e n) + η * V + C := by
      have := mul_le_mul_of_nonneg_left (show c.innerSize - n + Real.logb q (K' n) + 1 ≤
        c.innerSize - n + e n by simp only [e]; linarith) (by linarith : 0 ≤ A + η)
      linarith
    have hVκ : (V : ℝ) ≤ κ * (n + c.innerSize + 1) := by
      have hV : V ≤ 2 * 2 * c.innerSize + 3 * 1 := Compiler.card_vertex_le hfan
      have : (V : ℝ) ≤ 4 * c.innerSize + 3 := by exact_mod_cast hV
      nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) c.innerSize]
    have hmargin := hn c.innerSize V w (Nat.cast_nonneg _) (Nat.cast_nonneg _) hVκ hsize hsupply
    have hlog : Real.logb q ((K' n ^ 3 * (V + 1) * q ^ (w + 4) : ℕ) : ℝ) ≤
        (1 - A * ε / 2) * n := by
      push_cast
      rw [logb_residual (by linarith) (by positivity) (Nat.cast_nonneg _)]
      have := logb_le_mul_log hq2 (show (1 : ℝ) ≤ V + 1 by linarith [Nat.cast_nonneg (α := ℝ) V])
      simp only [e] at hmargin
      linarith
    linarith [agreement_le_of_layout I Acc c hS hb hfan hu π le_rfl,
      div_pow_le_exp hq2 (by positivity) (by positivity) hlog, hexp_mono _ (min_le_left _ _)]

end Cslib.Circuits.Frontier
