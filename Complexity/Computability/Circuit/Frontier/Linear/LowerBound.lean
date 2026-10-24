/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Compiler
public import Complexity.Computability.Circuit.Frontier.Demand
public import Complexity.Computability.Circuit.Linearize
public import Complexity.Foundations.Data.Matrix.TotallyRegular
import Complexity.Foundations.Data.Nat.IntermediateValue

/-!
# The frontier lower bound for linear maps

The frontier method applies to circuits with many outputs. For a circuit computing a linear map,
the demand comes from linear algebra instead of from counting rectangles.

Let a circuit over a field `F` compute `x ↦ M x` for an `N × N` matrix `M`, and cut its graph
(`Cslib.Circuits.Frontier.Compiler.graph`) along a set `P` of vertices: `P` reads the inputs `X`
and holds the outputs `Y`. If the runs on two inputs agree on the cut, splicing them
(`Cslib.Circuits.Frontier.Compiler.eval_splice`) shows that the outputs in `Y` do not see the
inputs outside `X`, and the outputs outside `Y` do not see the inputs in `X`. When `M` is totally
regular and `|X| + |Y| = N`, both blocks `M[Y, Xᶜ]` and `M[Yᶜ, X]` are square and nonsingular,
so the values on the cut determine the input. Every layout passes through such a `P`, since
`|X| + |Y|` grows by at most one per vertex, from `0` to `2 N`
(`Cslib.Circuits.Frontier.Compiler.exists_injective_frontier`), by a discrete intermediate value
theorem (`Nat.exists_eq_of_forall_le_add_one`).

How many values can a cut of `k` edges carry? A circuit has *linear capacity*
(`Cslib.Circuits.Circuit.LinearCapacity`) when the values of `k` wires never determine more than
`k` coordinates of the input. This holds

* over a finite alphabet, for every basis: `k` wires take at most `|F| ^ k` values
  (`Cslib.Circuits.Circuit.linearCapacity_of_finite`);
* over any field, for the affine basis: the values of `k` wires are an affine function of the
  input (`Cslib.Circuits.Circuit.linearCapacity_affine`);
* over an infinite field, for polynomial operations, after linearizing the circuit
  (`Cslib.Circuits.Circuit.Computes.exists_affine`).

It fails over infinite fields for arbitrary operations: an injection `F × F → F` lets one wire
carry two coordinates.

So every layout of the graph of the circuit has a frontier of at least `N` edges: the demand is
exactly `N`. For `s` inner gates of fan-in at most `r` the graph has cycle rank at most
`(r - 1) s + 1 - N`, and the comparison of demand and supply (`eventually_lt_of_demand`) gives
the coefficient of the frontier lower bound for decision problems.

**Main theorem** (`eventually_lt_mul_innerSize_of_isTotallyRegular`). Under `LayoutBound (r + 1) A`,
for every `ε > 0` and all large `N`, every circuit of fan-in at most `r` with linear capacity
computing a totally regular map `F^N → F^N` has `s` inner gates with
`(r - 1) s > (1 + 1/A - ε) N`, uniformly in the field. Constants are free.

## Main definitions

* `Cslib.Circuits.Circuit.LinearCapacity`: wires carry at most one coordinate each.

## Main results

* `Cslib.Circuits.Frontier.Compiler.exists_injective_frontier`: some frontier of every layout
  determines the input.
* `Cslib.Circuits.Frontier.exists_graph_of_isTotallyRegular`: the reduction theorem for linear
  maps.
* `Cslib.Circuits.Frontier.eventually_lt_mul_innerSize_of_isTotallyRegular`: the lower bound, for
  circuits with linear capacity; `..._finite`, `..._affine` and `..._isPolynomial` specialize it
  to finite fields with any basis, to any field with the affine basis, and to infinite fields with
  polynomial operations.

## References

* [L. G. Valiant, *Graph-theoretic arguments in low-level complexity*][Valiant1977]
* [P. Bürgisser, M. Clausen, M. A. Shokrollahi, *Algebraic Complexity
  Theory*][BurgisserClausenShokrollahi1997], Chapter 13
-/

@[expose] public section

open Set Filter Asymptotics Matrix

universe u v

namespace Cslib.Circuits

/-! ### Linear capacity -/

section Capacity

variable {σ : Signature} {U : Type*} {n m : ℕ}

/-- A circuit has *linear capacity* under an interpretation when its wires carry at most one
symbol each: whenever the values of a set `W` of wires determine the input, `n ≤ |W|`. -/
def Circuit.LinearCapacity (c : Circuit σ n m) (I : Interpretation σ U) : Prop :=
  ∀ W : Set (Wire n c.size),
    Function.Injective (fun (x : Fin n → U) (w : W) => c.program.trace I x w) → n ≤ W.ncard

/-- Over a finite alphabet every circuit has linear capacity: `k` wires take at most `|U| ^ k`
values. -/
theorem Circuit.linearCapacity_of_finite [Finite U] [Nontrivial U] (c : Circuit σ n m)
    (I : Interpretation σ U) : c.LinearCapacity I := by
  intro W hW
  have h := Nat.card_le_card_of_injective _ hW
  rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin,
    Nat.card_coe_set_eq] at h
  exact (Nat.pow_le_pow_iff_right Finite.one_lt_card).mp h

/-- Circuits over the affine basis have linear capacity: the values of `k` wires are an affine
function of the input, which is injective only if `n ≤ k`. -/
theorem Circuit.linearCapacity_affine {F : Type*} [Field F] (c : Circuit (affineSignature F) n m) :
    c.LinearCapacity (affineInterpretation F) := by
  intro W hW
  have := Fintype.ofFinite W
  choose L b hL using fun w : W => c.program.exists_affine_trace w.1
  let Φ : (Fin n → F) →ₗ[F] (W → F) := LinearMap.pi L
  have hΦ : Function.Injective Φ := fun x y hxy => hW (funext fun w => by
    have := congrFun hxy w
    simp only [LinearMap.pi_apply, Φ] at this
    simp only [hL, this])
  have := LinearMap.finrank_le_finrank_of_injective hΦ
  rwa [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] at this

end Capacity

namespace Frontier

/-! ### The graph of a circuit for a totally regular map -/

namespace Compiler

variable {F : Type u} [Field F] {σ : Signature.{v}} {I : Interpretation σ F} {N : ℕ}
  {M : Matrix (Fin N) (Fin N) F} {c : Circuit σ N N}

/-- The outputs of a circuit computing `x ↦ M x`. -/
private theorem eval_eq_mulVec (hc : c.Computes I fun x => M *ᵥ x) (x : Fin N → F) (o : Fin N) :
    c.eval I x o = (M *ᵥ x) o :=
  congrFun (hc x) o

/-- **Every output of a totally regular map depends on every input**, so in the graph of a
circuit computing it the vertex of every input is joined to every output vertex. -/
private theorem exists_reachable_of_isTotallyRegular (hM : M.IsTotallyRegular)
    (hc : c.Computes I fun x => M *ᵥ x) (i o : Fin N) :
    ∃ hi : Reach c (.input i),
      (graph c).toSimpleGraph.Reachable (.signal ⟨.input i, hi⟩) (.output o) := by
  classical
  refine exists_reachable_of_eval_ne (I := I) (x := 0) (y := Pi.single i 1) (fun k hk => ?_) ?_
  · simp [hk]
  · rw [eval_eq_mulVec hc, eval_eq_mulVec hc, mulVec_zero, mulVec_single_one]
    exact (hM.apply_ne_zero o i).symm

/-- The graph of a circuit computing a totally regular map with at least one input is
connected. -/
private theorem connected_of_isTotallyRegular (hN : 0 < N) (hM : M.IsTotallyRegular)
    (hc : c.Computes I fun x => M *ᵥ x) : (graph c).toSimpleGraph.Connected := by
  obtain ⟨hi, -⟩ := exists_reachable_of_isTotallyRegular hM hc ⟨0, hN⟩ ⟨0, hN⟩
  exact connected_of_reachable (v₀ := .signal ⟨.input ⟨0, hN⟩, hi⟩) fun o =>
    (exists_reachable_of_isTotallyRegular hM hc ⟨0, hN⟩ o).2

/-- A circuit computing a totally regular map reads all of its inputs. -/
private theorem read_eq_univ_of_isTotallyRegular (hM : M.IsTotallyRegular)
    (hc : c.Computes I fun x => M *ᵥ x) (Acc : Fin N → Set F) :
    (network c I Acc).read = univ := by
  rw [read_network]
  exact eq_univ_of_forall fun i => (exists_reachable_of_isTotallyRegular hM hc i i).1

omit [Field F] in
/-- In the network of a circuit computing a function, a vertex reads one input or holds one
output, or neither. -/
private theorem ncard_readAt_add_ncard_le (v : Vertex c) :
    ((network c I fun _ => univ).readAt v).ncard + {o | Vertex.output o = v}.ncard ≤ 1 := by
  rcases v with w | j | o
  · have h : {o | (Vertex.output o : Vertex c) = .signal w} = ∅ :=
      eq_empty_of_forall_notMem fun o ho => by cases ho
    rw [h, ncard_empty, add_zero]
    exact ncard_readAt_le I _ _
  · have h1 : (network c I fun _ => univ).readAt (.junction j) = ∅ :=
      eq_empty_of_forall_notMem fun i hi => by
        obtain ⟨_, h⟩ := site_eq_some (c := c) hi
        cases h
    have h2 : {o | (Vertex.output o : Vertex c) = .junction j} = ∅ :=
      eq_empty_of_forall_notMem fun o ho => by cases ho
    simp [h1]
  · have h1 : (network c I fun _ => univ).readAt (.output o) = ∅ :=
      eq_empty_of_forall_notMem fun i hi => by
        obtain ⟨_, h⟩ := site_eq_some (c := c) hi
        cases h
    have h2 : {o' | (Vertex.output o' : Vertex c) = .output o}.ncard ≤ 1 :=
      (ncard_le_one (toFinite _)).mpr fun o₁ h₁ o₂ h₂ => by
        rw [mem_ofPred_eq, Vertex.output.injEq] at h₁ h₂
        rw [h₁, h₂]
    rw [h1, ncard_empty, zero_add]
    exact h2

/-- **Some frontier of every layout determines the input.** For a circuit computing a totally
regular map, every layout of its graph has a time at which the values of the circuit on the
frontier determine the input. -/
theorem exists_injective_frontier (hM : M.IsTotallyRegular) (hc : c.Computes I fun x => M *ᵥ x)
    (π : Layout (Vertex c)) :
    ∃ t, Function.Injective fun (x : Fin N → F) (e : (graph c).frontier π t) =>
      c.program.trace I x e.1.signal.1 := by
  classical
  set G := network c I fun _ => univ
  -- `a t` counts the inputs read and the outputs held by the first `t` vertices.
  let outs : Set (Vertex c) → Set (Fin N) := fun P => {o | .output o ∈ P}
  let a : ℕ → ℕ := fun t => (G.readIn (π.initial t)).ncard + (outs (π.initial t)).ncard
  have h0 : a 0 = 0 := by simp [a, outs]
  have hT : N ≤ a (Nat.card (Vertex c)) := by
    -- All outputs are held at the end.
    simp only [a, outs, π.initial_of_card_le le_rfl, mem_univ, ofPred_true, ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hstep : ∀ t < Nat.card (Vertex c), a (t + 1) ≤ a t + 1 := by
    intro t ht
    set v := π.symm ⟨t, ht⟩
    have hsucc := π.initial_succ ht
    have hread : G.readIn (π.initial (t + 1)) ⊆ G.readIn (π.initial t) ∪ G.readAt v := by
      rw [hsucc]
      exact G.readIn_insert_subset _ _
    have houts : outs (π.initial (t + 1)) ⊆ outs (π.initial t) ∪ {o | .output o = v} := by
      intro o ho
      simp only [outs, mem_ofPred_eq, hsucc, mem_insert_iff] at ho
      exact ho.symm.imp id id
    have := ncard_le_ncard hread (toFinite _)
    have := ncard_le_ncard houts (toFinite _)
    have := ncard_union_le (G.readIn (π.initial t)) (G.readAt v)
    have := ncard_union_le (outs (π.initial t)) {o | .output o = v}
    have : (G.readAt v).ncard + {o | Vertex.output o = v}.ncard ≤ 1 :=
      ncard_readAt_add_ncard_le v
    simp only [a]
    omega
  obtain ⟨t, -, hat⟩ := Nat.exists_eq_of_forall_le_add_one (h0.trans_le (Nat.zero_le N)) hT hstep
  refine ⟨t, fun x x' hxx' => ?_⟩
  set P := π.initial t
  set X := G.readIn P
  set Y := outs P
  have hXY : X.ncard + Y.ncard = N := hat
  have hcut : ∀ e ∈ (graph c).edgeCut P,
      c.program.trace I x e.signal.1 = c.program.trace I x' e.signal.1 :=
    fun e he => congrFun hxx' ⟨e, he⟩
  have hcompl : ∀ S : Set (Fin N), Sᶜ.ncard = N - S.ncard := fun S => by
    have := ncard_add_ncard_compl S
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  -- Two inputs that agree on a set `B` of coordinates, and whose outputs agree on a set `R` of at
  -- least `|Bᶜ|` outputs, are equal: the matrix is totally regular.
  have key (B R : Set (Fin N)) (z y : Fin N → F) (hBR : Bᶜ.ncard ≤ R.ncard) (hzy : EqOn z y B)
      (hout : ∀ o ∈ R, c.eval I z o = c.eval I y o) : z = y := by
    refine sub_eq_zero.mp (hM.eq_zero_of_mulVec_eq_zero (rows := R.toFinset) (cols := Bᶜ.toFinset)
      (by rwa [← ncard_eq_toFinset_card', ← ncard_eq_toFinset_card']) (fun j hj => ?_)
      fun o ho => ?_)
    · simp [hzy (by simpa using hj)]
    · rw [mulVec_sub, Pi.sub_apply, ← eval_eq_mulVec hc, ← eval_eq_mulVec hc,
        hout o (by simpa using ho), sub_self]
  -- Off `X`: splice `x` at `P` with `x'` elsewhere; the outputs in `Y` are those of `x`.
  have hoff : X.piecewise x x' = x :=
    key X Y _ x (by rw [hcompl]; omega) (X.piecewise_eqOn x x') fun o ho =>
      (eval_splice hcut (X.piecewise_eqOn x x') (X.piecewise_eqOn_compl x x') o).1 ho
  -- On `X`: splice `x'` at `P` with `x` elsewhere; the outputs off `Y` are those of `x`.
  have hon : X.piecewise x' x = x :=
    key Xᶜ Yᶜ _ x (by rw [compl_compl, hcompl]; omega) (X.piecewise_eqOn_compl x' x) fun o ho =>
      (eval_splice (fun e he => (hcut e he).symm) (X.piecewise_eqOn x' x)
        (X.piecewise_eqOn_compl x' x) o).2 ho
  funext j
  by_cases hj : j ∈ X
  · simpa [X.piecewise_eq_of_mem _ _ hj] using (congrFun hon j).symm
  · simpa [X.piecewise_eq_of_notMem _ _ hj] using (congrFun hoff j).symm

/-- **Every layout is wide.** Every layout of the graph of a circuit with linear capacity
computing a totally regular map `F^N → F^N` has width at least `N`. -/
private theorem le_width_of_isTotallyRegular (hM : M.IsTotallyRegular)
    (hc : c.Computes I fun x => M *ᵥ x)
    (hcap : c.LinearCapacity I) (π : Layout (Vertex c)) : N ≤ (graph c).width π := by
  obtain ⟨t, ht⟩ := exists_injective_frontier hM hc π
  -- The wires carried by the frontier.
  set W := (fun e : Edge c => e.signal.1) '' (graph c).frontier π t
  have hW : Function.Injective fun (x : Fin N → F) (w : W) => c.program.trace I x w :=
    fun x x' h => ht (funext fun e => congrFun h ⟨_, mem_image_of_mem _ e.2⟩)
  exact (hcap W hW).trans ((ncard_image_le (toFinite _)).trans
    ((graph c).ncard_frontier_le_width π t))

end Compiler

/-! ### The lower bound -/

variable {F : Type u} [Field F] {σ : Signature.{v}} {I : Interpretation σ F} {N r : ℕ}
  {M : Matrix (Fin N) (Fin N) F} {c : Circuit σ N N}

/-- **The reduction theorem for linear maps.** A circuit with `s` inner gates of fan-in at most
`r ≥ 2` and linear capacity, computing a totally regular map `F^N → F^N` with `N ≥ 1`, yields a
connected, loopless multigraph of maximum degree `r + 1` with at most `2 r s + 3 N` vertices and
cycle rank at most `(r - 1) s + 1 - N`, every layout of which has width at least `N`. -/
theorem exists_graph_of_isTotallyRegular (hN : 0 < N) (hr : 2 ≤ r) (hfan : c.FanInAtMost r)
    (hM : M.IsTotallyRegular) (hc : c.Computes I fun x => M *ᵥ x) (hcap : c.LinearCapacity I) :
    ∃ (V E : Type) (_ : Finite V) (_ : Finite E) (G : Multigraph V E),
      G.toSimpleGraph.Connected ∧ G.Loopless ∧ G.MaxDegreeLE (r + 1) ∧
      Nat.card V ≤ 2 * r * c.innerSize + 3 * N ∧
      G.cycleRank + N ≤ (r - 1) * c.innerSize + 1 ∧
      ∀ π : Layout V, N ≤ G.width π := by
  have hconn := Compiler.connected_of_isTotallyRegular hN hM hc
  have hrank := Compiler.cycleRank_add_ncard_read_le I (fun _ => univ) hfan hconn
  rw [Compiler.read_eq_univ_of_isTotallyRegular hM hc, ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin] at hrank
  exact ⟨_, _, inferInstance, inferInstance, Compiler.graph c, hconn, Compiler.loopless,
    Compiler.maxDegreeLE hr hfan, Compiler.card_vertex_le hfan, hrank,
    Compiler.le_width_of_isTotallyRegular hM hc hcap⟩

/-- **The frontier lower bound for linear maps.** Let `r ≥ 2` and assume the layout hypothesis
for maximum degree `r + 1` with coefficient `A > 0`. For every `ε > 0` and all large `N`, every
circuit of fan-in at most `r` with linear capacity, over any field and any basis, that computes
`x ↦ M x` for a totally regular `N × N` matrix `M`, has `s` inner gates with
`(r - 1) s > (1 + 1/A - ε) N`. -/
theorem eventually_lt_mul_innerSize_of_isTotallyRegular (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] (σ : Signature.{v}) (I : Interpretation σ F)
      (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N), M.IsTotallyRegular →
        c.FanInAtMost r → c.Computes I (fun x => M *ᵥ x) → c.LinearCapacity I →
          (1 + 1 / A - ε) * N < (r - 1) * c.innerSize := by
  obtain ⟨η, hη, H⟩ := eventually_lt_of_demand hA (κ := 4) (by norm_num) hε
  obtain ⟨C, hC⟩ := hlayout η hη
  have he : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun N => (N : ℝ) :=
    isLittleO_const_left.mpr (Or.inr (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop))
  filter_upwards [H η hη le_rfl C _ he, eventually_ge_atTop 1] with N hN hN1
  intro F _ σ I M c hM hfan hc hcap
  obtain ⟨V, E, _, _, G, hconn, hloop, hdeg, hV, hrank, hwidth⟩ :=
    exists_graph_of_isTotallyRegular hN1 hr hfan hM hc hcap
  obtain ⟨π, hπ⟩ := hC V E G hconn hloop hdeg
  -- The quantities of the comparison.
  set s : ℝ := (r - 1) * c.innerSize
  have hcast : (((r - 1) * c.innerSize : ℕ) : ℝ) = s := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
  have hs : 0 ≤ s := hcast ▸ Nat.cast_nonneg _
  have hVs : (Nat.card V : ℝ) ≤ 4 * (N + s + 1) := by
    -- `2 r s + 3 N ≤ 4 (r - 1) s + 4 N`, since `2 r ≤ 4 (r - 1)`.
    have : 2 * r * c.innerSize + 3 * N ≤ 4 * ((r - 1) * c.innerSize) + 4 * N := by
      have : 2 * r ≤ 4 * (r - 1) := by omega
      nlinarith
    have h4 : (Nat.card V : ℝ) ≤ 4 * ((r - 1) * c.innerSize : ℕ) + 4 * N := by
      exact_mod_cast hV.trans this
    rw [hcast] at h4
    linarith
  refine hN s (Nat.card V) (G.width π) hs (Nat.cast_nonneg _) hVs ?_ ?_
  · -- The demand: every layout has width at least `N`.
    have h1 : (N : ℝ) ≤ G.width π := by exact_mod_cast hwidth π
    have h2 : 0 ≤ Real.log (Nat.card V + 1) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (Nat.card V)])
    linarith
  · -- The supply: the layout hypothesis, with the cycle rank of the reduction.
    have hrank' : (G.cycleRank : ℝ) ≤ s - N + 1 := by
      have : (G.cycleRank : ℝ) + N ≤ ((r - 1) * c.innerSize : ℕ) + 1 := by exact_mod_cast hrank
      linarith
    have := mul_le_mul_of_nonneg_left hrank' (by linarith : 0 ≤ A + η)
    linarith

/-- **The frontier lower bound for linear maps over finite fields**, for every basis. Under the
hypotheses of `eventually_lt_mul_innerSize_of_isTotallyRegular`, for every `ε > 0` and all large
`N`, every circuit of fan-in at most `r` over a finite field `F`, over any basis, that computes
`x ↦ M x` for a totally regular `N × N` matrix `M` has `s` inner gates with
`(r - 1) s > (1 + 1/A - ε) N`. -/
theorem eventually_lt_mul_innerSize_of_isTotallyRegular_finite (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Finite F] (σ : Signature.{v})
      (I : Interpretation σ F) (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N),
        M.IsTotallyRegular → c.FanInAtMost r → c.Computes I (fun x => M *ᵥ x) →
          (1 + 1 / A - ε) * N < (r - 1) * c.innerSize := by
  filter_upwards [eventually_lt_mul_innerSize_of_isTotallyRegular.{u, v} hr hA hlayout hε]
    with N hN
  intro F _ _ σ I M c hM hfan hc
  exact hN F σ I M c hM hfan hc (c.linearCapacity_of_finite I)

/-- **The frontier lower bound for linear maps over the affine basis**, over every field. -/
theorem eventually_lt_mul_innerSize_of_isTotallyRegular_affine (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] (M : Matrix (Fin N) (Fin N) F)
      (c : Circuit (affineSignature F) N N), M.IsTotallyRegular → c.FanInAtMost r →
        c.Computes (affineInterpretation F) (fun x => M *ᵥ x) →
          (1 + 1 / A - ε) * N < (r - 1) * c.innerSize := by
  filter_upwards [eventually_lt_mul_innerSize_of_isTotallyRegular.{u, u} hr hA hlayout hε]
    with N hN
  intro F _ M c hM hfan hc
  exact hN F _ _ M c hM hfan hc c.linearCapacity_affine

/-- **The frontier lower bound for linear maps over infinite fields**, for every basis of
polynomial operations: their coefficients and degrees are arbitrary. -/
theorem eventually_lt_mul_innerSize_of_isTotallyRegular_isPolynomial (hr : 2 ≤ r) {A : ℝ}
    (hA : 0 < A) (hlayout : LayoutBound (r + 1) A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Infinite F] (σ : Signature.{v})
      (I : Interpretation σ F), I.IsPolynomial → ∀ (M : Matrix (Fin N) (Fin N) F)
        (c : Circuit σ N N), M.IsTotallyRegular → c.FanInAtMost r →
          c.Computes I (fun x => M *ᵥ x) → (1 + 1 / A - ε) * N < (r - 1) * c.innerSize := by
  filter_upwards [eventually_lt_mul_innerSize_of_isTotallyRegular_affine.{u} hr hA hlayout hε]
    with N hN
  intro F _ _ σ I hI M c hM hfan hc
  obtain ⟨c', -, hinner, hfan', hc'⟩ := hc.exists_affine hI
  rw [← hinner]
  exact hN F M c' hM ((hfan' r).mpr hfan) hc'

end Frontier

end Cslib.Circuits
