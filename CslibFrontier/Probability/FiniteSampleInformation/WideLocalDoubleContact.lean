/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.WidePositiveSchurGraph

/-!
# Value and normal first-order contact on the positive Schur graph

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`WideLocalDoubleContact.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

open scoped BigOperators

namespace WidePolynomial

theorem tauHom_value_zero_on_positive_schur_graph
    {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
    (P : WidePoly (k + 1) (k + r))
    (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P)
    {y : SchurBaseVar k r → ℝ}
    (hδ : schurDelta y ≠ 0)
    (hpos : ∀ i a, 0 < positiveSchurGraph y i a)
    (hlambda : ∀ i, 0 < schurLambda y i) :
    peval (tauHomogenizeWide (by omega : 0 < k + 1)
      (by omega : 0 < k + r) P) (positiveSchurGraph y) = 0 := by
  exact tauHom_positive_row_cone_zero hk (by omega : 0 < k + r)
    P hDPI hRKO hpos (fun i => (hlambda i).le)
      (positiveSchurGraph_row_relation hδ)

theorem tauHom_normal_derivative_zero_on_positive_schur_graph
    {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
    (P : WidePoly (k + 1) (k + r))
    (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P)
    {y : SchurBaseVar k r → ℝ}
    (hδ : schurDelta y ≠ 0)
    (hpos : ∀ i a, 0 < positiveSchurGraph y i a)
    (hlambda : ∀ i, 0 < schurLambda y i)
    (β : Fin r) :
    MvPolynomial.eval
      (fun ia => positiveSchurGraph y ia.1 ia.2)
      (MvPolynomial.pderiv (Fin.last k, Fin.natAdd k β)
        (tauHomogenizeWide (by omega : 0 < k + 1)
          (by omega : 0 < k + r) P)) = 0 := by
  exact tauHom_row_cone_all_partials_zero hk (by omega : 0 < k + r)
    P hDPI hRKO hpos (fun i => (hlambda i).le)
      (positiveSchurGraph_row_relation hδ) (Fin.last k) (Fin.natAdd k β)

/-- A single open box on which both the value and every normal derivative
of the homogenized polynomial vanish. -/
theorem exists_tauHom_double_contact_schur_open_box
    {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
    (P : WidePoly (k + 1) (k + r))
    (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P) :
    ∃ l u : SchurBaseVar k r → ℝ,
      (∀ q, l q < u q) ∧
      ∀ y : SchurBaseVar k r → ℝ,
        (∀ q, y q ∈ Set.Ioo (l q) (u q)) →
        peval (tauHomogenizeWide (by omega : 0 < k + 1)
          (by omega : 0 < k + r) P) (positiveSchurGraph y) = 0 ∧
        ∀ β : Fin r,
          MvPolynomial.eval
            (fun ia => positiveSchurGraph y ia.1 ia.2)
            (MvPolynomial.pderiv (Fin.last k, Fin.natAdd k β)
              (tauHomogenizeWide (by omega : 0 < k + 1)
                (by omega : 0 < k + r) P)) = 0 := by
  obtain ⟨l, u, hlu, hbox⟩ :=
    exists_positive_schur_graph_open_box (k := k) (r := r) hk
  refine ⟨l, u, hlu, ?_⟩
  intro y hy
  obtain ⟨hδ, hpos, hlambda, hrow, hminor⟩ := hbox y hy
  exact ⟨tauHom_value_zero_on_positive_schur_graph hk hr P hDPI hRKO
      hδ hpos hlambda,
    fun β => tauHom_normal_derivative_zero_on_positive_schur_graph
      hk hr P hDPI hRKO hδ hpos hlambda β⟩

end WidePolynomial


end

end Cslib.FiniteSampleInformation
