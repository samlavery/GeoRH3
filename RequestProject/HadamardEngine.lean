import RequestProject.WeilContourMultiplicity

/-!
# Character-agnostic Hadamard engine: residue cancellation from matching orders

The Riemann-`ξ` proof `ZD.logDeriv_difference_meromorphicOrderAt_nonneg` hard-codes `riemannXi`. Its
content is general: for **any** two entire functions `f, P` that are nowhere locally zero and whose
analytic orders agree at every point, the difference `logDeriv f − logDeriv P` has nonnegative
meromorphic order everywhere — the simple poles (residue = order, `logDeriv_pole_of_order`) carry the
*same* residue and cancel. This is the reusable brick for porting the `ξ` Hadamard chain to Dirichlet
`L(·,χ)`: instantiate with `f = completedLFunction χ` and `P =` its zero-matched Weierstrass product.
-/

open Complex Filter Topology

namespace HadamardEngine

/-- **Generic residue cancellation.** Entire `f, P`, nowhere locally zero, with `analyticOrderAt f =
    analyticOrderAt P` at every point ⟹ `logDeriv f − logDeriv P` has `meromorphicOrderAt ≥ 0`
    everywhere (no poles). Character-agnostic core of `logDeriv_difference_meromorphicOrderAt_nonneg`. -/
theorem logDeriv_sub_orderNonneg {f P : ℂ → ℂ}
    (hf : ∀ z, AnalyticAt ℂ f z) (hP : ∀ z, AnalyticAt ℂ P z)
    (hfne : ∀ z, ¬ f =ᶠ[𝓝 z] 0)
    (hord : ∀ z, analyticOrderAt f z = analyticOrderAt P z) (z : ℂ) :
    0 ≤ meromorphicOrderAt (fun w => logDeriv f w - logDeriv P w) z := by
  have hfz_ne : analyticOrderAt f z ≠ ⊤ := fun h => hfne z (analyticOrderAt_eq_top.mp h)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfz_ne
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · -- order 0: `f z ≠ 0`, `P z ≠ 0`, both log-derivatives analytic
    have hfz : f z ≠ 0 := (hf z).analyticOrderAt_eq_zero.mp (by rw [← hn, h0]; simp)
    have hPz : P z ≠ 0 := (hP z).analyticOrderAt_eq_zero.mp (by rw [← hord z, ← hn, h0]; simp)
    have h_log_f : AnalyticAt ℂ (logDeriv f) z := by
      simpa [logDeriv] using ((hf z).deriv.div (hf z) hfz)
    have h_log_P : AnalyticAt ℂ (logDeriv P) z := by
      simpa [logDeriv] using ((hP z).deriv.div (hP z) hPz)
    exact (h_log_f.sub h_log_P).meromorphicOrderAt_nonneg
  · -- order `n ≥ 1`: both residues are `n`, principal parts cancel
    have hford : analyticOrderAt f z = (n : ℕ∞) := hn.symm
    have hPord : analyticOrderAt P z = (n : ℕ∞) := by rw [← hord z]; exact hn.symm
    obtain ⟨gf, hgf_an, hgf_ne, hf_punct⟩ :=
      ZD.WeilPositivity.Contour.logDeriv_pole_of_order (hf z) hford hpos
    obtain ⟨gP, hgP_an, hgP_ne, hP_punct⟩ :=
      ZD.WeilPositivity.Contour.logDeriv_pole_of_order (hP z) hPord hpos
    have h_log_gf : AnalyticAt ℂ (fun w => deriv gf w / gf w) z := by
      simpa [logDeriv] using (hgf_an.deriv.div hgf_an hgf_ne)
    have h_log_gP : AnalyticAt ℂ (fun w => deriv gP w / gP w) z := by
      simpa [logDeriv] using (hgP_an.deriv.div hgP_an hgP_ne)
    have h_punct :
        (fun w => logDeriv f w - logDeriv P w) =ᶠ[nhdsWithin z {z}ᶜ]
          (fun w => deriv gf w / gf w - deriv gP w / gP w) := by
      filter_upwards [hf_punct, hP_punct] with w hwf hwP
      change deriv f w / f w - deriv P w / P w = deriv gf w / gf w - deriv gP w / gP w
      rw [hwf, hwP]; ring_nf
    rw [meromorphicOrderAt_congr h_punct]
    exact (h_log_gf.sub h_log_gP).meromorphicOrderAt_nonneg

end HadamardEngine

#print axioms HadamardEngine.logDeriv_sub_orderNonneg
