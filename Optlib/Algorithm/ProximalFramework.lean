import Optlib.Function.Lsmooth
import Optlib.Function.Proximal
import Optlib.Convex.StronglyConvex
import Optlib.Algorithm.ProximalGradient
import Optlib.Algorithm.InexactProxiaml

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {x₀ xm : E} {f : E → ℝ} {f' : E → E} {σ : ℝ}

open Set Finset

lemma linearization_upper_bound (f : E → ℝ) (f' : E → E)
    (hf : ∀ x : E, HasGradientAt f (f' x) x)
    (hconv : ConvexOn ℝ univ f) (x₀ x : E) :
    f x ≥ f x₀ + inner (f' x₀) (x - x₀) := by
  have subderiv_eq : SubderivWithinAt f univ x₀ = {f' x₀} := by
    apply SubderivWithinAt_eq_gradient
    · simp
    · exact hconv
    · exact hf x₀
  have subderiv_at : f' x₀ ∈ SubderivAt f x₀ := by
    rw [← Subderivat_eq_SubderivWithinAt_univ]
    rw [subderiv_eq]
    simp
  rw [← mem_SubderivAt] at subderiv_at
  unfold HasSubgradientAt at subderiv_at
  exact subderiv_at x

lemma proximal_gradient_subdifferential (f h : E → ℝ) (f' : E → E)
    (pgm : proximal_gradient_method f h f' x₀)
    (k : ℕ) (hk : k > 0) :
    (1 / pgm.t) • (pgm.x (k-1) - pgm.x k) - f' (pgm.x (k-1)) ∈ SubderivAt h (pgm.x k) := by
  -- Get the proximal update condition
  have prox := pgm.update (k-1)
  -- This states: prox_prop (pgm.t • h) (pgm.x (k-1) - pgm.t • f' (pgm.x (k-1))) (pgm.x k)

  -- Simplify k - 1 + 1 to k
  have : k - 1 + 1 = k := Nat.sub_add_cancel hk
  simp only [this] at prox

  -- Apply the subdifferential characterization
  rw [prox_iff_subderiv_smul h pgm.hconv pgm.tpos (pgm.x k)] at prox
  have : (1 / pgm.t) • (pgm.x (k-1) - pgm.t • f' (pgm.x (k-1)) - pgm.x k) =
         (1 / pgm.t) • (pgm.x (k-1) - pgm.x k) - f' (pgm.x (k-1)) := by
    rw [smul_sub, smul_sub, smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt pgm.tpos), one_smul]
    module
  rwa [this] at prox

lemma pg_optimality_condition (f h : E → ℝ) (f' : E → E)
    (pgm : proximal_gradient_method f h f' x₀)
    (k : ℕ) (hk : k > 0) :
    ∀ x : E, f (pgm.x (k-1)) + inner (f' (pgm.x (k-1))) (x - pgm.x (k-1)) + h x ≥
      f (pgm.x (k-1)) + inner (f' (pgm.x (k-1))) (pgm.x k - pgm.x (k-1)) + h (pgm.x k) +
      (1 / pgm.t) * inner (pgm.x (k-1) - pgm.x k) (x - pgm.x k) := by
  intro x
  have h_subgrad : h x ≥ h (pgm.x k) +
    inner ((1 / pgm.t) • (pgm.x (k-1) - pgm.x k) - f' (pgm.x (k-1))) (x - pgm.x k) := by
    have key := proximal_gradient_subdifferential f h f' pgm k hk
    simp only [HasSubgradientAt] at key
    exact key x

  -- Expand the inner product
  rw [inner_sub_left] at h_subgrad
  rw [real_inner_smul_left] at h_subgrad

  -- Rearrange to get the desired inequality
  calc f (pgm.x (k-1)) + inner (f' (pgm.x (k-1))) (x - pgm.x (k-1)) + h x
      = f (pgm.x (k-1)) + inner (f' (pgm.x (k-1))) (x - pgm.x (k-1)) + h x := rfl
    _ ≥ f (pgm.x (k-1)) + inner (f' (pgm.x (k-1))) (x - pgm.x (k-1)) + h (pgm.x k) +
        (1 / pgm.t) * inner (pgm.x (k-1) - pgm.x k) (x - pgm.x k) -
        inner (f' (pgm.x (k-1))) (x - pgm.x k) := by linarith [h_subgrad]
    _ = f (pgm.x (k-1)) + inner (f' (pgm.x (k-1))) (pgm.x k - pgm.x (k-1)) + h (pgm.x k) +
        (1 / pgm.t) * inner (pgm.x (k-1) - pgm.x k) (x - pgm.x k) := by
          simp only [inner_sub_right]; ring_nf

lemma pg_epsilon_bound (f h : E → ℝ) (f' : E → E)
    (pgm : proximal_gradient_method f h f' x₀)
    (k : ℕ) :
    f (pgm.x k) - (f (pgm.x (k-1)) + inner (f' (pgm.x (k-1))) (pgm.x k - pgm.x (k-1))) ≤
      pgm.L / 2 * ‖pgm.x k - pgm.x (k-1)‖^2 := by
  -- Apply the L-smooth upper bound theorem
  have upper_bound := lipschitz_continuos_upper_bound' pgm.h₁ pgm.h₂
    (pgm.x (k-1)) (pgm.x k)

  linarith


lemma linearization_error_bound
  (f : E → ℝ) (f' : E → E) (x y : E) (L : NNReal)
  (hdiff : ∀ x₁ : E, HasGradientAt f (f' x₁) x₁)
  (hlip : LipschitzWith L f'):
  f y - (f x + inner (f' x) (y - x)) ≤ (L : ℝ) / 2 * ‖y - x‖^2 := by
  have upper_bound := lipschitz_continuos_upper_bound' hdiff hlip x y
  linarith

-- Helper lemma: Stepsize condition implies the desired bound
lemma stepsize_implies_bound
  (t : ℝ) (L : NNReal) (σ : ℝ)
  (hstep : t ≤ σ / L)
  (hL_pos : 0 < L) :
  t * L ≤ σ := by
  calc t * L
      ≤ (σ / L) * L := mul_le_mul_of_nonneg_right hstep (le_of_lt hL_pos)
    _ = σ := by field_simp [ne_of_gt hL_pos]


def proximal_gradient_is_IPP
  (f h : E → ℝ) (f' : E → E) (x₀ : E) (σ : ℝ)
  (pgm : proximal_gradient_method f h f' x₀)
  (hσ : 0 < σ ∧ σ ≤ 1)
  (hstep : pgm.t ≤ σ / pgm.L)
  (m : ℝ) (m_pos : 0 < m)
  (hsc : StrongConvexOn univ m (f + h))
  (hf_conv : ConvexOn ℝ univ f)
  (hh_conv : ConvexOn ℝ univ h)
  (hdiff : ∀ x₁ : E, HasGradientAt f (f' x₁) x₁) :
  InexactProximalPoint (f + h) f' σ x₀ where
  x := pgm.x
  x_tilde := pgm.x
  lam := λ k => if k = 0 then 1 else pgm.t
  delta := λ k => 0
  eps := λ k => if k = 0 then 0 else
    f (pgm.x k) - (f (pgm.x (k-1)) + inner (f' (pgm.x (k-1))) (pgm.x k - pgm.x (k-1)))
  m := m
  fsc := hsc
  fc := ConvexOn.add hf_conv hh_conv
  m_pos := m_pos
  σ_bound := hσ
  x_init := pgm.ori
  lam_pos := by
    intro k hk
    simp only [Nat.pos_iff_ne_zero] at hk
    simp [hk]
    exact pgm.tpos
  delta_nonneg := by
    intro k
    simp
  subgrad_cond := by
    intro k hk
    have hk_ne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
    simp [hk_ne]
    unfold EpsSubderivAt
    simp only [Set.mem_setOf_eq]
    intro y

    have f_bound := linearization_upper_bound f f' hdiff hf_conv (pgm.x (k-1)) y

    have opt_cond := pg_optimality_condition f h f' pgm k hk y

    calc (f + h) y
        = f y + h y := rfl
      _ ≥ (f (pgm.x (k-1)) + inner (f' (pgm.x (k-1))) (y - pgm.x (k-1))) + h y := by
          linarith [f_bound]
      _ ≥ (f (pgm.x (k-1)) + inner (f' (pgm.x (k-1))) (pgm.x k - pgm.x (k-1))) + h (pgm.x k) +
          (1 / pgm.t) * inner (pgm.x (k-1) - pgm.x k) (y - pgm.x k) := by
          linarith [opt_cond]
      _ = (f (pgm.x (k-1)) + inner (f' (pgm.x (k-1))) (pgm.x k - pgm.x (k-1))) +
          (1 / pgm.t) * inner (pgm.x (k-1) - pgm.x k) (y - pgm.x k) + h (pgm.x k) := by
          ring
      _ = f (pgm.x k) - (f (pgm.x k) - (f (pgm.x (k-1)) + inner (f' (pgm.x (k-1))) (pgm.x k - pgm.x (k-1)))) +
          (1 / pgm.t) * inner (pgm.x (k-1) - pgm.x k) (y - pgm.x k) + h (pgm.x k) := by
          ring
      _ = (f + h) (pgm.x k) + (1 / pgm.t) * inner (pgm.x (k-1) - pgm.x k) (y - pgm.x k) -
          (f (pgm.x k) - (f (pgm.x (k-1)) + inner (f' (pgm.x (k-1))) (pgm.x k - pgm.x (k-1)))) := by
          simp only [one_div, Pi.add_apply]; ring
      _ = (f + h) (pgm.x k) + inner ((1 / pgm.t) • (pgm.x (k-1) - pgm.x k)) (y - pgm.x k) -
          (f (pgm.x k) - (f (pgm.x (k-1)) + inner (f' (pgm.x (k-1))) (pgm.x k - pgm.x (k-1)))) := by
          rw [real_inner_smul_left]
      _ = (f + h) (pgm.x k) + inner ((pgm.t)⁻¹ • (pgm.x (k-1) - pgm.x k)) (y - pgm.x k) -
          (f (pgm.x k) - (f (pgm.x (k-1)) + inner (f' (pgm.x (k-1))) (pgm.x k - pgm.x (k-1)))) := by
          rw [one_div]
  prox_cond := by
    intro k hk
    have hk_ne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
    simp [hk_ne]
    -- Apply the linearization error bound
    have eps_bound := linearization_error_bound f f' (pgm.x (k-1)) (pgm.x k) pgm.L hdiff pgm.h₂

    -- Apply the stepsize condition
    have step_bound := stepsize_implies_bound pgm.t pgm.L σ hstep pgm.hL

    -- Chain the inequalities
    calc 2 * pgm.t *
         (f (pgm.x k) -
         (f (pgm.x (k-1)) + inner (f' (pgm.x (k-1))) (pgm.x k - pgm.x (k-1))))
      _ ≤ 2 * pgm.t * ((pgm.L : ℝ) / 2 * ‖pgm.x k - pgm.x (k-1)‖^2) := by
            apply mul_le_mul_of_nonneg_left eps_bound
            linarith [pgm.tpos]
      _ = pgm.t * (pgm.L : ℝ) * ‖pgm.x k - pgm.x (k-1)‖^2 := by ring
      _ ≤ σ * ‖pgm.x k - pgm.x (k-1)‖^2 := by
            gcongr


theorem proximal_gradient_convergence_rate
  (f h : E → ℝ) (f' : E → E) (x₀ : E) (σ : ℝ)
  (pgm : proximal_gradient_method f h f' x₀)
  (hσ : 0 < σ ∧ σ ≤ 1)
  (hstep : pgm.t ≤ σ / pgm.L)
  (m : ℝ) (m_pos : 0 < m)
  (hsc : StrongConvexOn univ m (f + h))
  (hf_conv : ConvexOn ℝ univ f)
  (hh_conv : ConvexOn ℝ univ h)
  (hdiff : ∀ x₁ : E, HasGradientAt f (f' x₁) x₁)
  (f_min_exists : ∃ x_star : E, IsMinOn (f + h) univ x_star)
  (k : ℕ+) :
  let ϕ := f + h
  let ippm := proximal_gradient_is_IPP f h f' x₀ σ pgm hσ hstep m m_pos hsc
              hf_conv hh_conv hdiff
  let Λ := ∑ i in Finset.range k, ippm.lam (i + 1)
  let x_hat := Λ⁻¹ • (∑ i in Finset.range k, ippm.lam (i + 1) • ippm.x_tilde (i + 1))
  let xstar := x_star ϕ f_min_exists
  ϕ x_hat - ϕ xstar ≤ (∑ i in Finset.range k, ippm.delta (i + 1)) / Λ + ‖x₀ - xstar‖^2 / (2 * Λ) := by

  -- Create the IPP instance from proximal gradient
  let ippm := proximal_gradient_is_IPP f h f' x₀ σ pgm hσ hstep m m_pos hsc
              hf_conv hh_conv hdiff

  -- Apply the general IPP convergence theorem directly
  exact inexact_proximal_convergence_rate ippm f_min_exists k
