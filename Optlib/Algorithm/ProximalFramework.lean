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

-- Helper lemma: Definition of ε for smooth part
lemma pg_epsilon_bound (f h : E → ℝ) (f' : E → E)
    (pgm : proximal_gradient_method f h f' x₀)
    (k : ℕ) (hk : k > 0) :
    f (pgm.x k) - (f (pgm.x (k-1)) + inner (f' (pgm.x (k-1))) (pgm.x k - pgm.x (k-1))) ≤
      pgm.L / 2 * ‖pgm.x k - pgm.x (k-1)‖^2 := by
  sorry


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
    intro k hk
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
    sorry
