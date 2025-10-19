import Optlib.Function.Lsmooth
import Optlib.Function.Proximal
import Optlib.Convex.StronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {x₀ xm : E} {f : E → ℝ} {f' : E → E} {σ : ℝ}

open Set Finset

noncomputable def f_star (f : E → ℝ) : ℝ := sInf (f '' univ)

variable (f_min_exists : ∃ x_star : E, IsMinOn f univ x_star)

def EpsSubderivAt (f : E → ℝ) (x : E) (ε : ℝ) : Set E :=
  {g | ∀ y, f y ≥ f x + inner g (y - x) - ε}

class InexactProximalPoint (f : E → ℝ) (f' : E → E) (σ : ℝ) (x₀ : E) where
  x : ℕ → E
  x_tilde : ℕ → E
  lam : ℕ → ℝ
  delta : ℕ → ℝ
  eps : ℕ → ℝ
  m : ℝ
  diff : ∀ x₁ : E, HasGradientAt f (f' x₁) x₁
  fsc : StrongConvexOn univ m f
  fc : ConvexOn ℝ univ f
  m_pos : 0 < m
  σ_bound : 0 < σ ∧ σ ≤ 1
  x_init : x 0 = x₀
  lam_pos : ∀ k : ℕ, k > 0 → 0 < lam k
  delta_nonneg : ∀ k : ℕ, k > 0 → 0 ≤ delta k
  -- Modified: Use ε-subdifferential
  subgrad_cond : ∀ k : ℕ, k > 0 →
    (1 / lam k) • (x (k - 1) - x k) ∈ EpsSubderivAt f (x_tilde k) (eps k)
  prox_cond : ∀ k : ℕ, k > 0 →
    ‖x k - x_tilde k‖^2 + 2 * lam k * eps k ≤
    σ * ‖x_tilde k - x (k - 1)‖^2 + 2 * delta k

variable (ippm : InexactProximalPoint f f' σ x₀)

noncomputable def v (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) : E :=
  (ippm.lam k)⁻¹ • (ippm.x (k - 1) - ippm.x k)

noncomputable def Gamma (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) (x : E) : ℝ :=
  f (ippm.x_tilde k) + inner (v ippm k) (x - ippm.x_tilde k) - ippm.eps k
noncomputable def objective (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) (x : E) : ℝ :=
  ippm.lam k * Gamma ippm k x + 1/2 * ‖x - ippm.x (k - 1)‖^2
-- Now Lemma 1(a) is provable
lemma inexact_proximal_lower_bound (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) (hk : k > 0) :
    ∀ x : E, Gamma ippm k x ≤ f x := by
  intro x
  unfold Gamma v
  have h := ippm.subgrad_cond k hk
  unfold EpsSubderivAt at h
  simp at h
  specialize h x
  linarith

lemma eps_subgrad_at_xk (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) (hk : k > 0) :
    f (ippm.x k) ≥ f (ippm.x_tilde k) +
    inner (v ippm k) (ippm.x k - ippm.x_tilde k) - ippm.eps k := by
  have h := ippm.subgrad_cond k hk
  simp [EpsSubderivAt] at h
  simpa [v] using h (ippm.x k)

-- Helper Lemma 2: Rearrange to get the gap
lemma gap_from_subgrad (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) (hk : k > 0) :
    f (ippm.x_tilde k) - f (ippm.x k) ≤
    -inner (v ippm k) (ippm.x k - ippm.x_tilde k) + ippm.eps k := by
  have h := eps_subgrad_at_xk ippm k hk
  linarith

-- Helper Lemma 3: Simplify the inner product term
lemma inner_product_expansion (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) :
    -inner (v ippm k) (ippm.x k - ippm.x_tilde k) =
    (1 / ippm.lam k) * inner (ippm.x (k-1) - ippm.x k) (ippm.x_tilde k - ippm.x k) := by
  unfold v
  rw [inner_smul_left]
  simp [real_inner_smul_left]
  have h : ippm.x k - ippm.x_tilde k = -(ippm.x_tilde k - ippm.x k) := by abel
  rw [h, inner_neg_right]
  simp [mul_neg, neg_neg]


-- Helper Lemma 4: Key norm identity
lemma norm_identity_for_three_points (a b c : E) :
    2 * inner (a - b) (c - b) = ‖a - b‖^2 + ‖c - b‖^2 - ‖a - c‖^2 := by
  have h : a - c = (a - b) - (c - b) := by abel
  have expand : ‖(a - b) - (c - b)‖^2 =
      ‖a - b‖^2 - 2 * inner (a - b) (c - b) + ‖c - b‖^2 := by
    apply norm_sub_sq_real
  rw [← h] at expand
  linarith

-- Helper Lemma 5: Express as sum of norms
lemma inner_as_norm_difference (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) (_hk : k > 0) :
    (1 / ippm.lam k) * inner (ippm.x (k-1) - ippm.x k) (ippm.x_tilde k - ippm.x k) =
    (1 / (2 * ippm.lam k)) * (‖ippm.x (k-1) - ippm.x k‖^2 +
                               ‖ippm.x_tilde k - ippm.x k‖^2 -
                               ‖ippm.x (k-1) - ippm.x_tilde k‖^2) := by
  have h := norm_identity_for_three_points (ippm.x (k-1)) (ippm.x k) (ippm.x_tilde k)
  -- Divide both sides of the identity by (2 * lam k)
  have h' := congrArg (fun t : ℝ => t / (2 * ippm.lam k)) h
  -- Turn divisions into multiplications by inverses
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h'

-- Helper Lemma 6: Combine with added terms
lemma combine_norm_terms (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) (hk : k > 0) :
    (1 / ippm.lam k) * inner (ippm.x (k-1) - ippm.x k) (ippm.x_tilde k - ippm.x k) +
    (1 / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x (k-1)‖^2 -
    (1 / (2 * ippm.lam k)) * ‖ippm.x k - ippm.x (k-1)‖^2 =
    (1 / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x k‖^2 := by
  rw [inner_as_norm_difference ippm k hk]
  have h1 : ‖ippm.x_tilde k - ippm.x (k-1)‖^2 = ‖ippm.x (k-1) - ippm.x_tilde k‖^2 := by
    rw [norm_sub_rev]
  have h2 : ‖ippm.x k - ippm.x (k-1)‖^2 = ‖ippm.x (k-1) - ippm.x k‖^2 := by
    rw [norm_sub_rev]
  rw [h1, h2]
  field_simp
  ring

-- Helper Lemma 7: Apply the proximal condition to get final bound
lemma apply_prox_condition (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) (hk : k > 0) :
    (1 / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x k‖^2 + ippm.eps k ≤
    (σ / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x (k-1)‖^2 + ippm.delta k / ippm.lam k := by
  have prox := ippm.prox_cond k hk
  have h : ‖ippm.x k - ippm.x_tilde k‖^2 = ‖ippm.x_tilde k - ippm.x k‖^2 := by
    rw [norm_sub_rev]
  rw [h] at prox
  have lam_pos := ippm.lam_pos k hk
  calc
    (1 / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x k‖^2 + ippm.eps k
        = (‖ippm.x_tilde k - ippm.x k‖^2 + 2 * ippm.lam k * ippm.eps k) / (2 * ippm.lam k) := by
          field_simp; ring
      _ ≤ (σ * ‖ippm.x_tilde k - ippm.x (k-1)‖^2 + 2 * ippm.delta k) / (2 * ippm.lam k) := by
          gcongr
      _ = (σ / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x (k-1)‖^2 + ippm.delta k / ippm.lam k := by
          field_simp; ring

-- Main Lemma 1(b): Putting it all together
lemma inexact_proximal_optimality_gap_bound (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ)
    (hk : k > 0) :
    f (ippm.x_tilde k) + (1 / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2
      - f (ippm.x k) - (1 / (2 * ippm.lam k)) * ‖ippm.x k - ippm.x (k - 1)‖^2
    ≤ (σ / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 + ippm.delta k / ippm.lam k := by
  -- Start with the gap from subgradient
  have gap := gap_from_subgrad ippm k hk

  -- Express inner product in a useful form
  have inner_expand := inner_product_expansion ippm k
  rw [inner_expand] at gap

  -- Main calculation
  calc f (ippm.x_tilde k) + (1 / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2
      - f (ippm.x k) - (1 / (2 * ippm.lam k)) * ‖ippm.x k - ippm.x (k - 1)‖^2
        = (f (ippm.x_tilde k) - f (ippm.x k)) +
          (1 / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
          (1 / (2 * ippm.lam k)) * ‖ippm.x k - ippm.x (k - 1)‖^2 := by ring
      _ ≤ ((1 / ippm.lam k) * inner (ippm.x (k-1) - ippm.x k) (ippm.x_tilde k - ippm.x k) + ippm.eps k) +
          (1 / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
          (1 / (2 * ippm.lam k)) * ‖ippm.x k - ippm.x (k - 1)‖^2 := by linarith [gap]
      _ = (1 / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x k‖^2 + ippm.eps k := by
          rw [← combine_norm_terms ippm k hk]; ring
      _ ≤ (σ / (2 * ippm.lam k)) * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 + ippm.delta k / ippm.lam k :=
          apply_prox_condition ippm k hk

lemma gradient_linear_part (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) (x : E) :
    HasGradientAt (fun y ↦ ippm.lam k * inner (v ippm k) (y - ippm.x_tilde k))
      (ippm.lam k • v ippm k) x := by
  sorry

lemma gradient_quadratic_part (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) (x : E) :
    HasGradientAt (fun y ↦ 1/2 * ‖y - ippm.x (k - 1)‖^2)
      (x - ippm.x (k - 1)) x := by
  sorry

lemma gradient_objective (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) (x : E) :
    HasGradientAt (objective ippm k)
      (ippm.lam k • v ippm k + (x - ippm.x (k - 1))) x := by
  sorry

lemma gradient_zero_at_iterate (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ)
    (hk : k > 0) :
    ippm.lam k • v ippm k + (ippm.x k - ippm.x (k - 1)) = 0 := by
  sorry

lemma objective_strongly_convex (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ)
    (hk : k > 0) :
    StrongConvexOn univ 1 (objective ippm k) := by
  sorry

lemma objective_convex (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ)
    (hk : k > 0) :
    ConvexOn ℝ univ (objective ippm k) := by
  sorry

lemma inexact_proximal_minimizer (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ)
    (hk : k > 0) :
    IsMinOn (objective ippm k) univ (ippm.x k) := by
  sorry


-- Lemma: The infimum of the objective equals its value at xk
lemma objective_infimum_at_iterate (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ)
    (hk : k > 0) :
    sInf ((objective ippm k) '' univ) = objective ippm k (ippm.x k) := by
  have min_at_xk := inexact_proximal_minimizer ippm k hk
  rw [isMinOn_univ_iff] at min_at_xk
  -- Show that objective ippm k (ippm.x k) is the infimum
  apply le_antisymm
  · -- sInf ((objective ippm k) '' univ) ≤ objective ippm k (ippm.x k)
    apply csInf_le
    · -- Bounded below
      use objective ippm k (ippm.x k)
      intros y hy
      obtain ⟨x, _, rfl⟩ := hy
      exact min_at_xk x
    · -- objective ippm k (ippm.x k) is in the image
      use ippm.x k
      simp
  · -- objective ippm k (ippm.x k) ≤ sInf ((objective ippm k) '' univ)
    apply le_csInf
    · -- The image is nonempty
      use objective ippm k (ippm.x k)
      use ippm.x k
      simp
    · -- objective ippm k (ippm.x k) is a lower bound
      intros y hy
      obtain ⟨x, _, rfl⟩ := hy
      exact min_at_xk x

-- Lemma: Identity relating objective at xk to objective at any point x
lemma objective_identity_with_norm (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ)
    (hk : k > 0) (x : E) :
    objective ippm k (ippm.x k) =
    objective ippm k x - 1/2 * ‖x - ippm.x k‖^2 := by
  unfold objective
  -- Gamma linearity
  have gamma_diff : Gamma ippm k x - Gamma ippm k (ippm.x k) = inner (v ippm k) (x - ippm.x k) := by
    unfold Gamma
    simp [inner_sub_right]


  -- Three-point identity
  have three_point : ‖x - ippm.x (k - 1)‖^2 - ‖ippm.x k - ippm.x (k - 1)‖^2 =
      ‖x - ippm.x k‖^2 + 2 * inner (x - ippm.x k) (ippm.x k - ippm.x (k - 1)) := by
    have h : x - ippm.x (k - 1) = (x - ippm.x k) + (ippm.x k - ippm.x (k - 1)) := by abel
    have expand : ‖(x - ippm.x k) + (ippm.x k - ippm.x (k - 1))‖^2 =
        ‖x - ippm.x k‖^2 + 2 * inner (x - ippm.x k) (ippm.x k - ippm.x (k - 1)) +
        ‖ippm.x k - ippm.x (k - 1)‖^2 := by
      apply norm_add_sq_real
    rw [← h] at expand
    linarith

  -- Use gradient zero condition
  have grad_zero := gradient_zero_at_iterate ippm k hk

  calc ippm.lam k * Gamma ippm k (ippm.x k) + 1/2 * ‖ippm.x k - ippm.x (k - 1)‖^2
      = ippm.lam k * Gamma ippm k x - ippm.lam k * inner (v ippm k) (x - ippm.x k) +
        1/2 * ‖ippm.x k - ippm.x (k - 1)‖^2 := by
          rw [← gamma_diff]; ring
    _ = ippm.lam k * Gamma ippm k x + 1/2 * ‖x - ippm.x (k - 1)‖^2 -
        1/2 * (‖x - ippm.x (k - 1)‖^2 - ‖ippm.x k - ippm.x (k - 1)‖^2) -
        ippm.lam k * inner (v ippm k) (x - ippm.x k) := by ring
    _ = ippm.lam k * Gamma ippm k x + 1/2 * ‖x - ippm.x (k - 1)‖^2 -
        1/2 * ‖x - ippm.x k‖^2 - inner (x - ippm.x k) (ippm.x k - ippm.x (k - 1)) -
        ippm.lam k * inner (v ippm k) (x - ippm.x k) := by
          rw [three_point]; ring
    _ = ippm.lam k * Gamma ippm k x + 1/2 * ‖x - ippm.x (k - 1)‖^2 - 1/2 * ‖x - ippm.x k‖^2 -
        inner (x - ippm.x k) (ippm.lam k • v ippm k + (ippm.x k - ippm.x (k - 1))) := by
          rw [inner_add_right, inner_smul_right]
          rw [real_inner_comm (x - ippm.x k) (v ippm k)]
          ring_nf
    _ = ippm.lam k * Gamma ippm k x + 1/2 * ‖x - ippm.x (k - 1)‖^2 - 1/2 * ‖x - ippm.x k‖^2 := by
          rw [grad_zero, inner_zero_right]
          ring

-- Lemma: Gamma evaluated at x_tilde k simplifies
lemma gamma_at_x_tilde (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) :
    Gamma ippm k (ippm.x_tilde k) = f (ippm.x_tilde k) - ippm.eps k := by
  unfold Gamma v
  simp [inner_zero_right, sub_self]

-- Lemma: Algebraic rearrangement for the objective terms
lemma objective_rearrangement (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) :
    ippm.lam k * (f (ippm.x_tilde k) - ippm.eps k) +
    1/2 * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
    1/2 * ‖ippm.x_tilde k - ippm.x k‖^2 =
    ippm.lam k * f (ippm.x_tilde k) +
    1/2 * (‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
           ‖ippm.x_tilde k - ippm.x k‖^2 -
           2 * ippm.lam k * ippm.eps k) := by
  ring

-- Lemma: Lower bound from proximal condition
lemma lower_bound_from_prox_condition (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ)
    (hk : k > 0) :
    ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
    ‖ippm.x_tilde k - ippm.x k‖^2 -
    2 * ippm.lam k * ippm.eps k
    ≥ (1 - σ) * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 - 2 * ippm.delta k := by
  have prox := ippm.prox_cond k hk
  have norm_sym : ‖ippm.x k - ippm.x_tilde k‖^2 = ‖ippm.x_tilde k - ippm.x k‖^2 := by
    rw [norm_sub_rev]
  rw [norm_sym] at prox

  calc ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 - ‖ippm.x_tilde k - ippm.x k‖^2 - 2 * ippm.lam k * ippm.eps k
      = ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 - (‖ippm.x_tilde k - ippm.x k‖^2 + 2 * ippm.lam k * ippm.eps k) := by ring
    _ ≥ ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 - (σ * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 + 2 * ippm.delta k) := by linarith [prox]
    _ = (1 - σ) * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 - 2 * ippm.delta k := by ring

lemma strengthen_lower_bound (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ)
    (hk : k > 0) :
    ippm.lam k * f (ippm.x_tilde k) +
    (1 - σ) / 2 * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
    ippm.delta k / 2
    ≥ ippm.lam k * f (ippm.x_tilde k) +
    (1 - σ) / 2 * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
    ippm.delta k := by
  have delta_nonneg := ippm.delta_nonneg k hk
  linarith

theorem inexact_proximal_minimum_lower_bound (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ)
    (hk : k > 0) :
    sInf ((objective ippm k) '' univ)
    ≥ ippm.lam k * f (ippm.x_tilde k) + (1 - σ) / 2 * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2
      - ippm.delta k := by
  -- Step 1: The infimum equals the objective at xk
  rw [objective_infimum_at_iterate ippm k hk]

  -- Step 2: Use the identity to relate it to x_tilde k
  rw [objective_identity_with_norm ippm k hk (ippm.x_tilde k)]
  unfold objective

  -- Step 3: Simplify Gamma at x_tilde k
  rw [gamma_at_x_tilde ippm k]

  -- Step 4: Algebraic rearrangement
  rw [objective_rearrangement ippm k]

  -- Step 5: Apply lower bound from proximal condition
  have bound := lower_bound_from_prox_condition ippm k hk

  calc ippm.lam k * f (ippm.x_tilde k) +
       1/2 * (‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
              ‖ippm.x_tilde k - ippm.x k‖^2 -
              2 * ippm.lam k * ippm.eps k)
      ≥ ippm.lam k * f (ippm.x_tilde k) +
        1/2 * ((1 - σ) * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 - 2 * ippm.delta k) := by
          linarith [bound]
    _ = ippm.lam k * f (ippm.x_tilde k) +
        (1 - σ) / 2 * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
        ippm.delta k := by ring
    _ ≥ ippm.lam k * f (ippm.x_tilde k) +
        (1 - σ) / 2 * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 -
        ippm.delta k := by linarith
