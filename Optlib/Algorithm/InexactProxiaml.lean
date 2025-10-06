import Optlib.Function.Lsmooth
import Optlib.Function.Proximal
import Optlib.Convex.StronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {x₀ xm : E} {f : E → ℝ} {f' : E → E} {σ : ℝ}

open Set Finset

noncomputable def f_star (f : E → ℝ) : ℝ := sInf (f '' univ)

variable (f_min_exists : ∃ x_star : E, IsMinOn f univ x_star)

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
  lam_pos : ∀ k : ℕ, 0 < lam k
  delta_nonneg : ∀ k : ℕ, 0 ≤ delta k
  subgrad_cond : ∀ k : ℕ, (1 / lam k) • (x (k - 1) - x k) ∈ SubderivAt (fun u ↦ f u + eps k * ‖u‖^2 / 2) (x_tilde k)
  prox_cond : ∀ k : ℕ, ‖x k - x_tilde k‖^2 + 2 * lam k * eps k ≤ σ * ‖x_tilde k - x (k - 1)‖^2 + delta k

variable (ippm : InexactProximalPoint f f' σ x₀)

noncomputable def v (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) : E :=
  (ippm.lam k)⁻¹ • (ippm.x (k - 1) - ippm.x k)

noncomputable def Gamma (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) (x : E) : ℝ :=
  f (ippm.x_tilde k) + inner (v ippm k) (x - ippm.x_tilde k) - ippm.eps k

-- Lemma 1(a): Γₖ is a lower bound for f
lemma inexact_proximal_lower_bound (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) :
    ∀ x : E, Gamma ippm k x ≤ f x := by
  intro x
  unfold Gamma v
  simp

  have subgrad := ippm.subgrad_cond k

  rw [← mem_SubderivAt] at subgrad
  have subgrad_ineq := subgrad x
  unfold HasSubgradientAt at subgrad_ineq
  simp at subgrad_ineq

  have inv_eq : (ippm.lam k)⁻¹ = 1 / ippm.lam k := by field_simp
  rw [inv_eq, real_inner_smul_left]

  have hcalc :
      f (ippm.x_tilde k)
        + (1 / ippm.lam k) * inner (ippm.x (k - 1) - ippm.x k) (x - ippm.x_tilde k)
        - ippm.eps k ≤
      f x := by
    calc
      f (ippm.x_tilde k)
          + (1 / ippm.lam k) * inner (ippm.x (k - 1) - ippm.x k) (x - ippm.x_tilde k)
          - ippm.eps k
        = (f (ippm.x_tilde k) + ippm.eps k * ‖ippm.x_tilde k‖^2 / 2)
            + (1 / ippm.lam k) * inner (ippm.x (k - 1) - ippm.x k) (x - ippm.x_tilde k)
            - ippm.eps k * ‖ippm.x_tilde k‖^2 / 2 - ippm.eps k := by ring

    _ ≤ f x + ippm.eps k * ‖x‖^2 / 2 - ippm.eps k * ‖ippm.x_tilde k‖^2 / 2 - ippm.eps k := by
      rw [inv_eq, real_inner_smul_left] at subgrad_ineq
      linarith [subgrad_ineq]

    _ = f x + ippm.eps k / 2 * (‖x‖^2 - ‖ippm.x_tilde k‖^2 - 2) := by ring

    _ ≤ f x := by
      have h : ippm.eps k / 2 * (‖x‖^2 - ‖ippm.x_tilde k‖^2 - 2) ≤ 0 := by sorry
      linarith

  exact (sub_le_iff_le_add).mp hcalc

-- Lemma 1(b): Upper bound for the optimality gap
lemma inexact_proximal_optimality_gap_bound (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) :
    f (ippm.x_tilde k) + 1 / (2 * ippm.lam k) * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2
      - f (ippm.x k) - 1 / (2 * ippm.lam k) * ‖ippm.x k - ippm.x (k - 1)‖^2
    ≤ σ / (2 * ippm.lam k) * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2 + ippm.delta k / ippm.lam k := by
  sorry

-- Lemma 1(c): xₖ minimizes the proximal subproblem
lemma inexact_proximal_minimizer (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) :
    IsMinOn (fun x ↦ ippm.lam k * Gamma ippm k x + 1/2 * ‖x - ippm.x (k - 1)‖^2) univ (ippm.x k) := by
  sorry

-- Lemma 1(d): Lower bound at the minimum
lemma inexact_proximal_minimum_lower_bound (ippm : InexactProximalPoint f f' σ x₀) (k : ℕ) :
    sInf ((fun x ↦ ippm.lam k * Gamma ippm k x + 1/2 * ‖x - ippm.x (k - 1)‖^2) '' univ)
    ≥ ippm.lam k * f (ippm.x_tilde k) + (1 - σ) / 2 * ‖ippm.x_tilde k - ippm.x (k - 1)‖^2
      - ippm.delta k := by
  sorry
