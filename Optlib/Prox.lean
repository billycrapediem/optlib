import Optlib.Function.Lsmooth
import Optlib.Function.Proximal
import Optlib.Convex.StronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {x₀ xm : E} {f : E → ℝ} {f' : E → E} {t : ℝ}

open Set Finset

-- First, we need to define what the optimal value is
-- This should be the minimum value of f over the domain
noncomputable def f_star (f : E → ℝ) : ℝ := sInf (f '' univ)

-- We also need to assume there exists a minimizer
-- This would typically be proven from strong convexity and other conditions
variable (f_min_exists : ∃ x_star : E, IsMinOn f univ x_star)

class ProximalMethodConstantStep (f : E → ℝ) (f' : E → E) (t : ℝ) (x₀ : E) where
  x : ℕ → E
  m : ℝ
  diff : ∀ x₁ : E, HasGradientAt f (f' x₁) x₁
  fsc : StrongConvexOn univ m f
  m_pos : 0 < m
  t_pos : 0 < t
  x_init : x 0 = x₀
  update : ∀ k : ℕ, prox_prop (t • f) (x k) (x (k + 1))

variable (ppm : ProximalMethodConstantStep f f' t x₀)

-- Helper: get the optimal point (assuming it exists and is unique)
noncomputable def x_star (f : E → ℝ) (h : ∃ x : E, IsMinOn f univ x) : E :=
  Classical.choose h

/--
  Theorem: Convergence rate of the proximal point method with constant step size.

  For all k ≥ 1, the suboptimality gap at iterate k is bounded by
    f(x_k) - f(x_*) ≤ (1 / (2 k t)) * ‖x₀ - x_*‖²
  where x_* is a minimizer of f.
-/
theorem proximal_method_convergence_rate : ∀ (k : ℕ+),
    f (ppm.x k) - f (x_star f f_min_exists) ≤ 1 / (2 * (k : ℝ) * t) * ‖x₀ - x_star f f_min_exists‖ ^ 2 := by
  intro k
  let x_star := x_star f f_min_exists
  -- Step 1: Prove the optimality condition
  have optimality_condition : ∀ x,
  f x + 1 / (2 * t) * ‖x - ppm.x k‖ ^ 2 ≥
  f (ppm.x (k + 1)) + 1 / (2 * t) * ‖ppm.x (k + 1) - ppm.x k‖ ^ 2 +
  1 / (2 * t) * ‖x - ppm.x (k + 1)‖ ^ 2 := by
    intro x

    -- Define the augmented objective function
    let g := fun u ↦ f u + 1 / (2 * t) * ‖u - ppm.x k‖ ^ 2

    sorry


  -- Step 2: Take x = x_k in the optimality condition.
    -- This gives a lower bound on the decrease in f plus a quadratic term.
  have step2 : f (ppm.x k) ≥ f (ppm.x (k + 1)) + 1 / t * ‖ppm.x (k + 1) - ppm.x k‖ ^ 2 := by
  -- Apply the optimality condition with x = x_k
    have h := optimality_condition (ppm.x k)
    have left_side_eq : f (ppm.x k) + 1 / (2 * t) * ‖ppm.x k - ppm.x k‖ ^ 2 = f (ppm.x k) := by
      simp [sub_self, norm_zero, zero_pow, mul_zero, add_zero]

    have right_side_eq : f (ppm.x (k + 1)) + 1 / (2 * t) * ‖ppm.x (k + 1) - ppm.x k‖ ^ 2 +
      1 / (2 * t) * ‖ppm.x k - ppm.x (k + 1)‖ ^ 2 =
      f (ppm.x (k + 1)) + 1 / t * ‖ppm.x (k + 1) - ppm.x k‖ ^ 2 := by
      have norm_sym : ‖ppm.x k - ppm.x (k + 1)‖ ^ 2 = ‖ppm.x (k + 1) - ppm.x k‖ ^ 2 := by
        rw [norm_sub_rev]
      rw [norm_sym]
      -- Combine coefficients: 1/(2t) + 1/(2t) = 1/t
      sorry
    rw [left_side_eq, right_side_eq] at h
    exact h


  have step3 : f x_star + 1 / (2 * t) * ‖x_star - ppm.x k‖ ^ 2 ≥
    f (ppm.x (k + 1)) + 1 / (2 * t) * ‖ppm.x (k + 1) - ppm.x k‖ ^ 2 +
    1 / (2 * t) * ‖x_star - ppm.x (k + 1)‖ ^ 2 := by
    exact optimality_condition x_star

  -- Step 4: Rearrange the inequality from Step 3 to isolate f(x_{k+1}) - f(x_*).
  -- This gives a recursive bound on the suboptimality gap in terms of squared distances.
  have key_inequality : f (ppm.x (k + 1)) - f x_star ≤
    1 / (2 * t) * ‖ppm.x k - x_star‖ ^ 2 - 1 / (2 * t) * ‖ppm.x (k + 1) - x_star‖ ^ 2 := by
    have h1 := step3
    have rearranged : f (ppm.x (k + 1)) ≤ f x_star + 1 / (2 * t) * ‖x_star - ppm.x k‖ ^ 2
                      - 1 / (2 * t) * ‖ppm.x (k + 1) - ppm.x k‖ ^ 2
                      - 1 / (2 * t) * ‖x_star - ppm.x (k + 1)‖ ^ 2 := by
      linarith [h1]
    have with_gap : f (ppm.x (k + 1)) - f x_star ≤ 1 / (2 * t) * ‖x_star - ppm.x k‖ ^ 2
                    - 1 / (2 * t) * ‖ppm.x (k + 1) - ppm.x k‖ ^ 2
                    - 1 / (2 * t) * ‖x_star - ppm.x (k + 1)‖ ^ 2 := by
      linarith [rearranged]
    have drop_middle_term : f (ppm.x (k + 1)) - f x_star ≤ 1 / (2 * t) * ‖x_star - ppm.x k‖ ^ 2
                           - 1 / (2 * t) * ‖x_star - ppm.x (k + 1)‖ ^ 2 := by
      have nonneg_middle : 0 ≤ 1 / (2 * t) * ‖ppm.x (k + 1) - ppm.x k‖ ^ 2 := by
        apply mul_nonneg
        · apply div_nonneg
          · norm_num
          · linarith [ppm.t_pos]
        · exact sq_nonneg _
      linarith [with_gap, nonneg_middle]
    have norm_symmetry_k : ‖x_star - ppm.x k‖ ^ 2 = ‖ppm.x k - x_star‖ ^ 2 := by
      rw [norm_sub_rev]
    have norm_symmetry_k1 : ‖x_star - ppm.x (k + 1)‖ ^ 2 = ‖ppm.x (k + 1) - x_star‖ ^ 2 := by
      rw [norm_sub_rev]
    rw [norm_symmetry_k, norm_symmetry_k1] at drop_middle_term
    exact drop_middle_term

  -- Step 5: Sum the key inequality from i = 0 to k - 1.
  have sum_right : (k : ℝ) * (f (ppm.x k) - f x_star) ≤
    ∑ i in Finset.range k, (f (ppm.x (i + 1)) - f x_star) := by
    sorry

  -- The sum of the key inequalities gives a telescoping sum of squared distances.
  have sum_bound : ∑ i in Finset.range k, (f (ppm.x (i + 1)) - f x_star) ≤
  1 / (2 * t) * ‖x₀ - x_star‖ ^ 2 - 1 / (2 * t) * ‖ppm.x k - x_star‖ ^ 2 := by
    have key_ineq_general : ∀ i : ℕ, i < k →
      f (ppm.x (i + 1)) - f x_star ≤
      1 / (2 * t) * ‖ppm.x i - x_star‖ ^ 2 - 1 / (2 * t) * ‖ppm.x (i + 1) - x_star‖ ^ 2 := by
      intro i hi
      sorry

    -- Sum the inequalities
    have sum_ineq : ∑ i in Finset.range k, (f (ppm.x (i + 1)) - f x_star) ≤
      ∑ i in Finset.range k, (1 / (2 * t) * ‖ppm.x i - x_star‖ ^ 2 -
                             1 / (2 * t) * ‖ppm.x (i + 1) - x_star‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact key_ineq_general i (Finset.mem_range.mp hi)

    -- The right-hand side is a telescoping sum
    have telescope : ∑ i in Finset.range k,
      (1 / (2 * t) * ‖ppm.x i - x_star‖ ^ 2 - 1 / (2 * t) * ‖ppm.x (i + 1) - x_star‖ ^ 2) =
      1 / (2 * t) * ‖ppm.x 0 - x_star‖ ^ 2 - 1 / (2 * t) * ‖ppm.x k - x_star‖ ^ 2 := by
      sorry

    -- Use the initial condition x_0 = x₀
    have x0_eq : ppm.x 0 = x₀ := ppm.x_init
    calc ∑ i in Finset.range k, (f (ppm.x (i + 1)) - f x_star)
        ≤ ∑ i in Finset.range k, (1 / (2 * t) * ‖ppm.x i - x_star‖ ^ 2 -
                                  1 / (2 * t) * ‖ppm.x (i + 1) - x_star‖ ^ 2) := sum_ineq
      _ = 1 / (2 * t) * ‖ppm.x 0 - x_star‖ ^ 2 - 1 / (2 * t) * ‖ppm.x k - x_star‖ ^ 2 := telescope
      _ = 1 / (2 * t) * ‖x₀ - x_star‖ ^ 2 - 1 / (2 * t) * ‖ppm.x k - x_star‖ ^ 2 := by
          rw [x0_eq]

  -- Step 6: Combine the previous two results to bound (k : ℝ) * (f(x_k) - f(x_*)).
  have final_bound : (k : ℝ) * (f (ppm.x k) - f x_star) ≤ 1 / (2 * t) * ‖x₀ - x_star‖ ^ 2 := by
    have intermediate := le_trans sum_right sum_bound

    have drop_negative : 1 / (2 * t) * ‖x₀ - x_star‖ ^ 2 - 1 / (2 * t) * ‖ppm.x k - x_star‖ ^ 2 ≤
                      1 / (2 * t) * ‖x₀ - x_star‖ ^ 2 := by
      sorry
    exact le_trans intermediate drop_negative

  have pos_k : (0 : ℝ) < k := by
    exact Nat.cast_pos.mpr k.pos

  have div_result : f (ppm.x k) - f x_star ≤ (1 / (2 * t) * ‖x₀ - x_star‖ ^ 2) / (k) := by
    rw [le_div_iff₀ pos_k]
    rw [mul_comm] at final_bound
    exact final_bound

  convert div_result using 1
  field_simp
  ring
