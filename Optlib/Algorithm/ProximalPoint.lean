import Optlib.Function.Lsmooth
import Optlib.Function.Proximal
import Optlib.Convex.StronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {x₀ xm : E} {f : E → ℝ} {f' : E → E} {t : ℝ}

open Set Finset

noncomputable def f_star (f : E → ℝ) : ℝ := sInf (f '' univ)

variable (f_min_exists : ∃ x_star : E, IsMinOn f univ x_star)

class ProximalPoint (f : E → ℝ) (f' : E → E) (t : ℝ) (x₀ : E) where
  x : ℕ → E
  m : ℝ
  diff : ∀ x₁ : E, HasGradientAt f (f' x₁) x₁
  fsc : StrongConvexOn univ m f
  fc: ConvexOn ℝ univ f
  m_pos : 0 < m
  t_pos : 0 < t
  x_init : x 0 = x₀
  update : ∀ k : ℕ, prox_prop (t • f) (x k) (x (k + 1))

variable (ppm : ProximalPoint f f' t x₀)

noncomputable def x_star (f : E → ℝ) (h : ∃ x : E, IsMinOn f univ x) : E :=
  Classical.choose h

lemma proximal_three_point_identity (ppm : ProximalPoint f f' t x₀) (k : ℕ) (x : E) :
    f x + 1 / (2 * t) * ‖x - ppm.x k‖ ^ 2 ≥
    f (ppm.x (k + 1)) + 1 / (2 * t) * ‖ppm.x (k + 1) - ppm.x k‖ ^ 2 +
    1 / (2 * t) * ‖x - ppm.x (k + 1)‖ ^ 2 := by
  have prox_cond := ppm.update k
  have subgrad : (1 / t) • (ppm.x k - ppm.x (k + 1)) ∈ SubderivAt f (ppm.x (k + 1)) := by
    rw [← prox_iff_subderiv_smul f ppm.fc ppm.t_pos (ppm.x (k + 1))]
    exact prox_cond
  rw [← mem_SubderivAt] at subgrad
  have subgrad_ineq := subgrad x
  simp [HasSubgradientAt] at subgrad_ineq
  have inv_eq_div : t⁻¹ = 1 / t := by field_simp
  conv_lhs at subgrad_ineq => arg 2; rw [inv_eq_div]
  have inner_expand : inner ((1 / t) • (ppm.x k - ppm.x (k + 1))) (x - ppm.x (k + 1)) =
      (1 / t) * inner (ppm.x k - ppm.x (k + 1)) (x - ppm.x (k + 1)) := by
    rw [real_inner_smul_left]
  rw [inner_expand] at subgrad_ineq
  have norm_identity : 2 * inner (ppm.x k - ppm.x (k + 1)) (x - ppm.x (k + 1)) =
      ‖ppm.x k - ppm.x (k + 1)‖ ^ 2 + ‖x - ppm.x (k + 1)‖ ^ 2 - ‖ppm.x k - x‖ ^ 2 := by
    have h : ppm.x k - x = (ppm.x k - ppm.x (k + 1)) - (x - ppm.x (k + 1)) := by abel
    sorry
  have norm_identity' : inner (ppm.x k - ppm.x (k + 1)) (x - ppm.x (k + 1)) =
      (‖ppm.x k - ppm.x (k + 1)‖ ^ 2 + ‖x - ppm.x (k + 1)‖ ^ 2 - ‖ppm.x k - x‖ ^ 2) / 2 := by
    have h := norm_identity
    linarith
  rw [norm_identity'] at subgrad_ineq
  calc f x + 1 / (2 * t) * ‖x - ppm.x k‖ ^ 2
      = f x + 1 / (2 * t) * ‖ppm.x k - x‖ ^ 2 := by rw [norm_sub_rev]
    _ ≥ f (ppm.x (k + 1)) + (1 / t) * ((‖ppm.x k - ppm.x (k + 1)‖ ^ 2 +
        ‖x - ppm.x (k + 1)‖ ^ 2 - ‖ppm.x k - x‖ ^ 2) / 2) +
        1 / (2 * t) * ‖ppm.x k - x‖ ^ 2 := by linarith [subgrad_ineq]
    _ = f (ppm.x (k + 1)) + 1 / (2 * t) * ‖ppm.x k - ppm.x (k + 1)‖ ^ 2 +
        1 / (2 * t) * ‖x - ppm.x (k + 1)‖ ^ 2 := by ring
    _ = f (ppm.x (k + 1)) + 1 / (2 * t) * ‖ppm.x (k + 1) - ppm.x k‖ ^ 2 +
        1 / (2 * t) * ‖x - ppm.x (k + 1)‖ ^ 2 := by rw [norm_sub_rev]

lemma proximal_descent (ppm : ProximalPoint f f' t x₀) (k : ℕ) :
    f (ppm.x k) ≥ f (ppm.x (k + 1)) + 1 / t * ‖ppm.x (k + 1) - ppm.x k‖ ^ 2 := by
  have h := proximal_three_point_identity ppm k (ppm.x k)
  have left_side_eq : f (ppm.x k) + 1 / (2 * t) * ‖ppm.x k - ppm.x k‖ ^ 2 = f (ppm.x k) := by
    simp [sub_self, norm_zero, zero_pow, mul_zero, add_zero]
  have right_side_eq : f (ppm.x (k + 1)) + 1 / (2 * t) * ‖ppm.x (k + 1) - ppm.x k‖ ^ 2 +
    1 / (2 * t) * ‖ppm.x k - ppm.x (k + 1)‖ ^ 2 =
    f (ppm.x (k + 1)) + 1 / t * ‖ppm.x (k + 1) - ppm.x k‖ ^ 2 := by
    have norm_sym : ‖ppm.x k - ppm.x (k + 1)‖ ^ 2 = ‖ppm.x (k + 1) - ppm.x k‖ ^ 2 := by
      rw [norm_sub_rev]
    rw [norm_sym]
    field_simp
    ring
  rw [left_side_eq, right_side_eq] at h
  exact h

lemma proximal_three_point_at_optimum (ppm : ProximalPoint f f' t x₀) (k : ℕ)
    (x_star : E) :
    f x_star + 1 / (2 * t) * ‖x_star - ppm.x k‖ ^ 2 ≥
    f (ppm.x (k + 1)) + 1 / (2 * t) * ‖ppm.x (k + 1) - ppm.x k‖ ^ 2 +
    1 / (2 * t) * ‖x_star - ppm.x (k + 1)‖ ^ 2 := by
  exact proximal_three_point_identity ppm k x_star

lemma proximal_key_inequality (ppm : ProximalPoint f f' t x₀) (k : ℕ) (x_star : E) :
    f (ppm.x (k + 1)) - f x_star ≤
    1 / (2 * t) * ‖ppm.x k - x_star‖ ^ 2 - 1 / (2 * t) * ‖ppm.x (k + 1) - x_star‖ ^ 2 := by
  have h1 := proximal_three_point_at_optimum ppm k x_star
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

lemma proximal_sum_inequality (ppm : ProximalPoint f f' t x₀) (k : ℕ+)
    (x_star : E) :
    (k : ℝ) * (f (ppm.x k) - f x_star) ≤
    ∑ i in Finset.range k, (f (ppm.x (i + 1)) - f x_star) := by
  -- Step 1: Prove that the sequence is decreasing
  have decreasing : ∀ i j : ℕ, i ≤ j → f (ppm.x j) ≤ f (ppm.x i) := by
    intro i j hij
    obtain ⟨n, rfl⟩ := Nat.le.dest hij
    clear hij
    induction n with
    | zero =>
      simp
    | succ n ih =>
      calc f (ppm.x (i + n + 1))
          ≤ f (ppm.x (i + n)) := by
            have desc := proximal_descent ppm (i + n)
            have nonneg : 0 ≤ 1 / t * ‖ppm.x (i + n + 1) - ppm.x (i + n)‖ ^ 2 := by
              apply mul_nonneg
              · apply div_nonneg
                · norm_num
                · linarith [ppm.t_pos]
              · exact sq_nonneg _
            linarith [desc, nonneg]
        _ ≤ f (ppm.x i) := ih

  have term_bound : ∀ i : ℕ, i < k →
      f (ppm.x k) - f x_star ≤ f (ppm.x (i + 1)) - f x_star := by
    intro i hi
    have le_k : i + 1 ≤ k := Nat.succ_le_of_lt hi
    have : f (ppm.x k) ≤ f (ppm.x (i + 1)) := decreasing (i + 1) k le_k
    linarith

  calc (k : ℝ) * (f (ppm.x k) - f x_star)
      = ∑ i in Finset.range k, (f (ppm.x k) - f x_star) := by
          rw [Finset.sum_const, Finset.card_range]
          simp
    _ ≤ ∑ i in Finset.range k, (f (ppm.x (i + 1)) - f x_star) := by
          apply Finset.sum_le_sum
          intro i hi
          exact term_bound i (Finset.mem_range.mp hi)

lemma proximal_telescoping_sum (ppm : ProximalPoint f f' t x₀) (k : ℕ+)
    (x_star : E) :
    ∑ i in Finset.range k, (f (ppm.x (i + 1)) - f x_star) ≤
    1 / (2 * t) * ‖x₀ - x_star‖ ^ 2 - 1 / (2 * t) * ‖ppm.x k - x_star‖ ^ 2 := by
  have key_ineq_general : ∀ i : ℕ, i < k →
    f (ppm.x (i + 1)) - f x_star ≤
    1 / (2 * t) * ‖ppm.x i - x_star‖ ^ 2 - 1 / (2 * t) * ‖ppm.x (i + 1) - x_star‖ ^ 2 := by
    intro i hi
    exact proximal_key_inequality ppm i x_star
  have sum_ineq : ∑ i in Finset.range k, (f (ppm.x (i + 1)) - f x_star) ≤
    ∑ i in Finset.range k, (1 / (2 * t) * ‖ppm.x i - x_star‖ ^ 2 -
                           1 / (2 * t) * ‖ppm.x (i + 1) - x_star‖ ^ 2) := by
    apply Finset.sum_le_sum
    intro i hi
    exact key_ineq_general i (Finset.mem_range.mp hi)
  have telescope : ∑ i in Finset.range k,
    (1 / (2 * t) * ‖ppm.x i - x_star‖ ^ 2 - 1 / (2 * t) * ‖ppm.x (i + 1) - x_star‖ ^ 2) =
    1 / (2 * t) * ‖ppm.x 0 - x_star‖ ^ 2 - 1 / (2 * t) * ‖ppm.x k - x_star‖ ^ 2 := by
    have h : ∀ n : ℕ, n > 0 →
      ∑ i in Finset.range n,
        (1 / (2 * t) * ‖ppm.x i - x_star‖ ^ 2 - 1 / (2 * t) * ‖ppm.x (i + 1) - x_star‖ ^ 2) =
        1 / (2 * t) * ‖ppm.x 0 - x_star‖ ^ 2 - 1 / (2 * t) * ‖ppm.x n - x_star‖ ^ 2 := by
      intro n
      induction n with
      | zero => intro; contradiction
      | succ n ih =>
        intro _
        rw [Finset.sum_range_succ]
        by_cases hn : n = 0
        · subst hn
          simp
        · have hn_pos : n > 0 := Nat.pos_of_ne_zero hn
          rw [ih hn_pos]
          ring
    apply h
    exact k.pos

  have x0_eq : ppm.x 0 = x₀ := ppm.x_init
  calc ∑ i in Finset.range k, (f (ppm.x (i + 1)) - f x_star)
      ≤ ∑ i in Finset.range k, (1 / (2 * t) * ‖ppm.x i - x_star‖ ^ 2 -
                                1 / (2 * t) * ‖ppm.x (i + 1) - x_star‖ ^ 2) := sum_ineq
    _ = 1 / (2 * t) * ‖ppm.x 0 - x_star‖ ^ 2 - 1 / (2 * t) * ‖ppm.x k - x_star‖ ^ 2 := telescope
    _ = 1 / (2 * t) * ‖x₀ - x_star‖ ^ 2 - 1 / (2 * t) * ‖ppm.x k - x_star‖ ^ 2 := by
        rw [x0_eq]

lemma proximal_combined_bound (ppm : ProximalPoint f f' t x₀) (k : ℕ+)
    (x_star : E) :
    (k : ℝ) * (f (ppm.x k) - f x_star) ≤ 1 / (2 * t) * ‖x₀ - x_star‖ ^ 2 := by
  have sum_right := proximal_sum_inequality ppm k x_star
  have sum_bound := proximal_telescoping_sum ppm k x_star
  have intermediate := le_trans sum_right sum_bound
  have drop_negative : 1 / (2 * t) * ‖x₀ - x_star‖ ^ 2 - 1 / (2 * t) * ‖ppm.x k - x_star‖ ^ 2 ≤
                  1 / (2 * t) * ‖x₀ - x_star‖ ^ 2 := by
    have nonneg_term : 0 ≤ 1 / (2 * t) * ‖ppm.x k - x_star‖ ^ 2 := by
      apply mul_nonneg
      · apply div_nonneg
        · norm_num
        · linarith [ppm.t_pos]
      · exact sq_nonneg _
    linarith
  exact le_trans intermediate drop_negative

/--
  Theorem: Convergence rate of the proximal point method with constant step size.

  For all k ≥ 1, the suboptimality gap at iterate k is bounded by
    f(x_k) - f(x_*) ≤ (1 / (2 k t)) * ‖x₀ - x_*‖²
  where x_* is a minimizer of f.
-/
theorem proximal_method_convergence_rate : ∀ (k : ℕ+),
    f (ppm.x k) - f (x_star f f_min_exists) ≤
    1 / (2 * (k : ℝ) * t) * ‖x₀ - x_star f f_min_exists‖ ^ 2 := by
  intro k
  let x_star := x_star f f_min_exists
  have final_bound := proximal_combined_bound ppm k x_star
  have pos_k : (0 : ℝ) < k := by
    exact Nat.cast_pos.mpr k.pos
  have div_result : f (ppm.x k) - f x_star ≤ (1 / (2 * t) * ‖x₀ - x_star‖ ^ 2) / (k) := by
    rw [le_div_iff₀ pos_k]
    rw [mul_comm] at final_bound
    exact final_bound
  convert div_result using 1
  field_simp
  ring
