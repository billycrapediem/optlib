/-
Copyright (c) 2024 Shengyang Xu, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengyang Xu, Chenyi Li
-/
import Mathlib.Topology.Semicontinuous
import Mathlib.Analysis.Convex.Basic
import Optlib.Convex.Subgradient
import Optlib.Function.Lsmooth
import Optlib.Convex.StronglyConvex
import Optlib.Function.MinimaClosedFunction

set_option linter.unusedVariables false

/-!
 proximal operator
-/
noncomputable section

set_option linter.unusedSectionVars false

open Set InnerProductSpace Topology Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {x y y₁ y₂ : E} {s : Set E} {f : E → ℝ}

/-
  a point satisfies the proximal property if it is a minimizer of the function f(u)+1/2‖u-x‖²
-/
def prox_prop (f : E → ℝ) (x : E) (xm : E) : Prop :=
  IsMinOn (fun u ↦ f u + ‖u - x‖ ^ 2 / 2) univ xm

/-
  the set of all points that satisfy the proximal property
-/
def prox_set (f : E → ℝ) (x : E) : Set E := {u | prox_prop f x u}

/-
  if the proximal set is nonempty then we can choose the point that satisfies the proximal property
-/
def prox_point (f : E → ℝ) (x : E) (h : ∃ y, prox_set f x y) : E :=
  Classical.choose h

variable [ProperSpace E]
/-
  The existence of the proximal for proper lower-semi-continuous function
-/
theorem prox_set_compact_of_lowersemi (f : E → ℝ) (hc : LowerSemicontinuous f)
    (lbdf : BddBelow (f '' univ)) :
    ∀ x, Nonempty (prox_set f x) ∧ IsCompact (prox_set f x) := by
  intro x
  let g := fun u ↦ f u + ‖u - x‖ ^ 2 / 2
  let epi := {p : (E × ℝ) | g p.1 ≤ p.2}
  let S := {y : E | g y ≤ g x}
  have eq : S = (g ⁻¹' Set.Iic (g x)) := by constructor
  let ImS := {g y | y ∈ S}
  have neImS : Set.Nonempty ImS := by
    use g x; simp [ImS]; use x; simp [S]
  rcases lbdf with ⟨L, Lbound⟩
  rw [mem_lowerBounds] at Lbound
  have boundg : ∀ (x : E), L ≤ g x := by
    intro z
    calc
      L ≤ f z := by
        specialize Lbound (f z); simp at Lbound; exact Lbound
      _ ≤ f z + ‖z - x‖ ^ 2 / 2 := by
        simp; linarith [sq_nonneg ‖z - x‖]
  have hg : LowerSemicontinuous g := by
    refine hc.add ?_
    have hcont : Continuous (fun z : E => ‖z - x‖ ^ 2 / 2) := by
      have h1 : Continuous (fun z : E => ‖z - x‖) := (continuous_id.sub continuous_const).norm
      have h2 : Continuous (fun z : E => ‖z - x‖ ^ 2) := h1.pow 2
      have h3 : Continuous (fun z : E => ‖z - x‖ ^ 2 * (1 / 2)) := h2.mul continuous_const
      simpa [div_eq_mul_inv, mul_comm] using h3
    exact hcont.lowerSemicontinuous
  have S_bddbelow : BddBelow ImS := by
    use L; rw [mem_lowerBounds]
    rintro gy ⟨y0, _, gyeq⟩; rw [← gyeq]; exact boundg y0
  have epi_closed : IsClosed epi := by
    apply bounded_lowersemicontinuous_to_epi_closed
    · exact lowerSemicontinuousOn_univ_iff.2 hg
    use L
  have closeds : IsClosed S := by
    rw [eq]
    rw [lowerSemicontinuous_iff_isClosed_preimage] at hg
    exact hg (g x)
  have compacts : IsCompact S := by
    let B := Metric.closedBall x (f x - L + 1)
    have sinb : S ⊆ B := by
      intro u uin; simp [S] at uin
      apply mem_closedBall_iff_norm.2
      have norm_bound: ‖u - x‖ ≤ f x - L + 1 := by
        have ieq : L + ‖u - x‖ ^ 2 / 2 ≤ f x:= by
          calc
          L + ‖u - x‖ ^ 2 / 2 ≤ g u := by
            simp [g]; specialize Lbound (f u); simp at Lbound; exact Lbound
          _ ≤ f x := by simp [g] at uin; exact uin
        rw [← le_sub_iff_add_le'] at ieq
        have aux {a b : ℝ} (h1 : a ^ 2 / 2 ≤ b) (h2 : 0 ≤ a) : a ≤ b + 1 := by
          rw [div_le_iff₀] at h1; rw [← abs_eq_self] at h2; rw [← h2]
          apply abs_le_of_sq_le_sq; rw [add_sq]; simp
          calc
            a ^ 2 ≤ b * 2 := h1
            _ ≤ b ^ 2 + 2 * b + 1 := by
              rw [add_right_comm, mul_comm]; simp; linarith [sq_nonneg b]
          calc
            0 ≤ a ^ 2 / 2 := by linarith [sq_nonneg a]
            _ ≤ b * 2 / 2 := by
              have h := mul_le_mul_of_nonneg_right h1 (by norm_num : 0 ≤ (1 / 2 : ℝ))
              simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
            _ ≤ b + 1 := by simp
          linarith
        apply aux ieq
        apply norm_nonneg
      exact norm_bound
    have compactb : IsCompact B := isCompact_closedBall x (f x - L + 1)
    rw [← closure_eq_iff_isClosed] at closeds; rw [← closeds]
    apply IsCompact.closure_of_subset compactb sinb
  rcases exists_seq_tendsto_sInf neImS S_bddbelow with ⟨fx, _, cfx, fxs⟩
  choose xn xsub xeq using fxs
  rcases IsCompact.tendsto_subseq compacts xsub with ⟨x', _, k, mono, cxk⟩
  have cfxk : Filter.Tendsto (g ∘ xn ∘ k) Filter.atTop (𝓝 (sInf ImS)) := by
    have xkeq : ∀ (n : ℕ), (g ∘ xn ∘ k) n = (fx ∘ k) n := fun n => xeq <| k n
    rw [tendsto_congr xkeq]
    apply Tendsto.comp cfx (StrictMono.tendsto_atTop mono)
  have inepi : (x', sInf ImS) ∈ epi := by
    let p := fun c ↦ (((fun n ↦ xn n) ∘ k) c, (g ∘ xn ∘ k) c)
    have pnin :  ∀ c : ℕ, p c ∈ epi := by
      simp [epi]
      exact fun c ↦
        Std.IsPreorder.le_refl (g (p c).1)
    apply IsClosed.isSeqClosed epi_closed pnin
    show Tendsto (fun c ↦ (((fun n ↦ xn n) ∘ k) c, (g ∘ xn ∘ k) c)) atTop (𝓝 (x', sInf ImS))
    apply Tendsto.prodMk_nhds cxk cfxk
  have minima_ieq : g x' ≤ sInf ImS := inepi
  have minima : ∀ w : E, g x' ≤ g w := by
    intro w
    by_cases hw : w ∈ S
    · have gwin : g w ∈ ImS := by use w
      have legw : sInf ImS ≤ g w := by
        rw [Real.sInf_le_iff S_bddbelow neImS]
        intro _ epos; use g w; use gwin; linarith
      linarith
    · have gwnin : g x < g w := by
        simp [g, S] at hw; simp [g]; exact hw
      have gxin : g x ∈ ImS := by use x; simp [g, S]
      have legw : sInf ImS ≤ g w := by
        rw [Real.sInf_le_iff S_bddbelow neImS]
        intro _ epos; use g x; use gxin; linarith
      linarith
  constructor
  · use x'; simp [prox_set]; rw [prox_prop, isMinOn_iff]
    intro v _; exact minima v
  · have aux : prox_set f x = {x | IsMinOn g univ x} := by
      simp [prox_set]; ext y
      constructor
      · intro yin; simp [prox_prop] at yin; simp; exact yin
      · intro yin; simp; rw [prox_prop]
        simp at yin; exact yin
    have nes : Nonempty S := by use x; simp [S]
    rw [eq] at compacts; rw [eq] at nes
    rw [aux] -- apply IsCompact_isMinOn_of_isCompact_preimage hc nes compacts
    have seq : {x | IsMinOn g univ x} = (g ⁻¹' Set.Iic (g x')) := by
      ext y
      constructor
      · exact fun hxx => isMinOn_iff.mp hxx x' trivial
      · intro yin; simp at yin
        exact fun x xuniv => le_trans yin ((fun x _ => minima x) x xuniv)
    simp only [seq]
    apply IsCompact.of_isClosed_subset compacts (LowerSemicontinuous.isClosed_preimage hg (g x'))
    apply Set.preimage_mono
    simp only [Set.Iic_subset_Iic]
    exact minima x

theorem prox_set_compact_of_convex (f : E → ℝ) (hc : ContinuousOn f univ)
    (hconv : ConvexOn ℝ univ f) :
    ∀ x, Nonempty (prox_set f x) ∧ IsCompact (prox_set f x) := by
  intro x
  have subd: ∃ z : E, Nonempty (SubderivAt f z) := by
    use x; apply SubderivAt.nonempty hconv hc
  have hc : LowerSemicontinuous f :=
    Continuous.lowerSemicontinuous (continuousOn_univ.mp hc)
  rcases subd with ⟨z, a, ain⟩
  rw [← mem_SubderivAt, HasSubgradientAt] at ain
  let g := fun u ↦ f u + ‖u - x‖ ^ 2 / 2
  let epi := {p : (E × ℝ) | g p.1 ≤ p.2}
  have second_lower_bound (y : E) : g y ≥ f z + ⟪a, y - z⟫_ℝ + ‖y - x‖ ^ 2 / 2 := by
    have h := ain y
    have h' := add_le_add_right h (‖y - x‖ ^ 2 / 2)
    simpa [g, add_comm, add_left_comm, add_assoc] using h'
  have lower_bound (y : E) : f z + ⟪a, x - z⟫_ℝ - ‖a‖ ^ 2 / 2 ≤ g y := by
    have : y - z = x - z + (y - x) := by simp
    specialize second_lower_bound y
    rw [this, inner_add_right, ← add_assoc, add_assoc] at second_lower_bound
    have : 0 ≤ ‖a‖ ^ 2 / 2 + ⟪a, y - x⟫_ℝ + ‖y - x‖ ^ 2 / 2 := by
      have hrewrite :
          ‖a‖ ^ 2 / 2 + ⟪a, y - x⟫_ℝ + ‖y - x‖ ^ 2 / 2
            = ‖a + (y - x)‖ ^ 2 / 2 := by
        have h1 :
            (‖a‖ ^ 2 + 2 * ⟪a, y - x⟫_ℝ + ‖y - x‖ ^ 2) / 2
              = ‖a + (y - x)‖ ^ 2 / 2 := by
          simpa using
            (congrArg (fun t : ℝ => t / 2) (norm_add_sq_real a (y - x))).symm
        have h2 :
            ‖a‖ ^ 2 / 2 + ⟪a, y - x⟫_ℝ + ‖y - x‖ ^ 2 / 2
              = (‖a‖ ^ 2 + 2 * ⟪a, y - x⟫_ℝ + ‖y - x‖ ^ 2) / 2 := by
          ring
        simpa [h2] using h1
      have hnonneg : 0 ≤ ‖a + (y - x)‖ ^ 2 / 2 := by
        exact div_nonneg (sq_nonneg ‖a + (y - x)‖) (by norm_num)
      simpa [hrewrite] using hnonneg
    calc
      f z + ⟪a, x - z⟫_ℝ - ‖a‖ ^ 2 / 2 ≤ f z + ⟪a, x - z⟫_ℝ - ‖a‖ ^ 2 / 2 +
        (‖a‖ ^ 2 / 2 + ⟪a, y - x⟫_ℝ + ‖y - x‖ ^ 2 / 2) := le_add_of_nonneg_right this
      _ = f z + ⟪a, x - z⟫_ℝ + (⟪a, y - x⟫_ℝ + ‖y - x‖ ^ 2 / 2) := by ring
      _ ≤ g y := second_lower_bound
  have hg : LowerSemicontinuous g := by
    have hcont : Continuous (fun z : E => ‖z - x‖ ^ 2 / 2) := by
      have h1 : Continuous (fun z : E => ‖z - x‖) := (continuous_id.sub continuous_const).norm
      have h2 : Continuous (fun z : E => ‖z - x‖ ^ 2) := h1.pow 2
      have h3 : Continuous (fun z : E => ‖z - x‖ ^ 2 * (1 / 2)) := h2.mul continuous_const
      simpa [div_eq_mul_inv, mul_comm] using h3
    exact hc.add hcont.lowerSemicontinuous
  have epi_closed : IsClosed epi := by
    apply bounded_lowersemicontinuous_to_epi_closed
    · exact lowerSemicontinuousOn_univ_iff.2 hg
    refine ⟨f z + ⟪a, x - z⟫_ℝ - ‖a‖ ^ 2 / 2, ?_⟩
    intro y; exact lower_bound y
  let S := {y : E| g y ≤ g z}
  have eq : S = (g ⁻¹' Set.Iic (g z)) := by constructor
  let ImS := {g y | y ∈ S}
  have neImS : Set.Nonempty ImS := by
    use g z; simp [ImS, S]; use z
  have S_bddbelow : BddBelow ImS := by
    use (f z + ⟪a, x - z⟫_ℝ - ‖a‖ ^ 2 / 2)
    rw [mem_lowerBounds]
    rintro gy ⟨y0, _, gyeq⟩
    rw [← gyeq]; exact lower_bound y0
  have closeds : IsClosed S := by
    rw [eq]
    rw [lowerSemicontinuous_iff_isClosed_preimage] at hg
    exact hg (g z)
  have compacts : IsCompact S := by
    let B := Metric.closedBall (x - a) (‖z - (x - a)‖ + 2)
    have sinb : S ⊆ B := by
      intro u uin
      simp [S] at uin
      apply mem_closedBall_iff_norm.2
      have ieq : f z + ⟪a, u - z⟫_ℝ + ‖u - x‖ ^ 2 / 2 ≤ f z + ‖z - x‖ ^ 2 / 2 + 1 := by
        calc
          f z + ⟪a, u - z⟫_ℝ + ‖u - x‖ ^ 2 / 2 ≤ g u := second_lower_bound u
          _ ≤ f z + ‖z - x‖ ^ 2 / 2 := uin
          _ ≤ f z + ‖z - x‖ ^ 2 / 2 + 1 := by linarith
          _ ≤ f z + ‖z - x‖ ^ 2 / 2 + 1 := by linarith
      rw [add_assoc, add_assoc, add_le_add_iff_left] at ieq
      have eq : ⟪a, u - z⟫_ℝ + ‖u - x‖ ^ 2 / 2 =
          (‖u - (x - a)‖ ^ 2 - ‖a‖ ^ 2 + 2 * ⟪x - z, a⟫_ℝ) / 2 := by
        field_simp; rw [← sub_add, norm_add_sq_real]; ring_nf
        rw [add_assoc, ← add_mul, ← inner_add_left, add_comm, real_inner_comm]; simp
      rw [eq] at ieq
      have ieq2 : ‖u - (x - a)‖ ^ 2 ≤ ‖z - (x - a)‖ ^ 2 + 2 := by
        -- clear the division by 2 on both sides
        have ieq' :=
          (mul_le_mul_of_nonneg_right ieq (by norm_num : 0 ≤ (2 : ℝ)))
        -- simplify ((·)/2)*2 = · and (·/2 + 1)*2 = · + 2
        have ieq' :
            ‖u - (x - a)‖ ^ 2 - ‖a‖ ^ 2 + 2 * ⟪x - z, a⟫_ℝ ≤ ‖z - x‖ ^ 2 + 2 := by
          have h2 : (2 : ℝ) ≠ 0 := by norm_num
          simpa [add_mul, mul_add, div_eq_mul_inv, h2] using ieq'
        rw [sub_add, sub_le_iff_le_add] at ieq'
        rw [add_right_comm, add_comm (‖z - x‖ ^ 2), norm_sub_rev z x] at ieq'
        rw [real_inner_comm, ← norm_sub_sq_real, ← sub_add a, sub_add_comm] at ieq'
        rw [sub_add] at ieq'
        exact ieq'
      have : |‖z - (x - a)‖ + 2| = ‖z - (x - a)‖ + 2 := by
        apply abs_of_pos; apply add_pos_of_nonneg_of_pos (norm_nonneg (z - (x - a)))
        simp
      rw [← abs_norm, ← this, ← sq_le_sq, add_sq]
      calc
        ‖u - (x - a)‖ ^ 2 ≤ ‖z - (x - a)‖ ^ 2 + 2 := ieq2
        _ ≤ ‖z - (x - a)‖ ^ 2 + 2 * ‖z - (x - a)‖ * 2 + 2 ^ 2 := by
          rw [add_assoc, add_le_add_iff_left]; apply le_add_of_nonneg_of_le
          simp; norm_num
--      exact norm_bound
    have compactb : IsCompact B := isCompact_closedBall (x - a) (‖z - (x - a)‖ + 2)
    rw [← closure_eq_iff_isClosed] at closeds; rw [← closeds]
    apply IsCompact.closure_of_subset compactb sinb
  rcases exists_seq_tendsto_sInf neImS S_bddbelow with ⟨fx, _, cfx, fxs⟩
  choose xn xsub xeq using fxs
  rcases IsCompact.tendsto_subseq compacts xsub with ⟨x', _, k, mono, cxk⟩
  have cfxk : Filter.Tendsto (g ∘ xn ∘ k) Filter.atTop (𝓝 (sInf ImS)) := by
    have xkeq : ∀ (n : ℕ), (g ∘ xn ∘ k) n = (fx ∘ k) n := fun n => xeq <| k n
    rw [tendsto_congr xkeq]
    apply Tendsto.comp cfx (StrictMono.tendsto_atTop mono)
  have inepi : (x', sInf ImS) ∈ epi := by
    let p := fun c ↦ (((fun n ↦ xn n) ∘ k) c, (g ∘ xn ∘ k) c)
    have pnin :  ∀ c : ℕ, p c ∈ epi := by simp [epi]; exact fun c ↦ Std.IsPreorder.le_refl (g (p c).1)
    apply IsClosed.isSeqClosed epi_closed pnin
    show Tendsto (fun c ↦ (((fun n ↦ xn n) ∘ k) c, (g ∘ xn ∘ k) c)) atTop (𝓝 (x', sInf ImS))
    apply Tendsto.prodMk_nhds cxk cfxk
  have minima_ieq : g x' ≤ sInf ImS := inepi
  have minima : ∀ w : E, g x' ≤ g w := by
      intro w
      by_cases hw : w ∈ S
      · have gwin : g w ∈ ImS := by use w
        have legw : sInf ImS ≤ g w := by
          rw [Real.sInf_le_iff S_bddbelow neImS]
          intro _ epos; use g w; use gwin; linarith
        linarith
      · have gwnin : g z < g w := by
          simp [S] at hw; simp [g]; exact hw
        have gzin : g z ∈ ImS := by use z; simp [S]
        have legw : sInf ImS ≤ g w := by
          rw [Real.sInf_le_iff S_bddbelow neImS]
          intro _ epos; use g z; use gzin; linarith
        linarith
  constructor
  · use x'; simp [prox_set]; rw [prox_prop, isMinOn_iff]
    intro v _; exact minima v
  · have aux : prox_set f x = {x | IsMinOn g univ x} := by
      simp [prox_set]; ext y
      constructor
      · intro yin; simp [prox_prop] at yin; simp; exact yin
      · intro yin; simp; rw [prox_prop]
        simp at yin; exact yin
    have nes : Nonempty S := by use z; simp [S]
    rw [eq] at compacts; rw [eq] at nes
    rw [aux] -- apply IsCompact_isMinOn_of_isCompact_preimage hc nes compacts
    have seq : {x | IsMinOn g univ x} = (g ⁻¹' Set.Iic (g x')) := by
      ext y
      constructor
      · exact fun hxx => isMinOn_iff.mp hxx x' trivial
      · intro yin; simp at yin
        exact fun x xuniv => le_trans yin ((fun x _ => minima x) x xuniv)
    simp only [seq]
    apply IsCompact.of_isClosed_subset compacts (LowerSemicontinuous.isClosed_preimage hg (g x'))
    apply Set.preimage_mono
    simp only [Set.Iic_subset_Iic]
    exact minima z

theorem prox_well_define (f : E → ℝ) (hc : LowerSemicontinuous f) (lbdf : BddBelow (f '' univ)) :
    ∀ x, ∃ y, prox_prop f x y := by
  intro x
  rcases (prox_set_compact_of_lowersemi f hc lbdf x).1 with ⟨y, yprop⟩
  use y; simp [prox_set] at yprop; exact yprop

theorem prox_well_define_convex (f : E → ℝ) (hc : ContinuousOn f univ)
    (hconv : ConvexOn ℝ univ f) :
  ∀ x, ∃ y, prox_prop f x y := by
  intro x
  rcases (prox_set_compact_of_convex f hc hconv x).1 with ⟨y, yprop⟩
  use y; simp [prox_set] at yprop; exact yprop

/-
  the definition of the proximal operator for a closed convex function
-/
def prox_point_c (f : E → ℝ) (x : E) (hc : LowerSemicontinuous f)
    (lbdf : BddBelow (f '' univ)) : E :=
  have h : ∃ y, prox_set f x y := by
    apply prox_well_define f hc lbdf x
  Classical.choose h

def prox_point_c' (f : E → ℝ) (x : E) (hc : ContinuousOn f univ)
    (hconv : ConvexOn ℝ univ f) : E :=
  have h : ∃ y, prox_set f x y := by
    apply prox_well_define_convex f hc hconv x
  Classical.choose h

section properties

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {s : Set E} {f : E → ℝ} {u x y₁ y₂ : E} {t : ℝ}

open Set InnerProductSpace

/-
  The uniqueness of the proximal for proper convex function
-/
theorem prox_unique_of_convex (f : E → ℝ) (x : E) (hfun : ConvexOn ℝ univ f)
    (h₁ : prox_prop f x y₁) (h₂ : prox_prop f x y₂) : y₁ = y₂ := by
  let g := fun u ↦ f u + ‖u - x‖ ^ 2 / 2
  let m := (1 : ℝ)
  have gsconv : StrongConvexOn univ m g := by
    apply strongconvex_of_convex_add_sq
    show ConvexOn ℝ univ f; apply hfun
  rw [prox_prop] at h₁
  rw [prox_prop] at h₂
  apply Strongly_Convex_Unique_Minima gsconv
  apply h₁; apply h₂; simp; simp; norm_num
/-
   The square of norm is convex on a convex set
-/
lemma convex_of_norm_sq {s : Set E} (x : E) (conv: Convex ℝ s) :
    ConvexOn ℝ s (fun (u : E) ↦ ‖u - x‖ ^ 2 / 2) := by
  rw [ConvexOn]; use conv
  intro y _ z _ a b anneg bnneg absum1
  have eq1 : a • y + b • z - x = a • (y - x) + b • (z - x) := by
    rw [smul_sub, smul_sub, add_comm_sub, sub_sub, ← add_smul, add_comm b a, absum1,
        one_smul, ← add_sub]
  rw [eq1]
  have ieq1 (u v : E) :
      ‖a • u + b • v‖ ^ 2 / 2 ≤ a * (‖u‖ ^ 2 / 2) + b * (‖v‖ ^ 2 / 2) := by
    have hbase :
        ‖a • u + b • v‖ ^ 2 ≤ a * ‖u‖ ^ 2 + b * ‖v‖ ^ 2 := by
      rw [norm_add_sq_real, add_comm, ← add_assoc]
      rw [norm_smul, norm_smul, mul_pow, mul_pow]; simp
      nth_rw 3 [← mul_one a]; nth_rw 3 [← one_mul b]
      rw [← absum1]; ring_nf; rw [add_right_comm]
      rw [add_le_add_iff_right (a ^ 2 * ‖u‖ ^ 2)]
      rw [add_comm]
      rw [add_le_add_iff_right (b ^ 2 * ‖v‖ ^ 2)]
      calc
        ⟪a • u, b • v⟫_ℝ * 2
            ≤ ‖a • u‖ * ‖b • v‖ * 2 := by
              have h := real_inner_le_norm (a • u) (b • v)
              exact mul_le_mul_of_nonneg_right h (by norm_num)
        _ = a * b * (2 * ‖u‖ * ‖v‖) := by
          rw [norm_smul, norm_smul]; simp
          rw [abs_of_nonneg anneg, abs_of_nonneg bnneg]; ring
        _ ≤ b * ‖v‖ ^ 2 * a + b * a * ‖u‖ ^ 2 := by
          have hab_nonneg : 0 ≤ a * b := mul_nonneg anneg bnneg
          have hineq : 2 * ‖u‖ * ‖v‖ ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
            simpa using two_mul_le_add_pow_two (‖u‖) (‖v‖)
          have hmul :
              a * b * (2 * ‖u‖ * ‖v‖) ≤ a * b * (‖u‖ ^ 2 + ‖v‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hineq hab_nonneg
          simp; grind
    have : (1 / 2 : ℝ) * ‖a • u + b • v‖ ^ 2
              ≤ (1 / 2 : ℝ) * (a * ‖u‖ ^ 2 + b * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hbase (by norm_num)
    simp; grind
  have h := ieq1 (y - x) (z - x)
  simpa [smul_eq_mul, div_eq_mul_inv, mul_add, mul_comm, mul_left_comm, mul_assoc] using h

/-
  Sub-derivative at x equal to sub-derivative within univ at x
-/
lemma Subderivat_eq_SubderivWithinAt_univ (f : E → ℝ) :
    SubderivWithinAt f univ u = SubderivAt f u := by
    apply subset_antisymm
    · intro p pin
      rw [SubderivWithinAt] at pin
      rw [← mem_SubderivAt, ← hasSubgradientWithinAt_univ]
      apply pin
    · intro p pin
      rw [← mem_SubderivAt, ← hasSubgradientWithinAt_univ] at pin;
      rw [SubderivWithinAt]
      apply pin

/-
  relation of proximal between a function and its shift
-/
theorem proximal_shift (a : E) {t : ℝ} (tnz : t ≠ 0) (f : E → ℝ):
    ∀ z : E, prox_prop (fun x ↦ f (t • x + a)) x z ↔
      prox_prop (t ^ 2 • f) (t • x + a) (t • z + a) := by
  intro z
  rw [prox_prop, prox_prop, isMinOn_univ_iff, isMinOn_univ_iff]
  simp
  constructor
  · intro cond y
    specialize cond (t⁻¹ • (y - a))
    rw [← smul_assoc, smul_eq_mul, mul_inv_cancel₀] at cond
    simp at cond
    calc
      t ^ 2 * f (t • z + a) + ‖t • z - t • x‖ ^ 2 / 2 =
          t ^ 2 * (f (t • z + a) + ‖z - x‖ ^ 2 / 2) := by
        rw [← smul_sub, norm_smul, mul_pow, mul_add]; field_simp; simp; grind
      _ ≤ t ^ 2 * (f y + ‖t⁻¹ • (y - a) - x‖ ^ 2 / 2) := by
        rw [mul_le_mul_iff_right₀]; use cond; rw [sq_pos_iff]; use tnz
      _ = t ^ 2 * f y + ‖t • ((1 / t) • (y - a) - x)‖ ^ 2 / 2 := by
        rw [mul_add, norm_smul, mul_pow]; field_simp; simp; grind
      _ = t ^ 2 * f y + ‖y - (t • x + a)‖ ^ 2 / 2 := by
        rw [smul_sub, ← smul_assoc, smul_eq_mul, ← sub_sub, sub_right_comm]; field_simp; simp
    use tnz
  · intro cond y
    specialize cond (t • y + a)
    rw [← smul_sub, norm_smul, mul_pow] at cond; simp at cond
    rw [← smul_sub, norm_smul, mul_pow] at cond; simp at cond
    rw [mul_div_assoc, ← mul_add, mul_div_assoc, ← mul_add] at cond
    rw [mul_le_mul_iff_right₀] at cond; use cond; rw [sq_pos_iff]; use tnz

/-
  relation of proximal between a function and its scale
-/
theorem proximal_scale {t : ℝ} (tpos : 0 < t) (f : E → ℝ):
    ∀ z : E, prox_prop (fun x ↦ t • f (t⁻¹ • x)) x z ↔
      prox_prop (t⁻¹ • f) (t⁻¹ • x) (t⁻¹ • z) := by
  intro z
  rw [prox_prop, prox_prop, isMinOn_univ_iff, isMinOn_univ_iff]
  simp
  constructor
  · intro cond y
    specialize cond (t • y)
    have tsq : 0 < t ^ 2 := by field_simp; aesop
    rw [← mul_le_mul_iff_right₀ tsq]
    calc
      t ^ 2 * (t⁻¹ * f (t⁻¹ • z) + ‖t⁻¹ • z - t⁻¹ • x‖ ^ 2 / 2) =
          t * f (t⁻¹ • z) + ‖z - x‖ ^ 2 / 2 := by
        rw [← smul_sub, norm_smul, mul_pow, mul_add, pow_two, ← mul_assoc, mul_assoc _ _ (t⁻¹)]
        rw [mul_inv_cancel₀, mul_div_assoc, ← mul_assoc]; simp
        rw [← pow_two, mul_inv_cancel₀]; repeat simp; repeat linarith
      _ ≤ t * f (t⁻¹ • t • y) + ‖t • y - x‖ ^ 2 / 2 := cond
      _ = t ^ 2 * (t⁻¹ * f y) + ‖t • (y - t⁻¹ • x)‖ ^ 2 / 2 := by
        rw [pow_two t, ← mul_assoc, mul_assoc _ _ (t⁻¹), mul_inv_cancel₀]
        rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀]; simp
        rw [smul_sub, ← smul_assoc, smul_eq_mul, mul_inv_cancel₀]; simp; repeat linarith
      _ = t ^ 2 * (t⁻¹ * f y + ‖y - t⁻¹ • x‖ ^ 2 / 2) := by
        rw [mul_add, norm_smul, mul_pow]; field_simp; simp; grind
  · intro cond y
    specialize cond (t⁻¹ • y)
    have tsq : 0 < t ^ 2 := by field_simp; exact sq_pos_of_pos tpos
    rw [← mul_le_mul_iff_right₀ tsq] at cond
    calc
      t * f (t⁻¹ • z) + ‖z - x‖ ^ 2 / 2 =
          t ^ 2 * (t⁻¹ * f (t⁻¹ • z) + ‖t⁻¹ • z - t⁻¹ • x‖ ^ 2 / 2) := by
        rw [← smul_sub, norm_smul, mul_pow, mul_add, pow_two t, ← mul_assoc, mul_assoc _ _ (t⁻¹)]
        rw [mul_inv_cancel₀, mul_div_assoc, ← mul_assoc]; simp
        rw [← pow_two, mul_inv_cancel₀]; repeat simp; repeat linarith
      _ ≤ t ^ 2 * (t⁻¹ * f (t⁻¹ • y) + ‖t⁻¹ • y - t⁻¹ • x‖ ^ 2 / 2) := cond
      _ = t ^ 2 * (t⁻¹ * f (t⁻¹ • y)) + ‖t • (t⁻¹ • y - t⁻¹ • x)‖ ^ 2 / 2 := by
        rw [mul_add, norm_smul, mul_pow]; field_simp; simp; grind
      _ = t * f (t⁻¹ • y) + ‖y - x‖ ^ 2 / 2 := by
        rw [pow_two t, ← mul_assoc, mul_assoc _ _ (t⁻¹), mul_inv_cancel₀]
        rw [smul_sub, ← smul_assoc, smul_eq_mul, mul_inv_cancel₀]; simp
        rw [← smul_assoc, smul_eq_mul, mul_inv_cancel₀]; simp; repeat linarith

/-
  change of proximal when added a linear components
-/
theorem proximal_add_linear (a : E) (f : E → ℝ):
    ∀ z : E, prox_prop (fun x ↦ f x + ⟪a, x⟫_ℝ) x z ↔
      prox_prop f (x - a) z := by
  intro z
  rw [prox_prop, prox_prop, isMinOn_univ_iff, isMinOn_univ_iff]
  have aux (v : E) : ‖v - (x - a)‖ ^ 2 / 2 =
      ‖v - x‖ ^ 2 / 2 + ⟪a, v⟫_ℝ + (‖a‖ ^ 2 / 2 - ⟪a, x⟫_ℝ) := by
    have hx : v - (x - a) = (v - x) + a := by
      simp [sub_eq_add_neg, add_comm, add_left_comm]
    have h := norm_add_sq_real (v - x) a
    have h' := congrArg (fun t : ℝ => t / 2) (by simpa [hx] using h)
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    have hinner : ⟪v - x, a⟫_ℝ = ⟪a, v⟫_ℝ - ⟪a, x⟫_ℝ := by
      simp [real_inner_comm, inner_sub_right]
    grind
  constructor
  · intro cond y
    specialize cond y
    grind
  · intro cond y
    specialize cond y
    grind

/-
  change of proximal when added a square components
-/
theorem proximal_add_sq (a : E) {l : ℝ} (lpos : 0 < l) (f : E → ℝ):
    ∀ z : E, prox_prop (fun x ↦ f x + l / 2 * ‖x - a‖ ^ 2) x z ↔
      prox_prop ((1 / (l + 1)) • f) ((1 / (l + 1)) • (x + l • a)) z := by
  intro z
  rw [prox_prop, prox_prop, isMinOn_univ_iff, isMinOn_univ_iff]
  have aux (v : E) : ‖v - (1 / (l + 1)) • (x + l • a)‖ ^ 2 / 2 =
      (l + 1)⁻¹ * (l / 2 * ‖v - a‖ ^ 2 + ‖v - x‖ ^ 2 / 2 + (((l + 1)⁻¹ * (‖x + l • a‖ ^ 2)
        - ‖x‖ ^ 2 - l * ‖a‖ ^ 2) / 2)) := by
    rw [div_mul_eq_mul_div, ← add_div, ← add_div, ← mul_div_assoc, div_left_inj']
    rw [norm_sub_sq_real, norm_smul, mul_pow, mul_add, sub_sub, mul_sub, ← mul_assoc, ← pow_two]
    rw [Real.norm_eq_abs, sq_abs, ← inv_eq_one_div, add_sub, add_sub_right_comm]
    rw [add_right_cancel_iff, norm_sub_sq_real, norm_sub_sq_real]
    rw [← mul_sub, mul_add, ← add_assoc, ← sub_sub, inner_smul_right]; simp
    rw [add_sub_right_comm]; simp; rw [mul_sub, ← add_sub_right_comm, ← add_sub_assoc]
    nth_rw 3 [← one_mul (‖v‖ ^ 2)]; rw [← add_mul, ← mul_assoc l, mul_comm l 2, sub_sub]
    rw [mul_assoc, ← mul_add, ← inner_smul_right _ _ l, ← inner_add_right]
    field_simp; simp
  constructor
  · intro cond y
    specialize cond y
    rw [aux, aux]; simp; rw [← mul_add, ← mul_add, mul_le_mul_iff_right₀]
    linarith [cond]; simp; linarith
  · intro cond y
    specialize cond y
    rw [aux, aux] at cond; simp at cond; rw [← mul_add, ← mul_add, mul_le_mul_iff_right₀] at cond
    linarith [cond]; simp; linarith

end properties

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {s : Set E} {f : E → ℝ} {u x: E} {t : ℝ}

/-
  u minimize the proximal at x iff x - u is subgradient
-/
theorem prox_iff_subderiv (f : E → ℝ) (hfun : ConvexOn ℝ univ f) :
    ∀ u : E, prox_prop f x u ↔ x - u ∈ SubderivAt f u := by
  intro u; rw [prox_prop, ← HasSubgradientAt_zero_iff_isMinOn, mem_SubderivAt]
  let g := fun u ↦ ‖u - x‖ ^ 2 / 2
  have hg : ConvexOn ℝ Set.univ g := by apply convex_of_norm_sq x (convex_univ)
  have hcg : ContinuousOn g univ := by
    have h1 : Continuous (fun z : E => ‖z - x‖) :=
      (continuous_id.sub continuous_const).norm
    have h2 : Continuous (fun z : E => ‖z - x‖ ^ 2) := h1.pow 2
    have h3 : Continuous (fun z : E => ‖z - x‖ ^ 2 * (1 / 2)) := h2.mul continuous_const
    simp; exact Continuous.div_const h2 2
  show 0 ∈ SubderivAt (f + g) u ↔ x - u ∈ SubderivAt f u
  have : SubderivAt (f + g) u = SubderivAt (g + f) u := by
    unfold SubderivAt; ext z; rw [Set.mem_setOf, Set.mem_setOf];
    constructor
    repeat
    unfold HasSubgradientAt; intro hy y; specialize hy y; simp at hy ⊢; linarith
  rw [this, ← SubderivAt.add hg hfun hcg]
  have subg : SubderivAt g u = {u - x} := by
    let g' := fun u ↦ u - x
    have gderiv : ∀ x, HasGradientAt g (g' x) x := gradient_of_sq
    have : SubderivWithinAt g univ u = {g' u} := by
      apply SubderivWithinAt_eq_gradient; simp
      have gconv : ConvexOn ℝ univ g := by
        rcases hfun with ⟨conv, _⟩
        apply convex_of_norm_sq
        apply conv
      apply gconv; apply gderiv
    rw [← Subderivat_eq_SubderivWithinAt_univ, this]
  rw [subg]; simp

/-
  If f is differentiable and convex on E, then u minimize the proximal at x iff ∇f(u) = x - u
-/
theorem prox_iff_grad (f : E → ℝ) {f' : E → E} (hfun : ConvexOn ℝ univ f)
    (hdiff : ∀ x, HasGradientAt f (f' x) x) :
    ∀ u : E, prox_prop f x u ↔ f' u = x - u := by
  intro u
  have iff_subderiv : ∀ u : E, prox_prop f x u ↔ x - u ∈ SubderivAt f u := by
    apply prox_iff_subderiv
    apply hfun
  specialize iff_subderiv u
  rw [iff_subderiv, ← Subderivat_eq_SubderivWithinAt_univ]
  have subderiv_eq_gradient : SubderivWithinAt f univ u = {f' u} := by
    apply SubderivWithinAt_eq_gradient; simp
    apply hfun; apply hdiff
  rw [subderiv_eq_gradient]; simp
  apply eq_comm

/-
  If f is differentiable and convex on E, then u minimize the proximal for t*f at x iff
  t ∇f(u) = x - u
-/
theorem prox_iff_grad_smul (f : E → ℝ) {f' : E → E} (t : ℝ) (hfun : ConvexOn ℝ univ f)
    (hdiff : ∀ x, HasGradientAt f (f' x) x) (tnonneg : 0 ≤ t) :
    ∀ u : E, prox_prop (t • f) x u ↔ t • f' u = x - u := by
  intro u
  let g := fun u ↦ (t • f) u
  let g' := fun u ↦ t • f' u
  have gconv : ConvexOn ℝ univ g := by
    apply ConvexOn.smul tnonneg hfun
  have gderiv : ∀ x, HasGradientAt g (g' x) x := by
    intro x
    simp only [Pi.smul_apply, g, g']
    apply HasGradientAt.const_smul'
    exact hdiff x
  rw [prox_iff_subderiv]
  have : SubderivWithinAt g univ u = {g' u} := by
      apply SubderivWithinAt_eq_gradient; simp
      apply gconv; apply gderiv
  rw [← Subderivat_eq_SubderivWithinAt_univ, this]; simp
  apply eq_comm
  apply gconv

/-
  u minimize the proximal for t*f at x iff (x - u)/t is subgradient
-/
theorem prox_iff_subderiv_smul (f : E → ℝ) {t : ℝ} (hfun : ConvexOn ℝ univ f) (ht : 0 < t) :
    ∀ u : E, prox_prop (t • f) x u ↔ (1 / t) • (x - u) ∈ (SubderivAt f u) := by
  intro u
  let g := fun u ↦ (t • f) u
  have tnonneg : 0 ≤ t := by linarith
  have gconv : ConvexOn ℝ univ g := by
    apply ConvexOn.smul tnonneg hfun
  rw [prox_iff_subderiv, ← mem_SubderivAt, ← mem_SubderivAt]
  rw [HasSubgradientAt, HasSubgradientAt]
  constructor
  · intro cond y
    specialize cond y; simp at cond
    rw [inner_smul_left]; simp
    rw [← mul_le_mul_iff_right₀ ht]; ring_nf; field_simp
    exact cond
  · intro cond y
    specialize cond y
    have hmul0 := mul_le_mul_of_nonneg_left cond (le_of_lt ht)
    have hmul : t * f y ≥ t * f u + t * ((1 / t) * ⟪x - u, y - u⟫_ℝ) := by
      simpa [mul_add, mul_assoc, inner_smul_left] using hmul0
    have htne : t ≠ 0 := ne_of_gt ht
    have eqt : t * ((1 / t) * ⟪x - u, y - u⟫_ℝ) = ⟪x - u, y - u⟫_ℝ := by
      field_simp [htne]
    simp; grind
  exact gconv

end
