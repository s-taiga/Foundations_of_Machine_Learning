import Mathlib.Analysis.NormedSpace.lpSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable
section

open Real ENNReal NNReal IsROrC BigOperators

-- A.1 Vectors and norms
/-
We will denote by H a vector space whose dimension may be infinite.
-/
variable (ℍ)
variable [NormedGroup ℍ] [NormedAddCommGroup ℍ] [NormedSpace ℝ ℍ]

-- A.1.1 Norms

/-
Definition A.1 A mapping Φ : H → R + is said to define a norm on H if it verifies the following
axioms:
• definiteness: ∀x ∈ H, Φ(x) = 0 ⇔ x = 0;
• homogeneity: ∀x ∈ H, ∀α ∈ R, Φ(αx) = |α|Φ(x);
• triangle inequality: ∀x, y ∈ H, Φ(x + y) ≤ Φ(x) + Φ(y).
-/
example : ℍ → ℝ≥0 := fun x : ℍ ↦ ‖x‖₊

theorem definiteness : ∀ x : ℍ, ‖x‖₊ = 0 ↔ x = 0 := fun x ↦ nnnorm_eq_zero (a := x)
theorem homogenity : ∀ x : ℍ, ∀ α : ℝ, ‖α • x‖₊ = |α| * ‖x‖₊ := by
  intro x α
  rw [nnnorm_smul]
  simp
theorem triangle_inequality : ∀ x y : ℍ, ‖x + y‖₊ ≤ ‖x‖₊ +  ‖y‖₊ := nnnorm_add_le
/-
Examples of vector norms are the absolute value on ℝ and the Euclidean (or L₂) norm on ℝᴺ .
-/
variable (ℍ' : ℕ → Type*) [∀ i, NormedAddCommGroup (ℍ' i)]
example : ∀ (x : lp ℍ' 2), ‖x‖ = (∑' i, ‖x i‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := fun x ↦ lp.norm_eq_tsum_rpow (by norm_num) x

/-
More generally, for any p ≥ 1 the L p norm is defined on R N as (A.1)
-/
example : ∀ p ≥ 1, (x : lp ℍ' p) → ‖x‖ = (∑' i, ‖x i‖ ^ (ENNReal.toReal p)) ^ (1 / (ENNReal.toReal p)) := by
  intro p hp₁ x
  have : 0 < ENNReal.toReal p := by
    sorry
  apply lp.norm_eq_tsum_rpow this x

/-
The L 1 , L 2 , and L ∞ norms are some of the most commonly used norms, where ‖x‖∞ = max j∈[N ] |x j|.
-/
example : ∀ (x : lp ℍ' ∞), ‖x‖ = ⨆ i, ‖x i‖ := lp.norm_eq_ciSup

/-
Two norms k · k and k · k 0 are said to be equivalent iff there exists α, β > 0 such that for all x ∈ H,
(A.2)
-/
def equivalent (n₁ n₂ : NNNorm ℍ) : Prop :=
  ∃ α β: ℝ≥0, ∀ x : ℍ, α * (n₁.nnnorm x) ≤ (n₂.nnnorm x) ∧ (n₂.nnnorm x) ≤ β * (n₁.nnnorm x)

/-
The following general inequalities relating these norms can be proven straightforwardly:
-/
-- lp ℍ p は比較ができなさそう

/-
Definition A.2 (Hilbert space) A Hilbert space is a vector space equipped with an inner product
h·, ·i and that is complete (all Cauchy sequences are convergent). The inner product induces a
norm defined as follows:
-/
variable (𝕜 ℍ: Type*) [NormedAddCommGroup ℍ] [IsROrC 𝕜] [InnerProductSpace 𝕜 ℍ]
local notation "⟪" x ", " y "⟫" => @inner 𝕜 ℍ _ x y

example : ∀ x : ℍ, ‖x‖ = Real.sqrt (re ⟪x, x⟫) := norm_eq_sqrt_inner


-- A.1.2 Dual norms

/-
Definition A.3 Let k · k be a norm on R N . Then, the dual norm k · k ∗ associated to k · k is the
norm defined by
-/
#check lp.tsum_mul_le_mul_norm

theorem holder_inequality {p q : ℝ≥0∞} (hpq : p.toReal.IsConjugateExponent q.toReal)
    (x : lp ℍ' p) (y : lp ℍ' q) : ∑' i, ‖x i‖ * ‖y i‖ ≤ ‖x‖ * ‖y‖ := by
  by_cases h : x = 0 ∨ y = 0
  . -- The statement holds trivially for x = 0 or y = 0
    rcases h with hx | hy
    . rw [hx]
      simp
    . rw [hy]
      simp
  . -- thus, we can assume x ≠ 0 and y ≠ 0.
    rw [not_or, ← Ne, ← Ne] at h
    have ⟨hnx, hny⟩ := h

    -- Let a, b > 0. By the concavity of log (see definition B.7), we can write
    have : ∀ (a b : ℝ), a > 0 ∧ b > 0 → log (1 / p.toReal * a ^ p.toReal + 1 / q.toReal * b ^ q.toReal) ≥ log (a * b) := by
      rintro a b ⟨ha, hb⟩
      calc
        log (1 / p.toReal * a ^ p.toReal + 1 / q.toReal * b ^ q.toReal)
        _ ≥ 1 / p.toReal * log a ^ p.toReal + 1 / q.toReal * log b ^ q.toReal := sorry
        _ = log a + log b := sorry
        _ = log (a * b) := by rw [← log_mul (ne_of_gt ha) (ne_of_gt hb)]

    -- Taking the exponential of the left- and right-hand sides gives
    have young_inequality : ∀ (a b : ℝ), a > 0 ∧ b > 0 →
        1 / p.toReal * a ^ p.toReal + 1 / q.toReal * b ^ q.toReal ≥ a * b := by
      rintro a b ⟨ha, hb⟩
      have hx : 1 / p.toReal * a ^ p.toReal + 1 / q.toReal * b ^ q.toReal > 0 := sorry
      have hy : a * b > 0 := sorry
      apply (log_le_log hy hx).mp (this a b ⟨ha, hb⟩)
    -- which is known as Young’s inequality.
    -- Using this inequality with a = |x j |/‖x‖p and b = |y j |/‖y‖q for j ∈ [N ] and summing up gives
    have : (∑' i, ‖x i‖ * ‖y i‖) / ‖x‖ * ‖y‖ ≤ 1 :=
      calc
        (∑' i, ‖x i‖ * ‖y i‖) / ‖x‖ * ‖y‖
        _ ≤ 1 / p.toReal * ‖x‖^p.toReal / ‖x‖^p.toReal + 1 / q.toReal * ‖y‖^q.toReal / ‖y‖^q.toReal := sorry
        _ = 1 / p.toReal + 1 / q.toReal := sorry
        _ = 1 := sorry
    -- simp [div_le_iff (by norm_num) this]
    sorry

theorem cauchy_schwarz_inequality_in_lib (x y : ℍ) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm x y


end
