import Mathlib.Data.Real.NNReal
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Abs
-- import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Finsupp
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Basis
import Mathlib.Data.Real.ConjugateExponents
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompleteLattice
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian

noncomputable
section

open NNReal BigOperators Real Set

-- A.1 Vectors and norms

-- A.1.1 Norms
namespace Norms
/-
Definition A.1 A mapping Φ : H → R + is said to define a norm on H if it verifies the following
axioms:
• definiteness: ∀x ∈ H, Φ(x) = 0 ⇔ x = 0;
• homogeneity: ∀x ∈ H, ∀α ∈ R, Φ(αx) = |α|Φ(x);
• triangle inequality: ∀x, y ∈ H, Φ(x + y) ≤ Φ(x) + Φ(y).
-/
class norm (ℍ) [AddCommMonoid ℍ] [Module ℝ ℍ] where
  --  mapping Φ : H → R + is said to define a norm on H
  φ : ℍ → ℝ≥0
  -- definiteness: ∀x ∈ H, Φ(x) = 0 ⇔ x = 0;
  definiteness : ∀ (x : ℍ), φ x = 0 ↔ x = 0
  -- homogeneity: ∀x ∈ H, ∀α ∈ R, Φ(αx) = |α|Φ(x)
  homogeneity : ∀ (x : ℍ), ∀ (α : ℝ), φ (α • x) = |α| * φ x
  -- triangle inequality: ∀x, y ∈ H, Φ(x + y) ≤ Φ(x) + Φ(y).
  triangle_inequality: ∀ (x y : ℍ), φ (x + y) ≤ φ x + φ y

export Inhabited (default)

/-
A norm is typically denoted by ‖ · ‖.
-/
-- notation n "‖" x "‖" => norm.φ n x
/-
Examples of vector norms are the absolute value on ℝ and the Euclidean (or L₂) norm on ℝᴺ .
-/
instance L₂ : norm (Fin N → ℝ) where
  φ := λ x ↦ sqrt (∑' j, (nnabs (x j)) ^ 2)
  definiteness := sorry
  homogeneity := sorry
  triangle_inequality := sorry

scoped notation "‖" x "‖₂" => L₂.φ x

instance Lₚ (p : ℕ) (hp : p ≥ 1) : norm (Fin N → ℝ) where
  φ := λ x ↦ (∑' j, (nnabs (x j)) ^ p) ^ (1 / p)
  definiteness := sorry
  homogeneity := sorry
  triangle_inequality := sorry

instance L₁ : norm (Fin N → ℝ) where
  φ := λ x ↦ ∑' j, nnabs (x j)
  definiteness := sorry
  homogeneity := sorry
  triangle_inequality := sorry

scoped notation "‖" x "‖₁" => L₁.φ x

-- TODO; この型の関数が必要
@[coe]
def coe_WithBot_to_NNReal (r : WithBot ℝ) : ℝ≥0 :=
  match r with
  | none => 0  -- 実際にはリストが空になることはないため、不要な分岐
  | some r => Real.toNNReal r

instance : CoeTC (WithBot ℝ) ℝ≥0 := ⟨coe_WithBot_to_NNReal⟩

instance L_inf : norm (Fin N → ℝ) where
  φ := λ x ↦ ⨆ i, nnabs (x i)
  definiteness := sorry
  homogeneity := sorry
  triangle_inequality := sorry

scoped notation "‖" x "‖_inf" => L_inf.φ x

variable {N} {x : Fin N → ℝ} {h : 1 ≤ N}

theorem lm1 {n : ℕ} {P : Fin (n + 1) → ℝ≥0} :
    ∑' (i : Fin (n + 1)), P i = P ⟨n, (by norm_num)⟩ + ∑' (i : Fin n), P i := by
  sorry

theorem A_3 : ‖x‖₂    ≤ ‖x‖₁ ∧ ‖x‖₁ ≤ NNReal.sqrt N * ‖x‖₂ := by
  rw [L₁, L₂]
  simp
  constructor
  . apply NNReal.sqrt_le_iff.mpr
    induction' N with n hi
    . contradiction
    . simp only [lm1]
      have n' : Fin (n + 1) := ⟨n, (by norm_num)⟩
      calc
        nnabs (x ⟨n, (by norm_num)⟩) ^ 2 + ∑' (i : Fin n), nnabs (x i) ^ 2
        -- _ ≤ nnabs (x ⟨n, (by norm_num)⟩) ^ 2 + (∑' (i : Fin n), nnabs (x i)) ^ 2 := by rw [@hi x _]  -- xの型が異なる
        _ ≤ (nnabs (x ⟨n, (by norm_num)⟩) + ∑' (i : Fin n), nnabs (x i)) ^ 2 := by sorry
  . rw [← NNReal.sqrt_mul]
    apply NNReal.le_sqrt_iff.mpr
    sorry
theorem A_4 : ‖x‖_inf ≤ ‖x‖₂ ∧ ‖x‖₂ ≤ NNReal.sqrt N * ‖x‖_inf := sorry
theorem A_5 : ‖x‖_inf ≤ ‖x‖₁ ∧ ‖x‖₁ ≤             N * ‖x‖_inf := sorry
-- ∀ {P : Fin 1 → ℝ≥0}, ∑' (i : Fin 1), P i = P ⟨0, (by norm_num)⟩

variable {p : ℕ} {hp : p ≥ 1}

set_option quotPrecheck false
local notation "‖" x "‖p" => (Lₚ p hp).φ x

theorem A_6 : ‖x‖_inf ≤ ‖x‖p ∧ ‖x‖p ≤ N ^ (1 / p) * ‖x‖_inf := by
  rw [L_inf, Lₚ]
  simp
  sorry

variable [NormedAddCommGroup (Fin N → ℝ)] [InnerProductSpace ℝ (Fin N → ℝ)]
-- def inner (x y : Fin N → ℝ) : ℝ := ∑' i, x i * y i

-- notation "⟪" x "," y "⟫" => inner x y
#check Pi.instZero

theorem zero_inner {x : Fin N → ℝ}: ⟪0, x⟫_ℝ = 0 := by
  sorry

theorem inner_zero {x : Fin N → ℝ}: ⟪x, 0⟫_ℝ = 0 := by
  sorry

section

variable {q : ℕ} {hq : q ≥ 1}

set_option quotPrecheck false
local notation "‖" x "‖q" => (Lₚ q hq).φ x

theorem holder_inequality {hd : IsConjugateExponent p q} :
    ∀ x y : Fin N → ℝ, |⟪x, y⟫_ℝ| ≤ ‖x‖p * ‖y‖q := by
  intro x y
  by_cases h' : x = 0 ∨ y = 0
  . -- The statement holds trivially for x = 0 or y = 0
    rcases h' with (hx | hy)
    . rw [hx]
      rw [zero_inner, abs_zero]
      apply zero_le (‖0‖p * ‖y‖q)
    . rw [hy]
      rw [inner_zero, abs_zero]
      apply zero_le (‖x‖p * ‖0‖q)
  . -- thus, we can assume x ≠ 0 and y ≠ 0.
    push_neg at h'
    have ⟨hnx, hny⟩ := h'

    have hpne : (p : ℝ) ≠ 0 := by
      apply ne_of_gt
      apply lt_of_lt_of_le
      apply zero_lt_one
      simpa
    have hqne : (q : ℝ) ≠ 0 := by
      apply ne_of_gt
      apply lt_of_lt_of_le
      apply zero_lt_one
      simpa

    -- Let a, b > 0. By the concavity of log (see definition B.7), we can write
    have : ∀ (a b : ℝ), a > 0 ∧ b > 0 → log (1 / p * a ^ p + 1 / q * b ^ q) ≥ log (a * b) := by
      rintro a b ⟨ha, hb⟩
      calc
        log (1 / p * a ^ p + 1 / q * b ^ q)
        _ ≥ 1 / p * log (a ^ p) + 1 / q * log (b ^ q) := sorry
        _ = log a + log b := by
          simp [log_pow, ← mul_assoc]
          rw [inv_mul_cancel hpne, inv_mul_cancel hqne, one_mul, one_mul]
        _ = log (a * b) := by rw [← log_mul (ne_of_gt ha) (ne_of_gt hb)]

    -- Taking the exponential of the left- and right-hand sides gives
    have young_inequality : ∀ (a b : ℝ), a > 0 ∧ b > 0 →
        1 / p * a ^ p + 1 / q * b ^ q ≥ a * b := by
      rintro a b ⟨ha, hb⟩
      have hx : 1 / p * a ^ p + 1 / q * b ^ q > 0 := sorry
      have hy : a * b > 0 := sorry
      apply (log_le_log hy hx).mp (this a b ⟨ha, hb⟩)
    -- which is known as Young’s inequality.
    -- Using this inequality with a = |x j |/‖x‖p and b = |y j |/‖y‖q for j ∈ [N ] and summing up gives
    have : (∑' i, |x i * y i|) / (‖x‖p * ‖y‖q) ≤ 1 :=
      calc
        (∑' i, |x i * y i|) / (‖x‖p * ‖y‖q)
        _ ≤ 1 / p * (‖x‖p / ‖x‖p) + 1 / q * (‖y‖q / ‖y‖q) := sorry
        _ = 1 / p + 1 / q := by
          rw [div_self, div_self, mul_one, mul_one]
          . intro hnormzero
            -- have := ((Lₚ p hp).definiteness y).mp hnormzero -- NNRealになってしまっている
            sorry
          sorry
        _ = 1 := by rw [hd.inv_add_inv_conj]
    sorry

end

theorem sqrt_eq_pow_half (x : ℝ≥0) : NNReal.sqrt x = x ^ (1 / 2) := by
  sorry

theorem l2_eq_lp : ‖x‖₂ = (Lₚ 2 (by norm_num)).φ x := by
  rw [L₂, Lₚ]
  simp
  rw [sqrt_eq_pow_half]

theorem cauchy_schwarz_inequality : ∀ x y : Fin N → ℝ, |⟪x, y⟫_ℝ| ≤ ‖x‖₂ * ‖y‖₂ := by
  intro x y
  rw [l2_eq_lp, l2_eq_lp]
  apply holder_inequality x y
  constructor
  . norm_num
  . ring

class hyperplane (w : Fin N → ℝ) (b : ℝ) (𝓗 : Set (Fin N → ℝ)) where
  prop: ∀ x ∈ 𝓗, ⟪w, x⟫_ℝ + b = 0

section

variable {w : Fin N → ℝ} {b}
-- A.12
def dₚ(x : Fin N → ℝ) (𝓗 : Set (Fin N → ℝ)) [hyperplane w b 𝓗] : ℝ :=
  ⨅ x' ∈ 𝓗, ‖x' - x‖p

theorem A_13 {q : ℕ} {hq : q ≥ 1} {hd : IsConjugateExponent p q} (x : Fin N → ℝ) (𝓗 : Set (Fin N → ℝ)) [hyperplane w b 𝓗] :
    @dₚ N p hp _ _ w b x 𝓗 _ = (⟪w, x⟫_ℝ + b) / (Lₚ q hq).φ w := by
  sorry

end

section

variable {q : ℕ} {hq : p ≤ q}

set_option quotPrecheck false
local notation "‖" x "‖q" => (Lₚ q (le_trans hp hq)).φ x

theorem proposition_A_6 (x : Fin N → ℝ) : ‖x‖q ≤ ‖x‖p ∧ ‖x‖p ≤ N ^ (1 / p - 1 / q) * ‖x‖q := by
  -- First, assume x 6 = 0, otherwise the inequalities hold trivially.
  by_cases h : x = 0
  . have hp0 := ((Lₚ p hp).definiteness x).mpr h
    have hq0 := ((Lₚ q (le_trans hp hq)).definiteness x).mpr h
    rw [hp0, hq0]
    simp
  constructor
  . -- Then the first inequality holds using 1 ≤ p ≤ q as follows:
    have :=
      calc
        (‖x‖p / ‖x‖q) ^ p
        _ = (∑' i, ((x i).toNNReal / (‖x‖q))) ^ p := sorry
        _ ≥ (∑' i, ((x i).toNNReal / (‖x‖q))) ^ q := sorry
        _ = 1 := sorry
    sorry
  -- Finally, the second inequality follows by using Hölder’s inequality (proposition A.4)
  calc
    ‖x‖p
    _ = (∑' i, (nnabs (x i)) ^ p) ^ (1 / p) := by rw [Lₚ]; simp
    _ ≤ ((∑' i, ((nnabs (x i)) ^ p) ^ (q / p)) ^ (p / q) * (∑' i : Fin N, 1 ^ (q / (q - p))) ^ (1 - p / q)) ^ (1 / p) := sorry
    _ = N ^ (1 / p - 1 / q) * ‖x‖q := sorry

end

end Norms

namespace Matrices

open Matrix

section

variable {m n : ℕ} {M : Matrix (Fin m) (Fin n) ℝ}

example : Mᵀ i j = M j i := by
  simp only [Matrix.transpose_apply]

variable {p : ℕ} {N : Matrix (Fin n) (Fin p) ℝ}

example : (M * N)ᵀ = Nᵀ * Mᵀ := by
  simp only [Matrix.transpose_mul]

end

section

variable {m : ℕ} {M : Matrix (Fin m) (Fin m) ℝ}

example : M.IsSymm ↔ ∀ i j, M i j = M j i := by
  apply IsSymm.ext_iff.trans
  tauto

example : M.IsSymm ↔ M = Mᵀ := by
  rw [Matrix.IsSymm]
  tauto

example : trace M = ∑ i, M i i := by
  simp only [trace, diag_apply]

end

example {m n: ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (N : Matrix (Fin n) (Fin m) ℝ) :
    trace (M * N) = trace (N * M) := trace_mul_comm M N

example {m n p: ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (N : Matrix (Fin n) (Fin p) ℝ) (P : Matrix (Fin p) (Fin m) ℝ) :
    trace (M * N * P) = trace (P * M * N) ∧ trace (P * M * N) = trace (N * P * M) := by
  constructor <;> rw [trace_mul_comm, Matrix.mul_assoc]


example {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) [Invertible M] : M * M⁻¹ = 1 ∧ M⁻¹ * M = 1 := by
  constructor
  . apply mul_inv_of_invertible
  . apply inv_mul_of_invertible

open Norms

example {m n p: ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (N : Matrix (Fin n) (Fin p) ℝ) (nM: norm (Matrix (Fin m) (Fin n) ℝ)) (nN: norm (Matrix (Fin n) (Fin p) ℝ))  (nP: norm (Matrix (Fin m) (Fin p) ℝ)):
    nP.φ (M * N) = nM.φ M * nN.φ N := by
  sorry

section

variable {m n : ℕ} (p : ℕ) (hp : p ≥ 1)

set_option quotPrecheck false
local notation "‖" x "‖p" => (Lₚ p hp).φ x

instance MatrixNorm : norm (Matrix (Fin m) (Fin n) ℝ) where
  φ := λ M ↦ ⨆ x ∈ {x | ‖x‖p ≤ 1}, ‖mulVec M x‖p
  definiteness := sorry
  homogeneity := sorry
  triangle_inequality := sorry

instance FrobeniusNorm : norm (Matrix (Fin m) (Fin n) ℝ) where
  φ := λ M ↦ sqrt (∑ i : Fin m, ∑ j : Fin n, (M i j).toNNReal ^ 2)
  definiteness := sorry
  homogeneity := sorry
  triangle_inequality := sorry

end

local notation "‖" M "‖F" => FrobeniusNorm.φ M

def FrobeniusProduct {m n: ℕ} (M N : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  trace (Mᵀ * N)

theorem lm1 {Λ} {P Q : Λ → ℝ} [Fintype Λ] (h : ∀ i, P i = Q i) : ∑ i, P i = ∑ i, Q i := by
  sorry

theorem lm2 {Λ} {P : Λ → ℝ≥0} [Fintype Λ] : ↑(∑ i, P i) = ∑ i, ↑(P i) := by
  sorry

theorem A_19_1 {m n: ℕ} {M : Matrix (Fin m) (Fin n) ℝ} : ‖M‖F ^ 2 = toNNReal (trace (Mᵀ * M)) := by
  unfold trace
  unfold diag
  unfold FrobeniusNorm
  simp
  have : ∀ i, (Mᵀ * M) i i = ∑ j, Mᵀ i j * M j i := λ i ↦ mul_apply (M := Mᵀ) (N := M)
  rw [lm1 this]
  -- rw [congr_fun (@mul_apply Mᵀ M i i)]
  sorry

end Matrices
