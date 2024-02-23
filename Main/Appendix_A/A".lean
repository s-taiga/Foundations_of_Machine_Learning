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
import Mathlib.Topology.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Fin.Basic

noncomputable
section

open NNReal BigOperators Real Set Filter
open scoped Topology

-- A.1 Vectors and norms

-- A.1.1 Norms
namespace Norms
/-
Definition A.1 A mapping Φ : ℍ → ℝ+ is said to define a norm on H if it verifies the following
axioms:
• definiteness: ∀x ∈ H, Φ(x) = 0 ⇔ x = 0;
• homogeneity: ∀x ∈ H, ∀α ∈ R, Φ(αx) = |α|Φ(x);
• triangle inequality: ∀x, y ∈ H, Φ(x + y) ≤ Φ(x) + Φ(y).
-/
class norm (ℍ) [AddCommMonoid ℍ] [Module ℝ ℍ] where
  --  mapping Φ : H → ℝ+ is said to define a norm on ℍ
  φ : ℍ → ℝ≥0
  -- definiteness: ∀x ∈ ℍ, Φ(x) = 0 ⇔ x = 0;
  definiteness : ∀ (x : ℍ), φ x = 0 ↔ x = 0
  -- homogeneity: ∀x ∈ ℍ, ∀α ∈ ℝ, Φ(αx) = |α|Φ(x)
  homogeneity : ∀ (x : ℍ), ∀ (α : ℝ), φ (α • x) = |α| * φ x
  -- triangle inequality: ∀x, y ∈ ℍ, Φ(x + y) ≤ Φ(x) + Φ(y).
  triangle_inequality: ∀ (x y : ℍ), φ (x + y) ≤ φ x + φ y

export Inhabited (default)

/-
A norm is typically denoted by ‖ · ‖.
-/
-- notation n "‖" x "‖" => norm.φ n x
/-
Examples of vector norms are the absolute value on ℝ and the Euclidean (or L₂) norm on ℝᴺ .
-/
variable {N : ℕ}
instance L₂ : norm (Fin N → ℝ) where
  φ := λ x ↦ toNNReal <| Real.sqrt (∑ j, |x j| ^ 2)
  definiteness := sorry
  homogeneity := sorry
  triangle_inequality := sorry

scoped notation "‖" x "‖₂" => L₂.φ x

/-
More generally, for any p ≥ 1 the Lₚ norm is defined on ℝᴺ as
-/
instance Lₚ (p : ℕ) (hp : p ≥ 1) : norm (Fin N → ℝ) where
  φ := λ x ↦ toNNReal <| (∑ j, |x j| ^ p) ^ (1 / p)
  definiteness := sorry
  homogeneity := sorry
  triangle_inequality := sorry

/-
The L₁ , L₂ , and L∞ norms are some of the most commonly used norms, where ‖x‖∞ = max j∈[ℕ] |xⱼ|.
-/
instance L₁ : norm (Fin N → ℝ) where
  φ := λ x ↦ toNNReal <| ∑ j, |x j|
  definiteness := sorry
  homogeneity := sorry
  triangle_inequality := sorry

scoped notation "‖" x "‖₁" => L₁.φ x

instance L_inf : norm (Fin N → ℝ) where
  φ := λ x ↦ toNNReal <| ⨆ i, |x i|
  definiteness := sorry
  homogeneity := sorry
  triangle_inequality := sorry

scoped notation "‖" x "‖_inf" => L_inf.φ x

/-
Two norms ‖·‖ and ‖·‖ 0 are said to be equivalent iff there exists α, β > 0 such that for all x ∈ ℍ,
-/
def NormEquiv {ℍ} [AddCommMonoid ℍ] [Module ℝ ℍ] (n₁ n₂ : norm ℍ) :=
  ∃ α > 0, ∃ β > 0, ∀ x : ℍ, α * n₁.φ x ≤ n₂.φ x ∧ n₂.φ x ≤ β * n₁.φ x

variable {x : Fin N → ℝ} {h : 1 ≤ N}

/-
The following general inequalities relating these norms can be proven straightforwardly:
-/

theorem A_3 : ‖x‖₂    ≤ ‖x‖₁ ∧ ‖x‖₁ ≤ NNReal.sqrt N * ‖x‖₂ := sorry
theorem A_4 : ‖x‖_inf ≤ ‖x‖₂ ∧ ‖x‖₂ ≤ NNReal.sqrt N * ‖x‖_inf := sorry
theorem A_5 : ‖x‖_inf ≤ ‖x‖₁ ∧ ‖x‖₁ ≤             N * ‖x‖_inf := sorry

/-
The second inequality of the first line can be shown using the Cauchy-Schwarz inequality presented later while the other inequalities are clear.
These inequalities show the equivalence of these three norms.
-/
example : @L₂ N = L₁ := sorry
example : @L_inf N = L₂ := sorry
example : @L_inf N = L₁ := sorry

/-
More generally, all norms on a finite-dimensional space are equivalent.
-/
example {n₁ n₂ : norm (Fin N → ℝ)} : n₁ = n₂ := sorry

variable {p : ℕ} {hp : p ≥ 1}

set_option quotPrecheck false
local notation "‖" x "‖p" => (Lₚ p hp).φ x

/-
The following additional properties hold for the L∞ norm: for all x ∈ ℍ,
-/
theorem A_6 : ‖x‖_inf ≤ ‖x‖p ∧ ‖x‖p ≤ N ^ (1 / p) * ‖x‖_inf := by
  sorry

-- theorem A_7 : Tendsto (λ p ↦ (Lₚ p _).φ x) atTop (𝓝 ‖x‖_inf) := by
--   sorry

variable [NormedAddCommGroup (Fin N → ℝ)] [InnerProductSpace ℝ (Fin N → ℝ)]

-- A.1.2 Dual norms
/-
Definition A.3 Let ‖·‖ be a norm on ℝᴺ . Then, the dual norm ‖·‖∗ associated to ‖·‖ is the norm defined by
-/
-- A.9
instance DualNorm (n₁ : norm (Fin N → ℝ)) : norm (Fin N → ℝ) where
  φ := λ y ↦ toNNReal <| ⨆ x ∈ {x | n₁.φ x = 1}, |⟪x, y⟫_ℝ|
  definiteness := sorry
  homogeneity := sorry
  triangle_inequality := sorry

/-
For any p, q ≥ 1 that are conjugate that is such that 1/p + 1/q = 1,
-/
example : ∀ p ≥ 1, ∀ q ≥ 1, IsConjugateExponent p q ↔ 1 / p + 1 / q = 1 := sorry

section

variable {q : ℕ} {hq : q ≥ 1}

set_option quotPrecheck false
local notation "‖" x "‖q" => (Lₚ q hq).φ x
/-
the Lp and Lq norms are dual norms of each other.
-/
example : @Lₚ N p hp = DualNorm (Lₚ q hq) := sorry
example : @Lₚ N q hq = DualNorm (Lₚ p hp) := sorry
/-
In particular, the dual norm of L₂ is the L₂ norm,
-/
example : @L₂ N = DualNorm L₂ := sorry
/-
and the dual norm of the L₁ norm is the L∞ norm.
-/
example : @L₁ N = DualNorm L_inf := sorry

/-
Proposition A.4 (Hölder’s inequality) Let p, q ≥ 1 be conjugate: x, y ∈ ℝᴺ, |⟨x, y⟩| ≤ ‖x‖p ‖y‖q
with equality when |yᵢ| = |xᵢ|ᵖ⁻¹ for all i ∈ [ℕ].
-/
-- A.10
theorem holder_inequality {hd : IsConjugateExponent p q} :
    ∀ x y : Fin N → ℝ, |⟪x, y⟫_ℝ| ≤ ‖x‖p * ‖y‖q := by
  intro x y
  by_cases h' : x = 0 ∨ y = 0
  . -- The statement holds trivially for x = 0 or y = 0
    sorry
  . -- thus, we can assume x ≠ 0 and y ≠ 0.
    -- Let a, b > 0. By the concavity of log (see definition B.7), we can write
    have : ∀ (a b : ℝ), a > 0 ∧ b > 0 → log (1 / p * a ^ p + 1 / q * b ^ q) ≥ log (a * b) := by
      rintro a b ⟨ha, hb⟩
      calc
        log (1 / p * a ^ p + 1 / q * b ^ q)
        _ ≥ 1 / p * log (a ^ p) + 1 / q * log (b ^ q) := sorry
        _ = log a + log b := sorry
        _ = log (a * b) := sorry

    -- Taking the exponential of the left- and right-hand sides gives
    have young_inequality : ∀ (a b : ℝ), a > 0 ∧ b > 0 →
        1 / p * a ^ p + 1 / q * b ^ q ≥ a * b := by
      rintro a b ⟨ha, hb⟩
      apply (log_le_log (by sorry) (by sorry)).mp (this a b ⟨ha, hb⟩)
    -- which is known as Young’s inequality.
    -- Using this inequality with a = |x j |/‖x‖p and b = |y j |/‖y‖q for j ∈ [N ] and summing up gives
    have : (∑' i, |x i * y i|) / (‖x‖p * ‖y‖q) ≤ 1 :=
      calc
        (∑' i, |x i * y i|) / (‖x‖p * ‖y‖q)
        _ ≤ 1 / p * (‖x‖p / ‖x‖p) + 1 / q * (‖y‖q / ‖y‖q) := sorry
        _ = 1 / p + 1 / q := sorry
        _ = 1 := by rw [hd.inv_add_inv_conj]
    sorry

end

/-
Corollary A.5 (Cauchy-Schwarz inequality) For all x, y ∈ ℝᴺ, |⟨x, y⟩| ≤ ‖x‖₂ ‖y‖₂ with equality iff x and y are collinear.
-/
-- A.11
theorem cauchy_schwarz_inequality : ∀ x y : Fin N → ℝ, |⟪x, y⟫_ℝ| ≤ ‖x‖₂ * ‖y‖₂ := by
  -- intro x y
  -- apply holder_inequality x y
  sorry

/-
Let 𝓗 be the hyperplane in R N whose equation is given by w · x + b = 0, or some normal vector w ∈ ℝᴺ and offset b ∈ ℝ.
-/
class hyperplane (w : Fin N → ℝ) (b : ℝ) (𝓗 : Set (Fin N → ℝ)) where
  prop: ∀ x ∈ 𝓗, ⟪w, x⟫_ℝ + b = 0

section

variable {w : Fin N → ℝ} {b}
/-
et dₚ(x, 𝓗) denote the distance of x to the hyperplane 𝓗, that is,
-/
-- A.12
def dₚ(x : Fin N → ℝ) (𝓗 : Set (Fin N → ℝ)) [hyperplane w b 𝓗] : ℝ :=
  ⨅ x' ∈ 𝓗, ‖x' - x‖p

/-
Then, the following identity holds for all p ≥ 1:
-/
theorem A_13 {q : ℕ} {hq : q ≥ 1} {hd : IsConjugateExponent p q} (x : Fin N → ℝ) (𝓗 : Set (Fin N → ℝ)) [hyperplane w b 𝓗] :
    @dₚ N p hp _ _ w b x 𝓗 _ = (⟪w, x⟫_ℝ + b) / (Lₚ q hq).φ w := by
  sorry
/-
where q is the conjugate of p: 1/p + 1/q = 1. (A.13) can be shown by a straightforward application of the results of appendix B to the constrained optimization problem (A.12).
-/
end

-- A.1.3 Relationship between norms
section
/-
A general form for the inequalities seen in equations (A.3), (A.4) and (A.5), which holds for all Lₚ norms, is shown in the following proposition.
-/
variable {q : ℕ} {hq : p ≤ q}

set_option quotPrecheck false
local notation "‖" x "‖q" => (Lₚ q (le_trans hp hq)).φ x
/-
Proposition A.6 Let 1 ≤ p ≤ q. Then the following inequalities hold for all x ∈ ℝᴺ :
‖x‖q ≤ ‖x‖p ∧ ‖x‖p ≤ N ^ (1 / p - 1 / q) * ‖x‖q
-/
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
    _ = (∑' i, (nnabs (x i)) ^ p) ^ (1 / p) := sorry
    _ ≤ ((∑' i, ((nnabs (x i)) ^ p) ^ (q / p)) ^ (p / q) * (∑' i : Fin N, 1 ^ (q / (q - p))) ^ (1 - p / q)) ^ (1 / p) := sorry
    _ = N ^ (1 / p - 1 / q) * ‖x‖q := sorry

end

end Norms

-- A.2 Matrices
namespace Matrices

open Matrix

section
/-
For a matrix M ∈ ℝᵐⁿ with m rows and n columns, we denote by Mᵢⱼ its ijth entry, for all i ∈ [m] and j ∈ [n].
-/
variable {m n : ℕ} {M : Matrix (Fin m) (Fin n) ℝ}

/-
For any m ≥ 1, we denote by Iₘ the m-dimensional identity matrix, and refer to it as I when the dimension is clear from the context.
-/
example : (1: (Matrix (Fin m) (Fin m) ℝ)) = (diagonal λ _ ↦ 1) := rfl

/-
The transpose of M is denoted by Mᵀ and defined by (Mᵀ)ᵢⱼ = Mᵢⱼ for all (i, j).
-/
example : Mᵀ i j = M j i := by
  simp only [Matrix.transpose_apply]

variable {p : ℕ} {N : Matrix (Fin n) (Fin p) ℝ}
/-
For any two matrices M ∈ ℝᵐⁿ and N ∈ ℝⁿᵖ , (MN)ᵀ = Nᵀ Mᵀ.
-/
example : (M * N)ᵀ = Nᵀ * Mᵀ := by
  simp only [Matrix.transpose_mul]

end

section

variable {m : ℕ} {M : Matrix (Fin m) (Fin m) ℝ}
/-
M is said to be symmetric iff Mᵢⱼ = Mⱼᵢ for all (i, j),
-/
example : M.IsSymm ↔ ∀ i j, M i j = M j i := by
  apply IsSymm.ext_iff.trans
  tauto
/-
that is, iff M = Mᵀ.
-/
example : M.IsSymm ↔ M = Mᵀ := by
  rw [Matrix.IsSymm]
  tauto

/-
The trace of a square matrix M is denoted by Tr[M] and defined as Tr[M] = ∑i=1 Mᵢᵢ.
-/
example : trace M = ∑ i, M i i := by
  simp only [trace, diag_apply]

end

/-
For any two matrices M ∈ ℝᵐⁿ and N ∈ ℝⁿᵖ, the following identity holds: Tr[MN] = Tr[NM].
-/
example {m n: ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (N : Matrix (Fin n) (Fin m) ℝ) :
    trace (M * N) = trace (N * M) := trace_mul_comm M N

/-
More generally, the following cyclic property holds with the appropriate dimensions for the matrices M, N, and P: Tr[MNP] = Tr[PMN] = Tr[NPM].
-/
theorem A_15 {m n p: ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (N : Matrix (Fin n) (Fin p) ℝ) (P : Matrix (Fin p) (Fin m) ℝ) :
    trace (M * N * P) = trace (P * M * N) ∧ trace (P * M * N) = trace (N * P * M) := by
  constructor <;> rw [trace_mul_comm, Matrix.mul_assoc]

/-
The inverse of a square matrix M, which exists when M has full rank, is denoted by M⁻¹ and is the unique matrix satisfying MM⁻¹ = M⁻¹ M = I.
-/
example {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) [Invertible M] : M * ⅟ M = 1 ∧ ⅟ M * M = 1 := by
  sorry

-- A.2.1 Matrix norms
open Norms

/-
A matrix norm is a norm defined over ℝᵐⁿ where m and n are the dimensions of the matrices considered.
Many matrix norms, including those discussed below, satisfy the following submultiplicative property:
-/
example {m n p: ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (N : Matrix (Fin n) (Fin p) ℝ)
    (nM: norm (Matrix (Fin m) (Fin n) ℝ)) (nN: norm (Matrix (Fin n) (Fin p) ℝ))  (nP: norm (Matrix (Fin m) (Fin p) ℝ)):
    nP.φ (M * N) = nM.φ M * nN.φ N := by
  sorry


variable {m n : ℕ} (p : ℕ) (hp : p ≥ 1)

set_option quotPrecheck false
local notation "‖" x "‖p" => (Lₚ p hp).φ x

/-
The matrix norm induced by the vector norm ‖·‖p or the operator norm induced by that norm is also denoted by ‖·‖p and defined by
-/
instance MatrixNormInduced : norm (Matrix (Fin m) (Fin n) ℝ) where
  φ := λ M ↦ ⨆ x ∈ {x | ‖x‖p ≤ 1}, ‖mulVec M x‖p
  definiteness := sorry
  homogeneity := sorry
  triangle_inequality := sorry

/-
The norm induced for p = 2 is known as the spectral norm, which equals the largest singular value of M (see section A.2.2), or the square-root of the largest eigenvalue of M > M:
-/

/-
Not all matrix norms are induced by vector norms. The Frobenius norm denoted by ‖·‖F is the most notable of such norms and is defined by:
-/
instance FrobeniusNorm : norm (Matrix (Fin m) (Fin n) ℝ) where
  φ := λ M ↦ sqrt (∑ i : Fin m, ∑ j : Fin n, (M i j).toNNReal ^ 2)
  definiteness := sorry
  homogeneity := sorry
  triangle_inequality := sorry

local notation "‖" M "‖F" => FrobeniusNorm.φ M


/-
The Frobenius norm can be interpreted as the L₂ norm of a vector when treating M as a vector of size mn. It also coincides with the norm induced by the Frobenius product, which is the inner product defined for all M, N ∈ ℝᵐⁿ by
-/
def FrobeniusProduct {m n: ℕ} (M N : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  trace (Mᵀ * N)

/-
This relates the Frobenius norm to the singular values of M: where r = rank(M).
-/
theorem A_19_1 {m n: ℕ} {M : Matrix (Fin m) (Fin n) ℝ} : ‖M‖F ^ 2 = trace (Mᵀ * M) := by
  sorry

/-
The second equality follows from properties of SPSD matrices (see section A.2.3).
-/

/-
For any j ∈ [n], let M j denote the jth column of M, that is M = [M 1 · · · M n ].
-/
example {m: ℕ} {M : Matrix (Fin 3) (Fin n) ℝ} : M i j = ![M 0 j, M 1 j, M 2 j] i := sorry

/-
Then, for any p, r ≥ 1, the L p,r group norm of M is defined by
-/

instance GroupNorm (r : ℕ) (hr : r ≥ 1) : norm (Matrix (Fin m) (Fin n) ℝ) where
  φ := λ M ↦ toNNReal <| (∑ j, ‖Mᵀ j‖p ^ r) ^ (1 / r)
  definiteness := sorry
  homogeneity := sorry
  triangle_inequality := sorry

/-
One of the most commonly used group norms is the L 2,1 norm defined by
-/
local notation "‖" M "‖₂,₁" => (GroupNorm 2 (by norm_num) 1 (by norm_num)).φ M

example {m n: ℕ} {M : Matrix (Fin m) (Fin n) ℝ} : ‖M‖₂,₁ = ∑ i, ‖Mᵀ i‖₂ := sorry

-- A.2.2 Singular value decomposition

section

variable {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)

/-
The compact singular value decomposition (SVD) of M, with r = rank(M) ≤ min(m, n), can be written as follows:
-/
/-
The r × r matrix Σ M = diag(σ 1 , . . . , σ r ) is diagonal and contains the non-zero singular values
of M sorted in decreasing order, that is σ 1 ≥ . . . ≥ σ r > 0. The matrices U M ∈ R m×r and
V M ∈ R n×r have orthonormal columns that contain the left and right singular vectors of M
corresponding to the sorted singular values.
-/
-- TODO: Mathlibに特異値分解の定義が無い
def σ: Fin M.rank → ℝ := sorry
def U: Matrix (Fin m) (Fin M.rank) ℝ := sorry
def V: Matrix (Fin n) (Fin M.rank) ℝ := sorry
-- Σ は使えない
def Sigma : Matrix (Fin M.rank) (Fin M.rank) ℝ := diagonal (σ M)
theorem SVD : M = (U M) * (Sigma M) * (V M)ᵀ := sorry

/-
We denote by U k ∈ R m×k the top k ≤ r left singular vectors of M.
-/
variable (k : ℕ) (hk : k ≤ M.rank)
def Uk: Matrix (Fin m) (Fin k) ℝ := submatrix (U M) id (Fin.castLEEmb hk)
/-
The orthogonal projection onto the span of U k can be written as P U k = U k Uᵀ k ,
-/
def PUk := (Uk M k hk) * (Uk M k hk)ᵀ

/-
where P U k is SPSD and idempotent, i.e., P 2 U = P U k .
-/
example : PUk M k hk ^ 2 = PUk M k hk := sorry

/-
Moreover, the orthogonal projection onto the subspace orthogonal to U k is defined as P U k ,⊥ .
-/
-- TODO: 定義がわからない

/-
Similar definitions, i.e., V k , P V k , P V k ,⊥ , hold for the right singular vectors.
-/
def Vk: Matrix (Fin n) (Fin k) ℝ := submatrix (V M) id (Fin.castLEEmb hk)
def PVk := (Vk M k hk) * (Vk M k hk)ᵀ

/-
The generalized inverse, or Moore-Penrose pseudo-inverse of a matrix M is denoted by M † and defined by
where Σ † M = diag(σ 1 −1 , . . . , σ r −1 ).
-/
def SigmaDagger : Matrix (Fin M.rank) (Fin M.rank) ℝ := diagonal λ i ↦ ((σ M) i)⁻¹
def GeneralizedInverse := (U M) * (SigmaDagger M) * (V M)ᵀ

local notation M "†" => GeneralizedInverse M

/-
For any square m × m matrix M with full rank, i.e., r = m, the pseudo-inverse coincides with the matrix inverse: M † = M −1 .
-/
example {m} {M : Matrix (Fin m) (Fin m) ℝ} {h : M.rank = m} : M† = M⁻¹ := sorry

-- A.2.3 Symmetric positive semidefinite (SPSD) matrices
/-
Definition A.7 A symmetric matrix M ∈ ℝᵐᵐ is said to be positive semidefinite iff
xᵀMx ≥ 0
for all x ∈ ℝᵐ.
-/
class SPSD (M : Matrix (Fin m) (Fin m) ℝ) : Prop where
  symmetry: M.IsSymm
  prop : ∀ x : Fin m → ℝ, x ⬝ᵥ (mulVec M x) ≥ 0

/-
M is said to be positive definite if the inequality is strict.
-/
class SPD (M : Matrix (Fin m) (Fin m) ℝ) extends SPSD M where
  strictly : ∀ x : Fin m → ℝ, x ⬝ᵥ (mulVec M x) > 0
/-
Kernel matrices (see chapter 6) and orthogonal projection matrices are two examples of SPSD matrices.
-/
example : SPSD (PUk M k hk) := sorry

/-
It is straightforward to show that a matrix M is SPSD iff its eigenvalues are all non-negative.
-/
example {M : Matrix (Fin m) (Fin m) ℝ} (hM: M.IsHermitian): SPSD M ↔ ∀ i, hM.eigenvalues i > 0 := sorry

/-
Furthermore, the following properties hold for any SPSD matrix M:
-/
variable {M : Matrix (Fin m) (Fin m) ℝ} [SPSD M]

/-
M admits a decomposition M = Xᵀ X for some matrix X and the Cholesky decomposition provides one such decomposition in which X is an upper triangular matrix.
-/
example : ∃ X: Matrix (Fin m) (Fin m) ℝ, M = Xᵀ * X ∧ BlockTriangular X id := sorry

/-
The left and right singular vectors of M are the same and the SVD of M is also its eigenvalue decomposition.
-/
example : (U M) = (V M) := sorry

/-
The SVD of an arbitrary matrix X = UX ΣX VXᵀ defines the SVD of two related SPSD matrices:
-/
section

variable (m : ℕ) (X : Matrix (Fin m) (Fin m) ℝ)
/-
the left singular vectors (UX) are the eigenvectors of XXᵀ,
-/
theorem lm1 : (X * Xᵀ).IsHermitian := by
  rw [← conjTranspose_eq_transpose_of_trivial]
  apply isHermitian_mul_conjTranspose_self
example : U X = submatrix (lm1 m X).eigenvectorMatrix id (Fin.castLEEmb (rank_le_height X)) := sorry

/-
the right singular vectors (V X ) are the eigenvectors of Xᵀ X
-/
theorem lm2 : (Xᵀ * X).IsHermitian := by
  rw [← conjTranspose_eq_transpose_of_trivial]
  apply isHermitian_mul_conjTranspose_self
example : V X = submatrix (lm2 m X).eigenvectorMatrix id (Fin.castLEEmb (rank_le_height X)) := sorry

/-
and the non-zero singular values of X are the square roots of the non-zero eigenvalues of XXᵀ and Xᵀ X.
-/
def nzσ := {i | σ X i > 0}.restrict (σ X)
def nzeXXT := {i | (lm1 m X).eigenvalues i > 0}.restrict (lm1 m X).eigenvalues
-- TODO: 定義域が異なるため比較できない
-- example : nzσ = nzeXXT := sorry

end
/-
The trace of M is the sum of its singular values, i.e., Tr[M] = ri=1 σ i (M), where rank(M) = r.
-/
example : trace M = ∑ i, σ M i := sorry

end

end Matrices
