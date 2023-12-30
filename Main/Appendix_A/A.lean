import Mathlib.Data.Vector
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Abs
-- import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Finsupp
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Basis

noncomputable
section

open NNReal
open BigOperators

variable (ι) (ℍ) [AddCommMonoid ℍ] [Module ℝ ℍ]
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
structure norm (ℍ) [AddCommMonoid ℍ] [Module ℝ ℍ] where
  --  mapping Φ : H → R + is said to define a norm on H
  φ : ℍ → ℝ≥0
  -- definiteness: ∀x ∈ H, Φ(x) = 0 ⇔ x = 0;
  definiteness : ∀ (x : ℍ), φ x = 0 ↔ x = 0
  -- homogeneity: ∀x ∈ H, ∀α ∈ R, Φ(αx) = |α|Φ(x)
  homogeneity : ∀ (x : ℍ), ∀ (α : ℝ), φ (α • x) = |α| * φ x
  -- triangle inequality: ∀x, y ∈ H, Φ(x + y) ≤ Φ(x) + Φ(y).
  triangle_inequality: ∀ (x y : ℍ), φ (x + y) ≤ φ x + φ y

/-
A norm is typically denoted by ‖ · ‖.
-/
-- notation n "‖" x "‖" => norm.φ n x
/-
Examples of vector norms are the absolute value on ℝ and the Euclidean (or L₂) norm on ℝᴺ .
-/
variable{N : ℕ} [AddCommMonoid (Basis (Fin N) ℝ ℝ)] [Module ℝ (Basis (Fin N) ℝ ℝ)]

instance L₂ : norm (Basis (Fin N) ℝ ℝ) where
  φ := fun x ↦ NNReal.sqrt (∑ j, (Real.nnabs (x j)) ^ 2)
  definiteness := sorry
  homogeneity := sorry
  triangle_inequality := sorry

notation "‖" x "‖₂" => L₂.φ x

/-
More generally, for any p ≥ 1 the L p norm is defined on R N as (A.1)
-/
-- TODO: n乗根の定義が多分無い
def n_th_root (p : ℕ) : ℝ≥0 → ℝ≥0 := sorry

instance Lₚ (p : ℕ) (hp : p ≥ 1) : norm (Basis (Fin N) ℝ ℝ) where
  φ := fun x ↦ n_th_root p (∑ j, (Real.nnabs (x j)) ^ p)
  definiteness := sorry
  homogeneity := sorry
  triangle_inequality := sorry


instance L₁ : norm (Basis (Fin N) ℝ ℝ) where
  φ := fun x ↦ ∑ j, Real.nnabs (x j)
  definiteness := sorry
  homogeneity := sorry
  triangle_inequality := sorry

notation "‖" x "‖₁" => L₁.φ x

/-
The L 1 , L 2 , and L ∞ norms are some of the most commonly used norms, where ‖x‖∞ = max j∈[N ] |x j|.
-/
-- TODO; この型の関数が必要
@[coe]
def coe_WithBot_to_NNReal (r : WithBot ℝ) : ℝ≥0 :=
  match r with
  | none => 0  -- 実際にはリストが空になることはないため、不要な分岐
  | some r => Real.toNNReal r

instance : CoeTC (WithBot ℝ) ℝ≥0 := ⟨coe_WithBot_to_NNReal⟩

instance L_inf : norm (Basis (Fin N) ℝ ℝ) where
  φ := fun x ↦ (Finset.univ.toList.map x).maximum
  definiteness := sorry
  homogeneity := sorry
  triangle_inequality := sorry

notation "‖" x "‖_inf" => L_inf.φ x

/-
Two norms k · k and k · k 0 are said to be equivalent iff there exists α, β > 0 such that for all x ∈ H,
(A.2)
-/
def equivalent (n₁ n₂ : norm ℍ) : Prop :=
  ∃ α β: ℝ≥0, ∀ x : ℍ, α * n₁.φ x ≤ n₂.φ x ∧ n₂.φ x ≤ β * n₁.φ x

/-
The following general inequalities relating these norms can be proven straightforwardly:
-/
variable (x : Basis (Fin N) ℝ ℝ)
theorem A_3 : ‖x‖₂    ≤ ‖x‖₁ ∧ ‖x‖₁ ≤ NNReal.sqrt N * ‖x‖₂ := sorry
theorem A_4 : ‖x‖_inf ≤ ‖x‖₂ ∧ ‖x‖₂ ≤ NNReal.sqrt N * ‖x‖_inf := sorry
theorem A_5 : ‖x‖_inf ≤ ‖x‖₁ ∧ ‖x‖₁ ≤             N * ‖x‖_inf := sorry
/-
The second inequality of the first line can be shown using the Cauchy-Schwarz inequality presented
later while the other inequalities are clear.
-/
/-
These inequalities show the equivalence of these three norms.
-/
example : equivalent (Basis (Fin N) ℝ ℝ) L₂ L₁ := by
  use 1, (NNReal.sqrt N)
  intro x
  simp
  apply A_3
/-
More generally, all norms on a finite-dimensional space are equivalent.
-/
/-
The following additional properties hold for the L ∞ norm: for all x ∈ H,
-/
theorem A_6 : ∀ p, (hp : p ≥ 1) → ‖x‖_inf ≤ norm.φ (Lₚ p hp) x ∧ norm.φ (Lₚ p hp) x ≤ n_th_root p N * ‖x‖_inf := sorry
-- TODO: A_7 の極限は使い方がわからないので後回し

/-
Definition A.2 (Hilbert space) A Hilbert space is a vector space equipped with an inner product
⟨·, ·⟩ and that is complete (all Cauchy sequences are convergent). The inner product induces a
norm defined as follows:
-/
end Norms

end
