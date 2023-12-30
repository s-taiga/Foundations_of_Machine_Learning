import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Probability.Notation
noncomputable
section
-- C.1 Probability
/-
sample space Ω: Ω is the set of all elementary events or outcomes possible in a trial, for example,
each of the six outcomes in {1, . . . , 6} when casting a die.
-/
-- def Ω': Set ℕ := {x | 1 ≤ x ∧ x ≤ 6}
-- def Ω'' : Finset ℕ := {1, 2, 3, 4, 5, 6}
-- instance : Fintype (Set Ω'') := by sorry
def Ω := Fin 7
/-
events set F : F is a σ-algebra, that is a set of subsets of Ω containing Ω that is closed under
complementation and countable union (therefore also countable intersection). An example of
an event may be “the die lands on an odd number”.
-/
-- def F' : MeasurableSpace Ω' where
--   MeasurableSet' := fun (A : Set Ω') ↦ A ⊆ Set.univ
--   measurableSet_empty := by
--     intro A ainem
--     apply False.elim
--     apply Set.not_mem_empty
--     apply ainem
--   measurableSet_compl := by
--     intro A _
--     apply Set.subset_univ
--   measurableSet_iUnion := by
--     intro f _
--     simp at *

-- def F'' : MeasurableSpace Ω'' where
--   MeasurableSet' := fun (A : Set Ω'') ↦ A ⊆ Set.univ
--   measurableSet_empty := by
--     intro A ainem
--     apply False.elim
--     apply Set.not_mem_empty
--     apply ainem
--   measurableSet_compl := by
--     intro A _
--     apply Set.subset_univ
--   measurableSet_iUnion := by
--     intro f _
--     simp at *

#check Prime 2

example : (if Even 2 then 1 else 2) = 1 := by
  -- have : (1 + 2 = 3) = True := sorry
  -- rw [this]
  -- dsimp [ite_true]
  simp [even_two]
  sorry

instance F : MeasurableSpace Ω where
  MeasurableSet' := fun A ↦ A ⊆ Set.univ
  measurableSet_empty := by
    intro A ainem
    apply False.elim
    apply Set.not_mem_empty
    apply ainem
  measurableSet_compl := by
    intro A _
    apply Set.subset_univ
  measurableSet_iUnion := by
    intro f _
    simp at *

-- the die lands on an odd number
-- def pr : (x : ℕ) → (h : 1 ≤ x ∧ x ≤ 6) → x ∈ Ω' := by
--   intro x
--   rw [Ω', Set.mem_setOf_eq]
--   simp

-- def dlod : Set Ω' := {
--   ⟨1, pr _ (by norm_num)⟩,
--   ⟨3, pr _ (by norm_num)⟩,
--   ⟨5, pr _ (by norm_num)⟩
-- }
-- example : F'.MeasurableSet' dlod := by
--   simp [F']
-- def A₁ : Set Ω' := Set.singleton ⟨1, pr _ (by norm_num)⟩
-- open BigOperators

-- def pr' {x : ℕ} (h : 1 ≤ x ∧ x ≤ 6): x ∈ Ω'' := by
--   rw [Ω'']
--   simp
--   sorry
-- def dlod' : Set Ω'' := {⟨1, pr' (by norm_num)⟩}
-- def fdlod' [Fintype dlod']: Finset Ω'' := Set.toFinset dlod'
def dlod'' : Set Ω := {⟨1, (by norm_num)⟩, ⟨3, (by norm_num)⟩, ⟨5, (by norm_num)⟩}
def fdlod [Fintype dlod''] : Finset Ω := Set.toFinset dlod''
instance : Fintype dlod'' := sorry
example : F.MeasurableSet' dlod'' := by
  simp [F]
example : Finset.card fdlod = 3 := by
  apply Finset.card_eq_three.mpr
  . use ⟨1, (by norm_num)⟩, ⟨3, (by norm_num)⟩, ⟨5, (by norm_num)⟩
    have : ((⟨1, (by norm_num)⟩: Ω) ≠ (⟨3, (by norm_num)⟩ : Ω)) = (1 ≠ 3) := by sorry
    rw [this]
    have : ((⟨1, (by norm_num)⟩: Ω) ≠ (⟨5, (by norm_num)⟩ : Ω)) = (1 ≠ 5) := by sorry
    rw [this]
    have : ((⟨3, (by norm_num)⟩: Ω) ≠ (⟨5, (by norm_num)⟩ : Ω)) = (3 ≠ 5) := by sorry
    rw [this]
    simp
    rw [fdlod, Set.toFinset]
  -- rw [← Finset.length_toList]
  -- rw [fdlod]
  -- rw [Set.toFinset]
/-
probability distribution: P is a mapping from the set of all events F to [0, 1] such that P[Ω] = 1,
P[∅] = 1, and, for all mutually exclusive events A 1 , . . . , A n ,
-/
-- def P' : MeasureTheory.ProbabilityMeasure Ω' where
--   val := {
--     measureOf := MeasureTheory.Measure.count,
--     empty := by simp,
--     mono := _,
--     iUnion_nat := _,
--     m_iUnion := _,
--     trimmed := _
--   }
--   property := _
-- def P'' : MeasureTheory.ProbabilityMeasure Ω'' where
--   val := {
--     measureOf := fun A ↦ ∑ i in A.toFinset, 1 / 6,
--     empty := _,
--     mono := _,
--     iUnion_nat := _,
--     m_iUnion := _,
--     trimmed := _
--   }
--   property := _
open MeasureTheory

def DiceFinMeasure : FiniteMeasure Ω where
  val := Measure.count
  property := by
    sorry

example : DiceFinMeasure {} = 0 := by
  simp

example : DiceFinMeasure.val dlod'' = 3 := by
  rw [DiceFinMeasure]
  simp
  rw [Measure.count_apply, dlod'']
  simp

def P : ProbabilityMeasure Ω := DiceFinMeasure.normalize
/-
μ univ = 1は定義されている
-/
-- C.2 Random variables
-- Definition C.1 (Random variables)
#check PMF

structure RandomVariable (Ω : Type*) [MeasurableSpace Ω] where
  measure : Ω → ℝ

-- Definition C.2 (Binomial distribution)
#check PMF.binomial
-- Definition C.3 (Normal distribution)
