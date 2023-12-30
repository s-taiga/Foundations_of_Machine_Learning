import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

noncomputable
section

open MeasureTheory

inductive Dice : Type
  | one : Dice
  | two : Dice
  | three : Dice
  | four : Dice
  | five : Dice
  | six : Dice

instance : Finite Dice := sorry

instance : Nonempty Dice := ⟨Dice.one⟩

instance : MeasurableSpace Dice := ⊤

def DiceFinMeasure : FiniteMeasure Dice := ⟨Measure.count, inferInstance⟩

def DiceMeasure : ProbabilityMeasure Dice := DiceFinMeasure.normalize

instance : DecidableEq Dice := by
  sorry

def univ_dice : Finset Dice := List.toFinset [ Dice.one, Dice.two, Dice.three, Dice.four, Dice.five, Dice.six ]

example : DiceFinMeasure.val univ_dice = 6 := by
  rw [DiceFinMeasure]
  simp
  rw [univ_dice, Finset.card]
  simp
  ring

def odd_dice : Finset Dice := List.toFinset [ Dice.one, Dice.three, Dice.five ]

example : Finset.card odd_dice = 3 := by
  rw [odd_dice, Finset.card]
  simp

example : DiceFinMeasure.val odd_dice = 3 := by
  rw [DiceFinMeasure]
  simp
  rw [odd_dice, Finset.card]
  simp
  ring

@[simp]
theorem DiceMeasure.mass : DiceFinMeasure.mass = 6 := by
  rw [DiceFinMeasure, FiniteMeasure.mass, ← FiniteMeasure.val_eq_toMeasure]
  simp
  rw [Measure.count]
  simp
  rw [tsum]
  simp
  rw [Function.support_const one_ne_zero]
  have dice_fin: Set.Finite (Set.univ : Set Dice) := sorry
  simp [dice_fin]
  rw [finsum]
  have : (fun i ↦ (1 : ENNReal)) ∘ (PLift.down : PLift Dice → Dice) = fun i ↦ 1 := sorry
  rw [this]
  rw [Function.support_const one_ne_zero]
  simp [dice_fin]
  sorry

open ENNReal

theorem dice_measure (s : Set Dice) : DiceMeasure s = 6⁻¹ * Measure.count s := by
  rw [DiceMeasure, FiniteMeasure.normalize]
  simp
  rw [← ProbabilityMeasure.val_eq_to_measure]
  simp only [FiniteMeasure.self_eq_mass_mul_normalize]
  rw [FiniteMeasure.toMeasure_smul]
  dsimp
  rw [DiceFinMeasure, ← FiniteMeasure.val_eq_toMeasure]
  simp

example : DiceMeasure Set.univ = 1 := by
  apply ProbabilityMeasure.coeFn_univ DiceMeasure

example : DiceMeasure { Dice.one } = (1/6 : ℝ≥0∞) := by
  rw [dice_measure]
  simp [Measure.count_singleton']

def Dice.odd : Set Dice := { Dice.one, Dice.three, Dice.five }

example : DiceMeasure Dice.odd = (1/2 : ℝ≥0∞) := by
  rw [dice_measure]
  rw [Measure.count_apply_finite]
  rw [Set.Finite.toFinset]
  sorry

example : DiceMeasure odd_dice = (1/2 : ℝ≥0∞) := by
  rw [dice_measure]
  simp
  rw [odd_dice, Finset.card]
  simp
  ring_nf
  have : (6 : ℝ≥0∞) = 2 * 3 := by ring
  rw [this, ENNReal.mul_inv, mul_assoc, ENNReal.inv_mul_cancel, mul_one]
  . norm_num
  . apply ne_top_of_lt
    have : (3 : ℝ≥0∞) < 4 := by
      norm_num
    apply this
  . norm_num
  . right
    norm_num

end
