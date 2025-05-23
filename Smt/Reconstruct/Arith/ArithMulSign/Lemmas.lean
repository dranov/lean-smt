/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Real.Basic

import Smt.Reconstruct.Arith.MulPosNeg.Lemmas

namespace Smt.Reconstruct.Arith

variable {α : Type}

variable [LinearOrderedCommRing α]

variable {a b : α}

mutual

theorem powNegEven : ∀ {k : Nat} {z : α}, z < 0 → Even k → z ^ k > 0 := by
  intros k z h₁ h₂
  cases k with
  | zero    => simp
  | succ k' =>
    have k'NotEven := Nat.even_add_one.mp h₂
    have k'Odd := Nat.not_even_iff_odd.mp k'NotEven
    have rc := powNegOdd h₁ k'Odd
    simp [Pow.pow]
    have mulZ := arith_mul_neg_lt ⟨h₁, rc⟩
    simp at mulZ
    rw [pow_succ, mul_comm]
    exact mulZ

theorem powNegOdd : ∀ {k : Nat} {z : α}, z < 0 → Odd k → z ^ k < 0 := by
  intros k z h₁ h₂
  cases k with
  | zero    => simp at h₂
  | succ k' =>
    simp only [Odd, add_left_inj] at h₂
    have k'Even : Even k' := (even_iff_exists_two_nsmul k').mpr h₂
    have rc := powNegEven h₁ k'Even
    simp only [gt_iff_lt]
    have mulZ := arith_mul_neg_lt ⟨h₁, rc⟩
    simp only [mul_zero, gt_iff_lt] at mulZ
    rw [pow_succ, mul_comm]
    exact mul_neg_of_neg_of_pos h₁ rc

end

theorem powPos : ∀ {k : Nat} {z : α}, z > 0 → z ^ k > 0 := by
  intro k z h
  cases k with
  | zero    => simp
  | succ k' =>
    have ih := @powPos k' z h
    rw [pow_succ]
    have h₂ := arith_mul_pos_lt ⟨h, ih⟩
    simp at h₂
    rw [mul_comm]
    exact h₂

theorem nonZeroEvenPow : ∀ {k : Nat} {z : α},
    z ≠ 0 → Even k → z ^ k > 0 := by
  intros k z h₁ h₂
  match lt_trichotomy z 0 with
  | Or.inl zNeg => exact powNegEven zNeg h₂
  | Or.inr (Or.inl zZero) => rw [zZero] at h₁; simp at h₁
  | Or.inr (Or.inr zPos)  => exact powPos zPos

theorem combineSigns₁ : a > 0 → b > 0 → b * a > 0 := by
  intros h₁ h₂
  have h := mul_lt_mul_of_pos_left h₁ h₂
  simp at h
  exact h

theorem combineSigns₂ : a > 0 → b < 0 → b * a < 0 := by
  intros h₁ h₂
  have h := mul_lt_mul_of_pos_right h₂ h₁
  simp at h
  exact h

theorem combineSigns₃ : a < 0 → b > 0 → b * a < 0 := by
  intros h₁ h₂
  have h := mul_lt_mul_of_pos_left h₁ h₂
  simp at h
  exact h

theorem combineSigns₄ : a < 0 → b < 0 → b * a > 0 := by
  intros h₁ h₂
  have h := mul_lt_mul_of_neg_left h₁ h₂
  simp at h
  exact h

theorem castPos : ∀ (a : Int), a > 0 → ↑a > 0 := by
  intros a h
  simp [h]

theorem castNeg : ∀ (a : Int), a < 0 → ↑a < 0 := by
  intros a h
  simp [h]

instance : HMul ℤ ℝ ℝ where
  hMul z r := ↑z * r

instance : HMul ℝ ℤ ℝ where
  hMul r z := r * ↑z

end Smt.Reconstruct.Arith
