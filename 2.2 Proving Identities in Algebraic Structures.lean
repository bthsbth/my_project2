import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

# 2.2 Proving Identities in Algebraic Structures

variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)



variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring






namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check MyRing.add_comm
#check add_comm
#check add_zero

end MyRing



theorem neg_add_cancel_leftt (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

theorem my_add_neg_cancel_right (a b : R) : a + b + -b = a := by
  sorry

theorem my_add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  sorry

theorem my_add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  sorry

theorem mul_zero (a : R) : a * 0 = 0 := by
have h : a * 0 + a * 0 = a * 0 + 0 := by
  rw [← mul_add, add_zero, add_zero]
rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  sorry

theorem my_neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  sorry

theorem my_eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  sorry

theorem my_eq_comm {a b : R} (h : a = b) : b = a := by
  sorry

theorem my_neg_zero : (-0 : R) = 0 := by
  apply my_eq_comm
  apply my_eq_neg_of_add_eq_zero
  rw [add_zero]

theorem mmy_neg_zero : (-0 : R) = 0 := by
  apply my_neg_eq_of_add_eq_zero
  rw [add_zero]


theorem my_neg_neg (a : R) : - -a = a := by
  sorry


example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

example (a b : R) : a - b = a + -b := by
  rw [sub_eq_add_neg]

example (a b : ℤ ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl

theorem self_sub (a : R) : a - a = 0 := by
  sorry

theorem my_one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem my_two_mul (a : R) : 2 * a = a + a := by
  sorry

variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)


theorem my_mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹) * a = 1 * a := by
    calc
      (a * a⁻¹) * a = a * (a⁻¹ * a) := by simp
      _ = a * 1 := by simp [inv_mul_cancel]
      _ = a := by simp [mul_one]
      _ = 1 * a := by simp [one_mul]
  exact mul_right_cancel h

theorem my_mul_one (a : G) : a * 1 = a := by
  have h : a * 1 * a⁻¹ = a * a⁻¹ := by
    calc
      a * 1 * a⁻¹ = a * (1 * a⁻¹) := by rw [mul_assoc]
      _ = a * a⁻¹ := by rw [one_mul]
  exact mul_right_cancel h

theorem my_mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h : (a * b) * (b⁻¹ * a⁻¹) = 1 := by
    calc
      (a * b) * (b⁻¹ * a⁻¹) = a * (b * (b⁻¹ * a⁻¹)) := by rw [mul_assoc]
      _ = a * (b * b⁻¹ * a⁻¹) := by rw [mul_assoc]
      _ = a * ((b * b⁻¹) * a⁻¹) := by rw [← mul_assoc]
      _ = a * (1 * a⁻¹) := by rw [mul_inv_cancel]
      _ = a * a⁻¹ := by rw [one_mul]
      _ = 1 := by rw [mul_inv_cancel]
  exact inv_eq_of_mul_eq_one_right h
