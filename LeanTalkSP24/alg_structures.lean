import Mathlib.Data.Real.Basic

class Group₁ (α : Type _) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  mul_left_inv : ∀ x : α, mul (inv x) x = one

@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def neg (a : Point) : Point := ⟨-a.x, -a.y, -a.z⟩

def zero : Point := ⟨0,0,0⟩

instance add_group_point: Group₁ Point where
  mul := add
  one := zero
  inv := neg
  mul_assoc := by simp [add, add_assoc]
  mul_one := by simp [add, zero]
  one_mul := by simp [add, zero]
  mul_left_inv := by simp [add, neg, zero]

end Point

instance hasMulGroup₁ {α : Type _} [Group₁ α] : Add α := ⟨Group₁.mul⟩

def v : Point := ⟨1,1,1⟩
#check v+v
