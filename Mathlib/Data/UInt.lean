import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Basic

lemma UInt8.size_positive : 0 < UInt8.size := by decide

lemma UInt16.size_positive : 0 < UInt16.size := by decide

lemma UInt32.size_positive : 0 < UInt32.size := by decide

lemma UInt64.size_positive : 0 < UInt64.size := by decide

lemma USize.size_positive : 0 < USize.size := usize_size_gt_zero

lemma UInt8.val_eq_of_lt : a < UInt8.size → (UInt8.ofNat a).val = a := Fin.val_eq_of_lt

lemma UInt32.val_eq_of_lt : a < UInt32.size → (UInt32.ofNat a).val = a := Fin.val_eq_of_lt

namespace UInt8

instance : Inhabited (Fin size) where
  default := Fin.ofNat' 0 size_positive

instance : AddSemigroup UInt8 where
  add_assoc := fun _ _ _ => congrArg mk (AddSemigroup.add_assoc _ _ _)

instance : AddCommSemigroup UInt8 where
  add_comm := fun _ _ => congrArg mk (AddCommSemigroup.add_comm _ _)

instance : Semigroup UInt8 where
  mul_assoc := fun _ _ _ => congrArg mk (Semigroup.mul_assoc _ _ _)

instance : Neg UInt8 where
  neg a := mk (-a.val)

lemma sub_def (a b : UInt8) : a - b = ⟨a.val - b.val⟩ := rfl

lemma mul_def (a b : UInt8) : a * b = ⟨a.val * b.val⟩ := rfl

lemma mod_def (a b : UInt8) : a % b = ⟨a.val % b.val⟩ := rfl

lemma add_def (a b : UInt8) : a + b = ⟨a.val + b.val⟩ := rfl

lemma eq_of_val_eq : ∀ {a b : UInt8}, a.val = b.val -> a = b
| ⟨f1⟩, ⟨f2⟩, h => congrArg mk h

lemma val_eq_of_eq : ∀ {a b : UInt8}, a = b -> a.val = b.val
| ⟨f1⟩, ⟨f2⟩, h => congrArg val h

@[simp] lemma mk_val_eq : ∀ (a : UInt8), mk a.val = a
| ⟨a, _⟩ => rfl

instance : Semiring UInt8 where
  add_zero := by
    intro a
    simp only [add_def]
    simp only [Semiring.add_zero]
    simp only [(Semiring.add_zero a.val : a.val + (0 : Fin UInt8.size) = a.val)]
    simp only [(Semiring.add_zero a.val : a.val + (0 : UInt8).val = a.val)]
    trace_state
    sorry
  mul_one := by
    intro a
    simp only [mul_def]
    simp only [Semiring.mul_one]
    simp only [(Semiring.mul_one a.val : a.val * (1 : Fin UInt8.size) = a.val)]
    simp only [(Semiring.mul_one a.val : a.val * (1 : UInt8).val = a.val)]
    trace_state
    sorry
  one_mul := sorry
  ofNat := sorry
  zero_add := sorry
  nsmul := sorry
  nsmul_zero' := sorry
  nsmul_succ' := sorry

  zero_mul := sorry
  mul_zero := sorry
  npow := sorry
  npow_zero' := sorry
  npow_succ' := sorry
  mul_add := sorry
  add_mul := sorry
  ofNat_succ := sorry

end UInt8

namespace USize
instance : Inhabited (Fin size) where
  default := Fin.ofNat' 0 size_positive

instance : AddSemigroup USize where
  add_assoc := fun _ _ _ => congrArg mk (AddSemigroup.add_assoc _ _ _)

instance : AddCommSemigroup USize where
  add_comm := fun _ _ => congrArg mk (AddCommSemigroup.add_comm _ _)

instance : Semigroup USize where
  mul_assoc := fun _ _ _ => congrArg mk (Semigroup.mul_assoc _ _ _)

instance : Neg USize where
  neg a := mk (-a.val)

lemma add_def (a b : USize) : a + b = ⟨a.val + b.val⟩ := rfl

lemma sub_def (a b : USize) : a - b = ⟨a.val - b.val⟩ := rfl

lemma mul_def (a b : USize) : a * b = ⟨a.val * b.val⟩ := rfl

lemma mod_def (a b : USize) : a % b = ⟨a.val % b.val⟩ := rfl

lemma eq_of_val_eq : ∀ {a b : USize}, a.val = b.val -> a = b
| ⟨f1⟩, ⟨f2⟩, h => congrArg mk h

lemma val_eq_of_eq : ∀ {a b : USize}, a = b -> a.val = b.val
| ⟨f1⟩, ⟨f2⟩, h => congrArg val h

@[simp] lemma mk_val_eq : ∀ (a : USize), mk a.val = a
| ⟨a, _⟩ => rfl

instance : Semiring USize where
  add_zero := by
    intro a
    simp only [add_def]
    simp only [Semiring.add_zero]
    simp only [(Semiring.add_zero a.val : a.val + (0 : Fin USize.size) = a.val)]
    simp only [(Semiring.add_zero a.val : a.val + (0 : USize).val = a.val)]
    trace_state
    sorry
  mul_one := by
    intro a
    simp only [mul_def]
    simp only [Semiring.mul_one]
    simp only [(Semiring.mul_one a.val : a.val * (1 : Fin USize.size) = a.val)]
    simp only [(Semiring.mul_one a.val : a.val * (1 : USize).val = a.val)]
    trace_state
    sorry
  one_mul := sorry
  ofNat := sorry
  zero_add := sorry
  nsmul := sorry
  nsmul_zero' := sorry
  nsmul_succ' := sorry
  zero_mul := sorry
  mul_zero := sorry
  npow := sorry
  npow_zero' := sorry
  npow_succ' := sorry
  mul_add := sorry
  add_mul := sorry
  ofNat_succ := sorry

end USize

namespace UInt8

/-- Is this an uppercase ASCII letter? -/
def isUpper (c : UInt8) : Bool :=
  c ≥ 65 && c ≤ 90

/-- Is this a lowercase ASCII letter? -/
def isLower (c : UInt8) : Bool :=
  c ≥ 97 && c ≤ 122

/-- Is this an alphabetic ASCII character? -/
def isAlpha (c : UInt8) : Bool :=
  c.isUpper || c.isLower

/-- Is this an ASCII digit character? -/
def isDigit (c : UInt8) : Bool :=
  c ≥ 48 && c ≤ 57

/-- Is this an alphanumeric ASCII character? -/
def isAlphanum (c : UInt8) : Bool :=
  c.isAlpha || c.isDigit

theorem toChar_aux (n : Nat) (h : n < size) : Nat.isValidChar (UInt32.ofNat n).1 := by
  rw [UInt32.val_eq_of_lt]
  exact Or.inl $ Nat.lt_trans h $ by decide
  exact Nat.lt_trans h $ by decide

/-- The numbers from 0 to 256 are all valid UTF-8 characters, so we can embed one in the other. -/
def toChar (n : UInt8) : Char := ⟨n.toUInt32, toChar_aux n.1 n.1.2⟩

end UInt8
