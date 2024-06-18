import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Basic

#print Semigroup
#print Monoid
#print Ring
#print Semiring
#print Mul

namespace valuable_stuff

  universe u

  class Mul (α : Type u) where
    /-- `a ⬝ b` computes the product of `a` and `b`. See `HMul`. -/
    mul : α → α → α

  -- macro_rules | `($x ⬝ $y)   => `(binop% Mul $x $y)
  infixl:70 " ⬝ "   => Mul.mul

  @[ext]
  class Semigroup (G : Type u) extends Mul G where
    /-- Multiplication is associative -/
    protected mul_assoc : ∀ a b c : G, (a ⬝ b) ⬝ c = a ⬝ (b ⬝ c)

  class One (α : Type u) where one : α

  notation "𝟙" => One.one

  class MulOneClass (M : Type u) extends One M, Mul M where
    /-- One is a left neutral element for multiplication -/
    protected one_mul : ∀ a : M, one ⬝ a = a
    /-- One is a right neutral element for multiplication -/
    protected mul_one : ∀ a : M, a ⬝ one = a

  class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
end valuable_stuff

namespace hb_stuff

  universe u

  class Bottom (α : Type u) where

  class MulOfBottom (α : Type u) where
    /-- `a ⬝ b` computes the product of `a` and `b`. See `HMul`. -/
    mul : α → α → α

  class Mul (α : Type u) extends Bottom α, MulOfBottom α where

  -- macro_rules | `($x ⬝ $y)   => `(binop% Mul $x $y)
  infixl:70 " ⬝ "   => MulOfBottom.mul

  class SemigroupOfMul (G : Type u) [MulOfBottom G] where
    /-- Multiplication is associative -/
    protected mul_assoc : ∀ a b c : G, (a ⬝ b) ⬝ c = a ⬝ (b ⬝ c)

  class Semigroup (G : Type u) extends Bottom G, Mul G, SemigroupOfMul G  where
  #print Semigroup

  class OneOfBottom (α : Type u) where one : α
  class One (α : Type u) extends Bottom α, OneOfBottom α where
  notation "𝟙" => OneOfBottom.one

  class MulOneOfBottom (M : Type u) [Bottom M] [OneOfBottom M] [MulOfBottom M] where
    /-- One is a left neutral element for multiplication -/
    protected one_mul : ∀ a : M, 𝟙 ⬝ a = a
    /-- One is a right neutral element for multiplication -/
    protected mul_one : ∀ a : M, a ⬝ 𝟙 = a

  class MulOne (M : Type u) extends Bottom M, One M, Mul M, MulOneOfBottom M where

  class Monoid (M : Type u) extends Bottom M, Semigroup M, MulOne M where
  #print Monoid
  #print MulOne

end hb_stuff

  #print MulOneClass
-- class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α

--   class Semiring (α : Type u) extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α

  --  class Ring (R : Type u) extends Semiring R, AddCommGroup R, AddGroupWithOne R
