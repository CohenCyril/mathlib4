import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Basic

#print Semigroup
#print Monoid
#print Ring
#print Semiring
#print Mul


-- macro "mixin": command =>  `(command|class X)
-- namespace valuable_stuff

--   universe u


--   class Mul (α : Type u) where
--     /-- `a ⬝ b` computes the product of `a` and `b`. See `HMul`. -/
--     mul : α → α → α

--   -- macro_rules | `($x ⬝ $y)   => `(binop% Mul $x $y)
--   infixl:70 " ⬝ "   => Mul.mul

--   @[ext]
--   class Semigroup (G : Type u) extends Mul G where
--     /-- Multiplication is associative -/
--     protected mul_assoc : ∀ a b c : G, (a ⬝ b) ⬝ c = a ⬝ (b ⬝ c)

--   class One (α : Type u) where one : α

--   notation "𝟙" => One.one

--   class MulOneClass (M : Type u) extends One M, Mul M where
--     /-- One is a left neutral element for multiplication -/
--     protected one_mul : ∀ a : M, one ⬝ a = a
--     /-- One is a right neutral element for multiplication -/
--     protected mul_one : ∀ a : M, a ⬝ one = a

--   class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
-- end valuable_stuff

namespace hb_stuff

  universe u

  -- class
  class Bottom (α : Type u) where
  instance (α : Type u) : Bottom α where

  -- mixin
  class MulOfBottom (α : Type u) where
    /-- `a ⬝ b` computes the product of `a` and `b`. See `HMul`. -/
    protected mul : α → α → α

  -- class
  class Mul (α : Type u) extends Bottom α, MulOfBottom α where
  -- should be Mul.mul
  def mul {α : Type u} [Mul α] := MulOfBottom.mul (α := α)
  -- macro_rules | `($x ⬝ $y)   => `(binop% Mul $x $y)

  -- loop
  instance (α : Type u) [Bottom α] [MulOfBottom α] : Mul α where
  infixl:70 " ⬝ "   => mul

  -- mixin
  class SemigroupOfMul (G : Type u) [MulOfBottom G] where
    /-- Multiplication is associative -/
    protected mul_assoc : ∀ a b c : G, (a ⬝ b) ⬝ c = a ⬝ (b ⬝ c)

  -- class
  class Semigroup (G : Type u) extends Bottom G, Mul G, SemigroupOfMul G  where
  #print Semigroup

  -- mixin
  class OneOfBottom (α : Type u) where one : α

  -- class
  class One (α : Type u) extends Bottom α, OneOfBottom α where

  instance (α : Type u) [Bottom α] [OneOfBottom α] : One α where
  def one {α : Type u} [One α] := OneOfBottom.one (α := α)
  notation "𝟙"   => one

  class MulOneOfMulAndOne (M : Type u) [Bottom M] [OneOfBottom M] [MulOfBottom M] where
    /-- One is a left neutral element for multiplication -/
    protected one_mul : ∀ a : M, 𝟙 ⬝ a = a
    /-- One is a right neutral element for multiplication -/
    protected mul_one : ∀ a : M, a ⬝ 𝟙 = a

  class MulOne (M : Type u) extends Bottom M, One M, Mul M, MulOneOfMulAndOne M where

  class Monoid (M : Type u) extends Bottom M, Semigroup M, MulOne M where


  -- factory
  class MonoidOfBottom (M : Type u) where
    one : M
    mul : M → M → M
    mul_assoc : ∀ a b c : M, mul (mul a b) c = mul a (mul b c)
    one_mul : ∀ a : M, mul one a = a
    mul_one : ∀ a : M, mul a one = a

  namespace MonoidOfBottom
    variable (M : Type u) [MonoidOfBottom M]

    @[local instance] def bottom : Bottom M where
    @[local instance] def mulofbottom : MulOfBottom M where
      mul := mul
    instance : Mul M where
    @[local instance] def oneofbottom : OneOfBottom M where
      one := one
    instance : One M where
    @[local instance] def muloneofbottom : MulOneOfMulAndOne M where
      one_mul := one_mul
      mul_one := mul_one
    instance : MulOne M where
    @[local instance] def semigroup : SemigroupOfMul M where
      mul_assoc := mul_assoc
    instance : Semigroup M where
    instance : Monoid M where
  end MonoidOfBottom

  instance : MonoidOfBottom ℕ where
    one := 1
    mul := Nat.mul
    mul_assoc := Nat.mul_assoc
    one_mul := Nat.one_mul
    mul_one := Nat.mul_one

  #synth Monoid ℕ


  #print Monoid
  #print MulOne

end hb_stuff

namespace pretend_hb
  universe u
  -- class

  mixin MulOfBottom (α : Type u) where
    /-- `a ⬝ b` computes the product of `a` and `b`. See `HMul`. -/
    mul : α → α → α

  class Mul (α : Type u) of MulOfBottom α
  infixl:70 " ⬝ "   => mul

  -- macro_rules | `($x ⬝ $y)   => `(binop% Mul $x $y)

  mixin SemigroupOfMul (G : Type u) [MulOfBottom G] where
    /-- Multiplication is associative -/
    mul_assoc : ∀ a b c : G, (a ⬝ b) ⬝ c = a ⬝ (b ⬝ c)

  class Semigroup (G : Type u) of Mul G, SemigroupOfMul G
  #print Semigroup

  -- mixin
  mixin OneOfBottom (α : Type u) where
    /-- TODO: One is one! -/
    one : α
  -- class
  class One (α : Type u) of OneOfBottom α
  notation "𝟙" => one

  mixin MulOneOfMulAndOne (M : Type u) [Bottom M] [OneOfBottom M] [MulOfBottom M] where
    /-- One is a left neutral element for multiplication -/
    one_mul : ∀ a : M, 𝟙 ⬝ a = a
    /-- One is a right neutral element for multiplication -/
    mul_one : ∀ a : M, a ⬝ 𝟙 = a

  class MulOne (M : Type u) of One M, Mul M, MulOneOfMulAndOne M

  class Monoid (M : Type u) of Semigroup M, MulOne M


  -- factory
  factory MonoidOfBottom (M : Type u) where
    one : M
    mul : M → M → M
    mul_assoc : ∀ a b c : M, mul (mul a b) c = mul a (mul b c)
    one_mul : ∀ a : M, mul one a = a
    mul_one : ∀ a : M, mul a one = a

  namespace MonoidOfBottom
    variable (M : Type u) [MonoidOfBottom M]

    local instance : MulOfBottom M where
      mul := mul
    local instance : OneOfBottom M where
      one := one
    local instance : MulOneOfMulAndOne M where
      one_mul := one_mul
      mul_one := mul_one
    local instance : SemigroupOfMul M where
      mul_assoc := mul_assoc
  end MonoidOfBottom

  instance : MonoidOfBottom ℕ where
    one := 1
    mul := Nat.mul
    mul_assoc := Nat.mul_assoc
    one_mul := Nat.one_mul
    mul_one := Nat.mul_one

  #synth Monoid ℕ

end pretend_hb

  #print MulOneClass
-- class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α

--   class Semiring (α : Type u) extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α

  --  class Ring (R : Type u) extends Semiring R, AddCommGroup R, AddGroupWithOne R
