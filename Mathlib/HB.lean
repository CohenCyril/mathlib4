import Lean
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Basic

#print Semigroup
#print Monoid
#print Ring
#print Semiring
#print Mul



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

-- namespace hb_stuff

--   universe u

--   -- class
--   class Bottom (α : Type u) where
--   instance (α : Type u) : Bottom α where

--   -- mixin
--   class MulOfBottom (α : Type u) where
--     /-- `a ⬝ b` computes the product of `a` and `b`. See `HMul`. -/
--     protected mul : α → α → α

--   -- class
--   class Mul (α : Type u) extends Bottom α, MulOfBottom α where
--   -- should be Mul.mul
--   def mul {α : Type u} [Mul α] := MulOfBottom.mul (α := α)
--   -- macro_rules | `($x ⬝ $y)   => `(binop% Mul $x $y)

--   structure MulType where
--     sort : Type u
--     classof : Mul sort

--   -- loop
--   instance (α : Type u) [Bottom α] [MulOfBottom α] : Mul α where
--   infixl:70 " ⬝ "   => mul

--   -- mixin
--   class SemigroupOfMul (G : Type u) [MulOfBottom G] where
--     /-- Multiplication is associative -/
--     protected mul_assoc : ∀ a b c : G, (a ⬝ b) ⬝ c = a ⬝ (b ⬝ c)

--   -- class
--   class Semigroup (G : Type u) extends Bottom G, Mul G, SemigroupOfMul G  where
--   #print Semigroup

--   -- mixin
--   class OneOfBottom (α : Type u) where one : α

--   -- class
--   class One (α : Type u) extends Bottom α, OneOfBottom α where

--   instance (α : Type u) [Bottom α] [OneOfBottom α] : One α where
--   def one {α : Type u} [One α] := OneOfBottom.one (α := α)
--   notation "𝟙"   => one

--   class MulOneOfMulAndOne (M : Type u) [Bottom M] [OneOfBottom M] [MulOfBottom M] where
--     /-- One is a left neutral element for multiplication -/
--     protected one_mul : ∀ a : M, 𝟙 ⬝ a = a
--     /-- One is a right neutral element for multiplication -/
--     protected mul_one : ∀ a : M, a ⬝ 𝟙 = a

--   class MulOne (M : Type u) extends Bottom M, One M, Mul M, MulOneOfMulAndOne M where

--   class Monoid (M : Type u) extends Bottom M, Semigroup M, MulOne M where


--   -- factory
--   class MonoidOfBottom (M : Type u) where
--     one : M
--     mul : M → M → M
--     mul_assoc : ∀ a b c : M, mul (mul a b) c = mul a (mul b c)
--     one_mul : ∀ a : M, mul one a = a
--     mul_one : ∀ a : M, mul a one = a

--   namespace MonoidOfBottom
--     variable (M : Type u) [MonoidOfBottom M]

--     @[local instance] def bottom : Bottom M where
--     @[local instance] def mulofbottom : MulOfBottom M where
--       mul := mul
--     instance : Mul M where
--     @[local instance] def oneofbottom : OneOfBottom M where
--       one := one
--     instance : One M where
--     @[local instance] def muloneofbottom : MulOneOfMulAndOne M where
--       one_mul := one_mul
--       mul_one := mul_one
--     instance : MulOne M where
--     @[local instance] def semigroup : SemigroupOfMul M where
--       mul_assoc := mul_assoc
--     instance : Semigroup M where
--     instance : Monoid M where
--   end MonoidOfBottom

--   instance : MonoidOfBottom ℕ where
--     one := 1
--     mul := Nat.mul
--     mul_assoc := Nat.mul_assoc
--     one_mul := Nat.one_mul
--     mul_one := Nat.mul_one

--   #synth Monoid ℕ


--   #print Monoid
--   #print MulOne

-- end hb_stuff

open Lean.Parser.Term
open Lean.Parser.Command

syntax (name := mixin) "mixin" declId
  ppIndent((ppSpace bracketedBinder)* «extends»? optType)
  ((" := " <|> " where ") (structCtor)? structFields)? optDeriving  : command

-- THIS WORKED
-- macro_rules | `(mixin $id:declId $binders* $[$«extends»]? $[: $ty]? $[$ceorwhere $[$K]? $fields]? $der) => `(class $id $binders* $[$«extends»]? $[: $ty]? $[where $[$K]?$fields:structFields]? $der)

macro_rules | `(mixin $id:declId $binders* $[$«extends»]? $[: $ty]? $[$ceorwhere $[$K]? $fields:structSimpleBinder*]? $der) => do
  let fields ← fields.mapM fun fields =>
    fields.mapM fun
    | `(structSimpleBinder| $[$doc:docComment]? $[$attrs:attributes]? protected $_:ident $_:optDeclSig) => Lean.Macro.throwError "Unexpected protected field in mixin"
    | `(structSimpleBinder| $[$doc:docComment]? $[$attrs:attributes]? private $_:ident $_:optDeclSig) => Lean.Macro.throwError "Unexpected private field in mixin"
    | `(structSimpleBinder| $[$doc:docComment]? $[$attrs:attributes]? $id:ident $sig:optDeclSig) =>
      `(structSimpleBinder| $[$doc:docComment]? $[$attrs:attributes]? protected $id:ident $sig:optDeclSig)
    | _ => Lean.Macro.throwUnsupported
  -- let fields ← fields.mapM fun fields ↦ do
  --   fields.mapM fun field ↦ do

      -- let x := field.raw[0]
      -- dbg_trace x
      -- let y  := `($«protected»)
      -- dbg_trace y
      -- by rcases rawfield with ⟨⟩
      -- return ⟨field.raw⟩ -- : Lean.TSyntax `Lean.Parser.Command.structExplicitBinder)
  `(class $id $binders* $[$«extends»]? $[: $ty]? $[where $[$K]?$fields*]? $der)

open Lean
open Lean.Parser
-- def classof            := leading_parser
--   " of " >> sepBy1 termParser ", "

-- def mixins            := leading_parser
--   sepBy1 termParser ", "

syntax mixins := term,*

syntax (name := mathclass) "mathclass" declId
  ppIndent((ppSpace bracketedBinder)* " of " mixins optType) : command
  -- ((" := " <|> " where ") (structCtor)? structFields)? optDeriving  : command

-- initialize dummyExt :
--     PersistentEnvExtension Unit Unit Unit ←
--   registerPersistentEnvExtension {
--     mkInitial := pure ()
--     addImportedFn := fun _ => pure ()
--     addEntryFn := fun _ _ => ()
--     exportEntriesFn := fun _ => #[]
--   }

open Elab.Command
elab_rules : command | `(mathclass $id:declId $binders* of $[$mixins],* $[: $ty]?) => do
  let K := none
  let fields := none
  -- let «extends» := classof.mapM (fun (c : TSyntax _) => match c with
  --   | `(of $[$stuff] ) => _
  -- )
  let decl_class ← `(
    class $id $binders* extends $mixins,* $[: $ty]? $[where $[$K]?$[$fields]*]?
    -- namespace $id
    --   structure type where (sort : Type*) («class» : $id)
    -- end $id
    )
  -- let env ← getEnv
  --  env.find?
  -- dbg_trace dummyExt.getState env
  elabCommand decl_class
  let env ← getEnv
  let onlyid ← match id with
    | `(declId| $id $[.{ $u,* }]?) => pure id
    | _ => throwError "parser bug"
  let fields := getStructureFieldsFlattened env onlyid.getId

  let implicit_binders : TSyntaxArray _ ← binders.mapM fun b : TSyntax _ => match b with
    | `(bracketedBinder| ($xs:ident* $[: $ty]?)) =>
      `(bracketedBinder| {$xs:ident* $[: $ty]?})
    | _ => pure b
  -- dbg_trace fields
  fields.forM fun f ↦ do
    match env.find? f with
      | none => do
         let args ← binders.concatMapM fun
            | `(bracketedBinder| ($xs:ident* $[: $_]?)) => pure xs
            | _ => pure #[]
         let decl_f ← `(def $(mkIdent f) $implicit_binders* [self : $onlyid:ident $args:ident*] := self.$(mkIdent f))
         elabCommand decl_f
      | _ => pure ()
  -- mixins.mapM fun m =>
  -- env.find?


-- macro_rules | `(mathclass $id:declId $binders* of $mixins,* $[: $ty]?) => do
--   let K := none
--   let fields := none
--   -- let «extends» := classof.mapM (fun (c : TSyntax _) => match c with
--   --   | `(of $[$stuff] ) => _
--   -- )
--   `(class $id $binders* extends $mixins,* $[: $ty]? $[where $[$K]?$[$fields]*]?
--     )
  -- `(class $id $binders* $[$«extends»]? $[: $ty]? $[where])

-- structFields =
-- manyIndent <|
--     ppLine >> checkColGe >> ppGroup (
--       structExplicitBinder <|> structImplicitBinder <|>
--       structInstBinder <|> structSimpleBinder)
--  := leading_parser
--     (structureTk <|> classTk) >>
--     -- Note: no error recovery here due to clashing with the `class abbrev` syntax
--     declId >>
--     ppIndent (many (ppSpace >> Term.bracketedBinder) >> optional «extends» >> Term.optType) >>
--     optional ((symbol " := " <|> " where ") >> optional structCtor >> structFields) >>
--     optDeriving

-- macro "mixin": command =>  `(command|class )
namespace pretend_hb
  universe u
  -- class

  mixin OneOfBottom (α : Type u) where
    /-- TODO: One is one! -/
    one : α
  -- class
  #print OneOfBottom.one

  mixin MulOfBottom (α : Type u) where
    /-- `a ⬝ b` computes the product of `a` and `b`. See `HMul`. -/
    mul : α → α → α
  -- #print MulOfBottom
  mathclass Mul (α : Type u) of MulOfBottom α
  infixl:70 " ⬝ "   => mul
  #print mul

  -- generate
  instance (α : Type u) [MulOfBottom α] : Mul α where


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
  #print one
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
