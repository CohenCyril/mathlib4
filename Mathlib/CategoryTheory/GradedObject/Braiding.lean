import Mathlib.CategoryTheory.GradedObject.Monoidal
import Mathlib.CategoryTheory.Monoidal.Braided

namespace CategoryTheory

open Category Limits

variable {I : Type*} [AddCommMonoid I] {C : Type*} [Category C] [MonoidalCategory C]

namespace GradedObject

namespace Monoidal

section Braided

variable [BraidedCategory C]

variable (X Y Z : GradedObject I C)

section

noncomputable def braiding [HasTensor X Y] [HasTensor Y X] : tensorObj X Y ≅ tensorObj Y X where
  hom k := tensorObjDesc (fun i j hij => (β_ _ _).hom ≫
    ιTensorObj Y X j i k (by simpa only [add_comm j i] using hij))
  inv k := tensorObjDesc (fun i j hij => (β_ _ _).inv ≫
    ιTensorObj X Y j i k (by simpa only [add_comm j i] using hij))

variable {Y Z} in
lemma braiding_naturality_right [HasTensor X Y] [HasTensor Y X] [HasTensor X Z] [HasTensor Z X]
    (f : Y ⟶ Z) :
    whiskerLeft X f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ whiskerRight f X  := by
  dsimp [braiding]
  aesop_cat

variable {X Y} in
lemma braiding_naturality_left [HasTensor Y Z] [HasTensor Z Y] [HasTensor X Z] [HasTensor Z X]
    (f : X ⟶ Y) :
    whiskerRight f Z ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ whiskerLeft Z f  := by
  dsimp [braiding]
  aesop_cat

end

section

variable
  [HasTensor X Y] [HasTensor Y X] [HasTensor Y Z] [HasTensor Z X] [HasTensor X Z]
  [HasTensor (tensorObj X Y) Z] [HasTensor X (tensorObj Y Z)]
  [HasTensor (tensorObj Y Z) X] [HasTensor Y (tensorObj Z X)]
  [HasTensor (tensorObj Y X) Z] [HasTensor Y (tensorObj X Z)]
  [HasGoodTensor₁₂Tensor X Y Z] [HasGoodTensorTensor₂₃ X Y Z]
  [HasGoodTensor₁₂Tensor Y Z X] [HasGoodTensorTensor₂₃ Y Z X]
  [HasGoodTensor₁₂Tensor Y X Z] [HasGoodTensorTensor₂₃ Y X Z]

lemma hexagon_forward :
    (associator X Y Z).hom ≫ (braiding X (tensorObj Y Z)).hom ≫ (associator Y Z X).hom =
      whiskerRight (braiding X Y).hom Z ≫ (associator Y X Z).hom ≫
        whiskerLeft Y (braiding X Z).hom := by
  ext k i₁ i₂ i₃ h
  dsimp [braiding]
  -- working on the LHS
  rw [ιTensorObj₃'_associator_hom_assoc, ιTensorObj₃_eq X Y Z i₁ i₂ i₃ k h _ rfl, assoc,
    ι_tensorObjDesc_assoc, assoc, BraidedCategory.braiding_naturality_assoc,
    BraidedCategory.braiding_tensor_right, assoc, assoc, assoc, assoc, Iso.hom_inv_id_assoc,
    ← ιTensorObj₃'_eq_assoc Y Z X i₂ i₃ i₁ k (by rw [add_comm _ i₁, ← add_assoc, h]) _ rfl,
    ιTensorObj₃'_associator_hom, Iso.inv_hom_id_assoc]
  -- working on the RHS
  rw [ιTensorObj₃'_eq X Y Z i₁ i₂ i₃ k h _ rfl, assoc, ι_tensorHom_assoc,
    ← MonoidalCategory.tensor_comp_assoc, id_comp, ι_tensorObjDesc,
    categoryOfGradedObjects_id, MonoidalCategory.comp_tensor_id, assoc,
    ← ιTensorObj₃'_eq_assoc Y X Z i₂ i₁ i₃ k
      (by rw [add_comm i₂ i₁, h]) (i₁ + i₂) (add_comm i₂ i₁),
    ιTensorObj₃'_associator_hom_assoc,
    ιTensorObj₃_eq Y X Z i₂ i₁ i₃ k (by rw [add_comm i₂ i₁, h]) _ rfl, assoc,
    ι_tensorHom, categoryOfGradedObjects_id, ← MonoidalCategory.id_tensor_comp_assoc,
    ι_tensorObjDesc, MonoidalCategory.id_tensor_comp, assoc,
    ← ιTensorObj₃_eq Y Z X i₂ i₃ i₁ k (by rw [add_comm _ i₁, ← add_assoc, h])
      (i₁ + i₃) (add_comm _ _ )]
  coherence

end

section

variable [HasTensor X Y] [HasTensor Y Z] [HasTensor Z X] [HasTensor Z Y] [HasTensor X Z]
  [HasTensor (tensorObj X Y) Z] [HasTensor X (tensorObj Y Z)]
  [HasTensor Z (tensorObj X Y)] [HasTensor (tensorObj Z X) Y]
  [HasTensor X (tensorObj Z Y)] [HasTensor (tensorObj X Z) Y]
  [HasGoodTensor₁₂Tensor X Y Z] [HasGoodTensorTensor₂₃ X Y Z]
  [HasGoodTensor₁₂Tensor Z X Y] [HasGoodTensorTensor₂₃ Z X Y]
  [HasGoodTensor₁₂Tensor X Z Y] [HasGoodTensorTensor₂₃ X Z Y]

lemma hexagon_reverse :
    (associator X Y Z).inv ≫ (braiding (tensorObj X Y) Z).hom ≫ (associator Z X Y).inv =
      whiskerLeft X (braiding Y Z).hom ≫ (associator X Z Y).inv ≫ whiskerRight (braiding X Z).hom Y := by
  ext k i₁ i₂ i₃ h
  dsimp [braiding]
  -- working on the LHS
  rw [ιTensorObj₃_associator_inv_assoc, ιTensorObj₃'_eq X Y Z i₁ i₂ i₃ k h _ rfl, assoc,
    ι_tensorObjDesc_assoc, assoc, BraidedCategory.braiding_naturality_assoc,
    BraidedCategory.braiding_tensor_left, assoc, assoc, assoc, assoc, Iso.inv_hom_id_assoc,
    ← ιTensorObj₃_eq_assoc Z X Y i₃ i₁ i₂ k (by rw [add_assoc, add_comm i₃, h]) _ rfl,
    ιTensorObj₃_associator_inv, Iso.hom_inv_id_assoc]
  -- working on the RHS
  rw [ιTensorObj₃_eq X Y Z i₁ i₂ i₃ k h _ rfl, assoc, ι_tensorHom_assoc,
    ← MonoidalCategory.tensor_comp_assoc, id_comp, ι_tensorObjDesc,
    categoryOfGradedObjects_id, MonoidalCategory.id_tensor_comp, assoc,
    ← ιTensorObj₃_eq_assoc X Z Y i₁ i₃ i₂ k
      (by rw [add_assoc, add_comm i₃, ← add_assoc, h]) (i₂ + i₃) (add_comm _ _),
    ιTensorObj₃_associator_inv_assoc,
    ιTensorObj₃'_eq X Z Y i₁ i₃ i₂ k (by rw [add_assoc, add_comm i₃, ← add_assoc, h]) _ rfl,
    assoc, ι_tensorHom, categoryOfGradedObjects_id, ← MonoidalCategory.comp_tensor_id_assoc,
    ι_tensorObjDesc, MonoidalCategory.comp_tensor_id, assoc,
    ιTensorObj₃'_eq Z X Y i₃ i₁ i₂ k (by rw [add_assoc, add_comm i₃, h]) (i₁ + i₃) (add_comm _ _)]
  coherence

end

end Braided

section Symmetric

variable [SymmetricCategory C]

variable (X Y : GradedObject I C) [HasTensor X Y] [HasTensor Y X]

@[reassoc (attr := simp)]
lemma symmetry :
    (braiding X Y).hom ≫ (braiding Y X).hom = 𝟙 _ := by
  dsimp [braiding]
  aesop_cat

end Symmetric

end Monoidal

section Instances

variable
  [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C)
    ((curryObj (MonoidalCategory.tensor C)).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C)
    ((curryObj (MonoidalCategory.tensor C)).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

noncomputable instance braidedCategory [BraidedCategory C] :
    BraidedCategory (GradedObject I C) where
  braiding X Y := Monoidal.braiding X Y
  braiding_naturality_left _ _:= Monoidal.braiding_naturality_left _ _
  braiding_naturality_right _ _ _ _  := Monoidal.braiding_naturality_right _ _
  hexagon_forward _ _ _ := Monoidal.hexagon_forward _ _ _
  hexagon_reverse _ _ _ := Monoidal.hexagon_reverse _ _ _

noncomputable instance symmetricCategory [SymmetricCategory C] :
    SymmetricCategory (GradedObject I C) where
  symmetry _ _ := Monoidal.symmetry _ _

section HasFiniteCoproducts

variable [HasFiniteCoproducts C]
    [∀ (X : C), PreservesFiniteCoproducts ((curryObj (MonoidalCategory.tensor C)).obj X)]
    [∀ (X : C), PreservesFiniteCoproducts ((curryObj (MonoidalCategory.tensor C)).flip.obj X)]

noncomputable example [BraidedCategory C] :
    BraidedCategory (GradedObject ℕ C) :=
  inferInstance

noncomputable example [SymmetricCategory C] :
    SymmetricCategory (GradedObject ℕ C) :=
  inferInstance

end HasFiniteCoproducts

end Instances

end GradedObject

end CategoryTheory
