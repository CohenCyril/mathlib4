/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Pointwise Kan extensions

In this file, we define the notion of pointwise (left) Kan Extension. Given two functors
`F : C ⥤ H` and `L : C ⥤ D`, and `E : LeftExtension L F`, we introduce a cocone
`E.coconeAt Y` for the functor `CostructuredArrow.proj L Y ⋙ F : CostructuredArrow L Y ⥤ H`,
and the type `E.IsPointwiseLeftKanExtensionAt Y` which expresses that `E.coconeAt Y` is colimit.
When this holds for all `Y : D`, we may say that `E` is a pointwise left Kan extension
(`E.IsPointwiseLeftKanExtension`).

Conversely, when `CostructuredArrow.proj L Y ⋙ F` has a colimit, we say that
`F` has a pointwise left Kan extension at `Y : D` (`HasPointwiseLeftKanExtensionAt L F Y`),
and if this holds for all `Y : D`, we construct a functor
`pointwiseLeftKanExtension L F : D ⥤ H` and show

 we say that `F` has a pointwise left Kan Extension at `Y : D`
(`HasPointwiseLeftKanExtensionAt L F Y`) if the functor
`CostructuredArrow.proj L Y ⋙ F : CostructuredArrow L Y ⥤ H` has a colimit.



## TODO

* Dualize the results

-/

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D H : Type*} [Category C] [Category D] [Category H] (L : C ⥤ D) (F : C ⥤ H)

abbrev HasPointwiseLeftKanExtensionAt (Y : D) :=
  HasColimit (CostructuredArrow.proj L Y ⋙ F)

abbrev HasPointwiseLeftKanExtension := ∀ (Y : D), HasPointwiseLeftKanExtensionAt L F Y

namespace LeftExtension

variable {F L} (E : LeftExtension L F)

@[simps]
def coconeAt (Y : D) : Cocone (CostructuredArrow.proj L Y ⋙ F) where
  pt := E.right.obj Y
  ι :=
    { app := fun g => E.hom.app g.left ≫ E.right.map g.hom
      naturality := fun g₁ g₂ φ => by
        dsimp
        rw [← CostructuredArrow.w φ]
        simp only [assoc, NatTrans.naturality_assoc, Functor.comp_map,
          Functor.map_comp, comp_id] }

def IsPointwiseLeftKanExtensionAt (Y : D) := IsColimit (E.coconeAt Y)

variable {E}

lemma IsPointwiseLeftKanExtensionAt.hasPointwiseLeftKanExtensionAt
    {E : LeftExtension L F} {Y : D} (h : E.IsPointwiseLeftKanExtensionAt Y) :
  HasPointwiseLeftKanExtensionAt L F Y := ⟨_, h⟩

variable (E)

abbrev IsPointwiseLeftKanExtension := ∀ (Y : D), E.IsPointwiseLeftKanExtensionAt Y

variable (h : E.IsPointwiseLeftKanExtension)

lemma IsPointwiseLeftKanExtension.hasPointwiseLeftKanExtension :
    HasPointwiseLeftKanExtension L F :=
  fun Y => (h Y).hasPointwiseLeftKanExtensionAt

def isUniversalOfPointwise : E.IsUniversal :=
  IsInitial.ofUniqueHom (fun G => StructuredArrow.homMk
        { app := fun Y => (h Y).desc (LeftExtension.coconeAt G Y)
          naturality := fun Y₁ Y₂ φ => (h Y₁).hom_ext (fun X => by
            rw [(h Y₁).fac_assoc (coconeAt G Y₁) X]
            simpa using (h Y₂).fac (coconeAt G Y₂) ((CostructuredArrow.map φ).obj X)) }
      (by
        ext X
        simpa using (h (L.obj X)).fac (LeftExtension.coconeAt G _) (CostructuredArrow.mk (𝟙 _))))
    (fun G => by
      suffices ∀ (m₁ m₂ : E ⟶ G), m₁ = m₂ by intros; apply this
      intro m₁ m₂
      ext Y
      apply (h Y).hom_ext
      intro X
      have eq₁ := congr_app (StructuredArrow.w m₁) X.left
      have eq₂ := congr_app (StructuredArrow.w m₂) X.left
      dsimp at eq₁ eq₂ ⊢
      simp only [assoc, NatTrans.naturality]
      rw [reassoc_of% eq₁, reassoc_of% eq₂])

--lemma IsPointwiseLeftKanExtension.hasLeftKanExtension :
--    HasLeftKanExtension L F where

end LeftExtension

section

variable [HasPointwiseLeftKanExtension L F]

@[simps]
noncomputable def pointwiseLeftKanExtension : D ⥤ H where
  obj Y := colimit (CostructuredArrow.proj L Y ⋙ F)
  map {Y₁ Y₂} f :=
    colimit.desc (CostructuredArrow.proj L Y₁ ⋙ F)
      (Cocone.mk (colimit (CostructuredArrow.proj L Y₂ ⋙ F))
        { app := fun g => colimit.ι (CostructuredArrow.proj L Y₂ ⋙ F)
            ((CostructuredArrow.map f).obj g)
          naturality := fun g₁ g₂ φ => by
            simpa using colimit.w (CostructuredArrow.proj L Y₂ ⋙ F)
              ((CostructuredArrow.map f).map φ) })
  map_id Y := colimit.hom_ext (fun j => by
    dsimp
    simp only [colimit.ι_desc, comp_id]
    congr
    apply CostructuredArrow.map_id)
  map_comp {Y₁ Y₂ Y₃} f f' := colimit.hom_ext (fun j => by
    dsimp
    simp only [colimit.ι_desc, colimit.ι_desc_assoc, comp_obj, CostructuredArrow.proj_obj]
    congr 1
    apply CostructuredArrow.map_comp)

@[simps]
noncomputable def pointwiseLeftKanExtensionUnit : F ⟶ L ⋙ pointwiseLeftKanExtension L F where
  app X := colimit.ι (CostructuredArrow.proj L (L.obj X) ⋙ F) (CostructuredArrow.mk (𝟙 (L.obj X)))
  naturality {X₁ X₂} f:= by
    simp only [comp_obj, pointwiseLeftKanExtension_obj, comp_map,
      pointwiseLeftKanExtension_map, colimit.ι_desc, CostructuredArrow.map_mk]
    rw [id_comp]
    let φ : CostructuredArrow.mk (L.map f) ⟶ CostructuredArrow.mk (𝟙 (L.obj X₂)) :=
      CostructuredArrow.homMk f
    exact colimit.w (CostructuredArrow.proj L (L.obj X₂) ⋙ F) φ

noncomputable def pointwiseLeftKanExtensionIsPointwiseLeftKanExtension :
    (LeftExtension.mk _ (pointwiseLeftKanExtensionUnit L F)).IsPointwiseLeftKanExtension :=
  fun X => IsColimit.ofIsoColimit (colimit.isColimit _) (Cocones.ext (Iso.refl _) (fun j => by
    dsimp
    simp only [comp_id, colimit.ι_desc, CostructuredArrow.map_mk]
    congr 1
    rw [id_comp]
    rfl))

noncomputable def pointwiseLeftKanExtensionIsUniversal :
    (LeftExtension.mk _ (pointwiseLeftKanExtensionUnit L F)).IsUniversal :=
  LeftExtension.isUniversalOfPointwise _
    (pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L F)

instance : (pointwiseLeftKanExtension L F).IsLeftKanExtension
    (pointwiseLeftKanExtensionUnit L F) where
  nonempty_isUniversal := ⟨pointwiseLeftKanExtensionIsUniversal L F⟩

--instance : HasLeftKanExtension L F :=
--  HasLeftKanExtension.mk' _ (F.pointwiseLeftKanExtensionNatTrans L)

end

end Functor

end CategoryTheory
