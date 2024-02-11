-- refactor of Limits.KanExtension
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

namespace CategoryTheory

open Category

namespace Limits

namespace IsColimit

variable {J C : Type*} [Category J] [Category C] {F : J ⥤ C} {c : Cocone F}
  (hc : IsColimit c)

lemma isIso_ι_app_of_isTerminal (X : J) (hX : IsTerminal X) : IsIso (c.ι.app X) := by
  change IsIso (coconePointUniqueUpToIso (colimitOfDiagramTerminal hX F) hc).hom
  infer_instance

end IsColimit

end Limits

namespace Functor

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
  {E : Type*} [Category E] [∀ (G : C ⥤ E), HasLeftKanExtension F G]

noncomputable def lan : (C ⥤ E) ⥤ (D ⥤ E) where
  obj G := leftKanExtension F G
  map {G₁ G₂} φ := descOfIsLeftKanExtension _ (leftKanExtensionUnit F G₁) _
    (φ ≫ leftKanExtensionUnit F G₂)

noncomputable def lanUnit : (𝟭 (C ⥤ E)) ⟶ lan F ⋙ (whiskeringLeft C D E).obj F where
  app G := leftKanExtensionUnit F G
  naturality {G₁ G₂} φ := by ext; simp [lan]

instance (G : C ⥤ E) : ((lan F).obj G).IsLeftKanExtension ((lanUnit F).app G) := by
  dsimp [lan, lanUnit]
  infer_instance

noncomputable def isPointwiseLeftKanExtensionLanUnit
    (G : C ⥤ E) [HasPointwiseLeftKanExtension F G] :
    (LeftExtension.mk _ ((lanUnit F).app G)).IsPointwiseLeftKanExtension := by
  have : HasPointwiseLeftKanExtension F ((𝟭 (C ⥤ E)).obj G) := by
    dsimp
    infer_instance
  exact isPointwiseLeftKanExtensionOfIsLeftKanExtension _ ((lanUnit F).app G)

-- this may be slightly generalized
noncomputable def Lan.homEquiv (G : C ⥤ E) (H : D ⥤ E) :
    ((lan F).obj G ⟶ H) ≃ (G ⟶ F ⋙ H) where
  toFun α := (lanUnit F).app G ≫ whiskerLeft _ α
  invFun β := descOfIsLeftKanExtension _ ((lanUnit F).app G) _ β
  left_inv α := by
    dsimp [lan, lanUnit]
    aesop_cat
  right_inv β := by aesop_cat

variable (E) in
noncomputable def Lan.adjunction : lan F ⊣ (whiskeringLeft _ _ E).obj F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := Lan.homEquiv F
      homEquiv_naturality_left_symm := fun {G₁ G₂ H} f α =>
        hom_ext_of_isLeftKanExtension _  ((lanUnit F).app G₁) _ _ (by
          ext X
          dsimp [homEquiv]
          rw [descOfIsLeftKanExtension_fac_app, NatTrans.comp_app, ← assoc]
          have h := congr_app ((lanUnit F).naturality f) X
          dsimp at h ⊢
          rw [← h, assoc, descOfIsLeftKanExtension_fac_app] )
      homEquiv_naturality_right := fun {G H₁ H₂} β f => by simp [homEquiv] }

variable (E) in
@[simp]
lemma Lan.adjunction_unit :
    (Lan.adjunction F E).unit =
      lanUnit F := by
  ext G : 2
  simp [lanUnit, adjunction, homEquiv]

namespace LeftExtension

namespace IsPointwiseLeftKanExtensionAt

variable {F}
variable {G : C ⥤ E} (e : LeftExtension F G) {X : C}
    (he : e.IsPointwiseLeftKanExtensionAt (F.obj X))

lemma isIso_hom_app [Full F] [Faithful F] : IsIso (e.hom.app X) := by
  simpa using he.isIso_ι_app_of_isTerminal _ CostructuredArrow.mkIdTerminal

end IsPointwiseLeftKanExtensionAt

end LeftExtension

section

variable [Full F] [Faithful F]

instance (G : C ⥤ E) (X : C) [HasPointwiseLeftKanExtension F G] :
    IsIso (((Lan.adjunction F E).unit.app G).app X) := by
  simpa using (isPointwiseLeftKanExtensionLanUnit F G (F.obj X)).isIso_hom_app

instance (G : C ⥤ E) [HasPointwiseLeftKanExtension F G] :
    IsIso ((Lan.adjunction F E).unit.app G) :=
  NatIso.isIso_of_isIso_app _

instance coreflective [∀ (G : C ⥤ E), HasPointwiseLeftKanExtension F G] :
    IsIso ((Lan.adjunction F E).unit) :=
  NatIso.isIso_of_isIso_app _

instance coreflective' [∀ (G : C ⥤ E), HasPointwiseLeftKanExtension F G] :
    IsIso (lanUnit F : (𝟭 (C ⥤ E)) ⟶ _) := by
  rw [← Lan.adjunction_unit]
  infer_instance

end

end Functor

end CategoryTheory
