/-
Copyright (c) 2026 Judah Towery. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judah Towery
-/

import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

/-!
# Tricategorical fragments

Defines some pieces that could build into the tricategory of bicategories.
-/

namespace CategoryTheory.Bicategory

open Category Bicategory

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄

open scoped Pseudofunctor.StrongTrans

variable {B C D E : Type*} [Bicategory.{w₁, v₁} B] [Bicategory.{w₂, v₂} C] [Bicategory.{w₃, v₃} D]
  [Bicategory.{w₄, v₄} E]

namespace Bicat

@[simps]
def postWhisker {F G : B ⥤ᵖ C} (η : F ⟶ G) (H : C ⥤ᵖ D) : 
    F.comp H ⟶ G.comp H where
  app _ := H.map (η.app _)
  naturality _ := {
    hom := (H.mapComp _ _).inv ≫ H.map₂ (η.naturality _).hom ≫ (H.mapComp _ _).hom
    inv := (H.mapComp _ _).inv ≫ H.map₂ (η.naturality _).inv ≫ (H.mapComp _ _).hom
    hom_inv_id := by simp [←assoc (H.map₂ _)]
    inv_hom_id := by simp [←assoc (H.map₂ _)] }
  naturality_naturality θ := by simp only [Pseudofunctor.comp_toPrelaxFunctor, 
                                  PrelaxFunctor.comp_toPrelaxFunctorStruct, 
                                  PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj,
                                  Prefunctor.comp_map, PrelaxFunctorStruct.comp_map₂, assoc]
                                calc
                                 _ = (H.mapComp _ _).inv ≫ H.map₂ ((F.map₂ θ) ▷ _) ≫
                                  H.map₂ (η.naturality _).hom ≫ (H.mapComp _ _).hom := by simp
                                 _ = (H.mapComp _ _).inv ≫ H.map₂ (η.naturality _).hom ≫
                                  H.map₂ (_ ◁ G.map₂ θ) ≫ 
                                  (H.mapComp (η.app _) (G.map _)).hom := 
                                 by rw [←assoc (H.map₂ (F.map₂ θ ▷ η.app _)), 
                                      ←PrelaxFunctor.map₂_comp, 
                                      congrArg H.map₂ (η.naturality_naturality θ)]
                                    simp
                                 _ = _ := by simp
  naturality_id b := by simp only [Pseudofunctor.comp_toPrelaxFunctor, 
                          PrelaxFunctor.comp_toPrelaxFunctorStruct, 
                         PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj,
                         Prefunctor.comp_map, Pseudofunctor.comp_mapId, Iso.trans_hom,
                         Functor.mapIso_hom, PrelaxFunctor.mapFunctor_map, whiskerLeft_comp,
                         assoc, comp_whiskerRight]
                        have := congrArg (fun t => (H.mapComp _ _).inv ≫ H.map₂ t ≫
                        (H.mapComp _ _).hom ≫ _ ◁ (H.mapId (G.obj _)).hom) (η.naturality_id b)
                        simp only [PrelaxFunctor.map₂_comp, assoc, Pseudofunctor.map₂_whisker_right,
                          Pseudofunctor.map₂_whisker_left] at this
                        nth_rewrite 2 [←assoc ((H.mapComp _ _).inv)] at this
                        rw [Iso.inv_hom_id_assoc, Iso.inv_hom_id, id_comp,
                          ←assoc (H.map₂ _), Pseudofunctor.map₂_left_unitor] at this
                        have h := H.toLax.map₂_rightUnitor (η.app b)
                        simp only [Pseudofunctor.toLax_toPrelaxFunctor, Pseudofunctor.toLax_mapId,
                          Pseudofunctor.toLax_mapComp] at h
                        simp only [h, assoc, Iso.inv_hom_id_assoc, whiskerLeft_inv_hom, comp_id,
                          Iso.inv_hom_id_assoc] at this
                        exact this
  naturality_comp f g := by simp only [Pseudofunctor.comp_toPrelaxFunctor,
                              PrelaxFunctor.comp_toPrelaxFunctorStruct,
                              PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj,
                              Prefunctor.comp_map, Pseudofunctor.comp_mapComp, Iso.trans_hom,
                              Functor.mapIso_hom, PrelaxFunctor.mapFunctor_map, whiskerLeft_comp,
                              assoc, comp_whiskerRight]
                            have := congrArg (fun t => (H.mapComp _ _).inv ≫ H.map₂ t ≫
                              (H.mapComp (η.app _) (_ ≫ _)).hom ≫ _ ◁ (H.mapComp _ _).hom)
                              (η.naturality_comp f g)
                            simp only [PrelaxFunctor.map₂_comp, Pseudofunctor.map₂_whisker_right,
                              Pseudofunctor.map₂_associator, Pseudofunctor.map₂_whisker_left, assoc,
                              Iso.inv_hom_id_assoc, whiskerLeft_inv_hom, comp_id] at this
                            have h := congrArg (fun t =>  _ ◁ (H.mapComp _ _).hom ≫ t ≫ 
                              H.map₂ (α_ _ _ _).inv ≫ (H.mapComp _ _).hom)
                              (H.toLax.mapComp_assoc_right (F.map f) (η.app _) (G.map g))
                            simp only [Pseudofunctor.toLax_toPrelaxFunctor, 
                              Pseudofunctor.toLax_mapComp,  assoc, whiskerLeft_hom_inv_assoc, 
                              ←assoc (H.map₂ (α_ _ _ _).hom), ←H.map₂_comp, 
                              Iso.inv_hom_id, Iso.hom_inv_id, H.map₂_id, id_comp, comp_id] at h
                            rw [←assoc (H.mapComp _ (_ ≫ _)).inv,
                              ←assoc ((_ ≫ H.map₂ (α_ _ _ _).inv)), assoc (H.mapComp _ _).inv,
                              h] at this
                            simp only [assoc] at this
                            exact this
                            
@[simps]
def whiskerRightId (F : B ⥤ᵖ C) (H : C ⥤ᵖ D) :
    𝟙 (F.comp H) ≅ postWhisker (𝟙 F) H where
  hom := {
    as := {
      app _ := (H.mapId (F.obj _)).inv
      naturality f := by have := H.toLax.map₂_leftUnitor (F.map f)
                         simp only [Pseudofunctor.toLax_toPrelaxFunctor, Pseudofunctor.toLax_mapId,
                           Pseudofunctor.toLax_mapComp] at this
                         simp [this] } }
  inv := {
    as := {
      app _ := (H.mapId (F.obj _)).hom
      naturality f := by have := H.toLax.map₂_leftUnitor (F.map f)
                         simp only [Pseudofunctor.toLax_toPrelaxFunctor, Pseudofunctor.toLax_mapId,
                         Pseudofunctor.toLax_mapComp] at this
                         simp [this] } }
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

@[simps]
def whiskerRightComp {F G K : B ⥤ᵖ C} (η : F ⟶ G) (θ : G ⟶ K) (H : C ⥤ᵖ D) :
    postWhisker (η ≫ θ) H ≅ postWhisker η H ≫ postWhisker θ H where
  hom := {
    as := {
      app _ := (H.mapComp (η.app _) (θ.app _)).hom
      naturality f := by simp only [Pseudofunctor.comp_toPrelaxFunctor, 
                           PrelaxFunctor.comp_toPrelaxFunctorStruct,
                           PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj,
                           Prefunctor.comp_map, postWhisker, Pseudofunctor.StrongTrans.comp_app,
                           Pseudofunctor.StrongTrans.categoryStruct_comp_naturality_hom,
                           comp_whiskerRight, whiskerLeft_comp, assoc, PrelaxFunctor.map₂_comp,
                           Pseudofunctor.map₂_whisker_right, Pseudofunctor.map₂_associator,
                           Pseudofunctor.map₂_whisker_left, Iso.inv_hom_id_assoc,
                           Pseudofunctor.StrongTrans.categoryStruct_comp_naturality_inv,
                           Iso.inv_hom_id, comp_id]
                         have := H.toLax.mapComp_assoc_right (F.map f) (η.app _) (θ.app _)
                         simp only [Pseudofunctor.toLax_toPrelaxFunctor,
                         Pseudofunctor.toLax_mapComp] at this
                         have h := congrArg (fun t => _ ◁ (H.mapComp _ _).hom ≫ t ≫
                           H.map₂ (α_ _ _ _).inv ≫ (H.mapComp _ _).hom) this
                         simp only [assoc, whiskerLeft_hom_inv_assoc] at h
                         have := H.toLax.mapComp_assoc_left_assoc _ _ _ ((H.mapComp _ _).hom ≫
                           (H.mapComp (η.app _) (θ.app _)).hom ▷ H.map (K.map f))
                         simp only [Pseudofunctor.toLax_toPrelaxFunctor,
                           Pseudofunctor.toLax_mapComp, Iso.inv_hom_id_assoc,
                           inv_hom_whiskerRight] at this
                         rw [←comp_id (α_ (H.map _) (H.map _) (H.map (K.map _))).inv, this,
                           ←assoc ((H.mapComp (F.map _) _).inv),
                           ←assoc ((H.mapComp (F.map _) _).inv ≫ _),
                           assoc ((H.mapComp (F.map _) _).inv), h, ←assoc (H.map₂ (α_ _ _ _).hom),
                           ←PrelaxFunctor.map₂_comp]
                         simp } }
  inv := {
    as := {
      app _ := (H.mapComp (η.app _) (θ.app _)).inv
      naturality f := by simp only [Pseudofunctor.comp_toPrelaxFunctor, 
                           PrelaxFunctor.comp_toPrelaxFunctorStruct,
                           PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj,
                           Prefunctor.comp_map, postWhisker, Pseudofunctor.StrongTrans.comp_app,
                           Pseudofunctor.StrongTrans.categoryStruct_comp_naturality_hom,
                           comp_whiskerRight, whiskerLeft_comp, assoc, PrelaxFunctor.map₂_comp,
                           Pseudofunctor.map₂_whisker_right, Pseudofunctor.map₂_associator,
                           Pseudofunctor.map₂_whisker_left, Iso.inv_hom_id_assoc,
                           Pseudofunctor.StrongTrans.categoryStruct_comp_naturality_inv,
                           Iso.inv_hom_id, comp_id]
                         have := H.toLax.mapComp_assoc_right (F.map f) (η.app _) (θ.app _)
                         simp only [Pseudofunctor.toLax_toPrelaxFunctor,
                         Pseudofunctor.toLax_mapComp] at this
                         have h := congrArg (fun t => _ ◁ (H.mapComp _ _).hom ≫ t ≫
                           H.map₂ (α_ _ _ _).inv ≫ (H.mapComp _ _).hom) this
                         simp only [assoc, whiskerLeft_hom_inv_assoc] at h
                         have := H.toLax.mapComp_assoc_left_assoc _ _ _ ((H.mapComp _ _).hom ≫
                           (H.mapComp (η.app _) (θ.app _)).hom ▷ H.map (K.map f))
                         simp only [Pseudofunctor.toLax_toPrelaxFunctor,
                           Pseudofunctor.toLax_mapComp, Iso.inv_hom_id_assoc,
                           inv_hom_whiskerRight] at this
                         rw [←comp_id (α_ (H.map _) (H.map _) (H.map (K.map _))).inv, this,
                           ←assoc ((H.mapComp (F.map _) _).inv),
                           ←assoc ((H.mapComp (F.map _) _).inv ≫ _),
                           assoc ((H.mapComp (F.map _) _).inv), h, ←assoc (H.map₂ (α_ _ _ _).hom),
                           ←PrelaxFunctor.map₂_comp]
                         simp } }
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

@[simps]
def whiskerRightIso {F G : B ⥤ᵖ C} {η θ : F ⟶ G} (α : η ≅ θ) (H : C ⥤ᵖ D) :
    postWhisker η H ≅ postWhisker θ H where
 hom := {
    as := {
      app _ := H.map₂ (α.hom.as.app _)
      naturality f := by simp only [Pseudofunctor.comp_toPrelaxFunctor,
                           PrelaxFunctor.comp_toPrelaxFunctorStruct,
                           PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj,
                           Prefunctor.comp_map, postWhisker, assoc]
                         have := congrArg (fun t => H.map₂ t ≫ 
                           (H.mapComp _ _).hom) (α.hom.as.naturality f)
                         simp only [PrelaxFunctor.map₂_comp, Pseudofunctor.map₂_whisker_right,
                           assoc, Iso.inv_hom_id, comp_id] at this
                         simp [←this] } }
 inv := {
   as := {
     app _ := H.map₂ (α.inv.as.app _)
     naturality f := by simp only [Pseudofunctor.comp_toPrelaxFunctor,
                          PrelaxFunctor.comp_toPrelaxFunctorStruct,
                          PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj,
                          Prefunctor.comp_map, postWhisker, assoc]
                        have := congrArg (fun t => H.map₂ t ≫
                          (H.mapComp _ _).hom) (α.inv.as.naturality f)
                        simp only [PrelaxFunctor.map₂_comp, Pseudofunctor.map₂_whisker_right,
                          assoc, Iso.inv_hom_id, comp_id] at this
                        simp [←this] } }
 hom_inv_id := by ext
                  simp [←H.map₂_comp, ←(Pseudofunctor.StrongTrans.homCategory_comp_as_app _ _) _]
 inv_hom_id := by ext
                  simp [←H.map₂_comp, ←(Pseudofunctor.StrongTrans.homCategory_comp_as_app _ _) _]

def whiskerRight {F G : B ⥤ᵖ C} (e : F ≌ G) (H : C ⥤ᵖ D) : F.comp H ≌ G.comp H :=
  Equivalence.mkOfAdjointifyCounit ((whiskerRightId _ _).trans ((whiskerRightIso e.unit _).trans
    (whiskerRightComp _ _ _))) ((whiskerRightComp _ _ _).symm.trans
    ((whiskerRightIso e.counit _).trans (whiskerRightId _ _).symm))

@[simps]
def preWhisker (H : B ⥤ᵖ C) {F G : C ⥤ᵖ D} (η : F ⟶ G) : H.comp F ⟶ H.comp G where
  app _ := η.app (H.obj _)
  naturality _ := η.naturality (H.map _)
  naturality_id _ := by simp only [Pseudofunctor.comp_toPrelaxFunctor,
                          PrelaxFunctor.comp_toPrelaxFunctorStruct,
                          PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj,
                          Prefunctor.comp_map, Pseudofunctor.comp_mapId, Iso.trans_hom,
                          Functor.mapIso_hom, PrelaxFunctor.mapFunctor_map, whiskerLeft_comp,
                          comp_whiskerRight, assoc]
                        rw [←(η.naturality_id _), ←assoc (_ ▷ _), η.naturality_naturality _, assoc]
  naturality_comp _ _ := by simp only [Pseudofunctor.comp_toPrelaxFunctor,
                              PrelaxFunctor.comp_toPrelaxFunctorStruct,
                              PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj,
                              Prefunctor.comp_map, Pseudofunctor.comp_mapComp, Iso.trans_hom,
                              Functor.mapIso_hom, PrelaxFunctor.mapFunctor_map, whiskerLeft_comp,
                              comp_whiskerRight, assoc]
                            rw [←η.naturality_comp _ _, ←assoc (η.naturality _).hom,
                            ←η.naturality_naturality _, assoc]

@[simp]
def whiskerLeftId (H : B ⥤ᵖ C) (F : C ⥤ᵖ D) : 𝟙 (H.comp F) ≅ preWhisker H (𝟙 F) := Iso.refl _

@[simp]
def whiskerLeftComp (H : B ⥤ᵖ C) {F G K : C ⥤ᵖ D} (η : F ⟶ G) (θ : G ⟶ K) :
    preWhisker H (η ≫ θ) ≅ preWhisker H η ≫ preWhisker H θ := Iso.refl _

@[simps]
def whiskerLeftIso (H : B ⥤ᵖ C) {F G : C ⥤ᵖ D} {η θ : F ⟶ G} (α : η ≅ θ) :
    preWhisker H η ≅ preWhisker H θ where
  hom := {
    as := {
      app _ := α.hom.as.app (H.obj _) } }
  inv := {
    as := {
      app _ := α.inv.as.app (H.obj _) } }
  hom_inv_id := by ext
                   simp [←(Pseudofunctor.StrongTrans.homCategory_comp_as_app _ _) _]
  inv_hom_id := by ext
                   simp [←(Pseudofunctor.StrongTrans.homCategory_comp_as_app _ _) _]

def whiskerLeft (H : B ⥤ᵖ C) {F G : C ⥤ᵖ D} (e : F ≌ G) : H.comp F ≌ H.comp G :=
  Equivalence.mkOfAdjointifyCounit ((whiskerLeftId _ _).trans ((whiskerLeftIso _ e.unit).trans
    (whiskerLeftComp _ _ _))) ((whiskerLeftComp _ _ _).symm.trans
    ((whiskerLeftIso _ e.counit).trans (whiskerLeftId _ _).symm))

@[simps]
def leftUnitorHom (F : C ⥤ᵖ B) : (Pseudofunctor.id C).comp F ⟶ F where
  app _ := 𝟙 _
  naturality _ := (ρ_ _) ≪≫ (λ_ _).symm

@[simps]
def leftUnitorInv (F : C ⥤ᵖ B) : F ⟶ (Pseudofunctor.id C).comp F where
  app _ := 𝟙 _
  naturality _ := (ρ_ _) ≪≫ (λ_ _).symm

@[simps]
def leftUnitorUnit (F : C ⥤ᵖ B) :
    𝟙 ((Pseudofunctor.id C).comp F) ≅ leftUnitorHom F ≫ leftUnitorInv F where
  hom := {
    as := {
      app _ := (λ_ _).inv
      naturality _ := by simp only [Pseudofunctor.comp_toPrelaxFunctor,
                            Pseudofunctor.id_toPrelaxFunctor,
                            PrelaxFunctor.comp_toPrelaxFunctorStruct,
                            PrelaxFunctor.id_toPrelaxFunctorStruct,
                            PrelaxFunctorStruct.comp_toPrefunctor,
                            PrelaxFunctorStruct.id_toPrefunctor, Prefunctor.id_comp,
                            Pseudofunctor.StrongTrans.categoryStruct_id_app,
                            Pseudofunctor.StrongTrans.comp_app, leftUnitorHom_app,
                            leftUnitorInv_app, unitors_inv_equal, whiskerLeft_rightUnitor_inv,
                            Pseudofunctor.StrongTrans.categoryStruct_comp_naturality_hom,
                            leftUnitorHom_naturality, Iso.trans_hom, Iso.symm_hom, whiskerRight_id,
                            assoc, leftUnitorInv_naturality, whiskerLeft_comp,
                            whiskerLeft_rightUnitor, id_whiskerLeft, Iso.hom_inv_id_assoc,
                            Iso.inv_hom_id_assoc,
                            Pseudofunctor.StrongTrans.categoryStruct_id_naturality_hom,
                            Iso.cancel_iso_hom_left, Iso.cancel_iso_inv_left]
                         rw [leftUnitor_comp_inv, assoc, Iso.hom_inv_id]
                         simp } }
  inv := {
    as := {
      app _ := (λ_ _).hom } }
  hom_inv_id := by simp only [Pseudofunctor.comp_toPrelaxFunctor, Pseudofunctor.id_toPrelaxFunctor,
                     PrelaxFunctor.comp_toPrelaxFunctorStruct,
                     PrelaxFunctor.id_toPrelaxFunctorStruct, PrelaxFunctorStruct.comp_toPrefunctor,
                     PrelaxFunctorStruct.id_toPrefunctor, Prefunctor.id_comp,
                     Pseudofunctor.StrongTrans.categoryStruct_id_app, unitors_inv_equal,
                     Pseudofunctor.toOplax_toPrelaxFunctor, Oplax.StrongTrans.toOplax_app,
                     Pseudofunctor.StrongTrans.toOplax_app, leftUnitorInv_app, unitors_equal]
                   ext
                   simp
  inv_hom_id := by simp only [Pseudofunctor.toOplax_toPrelaxFunctor,
                     Pseudofunctor.comp_toPrelaxFunctor, Pseudofunctor.id_toPrelaxFunctor,
                     PrelaxFunctor.comp_toPrelaxFunctorStruct,
                     PrelaxFunctor.id_toPrelaxFunctorStruct, PrelaxFunctorStruct.comp_toPrefunctor,
                     PrelaxFunctorStruct.id_toPrefunctor, Prefunctor.id_comp,
                     Oplax.StrongTrans.toOplax_app, Pseudofunctor.StrongTrans.toOplax_app,
                     leftUnitorInv_app, unitors_equal,
                     Pseudofunctor.StrongTrans.categoryStruct_id_app, unitors_inv_equal]
                   ext
                   simp

@[simps]
def leftUnitorCounit (F : C ⥤ᵖ B) : leftUnitorInv F ≫ leftUnitorHom F ≅ 𝟙 F where
  hom := {
    as := {
      app _ := (ρ_ _).hom } }
  inv := {
    as := {
      app _ := (ρ_ _).inv
      naturality _ := by simp only [Pseudofunctor.StrongTrans.categoryStruct_id_app,
                           Pseudofunctor.StrongTrans.comp_app, Pseudofunctor.comp_toPrelaxFunctor,
                           Pseudofunctor.id_toPrelaxFunctor,
                           PrelaxFunctor.comp_toPrelaxFunctorStruct,
                           PrelaxFunctor.id_toPrelaxFunctorStruct,
                           PrelaxFunctorStruct.comp_toPrefunctor,
                           PrelaxFunctorStruct.id_toPrefunctor, Prefunctor.id_comp,
                           leftUnitorInv_app, leftUnitorHom_app, whiskerLeft_rightUnitor_inv,
                           Pseudofunctor.StrongTrans.categoryStruct_comp_naturality_hom,
                           leftUnitorInv_naturality, Iso.trans_hom, Iso.symm_hom, whiskerRight_id,
                           assoc, leftUnitorHom_naturality, whiskerLeft_comp,
                           whiskerLeft_rightUnitor, id_whiskerLeft, Iso.hom_inv_id_assoc,
                           Iso.inv_hom_id_assoc,
                           Pseudofunctor.StrongTrans.categoryStruct_id_naturality_hom,
                           Iso.cancel_iso_hom_left, Iso.cancel_iso_inv_left]
                         rw [leftUnitor_comp_inv, assoc, Iso.hom_inv_id]
                         simp } }
  hom_inv_id := by simp only [Pseudofunctor.toOplax_toPrelaxFunctor,
                     Pseudofunctor.comp_toPrelaxFunctor, Pseudofunctor.id_toPrelaxFunctor,
                     PrelaxFunctor.comp_toPrelaxFunctorStruct,
                     PrelaxFunctor.id_toPrelaxFunctorStruct, PrelaxFunctorStruct.comp_toPrefunctor,
                     PrelaxFunctorStruct.id_toPrefunctor, Prefunctor.id_comp,
                     Oplax.StrongTrans.toOplax_app, Pseudofunctor.StrongTrans.toOplax_app,
                     leftUnitorInv_app, Pseudofunctor.StrongTrans.categoryStruct_id_app]
                   ext
                   simp
  inv_hom_id := by simp only [Pseudofunctor.StrongTrans.categoryStruct_id_app,
                     Pseudofunctor.toOplax_toPrelaxFunctor, Pseudofunctor.comp_toPrelaxFunctor,
                     Pseudofunctor.id_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
                     PrelaxFunctor.id_toPrelaxFunctorStruct, PrelaxFunctorStruct.comp_toPrefunctor,
                     PrelaxFunctorStruct.id_toPrefunctor, Prefunctor.id_comp,
                     Oplax.StrongTrans.toOplax_app, Pseudofunctor.StrongTrans.toOplax_app,
                     leftUnitorInv_app]
                   ext
                   simp

def leftUnitor (F : C ⥤ᵖ B) : (Pseudofunctor.id C).comp F ≌ F := 
    Equivalence.mkOfAdjointifyCounit (leftUnitorUnit F) (leftUnitorCounit F)

@[simps]
def rightUnitorHom (F : B ⥤ᵖ C) : F.comp (Pseudofunctor.id C) ⟶ F where
  app _ := 𝟙 _ 
  naturality _ := (ρ_ _) ≪≫ (λ_ _).symm

@[simps]
def rightUnitorInv (F : B ⥤ᵖ C) : F ⟶ F.comp (Pseudofunctor.id C) where
  app _ := 𝟙 _ 
  naturality _ := (ρ_ _) ≪≫ (λ_ _).symm

@[simps]
def rightUnitorUnit (F : B ⥤ᵖ C) :
    𝟙 (F.comp (Pseudofunctor.id C)) ≅ rightUnitorHom F ≫ rightUnitorInv F where
  hom := {
    as := {
      app _ := (ρ_ _).inv
      naturality _ := by simp only [Pseudofunctor.comp_toPrelaxFunctor,
                           Pseudofunctor.id_toPrelaxFunctor,
                           PrelaxFunctor.comp_toPrelaxFunctorStruct,
                           PrelaxFunctor.id_toPrelaxFunctorStruct,
                           PrelaxFunctorStruct.comp_toPrefunctor,
                           PrelaxFunctorStruct.id_toPrefunctor, Prefunctor.comp_id,
                           Pseudofunctor.StrongTrans.categoryStruct_id_app,
                           Pseudofunctor.StrongTrans.comp_app, rightUnitorHom_app,
                           rightUnitorInv_app, whiskerLeft_rightUnitor_inv,
                           Pseudofunctor.StrongTrans.categoryStruct_comp_naturality_hom,
                           rightUnitorHom_naturality, Iso.trans_hom, Iso.symm_hom,
                           whiskerRight_id, assoc, rightUnitorInv_naturality, whiskerLeft_comp,
                           whiskerLeft_rightUnitor, id_whiskerLeft, Iso.hom_inv_id_assoc,
                           Iso.inv_hom_id_assoc,
                           Pseudofunctor.StrongTrans.categoryStruct_id_naturality_hom,
                           Iso.cancel_iso_hom_left, Iso.cancel_iso_inv_left]
                         rw [leftUnitor_comp_inv, assoc, Iso.hom_inv_id]
                         simp } }
  inv := {
    as := {
      app _ := (ρ_ _).hom } }
  hom_inv_id := by simp only [Pseudofunctor.comp_toPrelaxFunctor, Pseudofunctor.id_toPrelaxFunctor,
                     PrelaxFunctor.comp_toPrelaxFunctorStruct,
                     PrelaxFunctor.id_toPrelaxFunctorStruct, PrelaxFunctorStruct.comp_toPrefunctor,
                     PrelaxFunctorStruct.id_toPrefunctor, Prefunctor.comp_id,
                     Pseudofunctor.StrongTrans.categoryStruct_id_app,
                     Pseudofunctor.toOplax_toPrelaxFunctor, Oplax.StrongTrans.toOplax_app,
                     Pseudofunctor.StrongTrans.toOplax_app, rightUnitorHom_app]
                   ext
                   simp
  inv_hom_id := by simp only [Pseudofunctor.toOplax_toPrelaxFunctor,
                     Pseudofunctor.comp_toPrelaxFunctor, Pseudofunctor.id_toPrelaxFunctor,
                     PrelaxFunctor.comp_toPrelaxFunctorStruct,
                     PrelaxFunctor.id_toPrelaxFunctorStruct, PrelaxFunctorStruct.comp_toPrefunctor,
                     PrelaxFunctorStruct.id_toPrefunctor, Prefunctor.comp_id,
                     Oplax.StrongTrans.toOplax_app, Pseudofunctor.StrongTrans.toOplax_app,
                     rightUnitorHom_app, Pseudofunctor.StrongTrans.categoryStruct_id_app]
                   ext
                   simp

@[simps]
def rightUnitorCounit (F : B ⥤ᵖ C) : rightUnitorInv F ≫ rightUnitorHom F ≅ 𝟙 F where
  hom := {
    as := {
      app _ := (ρ_ _).hom } }
  inv := {
    as := {
      app _ := (ρ_ _).inv
      naturality _ := by simp only [Pseudofunctor.StrongTrans.categoryStruct_id_app,
                           Pseudofunctor.StrongTrans.comp_app,
                           Pseudofunctor.comp_toPrelaxFunctor, Pseudofunctor.id_toPrelaxFunctor,
                           PrelaxFunctor.comp_toPrelaxFunctorStruct,
                           PrelaxFunctor.id_toPrelaxFunctorStruct,
                           PrelaxFunctorStruct.comp_toPrefunctor,
                           PrelaxFunctorStruct.id_toPrefunctor, Prefunctor.comp_id,
                           rightUnitorInv_app, rightUnitorHom_app, whiskerLeft_rightUnitor_inv,
                           Pseudofunctor.StrongTrans.categoryStruct_comp_naturality_hom,
                           rightUnitorInv_naturality, Iso.trans_hom, Iso.symm_hom, whiskerRight_id,
                           assoc, rightUnitorHom_naturality, whiskerLeft_comp,
                           whiskerLeft_rightUnitor, id_whiskerLeft, Iso.hom_inv_id_assoc,
                           Iso.inv_hom_id_assoc,
                           Pseudofunctor.StrongTrans.categoryStruct_id_naturality_hom,
                           Iso.cancel_iso_hom_left, Iso.cancel_iso_inv_left]
                         rw [leftUnitor_comp_inv, assoc, Iso.hom_inv_id]
                         simp } }
  hom_inv_id := by simp only [Pseudofunctor.toOplax_toPrelaxFunctor,
                     Pseudofunctor.comp_toPrelaxFunctor, Pseudofunctor.id_toPrelaxFunctor,
                     PrelaxFunctor.comp_toPrelaxFunctorStruct,
                     PrelaxFunctor.id_toPrelaxFunctorStruct, PrelaxFunctorStruct.comp_toPrefunctor,
                     PrelaxFunctorStruct.id_toPrefunctor, Prefunctor.comp_id,
                     Oplax.StrongTrans.toOplax_app, Pseudofunctor.StrongTrans.toOplax_app,
                     rightUnitorInv_app, Pseudofunctor.StrongTrans.categoryStruct_id_app]
                   ext
                   simp
  inv_hom_id := by simp only [Pseudofunctor.StrongTrans.categoryStruct_id_app,
                     Pseudofunctor.toOplax_toPrelaxFunctor, Pseudofunctor.comp_toPrelaxFunctor,
                     Pseudofunctor.id_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
                     PrelaxFunctor.id_toPrelaxFunctorStruct, PrelaxFunctorStruct.comp_toPrefunctor,
                     PrelaxFunctorStruct.id_toPrefunctor, Prefunctor.comp_id,
                     Oplax.StrongTrans.toOplax_app, Pseudofunctor.StrongTrans.toOplax_app,
                     rightUnitorInv_app]
                   ext
                   simp

def rightUnitor (F : B ⥤ᵖ C) : F.comp (Pseudofunctor.id C) ≌ F :=
    Equivalence.mkOfAdjointifyCounit (rightUnitorUnit F) (rightUnitorCounit F)

@[simps]
def associatorHom (F : B ⥤ᵖ C) (G : C ⥤ᵖ D) (H : D ⥤ᵖ E) :
    (F.comp G).comp H ⟶ F.comp (G.comp H) where
  app _ := 𝟙 _
  naturality _ := {
    hom := (ρ_ _).hom ≫ (λ_ _).inv
    inv := (λ_ _).hom ≫ (ρ_ _).inv }

@[simps]
def associatorInv (F : B ⥤ᵖ C) (G : C ⥤ᵖ D) (H : D ⥤ᵖ E) :
    F.comp (G.comp H) ⟶ (F.comp G).comp H where
  app _ := 𝟙 _
  naturality _ := {
    hom := (ρ_ _).hom ≫ (λ_ _).inv
    inv := (λ_ _).hom ≫ (ρ_ _).inv }

@[simps]
def associatorUnit (F : B ⥤ᵖ C) (G : C ⥤ᵖ D) (H : D ⥤ᵖ E) :
    𝟙 ((F.comp G).comp H) ≅ associatorHom F G H ≫ associatorInv F G H where
  hom := {
    as := {
      app _ := (λ_ _).inv
      naturality _ := by simp only [Pseudofunctor.comp_toPrelaxFunctor,
                            PrelaxFunctor.comp_toPrelaxFunctorStruct,
                            PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_assoc,
                            Prefunctor.comp_obj, Prefunctor.comp_map,
                            Pseudofunctor.StrongTrans.categoryStruct_id_app,
                            Pseudofunctor.StrongTrans.comp_app, associatorHom_app,
                            associatorInv_app, unitors_inv_equal, whiskerLeft_rightUnitor_inv,
                            Pseudofunctor.StrongTrans.categoryStruct_comp_naturality_hom,
                            associatorHom_naturality_hom, whiskerRight_id, assoc,
                            associatorInv_naturality_hom, whiskerLeft_comp, whiskerLeft_rightUnitor,
                            id_whiskerLeft, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
                            Pseudofunctor.StrongTrans.categoryStruct_id_naturality_hom,
                            Iso.cancel_iso_hom_left, Iso.cancel_iso_inv_left]
                         rw [leftUnitor_comp_inv, assoc, Iso.hom_inv_id]
                         simp } }
  inv := {
    as := {
      app _ := (λ_ _).hom } }
  hom_inv_id := by simp only [Pseudofunctor.comp_toPrelaxFunctor,
                     PrelaxFunctor.comp_toPrelaxFunctorStruct,
                     PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_assoc,
                     Prefunctor.comp_obj, Pseudofunctor.StrongTrans.categoryStruct_id_app,
                     unitors_inv_equal, Pseudofunctor.toOplax_toPrelaxFunctor,
                     Oplax.StrongTrans.toOplax_app, Pseudofunctor.StrongTrans.toOplax_app,
                     associatorInv_app, unitors_equal]
                   ext
                   simp
  inv_hom_id := by simp only [Pseudofunctor.toOplax_toPrelaxFunctor,
                     Pseudofunctor.comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
                     PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_assoc,
                     Prefunctor.comp_obj, Oplax.StrongTrans.toOplax_app,
                     Pseudofunctor.StrongTrans.toOplax_app, associatorInv_app, unitors_equal,
                     Pseudofunctor.StrongTrans.categoryStruct_id_app, unitors_inv_equal]
                   ext
                   simp

@[simps]
def associatorCounit (F : B ⥤ᵖ C) (G : C ⥤ᵖ D) (H : D ⥤ᵖ E) :
    associatorInv F G H ≫ associatorHom F G H ≅ 𝟙 (F.comp (G.comp H)) where
  hom := {
    as := {
      app _ := (ρ_ _).hom } }
  inv := {
    as := {
      app _ := (ρ_ _).inv
      naturality _ := by simp only [Pseudofunctor.comp_toPrelaxFunctor,
                           PrelaxFunctor.comp_toPrelaxFunctorStruct,
                           PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj,
                           Prefunctor.comp_map, Pseudofunctor.StrongTrans.categoryStruct_id_app,
                           Pseudofunctor.StrongTrans.comp_app, Prefunctor.comp_assoc,
                           associatorInv_app, associatorHom_app, whiskerLeft_rightUnitor_inv,
                           Pseudofunctor.StrongTrans.categoryStruct_comp_naturality_hom,
                           associatorInv_naturality_hom, whiskerRight_id, assoc,
                           associatorHom_naturality_hom, whiskerLeft_comp, whiskerLeft_rightUnitor,
                           id_whiskerLeft, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
                           Pseudofunctor.StrongTrans.categoryStruct_id_naturality_hom,
                           Iso.cancel_iso_hom_left, Iso.cancel_iso_inv_left]
                         rw [leftUnitor_comp_inv, assoc, Iso.hom_inv_id]
                         simp } }
  hom_inv_id := by simp only [Pseudofunctor.toOplax_toPrelaxFunctor,
                     Pseudofunctor.comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
                     PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj,
                     Prefunctor.comp_assoc, Oplax.StrongTrans.toOplax_app,
                     Pseudofunctor.StrongTrans.toOplax_app, associatorInv_app,
                     Pseudofunctor.StrongTrans.categoryStruct_id_app]
                   ext
                   simp
  inv_hom_id := by simp only [Pseudofunctor.comp_toPrelaxFunctor,
                     PrelaxFunctor.comp_toPrelaxFunctorStruct,
                     PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj,
                     Pseudofunctor.StrongTrans.categoryStruct_id_app,
                     Pseudofunctor.toOplax_toPrelaxFunctor, Prefunctor.comp_assoc,
                     Oplax.StrongTrans.toOplax_app, Pseudofunctor.StrongTrans.toOplax_app,
                     associatorInv_app]
                   ext
                   simp

def associator (F : B ⥤ᵖ C) (G : C ⥤ᵖ D) (H : D ⥤ᵖ E) :
    (F.comp G).comp H ≌ F.comp (G.comp H) :=
  Equivalence.mkOfAdjointifyCounit (associatorUnit F G H) (associatorCounit F G H)

scoped infixr:81 " ◁ₚ " => Bicat.whiskerLeft
scoped infixl:81 " ▷ₚ " => Bicat.whiskerRight
scoped notation "α_ₚ" => Bicat.associator
scoped notation "λ_ₚ" => Bicat.leftUnitor
scoped notation "ρ_ₚ" => Bicat.rightUnitor

end Bicat
