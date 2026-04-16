import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

namespace CategoryTheory.Bicategory

open Category Bicategory

universe w₁ w₂ v₁ v₂

open scoped Pseudofunctor.StrongTrans

structure PreBiequivalence (B C : Type*) [Bicategory.{w₁, v₁} B] [Bicategory.{w₂, v₂} C] where
  hom : B ⥤ᵖ C
  inv : C ⥤ᵖ B
  unit : Pseudofunctor.id B ≌ hom.comp inv
  counit : inv.comp hom ≌ Pseudofunctor.id C

variable {B C : Type*} [Bicategory.{w₁, v₁} B] [Bicategory.{w₂, v₂} C]

def refl : PreBiequivalence B B where
  hom := Pseudofunctor.id B
  inv := Pseudofunctor.id B
  unit := {
    hom := {
      app _ := 𝟙 _
      naturality _ := {
        hom := (ρ_ _).hom ≫ (λ_ _).inv
        inv := (λ_ _).hom ≫ (ρ_ _).inv } }
    inv := {
      app _ := 𝟙 _
      naturality _ := {
        hom := (ρ_ _).hom ≫ (λ_ _).inv
        inv := (λ_ _).hom ≫ (ρ_ _).inv } }
    unit := {
      hom := {
        as := {
          app _ := (λ_ _).inv
          naturality _ := by simp [←leftUnitor_inv_whiskerRight] } }
      inv := {
        as := {
          app x := (λ_ (𝟙 x)).hom
          naturality f := by simp only [Pseudofunctor.id_toPrelaxFunctor, PrelaxFunctor.id_toPrelaxFunctorStruct,
    PrelaxFunctorStruct.id_toPrefunctor, Prefunctor.id_obj, Prefunctor.id_map,
    Pseudofunctor.StrongTrans.categoryStruct_id_app, Pseudofunctor.comp_toPrelaxFunctor,
    PrelaxFunctor.comp_toPrelaxFunctorStruct, PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_id,
    Pseudofunctor.StrongTrans.comp_app, unitors_inv_equal,
    Pseudofunctor.StrongTrans.categoryStruct_comp_naturality_hom, whiskerRight_id, assoc, whiskerLeft_comp,
   id_whiskerLeft, Iso.hom_inv_id_assoc, ←leftUnitor_inv_whiskerRight, Iso.inv_hom_id_assoc,
    Pseudofunctor.StrongTrans.categoryStruct_id_naturality_hom, whiskerLeft_rightUnitor] 
                             rw [←assoc ((α_ f _ _).inv), ←whiskerLeft_rightUnitor, unitors_equal, ←comp_whiskerRight, unitors_equal, Iso.inv_hom_id, id_whiskerRight] 
                             nth_rewrite 2 [←assoc (f ◁ (ρ_ (𝟙 _)).hom)]
                             rw [←assoc ((f ◁ (ρ_ (𝟙 _)).hom ≫ (ρ_ f).hom)), assoc (f ◁ (ρ_ (𝟙 _)).hom)]
                             have := comp_id (f ◁ (ρ_ (𝟙 _)).hom ≫ (ρ_ f).hom ≫ (λ_ f).inv)
        }
      }
    }
  }

