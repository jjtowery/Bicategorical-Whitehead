/-
Copyright (c) 2026 Judah Towery. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judah Towery
-/

import «Bicategorical Whitehead».LaxTerminal
import «Bicategorical Whitehead».OplaxComma
import «Bicategorical Whitehead».Bicat

/-!
# Biequivalences of bicategories.

Defines biequivalences as half-biadjoint biequivalences.

Provides `Biequivalence.mkofAdjointifyCounit` that strictifies pseudoinverse data into a
`Biequivalence`.

Defines essentially surjective, essentially full, and fully faithful lax functors.

Proves the bicategorical whitehead theorem: A pseudofunctor is a biequivalence if and only if it is
essentially surjective, essentially full, and fully faithful.
-/

namespace CategoryTheory.Bicategory

open Category Bicategory Bicat

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄

open scoped Pseudofunctor.StrongTrans

variable {B C D E : Type*} [Bicategory.{w₁, v₁} B] [Bicategory.{w₂, v₂} C] [Bicategory.{w₃, v₃} D]
[Bicategory.{w₄, v₄} E]

/-- Symmetry of equivalence. Should go to existing API. -/
def Equivalence.symm {a b : B} (e : a ≌ b) : b ≌ a :=
  Equivalence.mkOfAdjointifyCounit e.counit.symm e.unit.symm

/-- Transitivity of equivalence. Should go to existing API. -/
def Equivalence.trans {a b c : B} (e₁ : a ≌ b) (e₂ : b ≌ c) : a ≌ c := 
  Equivalence.mkOfAdjointifyCounit (e₁.unit ≪≫ whiskerRightIso (ρ_ _).symm _ ≪≫ whiskerRightIso
  (whiskerLeftIso _ e₂.unit) _ ≪≫ whiskerRightIso (α_ _ _ _).symm _ ≪≫ α_ _ _ _)
  (α_ _ _ _ ≪≫ whiskerLeftIso _ (α_ _ _ _).symm ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso
  (whiskerLeftIso _ e₁.counit) _ ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso _ (λ_ _) ≪≫ e₂.counit)

namespace Biequivalence

@[simp]
def leftZigzag {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) :=
  postWhisker η.hom F ≫ associatorHom F G F ≫ preWhisker F ε.hom

end Biequivalence

/-- Biequivalence defined as a half-biadjoint biequivalence. 
A pseudofunctor `F : B ⥤ᵖ C` is a biequivalence if there is a pseudofunctor `G : C ⥤ᵖ B`
with internal equivalences `𝟙 B ≌ GF` and `FG ≌ 𝟙 C` in their respective pseudofunctor bicategories.

The internal equivalence `FG ≌ 𝟙 C` entails the following data:
Strong transformations `ε : FG ⟶ 𝟙 C` and `ε' : 𝟙 C ⟶ FG`;
Invertible modifications `Γ : 𝟙 (𝟙 C) ≅ εε'` and `Γ' : ε'ε ≅ 𝟙 (FG)`.

The internal equivalence `𝟙 B ≌ GF` entails the following data:
Strong transformations `η : 𝟙 B ⟶ GF` and `η' : GF ⟶ 𝟙 B`;
Invertible modifications `θ : 𝟙 (𝟙 B) ≅ η'η` and `θ' : ηη' ≅ 𝟙 (GF)`. 

`Biequivalence.mkOfAdjointifyCounit` allows one to construct a `Biequivalence` from just this
pseudo-inverse data. -/
@[ext]
structure Biequivalence (B C : Type*) [Bicategory.{w₁, v₁} B] [Bicategory.{w₂, v₂} C] where
  hom : B ⥤ᵖ C
  inv : C ⥤ᵖ B
  unit : Pseudofunctor.id B ≌ hom.comp inv
  counit : inv.comp hom ≌ Pseudofunctor.id C
  left_triangle : Biequivalence.leftZigzag unit counit ≅ (λₚ_ hom).hom ≫ (ρₚ_ hom).inv

namespace Biequivalence

/- Some definitions and lemmas for the strictification result. -/

def leftZigzagIso {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) := (η ▷ₚ F).trans ((αₚ_ F G F).trans (F ◁ₚ ε))

@[simp]
theorem leftZigzagIso_hom {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) : (leftZigzagIso η ε).hom = leftZigzag η ε := rfl

def rightZigzagIso {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) := (G ◁ₚ η).trans (((αₚ_ G F G).symm).trans (ε ▷ₚ G))

@[simp]
def leftZigzagIso_symm_hom {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) : (rightZigzagIso ε.symm η.symm).hom ≅
    (leftZigzagIso η ε).inv := (α_ _ _ _).symm

/- Move these to Bicat.lean later. -/
@[simp]
def whiskerLeft_trans_hom (H : B ⥤ᵖ C) {F G K : C ⥤ᵖ D} (e₁ : F ≌ G) (e₂ : G ≌ K) :
    (H ◁ₚ (e₁.trans e₂)).hom ≅ (H ◁ₚ e₁).hom ≫ (H ◁ₚ e₂).hom := eqToIso rfl

@[simp]
def associator_naturality_right_hom (F : B ⥤ᵖ C) (G : C ⥤ᵖ D) {H K : D ⥤ᵖ E} (χ : H ≌ K) :
    (αₚ_ F G H).hom ≫ (F ◁ₚ (G ◁ₚ χ)).hom ≅ ((F.comp G) ◁ₚ χ).hom ≫ (αₚ_ F G K).hom where
  hom := {
    as := {
      app _ := (λ_ _).hom ≫ (ρ_ _).inv } }
  inv := {
    as := {
      app _ := (ρ_ _).hom ≫ (λ_ _).inv } }
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

@[simp]
def whisker_exchange_hom_hom {F G : B ⥤ᵖ C} {H K : C ⥤ᵖ D} (η : F ≌ G) (χ : H ≌ K) :
    (η ▷ₚ H).hom ≫ (G ◁ₚ χ).hom ⟶ (F ◁ₚ χ).hom ≫ (η ▷ₚ K).hom where
  as := {
    app _ := (χ.hom.naturality (η.hom.app _)).hom
    naturality f := by
      simp only [Pseudofunctor.comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
      PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj, Prefunctor.comp_map,
      whiskerRight_hom, whiskerLeft_hom, Pseudofunctor.StrongTrans.comp_app, postWhisker_app,
      preWhisker_app, Pseudofunctor.StrongTrans.categoryStruct_comp_naturality_hom,
      preWhisker_naturality, postWhisker_naturality_hom, whiskerLeft_comp, assoc, comp_whiskerRight]
      have := congrArg (fun f => f ≫ (α_ _ _ _).inv) (χ.hom.naturality_comp (η.hom.app _) (G.map f))
      simp only [Iso.hom_inv_id, assoc, comp_id] at this
      rw [←this, ←assoc (H.map₂ _ ▷ _), χ.hom.naturality_naturality (η.hom.naturality _).hom, assoc]
      have := congrArg (fun g => (α_ _ _ _).inv ≫ (H.mapComp _ _).inv ▷ _ ≫ g ≫
        _ ◁ (K.mapComp _ _).inv ≫ _ ◁ K.map₂ (η.hom.naturality _).hom ≫ _ ◁ (K.mapComp _ _).hom ≫
        (α_ _ _ _).inv) (χ.hom.naturality_comp (F.map f) (η.hom.app _))
      simp only [assoc, inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc] at this
      rw [←assoc (χ.hom.app _ ◁  _), whiskerLeft_hom_inv, id_comp] at this
      rw [this] }

@[simp]
def whisker_exchange_hom {F G : B ⥤ᵖ C} {H K : C ⥤ᵖ D} (η : F ≌ G) (χ : H ≌ K) :
    (η ▷ₚ H).hom ≫ (G ◁ₚ χ).hom ≅ (F ◁ₚ χ).hom ≫ (η ▷ₚ K).hom where
  hom := whisker_exchange_hom_hom η χ
  inv := {
    as := {
      app _ := (χ.hom.naturality (η.hom.app _)).inv
      naturality {a b} f := by
        simp only [Pseudofunctor.comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
          PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj, Prefunctor.comp_map,
          whiskerLeft_hom, whiskerRight_hom, Pseudofunctor.StrongTrans.comp_app, preWhisker_app,
          postWhisker_app, Pseudofunctor.StrongTrans.categoryStruct_comp_naturality_hom,
          postWhisker_naturality_hom, comp_whiskerRight, preWhisker_naturality, assoc,
          whiskerLeft_comp]
        have h := congrArg (fun g => _ ◁ (χ.hom.naturality _).inv ≫ g ≫
          (χ.hom.naturality _).inv ▷ K.map _) ((whisker_exchange_hom_hom η χ).as.naturality f)
        have : (whisker_exchange_hom_hom η χ).as.app a = (χ.hom.naturality _).hom := rfl
        simp only [Pseudofunctor.comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
          PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj, Prefunctor.comp_map,
          whiskerRight_hom, whiskerLeft_hom, Pseudofunctor.StrongTrans.comp_app, postWhisker_app,
          preWhisker_app, Pseudofunctor.StrongTrans.categoryStruct_comp_naturality_hom,
          preWhisker_naturality, postWhisker_naturality_hom, whiskerLeft_comp, assoc,
          comp_whiskerRight, this, hom_inv_whiskerRight, comp_id] at h
        have : (whisker_exchange_hom_hom η χ).as.app b = (χ.hom.naturality _).hom := rfl
        rw [←h, ←assoc (_ ◁ (χ.hom.naturality _).inv), ←whiskerLeft_comp, this]
        simp } }
  hom_inv_id := by ext; simp 
  inv_hom_id := by ext; simp

@[simp]
theorem leftUnitor_hom_app (F : B ⥤ᵖ C) (a : B) : (λₚ_ F).hom.app a = 𝟙 (F.obj a) := rfl

@[simp]
theorem leftUnitor_hom_naturality_hom (F : B ⥤ᵖ C) {a b : B} (f : a ⟶ b) :
    ((λₚ_ F).hom.naturality f).hom = (ρ_ (F.map f)).hom ≫ (λ_ (F.map f)).inv := rfl

@[simp]
def leftUnitor_naturality_hom {F : B ⥤ᵖ C} (χ : F ≌ F) :
    (Pseudofunctor.id B ◁ₚ χ).hom ≫ (λₚ_ F).hom ≅ (λₚ_ F).hom ≫ χ.hom where
  hom := {
    as := {
      app _ := (ρ_ _).hom ≫ (λ_ _).inv } }
  inv := {
    as := {
      app _ := (λ_ _).hom ≫ (ρ_ _).inv } }
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

@[simp]
def leftUnitor_conj_hom {F : B ⥤ᵖ C} (χ : F ≌ F) :
    (Pseudofunctor.id B ◁ₚ χ).hom ≅ (((λₚ_ F).hom ≫ χ.hom) ≫ (λₚ_ F).inv) :=
  (ρ_ (Pseudofunctor.id B ◁ₚ χ).hom).symm ≪≫ whiskerLeftIso _ (λₚ_ F).unit ≪≫ (α_ _ _ _).symm ≪≫
  whiskerRightIso (leftUnitor_naturality_hom χ) _

def leftZigzagIso_whiskerLeft_trans_hom {F : B ⥤ᵖ C} {G : C ⥤ᵖ B}
    (η : Pseudofunctor.id B ≌ F.comp G) (ε : G.comp F ≌ Pseudofunctor.id C) (χ : F ≌ F) :
    (leftZigzagIso η ((G ◁ₚ χ).trans ε)).hom ≅
    (((λₚ_ F).hom ≫ χ.hom) ≫ (λₚ_ F).inv) ≫ (leftZigzagIso η ε).hom :=
  eqToIso (by simp [leftZigzag]) ≪≫
  whiskerLeftIso _ (whiskerLeftIso _ (whiskerLeft_trans_hom _ _ _)) ≪≫
  whiskerLeftIso _ ((α_ _ _ _).symm ≪≫ whiskerRightIso (associator_naturality_right_hom _ _ _) _ ≪≫
  (α_ _ _ _)) ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso (whisker_exchange_hom _ _ ≪≫
  whiskerRightIso (leftUnitor_conj_hom _) (_ ▷ₚ _).hom ) _ ≪≫ (α_ _ _ _)
  
def adjointifyCounit_correction_hom {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) :
    (((ρₚ_ F).symm).trans ((rightZigzagIso ε.symm η.symm).trans (λₚ_ F))).hom ≅
    (((ρₚ_ F).symm).trans (((leftZigzagIso η ε).symm).trans (λₚ_ F))).hom := by
  simpa using whiskerLeftIso _ (whiskerRightIso (leftZigzagIso_symm_hom _ _) _)

/-- Creates a biequivalence from pseudo-inverse data. -/
def mkOfAdjointifyCounit {hom : B ⥤ᵖ C} {inv : C ⥤ᵖ B} (unit : Pseudofunctor.id B ≌ hom.comp inv) 
    (counit : inv.comp hom ≌ Pseudofunctor.id C) : Biequivalence B C where
  hom := hom
  inv := inv
  unit := unit
  counit := (_ ◁ₚ (((ρₚ_ _).symm).trans ((rightZigzagIso _ _).trans (λₚ_ _)))).trans _
  left_triangle := (eqToIso (leftZigzagIso_hom _ ((_ ◁ₚ _).trans _))).symm ≪≫
    (by simpa using leftZigzagIso_whiskerLeft_trans_hom _ _ _) ≪≫
    (whiskerRightIso (whiskerRightIso (whiskerLeftIso _ 
    (adjointifyCounit_correction_hom unit counit)) _) _) ≪≫ whiskerRightIso (α_ _ _ _) _ ≪≫
    whiskerRightIso (whiskerLeftIso _ (α_ _ _ _)) _ ≪≫
    whiskerRightIso (whiskerLeftIso _ (whiskerLeftIso _ (α_ _ _ _))) _ ≪≫
    whiskerRightIso (whiskerLeftIso _ (whiskerLeftIso _ (whiskerLeftIso _ (λₚ_ _).unit.symm))) _ ≪≫
    whiskerRightIso (whiskerLeftIso _ (whiskerLeftIso _ (ρ_ _))) _ ≪≫ (α_ _ _ _) ≪≫
    whiskerLeftIso _ (α_ _ _ _) ≪≫ whiskerLeftIso _ (whiskerLeftIso _ (leftZigzagIso _ _).counit) ≪≫
    whiskerLeftIso _ (ρ_ _)

/-- Reflexivity of biequivalence. -/
def refl : Biequivalence B B := mkOfAdjointifyCounit (λₚ_ _).symm (λₚ_ _)

/-- Symmetry of biequivalence. -/
def symm (e : Biequivalence B C) : Biequivalence C B := mkOfAdjointifyCounit
  (Equivalence.mkOfAdjointifyCounit e.counit.counit.symm e.counit.unit.symm)
  (Equivalence.mkOfAdjointifyCounit e.unit.counit.symm e.unit.unit.symm)

/-- Transitivity of biequivalence. -/
def trans (e₁ : Biequivalence B C) (e₂ : Biequivalence C D) : Biequivalence B D :=
  mkOfAdjointifyCounit
  (e₁.unit.trans ((_ ◁ₚ (λₚ_ _).symm).trans ((_ ◁ₚ (e₂.unit ▷ₚ _)).trans ((_ ◁ₚ (αₚ_ _ _ _)).trans
  (αₚ_ _ _ _).symm))))
  (((αₚ_ _ _ _).trans ((_ ◁ₚ (αₚ_ _ _ _).symm).trans ((_ ◁ₚ (e₁.counit ▷ₚ _)).trans
  (_ ◁ₚ (λₚ_ _))))).trans e₂.counit)

end Biequivalence
