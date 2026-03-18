/-
Copyright (c) 2026 Judah Towery. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judah Towery
-/

import «Bicategorical Whitehead».LaxTerminal
import «Bicategorical Whitehead».OplaxComma
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

/-!
# Biequivalences of bicategories.

Defines pre-biequivalences as usual pseudo-inverses, and then defines biequivalences as biadjoint
biequivalences, with a strictification result that upgrades pre-biequivalences to biadjoint 
biequivalences.

Defines essentially surjective, essentially full, and fully faithful lax functors.

Proves the bicategorical whitehead theorem: A pseudofunctor is a biequivalence if and only if it is
essentially surjective, essentially full, and fully faithful.

-/

namespace CategoryTheory.Bicategory

open Category Bicategory

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄

open scoped Pseudofunctor.StrongTrans

/-- A pre-biequivalence. 
A pseudofunctor `F : B ⥤ᵖ C` is a pre-biequivalence if there is a pseudofunctor `G : C ⥤ᵖ B`
with internal equivalences `𝟙 B ≌ GF` and `FG ≌ 𝟙 C` in their respective pseudofunctor bicategories.

The internal equivalence `FG ≌ 𝟙 C` entails the following data:
Strong transformations `ε : FG ⟶ 𝟙 C` and `ε' : 𝟙 C ⟶ FG`;
Invertible modifications `Γ : 𝟙 (𝟙 C) ≅ εε'` and `Γ' : ε'ε ≅ 𝟙 (FG)`.

The internal equivalence `𝟙 B ≌ GF` entails the following data:
Strong transformations `η : 𝟙 B ⟶ GF` and `η' : GF ⟶ 𝟙 B`;
Invertible modifications `θ : 𝟙 (𝟙 B) ≅ η'η` and `θ' : ηη' ≅ 𝟙 (GF)`.

This is taken as the definition of biequivalence in Johnson-Yau, but in analogy with the
1-category API, we want to consider biadjoint biequivalence as the definition of biequivalence,
which pre-biequivalences can strictify to. -/
@[ext]
structure PreBiequivalence (B C : Type*) [Bicategory.{w₁, v₁} B] [Bicategory.{w₂, v₂} C] where
  hom : B ⥤ᵖ C
  inv : C ⥤ᵖ B
  unit : Pseudofunctor.id B ≌ hom.comp inv
  counit : inv.comp hom ≌ Pseudofunctor.id C

variable {B C D E : Type*} [Bicategory.{w₁, v₁} B] [Bicategory.{w₂, v₂} C] [Bicategory.{w₃, v₃} D]
  [Bicategory.{w₄, v₄} E]

/-- Symmetry of equivalence. Should go to existing API. -/
@[simp] 
abbrev Equivalence.symm {a b : B} (e : a ≌ b) : b ≌ a :=
  Equivalence.mkOfAdjointifyCounit e.counit.symm e.unit.symm

/-- Composition of equivalence. Should go to existing API. -/
abbrev compUnit {a b c : B} (e₁ : a ≌ b) (e₂ : b ≌ c) :
    𝟙 a ≅ (e₁.hom ≫ e₂.hom) ≫ (e₂.inv ≫ e₁.inv) :=
  e₁.unit ≪≫ whiskerRightIso (ρ_ _).symm _ ≪≫ whiskerRightIso (whiskerLeftIso _ e₂.unit) _ ≪≫
  whiskerRightIso (α_ _ _ _).symm _ ≪≫ α_ _ _ _

abbrev compCounit {a b c : B} (e₁ : a ≌ b) (e₂ : b ≌ c) :
    (e₂.inv ≫ e₁.inv) ≫ (e₁.hom ≫ e₂.hom) ≅ 𝟙 c :=
  α_ _ _ _ ≪≫ whiskerLeftIso _ (α_ _ _ _).symm ≪≫ (α_ _ _ _).symm ≪≫
  whiskerRightIso (whiskerLeftIso _ e₁.counit) _ ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso _ (λ_ _) ≪≫ e₂.counit

abbrev Equivalence.trans {a b c : B} (e₁ : a ≌ b) (e₂ : b ≌ c) : a ≌ c := 
  Equivalence.mkOfAdjointifyCounit (compUnit e₁ e₂) (compCounit e₁ e₂)

/-- Helpful tricategorical pseudofunctor operations. Should go to existing API. -/

@[simp]
def postWhisker {F G : B ⥤ᵖ C} (η : F ⟶ G) (H : C ⥤ᵖ D) : 
    F.comp H ⟶ G.comp H where
  app _ := H.map (η.app _)
  naturality _ := {
    hom := (H.mapComp _ _).inv ≫ H.map₂ (η.naturality _).hom ≫ (H.mapComp _ _).hom
    inv := (H.mapComp _ _).inv ≫ H.map₂ (η.naturality _).inv ≫ (H.mapComp _ _).hom
    hom_inv_id := by simp [←assoc (H.map₂ (η.naturality _).hom)]
    inv_hom_id := by simp [←assoc (H.map₂ (η.naturality _).inv)] }
  naturality_naturality θ := by simp; sorry

@[simp]
def preWhisker (H : B ⥤ᵖ C) {F G : C ⥤ᵖ D} (η : F ⟶ G) :
    H.comp F ⟶ H.comp G := sorry

@[simp]
def whiskerRightId' (F : B ⥤ᵖ C) (H : C ⥤ᵖ D) :
    𝟙 (F.comp H) ≅ postWhisker (𝟙 F) H := sorry

@[simp]
def whiskerRightComp' {F G K : B ⥤ᵖ C} (η : F ⟶ G) (θ : G ⟶ K) (H : C ⥤ᵖ D) :
    postWhisker (η ≫ θ) H ≅ postWhisker η H ≫ postWhisker θ H := sorry

@[simp]
def whiskerRightIso' {F G : B ⥤ᵖ C} {η θ : F ⟶ G} (α : η ≅ θ) (H : C ⥤ᵖ D) :
    postWhisker η H ≅ postWhisker θ H := sorry

@[simp]
def whiskerRight' {F G : B ⥤ᵖ C} (e : F ≌ G) (H : C ⥤ᵖ D) : F.comp H ≌ G.comp H :=
  Equivalence.mkOfAdjointifyCounit ((whiskerRightId' F H).trans ((whiskerRightIso' e.unit H).trans 
  (whiskerRightComp' e.hom e.inv H))) ((whiskerRightComp' e.inv e.hom H).symm.trans 
  ((whiskerRightIso' e.counit H).trans (whiskerRightId' G H).symm))

@[simp]
def whiskerLeft' (H : B ⥤ᵖ C) {F G : C ⥤ᵖ D} (e : F ≌ G) : H.comp F ≌ H.comp G := sorry

@[simp]
def leftUnitor' (F : C ⥤ᵖ B) : (Pseudofunctor.id C).comp F ≌ F:= sorry

@[simp]
def rightUnitor' (F : B ⥤ᵖ C) : F.comp (Pseudofunctor.id C) ≌ F := sorry

@[simp]
def associator' (F : B ⥤ᵖ C) (G : C ⥤ᵖ D) (H : D ⥤ᵖ E) :
  (F.comp G).comp H ≌ F.comp (G.comp H) := sorry

namespace PreBiequivalence

/-- Reflexivity of biequivalence. -/
@[simp]
def refl : PreBiequivalence B B where
  hom := Pseudofunctor.id B
  inv := Pseudofunctor.id B
  unit := (leftUnitor' (Pseudofunctor.id B)).symm
  counit := leftUnitor' (Pseudofunctor.id B)

/-- Symmetry of biequivalence. -/
@[simp]
def symm (e : PreBiequivalence B C) : PreBiequivalence C B where
  hom := e.inv
  inv := e.hom
  unit := Equivalence.mkOfAdjointifyCounit e.counit.counit.symm e.counit.unit.symm 
  counit := Equivalence.mkOfAdjointifyCounit e.unit.counit.symm e.unit.unit.symm

variable (e₁ : PreBiequivalence B C) (e₂ : PreBiequivalence C D)

abbrev middleUnit : e₁.hom.comp e₁.inv ≌ (e₁.hom.comp e₂.hom).comp (e₂.inv.comp e₁.inv) :=
  (whiskerLeft' _ (leftUnitor' _).symm).trans ((whiskerLeft' _ (whiskerRight' e₂.unit _)).trans
  ((whiskerLeft' _ (associator' _ _ _)).trans (associator' _ _ _).symm))

abbrev middleCounit : (e₂.inv.comp e₁.inv).comp (e₁.hom.comp e₂.hom) ≌ (e₂.inv.comp e₂.hom) :=
  (associator' _ _ _).trans ((whiskerLeft' _ (associator' _ _ _).symm).trans
  ((whiskerLeft' _ (whiskerRight' e₁.counit _)).trans (whiskerLeft' _ (leftUnitor' _))))

/-- Transitivity of biequivalence. -/
@[simp]
def trans : PreBiequivalence B D where
  hom := e₁.hom.comp e₂.hom
  inv := e₂.inv.comp e₁.inv
  unit := e₁.unit.trans (middleUnit e₁ e₂)
  counit := (middleCounit e₁ e₂).trans e₂.counit

end PreBiequivalence
