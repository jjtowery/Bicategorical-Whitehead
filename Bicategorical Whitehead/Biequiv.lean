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

universe w₁ w₂ w₃ v₁ v₂ v₃

open scoped Pseudofunctor.StrongTrans

variable {B C D : Type*} [Bicategory.{w₁, v₁} B] [Bicategory.{w₂, v₂} C] [Bicategory.{w₃, v₃} D]

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

def leftZigzag {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) :=
  postWhisker η.hom F ≫ associatorHom F G F ≫ preWhisker F ε.hom

def rightZigzag {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) :=
  preWhisker G η.hom ≫ associatorInv G F G ≫ postWhisker ε.hom G

end Biequivalence

/-- Biequivalence defined as half-biadjoint biequivalence. 
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
  left_triangle : Biequivalence.leftZigzag unit counit ≅ (λ_ₚ hom).hom ≫ (ρ_ₚ hom).inv

namespace Biequivalence

/- Some definitions and lemmas for the strictification result.
All of this should go to existing API/another file. -/

@[simp]
theorem Equivalence.trans_assoc {a b c d : B} (e₁ : a ≌ b) (e₂ : b ≌ c) (e₃ : c ≌ d) :
    (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) := by sorry

@[simp]
theorem Equivalence.trans_id {a b : B} (e : a ≌ b) : e.trans (Equivalence.id b) = e := by sorry

@[simp]
theorem Equivalence.id_trans {a b : B} (e : a ≌ b) : (Equivalence.id a).trans e = e := by sorry

@[simp]
theorem Equivalence.trans_symm {a b : B} (e : a ≌ b) : e.trans e.symm = Equivalence.id a := by sorry

@[simp]
theorem Equivalence.symm_trans {a b : B} (e : a ≌ b) : e.symm.trans e = Equivalence.id b := by sorry

@[simp]
theorem Equivalence.symm_hom {a b : B} (e : a ≌ b) : e.symm.hom = e.inv := rfl

@[simp]
theorem Equivalence.symm_inv {a b : B} (e : a ≌ b) : e.symm.inv = e.hom := rfl

@[simp]
theorem Equivalence.trans_hom {a b c : B} (e₁ : a ≌ b) (e₂ : b ≌ c) : (e₁.trans e₂).hom =
    e₁.hom ≫ e₂.hom := rfl

@[simp]
theorem Equivalence.trans_inv {a b c : B} (e₁ : a ≌ b) (e₂ : b ≌ c) : (e₁.trans e₂).inv =
    e₂.inv ≫ e₁.inv := rfl
/-
@[simp]
theorem whiskerLeft_leftUnitor (H : B ⥤ᵖ C) (F : C ⥤ᵖ D) : whiskerLeft H (leftUnitor F) =
    (associator H (Pseudofunctor.id C) F).symm.trans (whiskerRight (rightUnitor H) F) := by sorry

@[simp]
theorem whiskerRight_rightUnitor (F : B ⥤ᵖ C) (H : C ⥤ᵖ D) : whiskerRight (rightUnitor F) H =
    (associator F (Pseudofunctor.id C) H).trans (whiskerLeft F (leftUnitor H)) := by sorry

@[simp]
theorem whiskerLeft_symm (H : B ⥤ᵖ C) {F G : C ⥤ᵖ D} (e : F ≌ G) : whiskerLeft H e.symm =
    (whiskerLeft H e).symm := by sorry

@[simp]
theorem whiskerRight_symm {F G : B ⥤ᵖ C} (e : F ≌ G) (H : C ⥤ᵖ D) : whiskerRight e.symm H =
    (whiskerRight e H).symm := by sorry

@[simp]
theorem whiskerLeft_trans (H : B ⥤ᵖ C) {F G K : C ⥤ᵖ D} (e₁ : F ≌ G) (e₂ : G ≌ K) :
    whiskerLeft H (e₁.trans e₂) = (whiskerLeft H e₁).trans (whiskerLeft H e₂) := by sorry

@[simp]
theorem whiskerRight_trans {F G K : B ⥤ᵖ C} (e₁ : F ≌ G) (e₂ : G ≌ K) (H : C ⥤ᵖ D) :
    whiskerRight (e₁.trans e₂) H = (whiskerRight e₁ H).trans (whiskerRight e₂ H) := by sorry -/

def leftZigzagIso {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) := (η ▷ₚ F).trans ((α_ₚ F G F).trans (F ◁ₚ ε))

def rightZigzagIso {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) := (G ◁ₚ η).trans (((α_ₚ G F G).symm).trans (ε ▷ₚ G))

@[simp]
theorem leftZigzagIso_symm {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) : rightZigzagIso ε.symm η.symm = (leftZigzagIso η ε).symm :=
  by sorry

@[simp]
theorem leftZigzagIso_whiskerLeft_trans {F : B ⥤ᵖ C} {G : C ⥤ᵖ B}
    (η : Pseudofunctor.id B ≌ F.comp G) (ε : G.comp F ≌ Pseudofunctor.id C) (χ : F ≌ F) :
    leftZigzagIso η ((G ◁ₚ χ).trans ε) = (leftZigzagIso η ε).trans (χ ▷ₚ (Pseudofunctor.id C)) := by
  sorry

@[simp]
theorem whiskerRight_id {F : B ⥤ᵖ C} (χ : F ≌ F) : Bicat.whiskerRight χ (Pseudofunctor.id C) =
    (ρ_ₚ F).trans (χ.trans (ρ_ₚ F).symm) := by sorry

@[simp]
def adjointifyCounit {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) := (G ◁ₚ (((ρ_ₚ F).symm).trans
    ((rightZigzagIso ε.symm η.symm).trans (λ_ₚ F)))).trans ε

@[simp]
theorem adjointifyCounit_left_triangle_hom {F : B ⥤ᵖ C} {G : C ⥤ᵖ B}
    (η : Pseudofunctor.id B ≌ F.comp G) (ε : G.comp F ≌ Pseudofunctor.id C) :
    (leftZigzagIso η (adjointifyCounit η ε)).hom = (λ_ₚ F).hom ≫ (ρ_ₚ F).inv := by
  let χ := ((ρ_ₚ F).symm).trans (((leftZigzagIso η ε).symm).trans (λ_ₚ F))
  have h : χ = ((ρ_ₚ F).symm).trans (((leftZigzagIso η ε).symm).trans (λ_ₚ F)) := by simp [χ]
  have : (leftZigzagIso η ε).trans ((ρ_ₚ F).trans (χ.trans (ρ_ₚ F).symm)) =
    (λ_ₚ F).trans (ρ_ₚ F).symm := by simp [h, ←Equivalence.trans_assoc]
  simp [←h, this]

/-- Creates a biequivalence from pseudo-inverse data. -/
def mkOfAdjointifyCounit (hom : B ⥤ᵖ C) (inv : C ⥤ᵖ B) (unit : Pseudofunctor.id B ≌ hom.comp inv) 
    (counit : inv.comp hom ≌ Pseudofunctor.id C) : Biequivalence B C where
  hom := hom
  inv := inv
  unit := unit
  counit := adjointifyCounit unit counit
  left_triangle := eqToIso (adjointifyCounit_left_triangle_hom unit counit)

/-- Reflexivity of biequivalence. -/
def refl : Biequivalence B B := mkOfAdjointifyCounit (Pseudofunctor.id B) (Pseudofunctor.id B)
  (λ_ₚ (Pseudofunctor.id B)).symm (λ_ₚ (Pseudofunctor.id B))

/-- Symmetry of biequivalence. -/
def symm (e : Biequivalence B C) : Biequivalence C B := mkOfAdjointifyCounit (e.inv) (e.hom)
  (Equivalence.mkOfAdjointifyCounit e.counit.counit.symm e.counit.unit.symm)
  (Equivalence.mkOfAdjointifyCounit e.unit.counit.symm e.unit.unit.symm)

/-- Transitivity of biequivalence. -/
def trans (e₁ : Biequivalence B C) (e₂ : Biequivalence C D) : Biequivalence B D :=
  mkOfAdjointifyCounit (e₁.hom.comp e₂.hom) (e₂.inv.comp e₁.inv)
  (e₁.unit.trans ((_ ◁ₚ (λ_ₚ _).symm).trans ((_ ◁ₚ (e₂.unit ▷ₚ _)).trans ((_ ◁ₚ (α_ₚ _ _ _)).trans 
  (α_ₚ _ _ _).symm)))) (((α_ₚ _ _ _).trans ((_ ◁ₚ (α_ₚ _ _ _).symm).trans
  ((_ ◁ₚ (e₁.counit ▷ₚ _)).trans (_ ◁ₚ (λ_ₚ _))))).trans e₂.counit)

end Biequivalence
