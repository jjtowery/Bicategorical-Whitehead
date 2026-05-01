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
  left_triangle : Biequivalence.leftZigzag unit counit ≅ (λₚ_ hom).hom ≫ (ρₚ_ hom).inv

namespace Biequivalence

/- Some definitions and lemmas for the strictification result.
All of this should go to existing API/another file. -/
/-
@[simp]
theorem Equivalence.symm_hom {a b : B} (e : a ≌ b) : e.symm.hom = e.inv := rfl

@[simp]
theorem Equivalence.symm_inv {a b : B} (e : a ≌ b) : e.symm.inv = e.hom := rfl

@[simp]
theorem Equivalence.trans_hom {a b c : B} (e₁ : a ≌ b) (e₂ : b ≌ c) : (e₁.trans e₂).hom =
    e₁.hom ≫ e₂.hom := rfl

@[simp]
theorem Equivalence.trans_inv {a b c : B} (e₁ : a ≌ b) (e₂ : b ≌ c) : (e₁.trans e₂).inv =
    e₂.inv ≫ e₁.inv := rfl -/
/-
@[simp]
theorem Equivalence.trans_assoc {a b c d : B} (e₁ : a ≌ b) (e₂ : b ≌ c) (e₃ : c ≌ d) :
    (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) := sorry

@[simp]
theorem Equivalence.trans_id {a b : B} (e : a ≌ b) : e.trans (Equivalence.id b) = e := by sorry

@[simp]
theorem Equivalence.id_trans {a b : B} (e : a ≌ b) : (Equivalence.id a).trans e = e := by sorry

@[simp]
theorem Equivalence.trans_symm {a b : B} (e : a ≌ b) : e.trans e.symm = Equivalence.id a := by sorry

@[simp]
theorem Equivalence.symm_trans {a b : B} (e : a ≌ b) : e.symm.trans e = Equivalence.id b := by sorry -/

/-
@[simp]
theorem whiskerLeft_leftUnitor (H : B ⥤ᵖ C) (F : C ⥤ᵖ D) : whiskerLeft H (leftUnitor F) =
    (associator H (Pseudofunctor.id C) F).symm.trans (whiskerRight (rightUnitor H) F) := by sorry

@[simp]
theorem whiskerRight_rightUnitor (F : B ⥤ᵖ C) (H : C ⥤ᵖ D) : whiskerRight (rightUnitor F) H =
    (associator F (Pseudofunctor.id C) H).trans (whiskerLeft F (leftUnitor H)) := by sorry
-/
/- 
@[simp]
theorem whiskerLeft_symm (H : B ⥤ᵖ C) {F G : C ⥤ᵖ D} (e : F ≌ G) : H ◁ₚ e.symm =
    (H ◁ₚ e).symm := by
  sorry

@[simp]
theorem whiskerRight_symm {F G : B ⥤ᵖ C} (e : F ≌ G) (H : C ⥤ᵖ D) : e.symm ▷ₚ H =
    (e ▷ₚ H).symm := by
  sorry -/
/-
@[simp]
theorem whiskerLeft_trans (H : B ⥤ᵖ C) {F G K : C ⥤ᵖ D} (e₁ : F ≌ G) (e₂ : G ≌ K) :
    whiskerLeft H (e₁.trans e₂) = (whiskerLeft H e₁).trans (whiskerLeft H e₂) := by sorry

@[simp]
theorem whiskerRight_trans {F G K : B ⥤ᵖ C} (e₁ : F ≌ G) (e₂ : G ≌ K) (H : C ⥤ᵖ D) :
    whiskerRight (e₁.trans e₂) H = (whiskerRight e₁ H).trans (whiskerRight e₂ H) := by sorry -/

def leftZigzagIso {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) := (η ▷ₚ F).trans ((αₚ_ F G F).trans (F ◁ₚ ε))

@[simp]
theorem leftZigzagIso_hom {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) : (leftZigzagIso η ε).hom = leftZigzag η ε := rfl

def rightZigzagIso {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) := (G ◁ₚ η).trans (((αₚ_ G F G).symm).trans (ε ▷ₚ G))
/-
@[simp]
theorem rightZigzagIso_hom {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) : (rightZigzagIso η ε).hom = rightZigzag η ε := rfl-/

def leftZigzagIso_symm_hom {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) : (rightZigzagIso ε.symm η.symm).hom ≅
    (leftZigzagIso η ε).inv := (α_ _ _ _).symm
/- 
def leftZigzagIso_symm_inv {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) : (rightZigzagIso ε.symm η.symm).inv ≅
    (leftZigzagIso η ε).hom := α_ _ _ _ -/

def leftZigzag_congr_counit_hom {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} {η : Pseudofunctor.id B ≌ F.comp G}
    {ε₁ ε₂ : G.comp F ≌ Pseudofunctor.id C} (h : ε₁.hom ≅ ε₂.hom) : leftZigzag η ε₁ ≅
    leftZigzag η ε₂ := (α_ _ _ _).symm ≪≫
  whiskerLeftIso (postWhisker η.hom F ≫ associatorHom F G F) (Bicat.whiskerLeftIso F h) ≪≫ α_ _ _ _

def leftZigzagIso_whiskerLeft_trans_hom {F : B ⥤ᵖ C} {G : C ⥤ᵖ B}
    (η : Pseudofunctor.id B ≌ F.comp G) (ε : G.comp F ≌ Pseudofunctor.id C) (χ : F ≌ F) :
    (leftZigzagIso η ((G ◁ₚ χ).trans ε)).hom ≅ (leftZigzagIso η ε).hom ≫ (χ ▷ₚ Pseudofunctor.id C).hom := sorry

@[simp]
theorem rightUnitor_hom_app (F : B ⥤ᵖ C) (a : B) : (ρₚ_ F).hom.app a = 𝟙 (F.obj a) := rfl

@[simp]
theorem rightUnitor_hom_naturality_hom (F : B ⥤ᵖ C) {a b : B} (f : a ⟶ b) :
    ((ρₚ_ F).hom.naturality f).hom = (ρ_ (F.map f)).hom ≫ (λ_ (F.map f)).inv := rfl

def rightUnitor_naturality_hom {F : B ⥤ᵖ C} (χ : F ≌ F) : (χ ▷ₚ Pseudofunctor.id C).hom ≫
    (ρₚ_ F).hom ≅ (ρₚ_ F).hom ≫ χ.hom where
  hom := {
    as := {
      app _ := (ρ_ _).hom ≫ (λ_ _).inv } }
  inv := {
    as := {
      app _ := (λ_ _).hom ≫ (ρ_ _).inv } }
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

def whiskerRight_id_hom {F : B ⥤ᵖ C} (χ : F ≌ F) : (χ ▷ₚ Pseudofunctor.id C).hom ≅
    (ρₚ_ F).hom ≫ (χ.hom ≫ (ρₚ_ F).inv) := (ρ_ _).symm ≪≫ whiskerLeftIso _ (ρₚ_ _).unit ≪≫
  (α_ _ _ _).symm ≪≫ whiskerRightIso (rightUnitor_naturality_hom _) _ ≪≫ (α_ _ _ _)

def adjointifyCounit {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) := (_ ◁ₚ (((ρₚ_ _).symm).trans
  ((rightZigzagIso ε.symm η.symm).trans (λₚ_ _)))).trans ε

def adjointifyCounit_correction_hom {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) : (((ρₚ_ F).symm).trans
    ((rightZigzagIso ε.symm η.symm).trans (λₚ_ F))).hom ≅ (((ρₚ_ F).symm).trans
    (((leftZigzagIso η ε).symm).trans (λₚ_ F))).hom := by
  simpa using whiskerLeftIso _ (whiskerRightIso (leftZigzagIso_symm_hom _ _) _)

def adjointifyCounit_counit_hom {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) : (((G ◁ₚ (((ρₚ_ F).symm).trans
    ((rightZigzagIso ε.symm η.symm).trans (λₚ_ F)))).trans ε).hom) ≅ (((G ◁ₚ (((ρₚ_ F).symm).trans
    (((leftZigzagIso η ε).symm).trans (λₚ_ F)))).trans ε).hom) := by
 simpa using whiskerRightIso (Bicat.whiskerLeftIso _ (adjointifyCounit_correction_hom _ _)) _

def adjointifyCounit_replace {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (η : Pseudofunctor.id B ≌ F.comp G)
    (ε : G.comp F ≌ Pseudofunctor.id C) : leftZigzag η (adjointifyCounit η ε) ≅ leftZigzag η
    ((G ◁ₚ (((ρₚ_ F).symm).trans (((leftZigzagIso η ε).symm).trans (λₚ_ F)))).trans ε) := by
  simpa using leftZigzag_congr_counit_hom (η := η) (adjointifyCounit_counit_hom _ _)

def adjointifyCounit_left_triangle_expand {F : B ⥤ᵖ C} {G : C ⥤ᵖ B}
    (η : Pseudofunctor.id B ≌ F.comp G) (ε : G.comp F ≌ Pseudofunctor.id C) :
    leftZigzag η ((G ◁ₚ ((ρₚ_ F).symm.trans (((leftZigzagIso η ε).symm).trans (λₚ_ F)))).trans ε) ≅
    (leftZigzagIso η ε).hom ≫ (ρₚ_ F).hom ≫ (((ρₚ_ F).inv ≫ (leftZigzagIso η ε).inv ≫ (λₚ_ F).hom) ≫
    (ρₚ_ F).inv) := by
  calc
   _ ≅ (leftZigzagIso η (((_ ◁ₚ ((ρₚ_ _).symm.trans
       ((leftZigzagIso η ε).symm.trans (λₚ_ _))))).trans ε)).hom := eqToIso (by simp)
   _ ≅ (leftZigzagIso η ε).hom ≫ (((ρₚ_ _).symm.trans
       ((leftZigzagIso η ε).symm.trans (λₚ_ _))) ▷ₚ _).hom := by
     simpa using leftZigzagIso_whiskerLeft_trans_hom _ _ _  
   _ ≅ (leftZigzagIso η ε).hom ≫ ((ρₚ_ _).hom ≫ (((ρₚ_ F).symm.trans
       ((leftZigzagIso η ε).symm.trans (λₚ_ _)))).hom ≫ (ρₚ_ _).inv) := whiskerLeftIso _
     (whiskerRight_id_hom ((ρₚ_ _).symm.trans ((leftZigzagIso η ε).symm.trans (λₚ_ _))))
   _ ≅ _  := by
     have : ((ρₚ_ _).symm.trans ((leftZigzagIso η ε).symm.trans (λₚ_ _))).hom =
         (ρₚ_ _).inv ≫ ((leftZigzagIso η ε).inv ≫ (λₚ_ _).hom) := by rfl
     exact whiskerLeftIso _ (whiskerLeftIso _ (whiskerRightIso (eqToIso this) _))

/-- Creates a biequivalence from pseudo-inverse data. -/
def mkOfAdjointifyCounit (hom : B ⥤ᵖ C) (inv : C ⥤ᵖ B) (unit : Pseudofunctor.id B ≌ hom.comp inv) 
    (counit : inv.comp hom ≌ Pseudofunctor.id C) : Biequivalence B C where
  hom := hom
  inv := inv
  unit := unit
  counit := adjointifyCounit unit counit
  left_triangle := adjointifyCounit_replace _ _ ≪≫ adjointifyCounit_left_triangle_expand _ _ ≪≫
    whiskerLeftIso _ ((α_ _ _ _).symm) ≪≫ whiskerLeftIso _ (whiskerRightIso ((α_ _ _ _).symm) _) ≪≫
    whiskerLeftIso _ (whiskerRightIso (whiskerRightIso (ρₚ_ _).unit.symm _) _) ≪≫
    whiskerLeftIso _ (whiskerRightIso (λ_ _) _) ≪≫ (α_ _ _ _).symm ≪≫
    whiskerRightIso ((α_ _  _ _).symm) _ ≪≫
    whiskerRightIso (whiskerRightIso (leftZigzagIso _ _).unit.symm _) _ ≪≫ whiskerRightIso (λ_ _) _

/-- Reflexivity of biequivalence. -/
def refl : Biequivalence B B := mkOfAdjointifyCounit (Pseudofunctor.id B) (Pseudofunctor.id B)
  (λₚ_ (Pseudofunctor.id B)).symm (λₚ_ (Pseudofunctor.id B))

/-- Symmetry of biequivalence. -/
def symm (e : Biequivalence B C) : Biequivalence C B := mkOfAdjointifyCounit (e.inv) (e.hom)
  (Equivalence.mkOfAdjointifyCounit e.counit.counit.symm e.counit.unit.symm)
  (Equivalence.mkOfAdjointifyCounit e.unit.counit.symm e.unit.unit.symm)

/-- Transitivity of biequivalence. -/
def trans (e₁ : Biequivalence B C) (e₂ : Biequivalence C D) : Biequivalence B D :=
  mkOfAdjointifyCounit (e₁.hom.comp e₂.hom) (e₂.inv.comp e₁.inv)
  (e₁.unit.trans ((_ ◁ₚ (λₚ_ _).symm).trans ((_ ◁ₚ (e₂.unit ▷ₚ _)).trans ((_ ◁ₚ (αₚ_ _ _ _)).trans 
  (αₚ_ _ _ _).symm)))) (((αₚ_ _ _ _).trans ((_ ◁ₚ (αₚ_ _ _ _).symm).trans
  ((_ ◁ₚ (e₁.counit ▷ₚ _)).trans (_ ◁ₚ (λₚ_ _))))).trans e₂.counit)

end Biequivalence
