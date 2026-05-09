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
  mkOfAdjointifyCounit e.counit.symm e.unit.symm

/-- Transitivity of equivalence. Should go to existing API. -/
def Equivalence.trans {a b c : B} (e₁ : a ≌ b) (e₂ : b ≌ c) : a ≌ c := 
  mkOfAdjointifyCounit 
  (e₁.unit ≪≫ whiskerRightIso (ρ_ _).symm _ ≪≫ whiskerRightIso
  (whiskerLeftIso _ e₂.unit) _ ≪≫ whiskerRightIso (α_ _ _ _).symm _ ≪≫ α_ _ _ _)
  (α_ _ _ _ ≪≫ whiskerLeftIso _ (α_ _ _ _).symm ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso
  (whiskerLeftIso _ e₁.counit) _ ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso _ (λ_ _) ≪≫ e₂.counit)

/-- Application of an equivalence to an object. -/
def Equivalence.app {F G : B ⥤ᵖ C} (e : F ≌ G) (b : B) : F.obj b ≌ G.obj b :=
  mkOfAdjointifyCounit
    { hom := _
      inv := _
      hom_inv_id := by
        have := congrArg (fun m => m.as.app b) e.unit.hom_inv_id
        simp only [Pseudofunctor.StrongTrans.categoryStruct_id_app,
        Pseudofunctor.StrongTrans.homCategory_id_as_app,
        Pseudofunctor.StrongTrans.homCategory_comp_as_app] at this
        exact this
      inv_hom_id := by
        have := congrArg (fun m => m.as.app b) e.unit.inv_hom_id
        simp only [Pseudofunctor.StrongTrans.categoryStruct_id_app,
        Pseudofunctor.StrongTrans.homCategory_id_as_app,
        Pseudofunctor.StrongTrans.homCategory_comp_as_app] at this
        exact this }
    { hom := _
      inv := _
      hom_inv_id := by
        have := congrArg (fun m => m.as.app b) e.counit.hom_inv_id
        simp only [Pseudofunctor.StrongTrans.categoryStruct_id_app,
        Pseudofunctor.StrongTrans.homCategory_id_as_app,
        Pseudofunctor.StrongTrans.homCategory_comp_as_app] at this
        exact this
      inv_hom_id := by
        have := congrArg (fun m => m.as.app b) e.counit.inv_hom_id
        simp only [Pseudofunctor.StrongTrans.categoryStruct_id_app,
        Pseudofunctor.StrongTrans.homCategory_id_as_app,
        Pseudofunctor.StrongTrans.homCategory_comp_as_app] at this
        exact this }

@[simp]
theorem Equivalence.app_hom {F G : B ⥤ᵖ C} (e : F ≌ G) (b : B) : (e.app b).hom = e.hom.app b := rfl

@[simp]
theorem Equivalence.app_inv {F G : B ⥤ᵖ C} (e : F ≌ G) (b : B) : (e.app b).inv = e.inv.app b := rfl

/- These results are for constructing the induced equivalence in Example 6.2.7/Lemma 6.2.12 in
Johnson-Yau. -/

/-- Left whiskering by an equivalence is an equivalence on 2-cells. -/
@[simp]
def Equivalence.whiskerLeftEquiv {a b c : B} (e : a ≌ b) (f g : b ⟶ c) :
    (f ⟶ g) ≃ (e.hom ≫ f ⟶ e.hom ≫ g) where
  toFun _ := _
  invFun β := _ ≫ _ ▷ _ ≫ _ ≫ _ ◁ β ≫ _ ≫ _ ▷ _ ≫ _
  left_inv α := by
    have : ((λ_ _).symm ≪≫ whiskerRightIso e.counit.symm _ ≪≫ α_ _ _ _).hom ≫ _ ◁ (_◁ α) =
        α ≫ ((λ_ _).symm ≪≫ whiskerRightIso e.counit.symm _ ≪≫ α_ _ _ _).hom := by
      calc
       _ = (λ_ _).inv ≫ e.counit.inv ▷ _ ≫ (_ ◁ α) ≫ (α_ _ _ _).hom := by simp
       _ = (λ_ _).inv ≫ _ ≫ _ ≫ _ := by rw [whisker_exchange_assoc]
       _ = _ := by simp
    have := congrArg (fun t => t ≫ ((λ_ _).symm ≪≫ whiskerRightIso e.counit.symm _ ≪≫ α_ _ _ _).inv)
      this
    simpa
  right_inv β := by
    have h₁ (h : b ⟶ c) : _ ◁ ((λ_ _).symm ≪≫ whiskerRightIso e.counit.symm _ ≪≫ α_ _ _ _).hom =
        ((λ_ _).symm ≪≫ whiskerRightIso e.unit _ ≪≫ α_ _ _ (_ ≫ h)).hom := by
      have := congrArg (fun t => (ρ_ _).inv ▷ _ ≫ (whiskerRightIso t _).inv ≫ e.unit.hom ▷ _ ▷ _ ≫
          (α_ _ _ _).hom ≫ (α_ _ _ (_ ≫ h)).hom) e.left_triangle
      simp only [bicategoricalIsoComp, BicategoricalCoherence.assoc_iso,
        BicategoricalCoherence.whiskerRight_iso, BicategoricalCoherence.refl_iso, Iso.trans_assoc,
        whiskerRightIso_inv, Iso.trans_inv, whiskerLeftIso_inv, Iso.refl_inv, whiskerRight_comp,
        id_whiskerRight, id_comp, Iso.inv_hom_id, comp_id, assoc, comp_whiskerRight, whisker_assoc,
        inv_hom_whiskerRight_whiskerRight_assoc, pentagon_inv_hom_hom_hom_hom, Iso.inv_hom_id_assoc,
        triangle_assoc_comp_right_inv_assoc, Iso.symm_inv, leftUnitor_inv_whiskerRight,
        inv_hom_whiskerRight_assoc] at this
      simpa
    have h₂ (h : b ⟶ c) : _ ◁ ((λ_ _).symm ≪≫ whiskerRightIso e.counit.symm _ ≪≫ α_ _ _ _).inv =
        ((λ_ _).symm ≪≫ whiskerRightIso e.unit _ ≪≫ α_ _ _ (_ ≫ h)).inv := by
      have : whiskerLeftIso _ ((λ_ _).symm ≪≫ whiskerRightIso e.counit.symm _ ≪≫ α_ _ _ _) =
          (λ_ _).symm ≪≫ whiskerRightIso e.unit _ ≪≫ α_ e.hom e.inv (_ ≫ h) := by
        ext
        simpa using h₁ h
      simpa using congrArg (fun t => t.inv) this
    simp only [whiskerLeft_comp]
    simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, whiskerLeft_comp,
      whiskerRight_comp, assoc] at h₁
    simp only [Iso.trans_inv, whiskerRightIso_inv, Iso.symm_inv, assoc, whiskerLeft_comp,
      whiskerRight_comp] at h₂
    simp only [h₁ f, h₂ g, ←assoc]
    have : ((λ_ _).symm ≪≫ whiskerRightIso e.unit _ ≪≫ α_ _ _ _).hom ≫ _ ◁ (_ ◁ β) =
        β ≫ ((λ_ _).symm ≪≫ whiskerRightIso e.unit _ ≪≫ α_ _ _ (_ ≫ g)).hom := by
      calc
       _ = (λ_ _).inv ≫ e.unit.hom ▷  _ ≫ ((_ ≫ _) ◁ β) ≫ (α_ _ _ _).hom := by simp
       _ = (λ_ _).inv ≫ (_ ◁ _) ≫ _ ▷ _ ≫ (α_ _ _ _).hom := by rw [whisker_exchange_assoc]
       _ = _ := by simp
    have := congrArg (fun t => t ≫ ((λ_ _).symm ≪≫ whiskerRightIso e.unit _ ≪≫ α_ _ _ _).inv) this
    simpa

/-- Right whiskering by an equivalence is an equivalence on 2-cells. -/
@[simp]
def Equivalence.whiskerRightEquiv {a b c : B} (e : b ≌ c) (f g : a ⟶ b) :
    (f ⟶ g) ≃ (f ≫ e.hom ⟶ g ≫ e.hom) where
  toFun _ := _
  invFun β := _ ≫ _ ≫ _ ≫ β ▷_ ≫ _ ≫ _ ≫ _
  left_inv α := by
    have : ((ρ_ _).symm ≪≫ whiskerLeftIso _ e.unit ≪≫ (α_ _ _ _).symm).hom ≫ ((α ▷ _) ▷ _) =
        α ≫ ((ρ_ _).symm ≪≫ whiskerLeftIso _ e.unit ≪≫ (α_ _ _ _).symm).hom := by
      calc
       _ = (ρ_ _).inv ≫ _ ◁ e.unit.hom ≫ α ▷ _ ≫ (α_ _ _ _).inv := by simp
       _ = (ρ_ _).inv ≫ α ▷ _ ≫ _ ◁ e.unit.hom ≫ (α_ _ _ _).inv := by rw [whisker_exchange_assoc]
       _ = _ := by simp
    simpa using
      congrArg (fun t => t ≫ ((ρ_ _).symm ≪≫ whiskerLeftIso _ e.unit ≪≫ (α_ _ _ _).symm).inv) this
  right_inv β := by
    have h₁ (h : a ⟶ b) : ((ρ_ h).symm ≪≫ whiskerLeftIso h e.unit ≪≫ (α_ _ _ _).symm).hom ▷ _ =
      (α_ _ _ _ ≪≫ whiskerLeftIso _ e.counit ≪≫ ρ_ _).inv := by
      have hiso (i : a ⟶ b) : whiskerRightIso ((ρ_ _).symm ≪≫ whiskerLeftIso _ e.unit ≪≫
        (α_ _ _ _).symm) _ ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso _ e.counit ≪≫ ρ_ _ = Iso.refl (i ≫ _) := by
        have := congrArg (fun t => whiskerLeftIso i t) e.left_triangle
        simp only [bicategoricalIsoComp, BicategoricalCoherence.assoc_iso,
          BicategoricalCoherence.whiskerRight_iso, BicategoricalCoherence.refl_iso,
          Iso.trans_assoc] at this
        calc
         _ = whiskerRightIso (ρ_ _).symm _ ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso _
           (whiskerRightIso e.unit _ ≪≫ α_ _ _ _ ≪≫ whiskerRightIso (Iso.refl e.hom) _ ≪≫
         whiskerLeftIso _ e.counit) ≪≫ (α_ _ _ _).symm ≪≫ ρ_ _ := by ext; simp
         _ = whiskerRightIso (ρ_ _).symm e.hom ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso _ (λ_ e.hom ≪≫
           (ρ_ e.hom).symm) ≪≫ (α_ _ _ _).symm ≪≫ ρ_ _ := by rw [this]
         _ = _ := by ext; simp
      have := congrArg Iso.hom (hiso h)
      calc
       _ = ((whiskerRightIso ((ρ_ _).symm ≪≫ whiskerLeftIso _ e.unit ≪≫ (α_ _ _ _).symm) _).hom ≫
         (α_ _ _ _ ≪≫ whiskerLeftIso _ e.counit ≪≫ ρ_ _).hom ≫ (α_ _ _ _ ≪≫
         whiskerLeftIso _ e.counit ≪≫ ρ_ _).inv) := by simp
       _ = _ := by simpa using congrArg (fun t => t ≫ (α_ (h ≫ e.hom) e.inv e.hom ≪≫
         whiskerLeftIso (h ≫ e.hom) e.counit ≪≫ ρ_ (h ≫ e.hom)).inv) this
    have h₂ (h : a ⟶ b) : ((ρ_ _).symm ≪≫ whiskerLeftIso _ e.unit ≪≫ (α_ _ _ _).symm).inv ▷ _ =
      (α_ _ _ _ ≪≫ whiskerLeftIso _ e.counit ≪≫ ρ_ (h ≫ _)).hom := by
      have : whiskerRightIso ((ρ_ _).symm ≪≫ whiskerLeftIso _ e.unit ≪≫ (α_ _ _ _).symm) _ =
        (α_ _ _ _ ≪≫ whiskerLeftIso _ e.counit ≪≫ ρ_ (h ≫ _)).symm := by ext; simpa using h₁ h
      have := congrArg (fun t => t.inv) this
      simpa
    have : ((β ▷ _) ▷ _) ≫ (α_ _ _ _ ≪≫ whiskerLeftIso _ e.counit ≪≫ ρ_ _).hom =
      (α_ _ _ _ ≪≫ whiskerLeftIso _ e.counit ≪≫ ρ_ _).hom ≫ β := by
      calc
       _ = (α_ _ _ _).hom ≫ β ▷ _ ≫ _ ◁ e.counit.hom ≫ (ρ_ _).hom := by simp
       _ = (α_ _ _ _).hom ≫ _ ◁ e.counit.hom ≫ β ▷ _ ≫ (ρ_ _).hom := by rw [whisker_exchange_assoc]
       _ = _ := by simp
    simp only [comp_whiskerRight, whisker_assoc, assoc, triangle_assoc_comp_right,
      triangle_assoc_comp_right_inv_assoc]
    simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, comp_whiskerRight, whisker_assoc,
      assoc, triangle_assoc_comp_right_inv_assoc, Iso.trans_inv, whiskerLeftIso_inv,
      comp_whiskerLeft] at h₁
    simp only [Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv, assoc, comp_whiskerRight,
      whisker_assoc, triangle_assoc_comp_right, Iso.trans_hom, whiskerLeftIso_hom,
      comp_whiskerLeft] at h₂
    rw [h₂ g, ←assoc (_ ◁ _), ←assoc (_ ≫ _), ←assoc ((_ ≫ (α_ _ _ _).inv)), assoc (_ ≫ _ ◁ _ ▷ _),
      assoc (_ ◁ _), h₁ f]
    have := congrArg (fun t => (α_ _ _ _ ≪≫ whiskerLeftIso _ e.counit ≪≫ ρ_ _).inv ≫ t) this
    simpa

@[simp]
def Equivalence.conjEquiv {a b : B} {f₁ f₂ g₁ g₂ : a ⟶ b} (i₁ : f₁ ≅ f₂) (i₂ : g₁ ≅ g₂) :
    (f₁ ⟶ g₁) ≃ (f₂ ⟶ g₂) where
  toFun α := i₁.inv ≫ α ≫ i₂.hom
  invFun β := i₁.hom ≫ β ≫ i₂.inv
  left_inv α := by simp
  right_inv β := by simp

/-- The equivalence `C(FX, FY) ⟶ C(GX, GY)` induced by an adjoint equivalence. -/
@[simp]
def Equivalence.map₂EquivOfEquiv {F G : B ⥤ᵖ C} (e : F ≌ G) {a b : B} (f g : a ⟶ b) :
    (F.map f ⟶ F.map g) ≃ (G.map f ⟶ G.map g) :=
  (whiskerRightEquiv (app e b) _ _).trans
  ((conjEquiv (e.hom.naturality _) (e.hom.naturality _)).trans
  (whiskerLeftEquiv (app e a) _ _).symm)

@[simp]
theorem Equivalence.map₂EquivOfEquiv_apply {F G : B ⥤ᵖ C} (e : F ≌ G) {a b : B} {f g : a ⟶ b}
    (α : f ⟶ g) : e.map₂EquivOfEquiv f g (F.map₂ α) = G.map₂ α := by
  have : ((e.hom.naturality _).inv ≫ F.map₂ α ▷ (e.app _).hom) ≫ (e.hom.naturality _).hom =
    _ ◁ G.map₂ α := by simp
  simp only [map₂EquivOfEquiv, whiskerRightEquiv, conjEquiv, whiskerLeftEquiv, Equiv.trans_apply,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, whiskerLeft_comp, assoc]
  rw [←assoc (_ ◁ _), ←whiskerLeft_comp, ←assoc (_ ◁ _), ←whiskerLeft_comp, this]
  simpa using (whiskerLeftEquiv (e.app _) _ _).left_inv _

@[simp]
def Equivalence.cancelLeftWhiskerIso {a b c : B} (e : a ≌ b) {f g : b ⟶ c}
    (i : e.hom ≫ f ≅ e.hom ≫ g) : f ≅ g where
  hom := (whiskerLeftEquiv e f g).symm i.hom
  inv := (whiskerLeftEquiv e g f).symm i.inv

@[simp]
def Equivalence.cancelRightWhiskerIso {a b c : B} (e : b ≌ c) {f g : a ⟶ b}
    (i : f ≫ e.hom ≅ g ≫ e.hom) : f ≅ g where
  hom := (whiskerRightEquiv e f g).symm i.hom
  inv := (whiskerRightEquiv e g f).symm i.inv

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

/-- A lax functor is essentially surjective if it is surjective on adjoint equivalence classes of
objects. Equivalently, every object of the target is equivalent to an object in the image. -/
@[simp]
def EssentiallySurjective (F : B ⥤ᴸ C) := ∀ c : C, ∃ b : B, Nonempty (F.obj b ≌ c)

namespace EssentiallySurjective

/-- One direction of the bicategorical Whitehead theorem: a biequivalence is essentially
surjective. -/
@[simp]
theorem hom (e : Biequivalence B C) : EssentiallySurjective e.hom.toLax := by
  intro c
  refine ⟨e.inv.obj c, ⟨?_⟩⟩
  simpa using Equivalence.app e.counit c

@[simp]
theorem inv (e : Biequivalence B C) : EssentiallySurjective e.inv.toLax := by
  intro b
  refine ⟨e.hom.obj b, ⟨?_⟩⟩
  simpa using (Equivalence.app e.unit b).symm

end EssentiallySurjective

/-- A lax functor is fully faithful if it is a bijection on 2-cells. -/
@[simp]
def FullyFaithful (F : B ⥤ᴸ C) :=
  ∀ {a b : B} (f g : a ⟶ b), Function.Bijective (fun η : f ⟶ g => F.map₂ η)

namespace FullyFaithful

@[simp]
theorem id (B : Type*) [Bicategory B] :
    FullyFaithful (LaxFunctor.id B) := fun _ _ => Function.bijective_id

@[simp]
theorem of_equiv {F G : B ⥤ᵖ C} (e : F ≌ G) (hF : FullyFaithful F.toLax) :
    FullyFaithful G.toLax := by
  intro _ _ f g
  have : (fun t : f ⟶ g => G.map₂ t) =
      (fun t : f ⟶ g => (e.map₂EquivOfEquiv _ _).toFun (F.map₂ t)) := by
    funext
    exact (Equivalence.map₂EquivOfEquiv_apply _ _).symm
  simp only [Pseudofunctor.toLax_toPrelaxFunctor]
  rw [this]
  exact (e.map₂EquivOfEquiv _ _).bijective.comp (by simpa using hF _ _)

@[simp]
theorem of_comp {F : B ⥤ᵖ C} {G : C ⥤ᵖ B} (hGF : FullyFaithful (F.comp G).toLax)
    (hFG : FullyFaithful (G.comp F).toLax) : FullyFaithful F.toLax := by
  intro _ _ f g
  constructor
  · intro _ _ h
    apply (hGF f g).1
    simpa using congrArg (fun t => G.map₂ t) h
  · intro _
    have : Function.Injective (fun τ : F.map f ⟶ F.map g => G.map₂ τ) := by
      intro _ _ hτ
      apply (hFG (F.map f) (F.map g)).1
      simpa using congrArg (fun t => F.map₂ t) hτ
    obtain ⟨α, hα⟩ := (hGF f g).2 (G.map₂ _)
    refine ⟨α, ?_⟩
    apply this
    simpa

/-- One direction of the bicategorical Whitehead theorem: a biequivalence is fully faithful. -/
@[simp]
theorem hom (e : Biequivalence B C) : FullyFaithful e.hom.toLax :=
  of_comp (of_equiv e.unit (id B)) (of_equiv e.counit.symm (id C))

@[simp]
theorem inv (e : Biequivalence B C) : FullyFaithful e.inv.toLax :=
  of_comp (of_equiv e.counit.symm (id C)) (of_equiv e.unit (id B))

@[simp]
theorem nonempty_iso_of_map_iso {F : B ⥤ᵖ C} (hF : FullyFaithful F.toLax) {a b : B} {f g : a ⟶ b}
    (i : F.map f ≅ F.map g) : Nonempty (f ≅ g) := by
  obtain ⟨α, hα⟩ := (hF f g).2 i.hom
  obtain ⟨β, hβ⟩ := (hF g f).2 i.inv
  simp only [Pseudofunctor.toLax_toPrelaxFunctor] at hα
  simp only [Pseudofunctor.toLax_toPrelaxFunctor] at hβ
  refine ⟨ 
    { hom := α
      inv := β
      hom_inv_id := ?_
      inv_hom_id := ?_ }⟩
  · apply (hF f f).1
    simp only [Pseudofunctor.toLax_toPrelaxFunctor, PrelaxFunctor.map₂_comp, PrelaxFunctor.map₂_id]
    rw [hα, hβ, i.hom_inv_id]
  · apply (hF g g).1
    simp only [Pseudofunctor.toLax_toPrelaxFunctor, PrelaxFunctor.map₂_comp, PrelaxFunctor.map₂_id]
    rw [hα, hβ, i.inv_hom_id]

end FullyFaithful

/-- A lax functor is essentially full if it is surjective on isomorphism classes of 1-cells.
Equivalently, every 1-cell between objects in the image is isomorphic to the image of a 1-cell. -/
@[simp]
def EssentiallyFull (F : B ⥤ᴸ C) :=
  ∀ {a b: B} (f : F.obj a ⟶ F.obj b), ∃ g : a ⟶ b, Nonempty (F.map g ≅ f)

namespace EssentiallyFull

/-- One direction of the bicategorical Whitehead theorem: a biequivalence is essentially full. -/
@[simp]
theorem hom (e : Biequivalence B C) : EssentiallyFull e.hom.toLax := by
  intro _ _ h
  exact ⟨(e.unit.app _).hom ≫ e.inv.map h ≫ (e.unit.app _).inv,
    FullyFaithful.nonempty_iso_of_map_iso (FullyFaithful.inv _)
    (Equivalence.cancelLeftWhiskerIso _ ((α_ _ _ _ ≪≫ whiskerLeftIso _ (e.unit.app _).counit ≪≫
    ρ_ ((e.unit.app _).hom ≫ _)).symm ≪≫ whiskerRightIso (α_ _ _ _) _ ≪≫ α_ _ _ _ ≪≫
    whiskerLeftIso _ (α_ _ _ _) ≪≫ whiskerLeftIso _ (α_ _ _ _).symm ≪≫ (α_ _ _ _).symm ≪≫
    (e.unit.hom.naturality _))).symm⟩

@[simp]
theorem inv (e : Biequivalence B C) : EssentiallyFull e.inv.toLax := by
  intro _ _ h
  exact ⟨(e.counit.app _).inv ≫ e.hom.map h ≫ (e.counit.app _).hom,
    FullyFaithful.nonempty_iso_of_map_iso (FullyFaithful.hom e)
    (Equivalence.cancelRightWhiskerIso (e.counit.app _)
    ((by simpa using e.counit.hom.naturality _) ≪≫ (α_ _ _ _).symm ≪≫
    (whiskerRightIso (e.counit.app _).unit _).symm ≪≫ λ_ _))⟩

end EssentiallyFull

end Biequivalence
