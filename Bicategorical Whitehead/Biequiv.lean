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
theorem hom (e : Biequivalence B C) : EssentiallySurjective e.hom.toLax := fun c =>
  ⟨e.inv.obj c, ⟨by simpa using Equivalence.app e.counit c⟩⟩

@[simp]
theorem inv (e : Biequivalence B C) : EssentiallySurjective e.inv.toLax := fun b =>
  ⟨e.hom.obj b, ⟨by simpa using (Equivalence.app e.unit b).symm⟩⟩

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
    exact ⟨α, by apply this; simpa⟩

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
theorem hom (e : Biequivalence B C) : EssentiallyFull e.hom.toLax := fun h =>
  ⟨(e.unit.app _).hom ≫ e.inv.map h ≫ (e.unit.app _).inv,
  FullyFaithful.nonempty_iso_of_map_iso (FullyFaithful.inv _)
  (Equivalence.cancelLeftWhiskerIso _ ((α_ _ _ _ ≪≫ whiskerLeftIso _ (e.unit.app _).counit ≪≫
  ρ_ ((e.unit.app _).hom ≫ _)).symm ≪≫ whiskerRightIso (α_ _ _ _) _ ≪≫ α_ _ _ _ ≪≫
  whiskerLeftIso _ (α_ _ _ _) ≪≫ whiskerLeftIso _ (α_ _ _ _).symm ≪≫ (α_ _ _ _).symm ≪≫
  (e.unit.hom.naturality _))).symm⟩

@[simp]
theorem inv (e : Biequivalence B C) : EssentiallyFull e.inv.toLax := fun h =>
  ⟨(e.counit.app _).inv ≫ e.hom.map h ≫ (e.counit.app _).hom,
  FullyFaithful.nonempty_iso_of_map_iso (FullyFaithful.hom _)
  (Equivalence.cancelRightWhiskerIso (e.counit.app _) ((by simpa using e.counit.hom.naturality _) ≪≫
  (α_ _ _ _).symm ≪≫ (whiskerRightIso (e.counit.app _).unit _).symm ≪≫ λ_ _))⟩

end EssentiallyFull

end Biequivalence

class IsBiequivalence (F : B ⥤ᴸ C) where
  essSurj : Biequivalence.EssentiallySurjective F
  essFull : Biequivalence.EssentiallyFull F
  fullFaith : Biequivalence.FullyFaithful F

namespace IsBiequivalence

@[simp]
def BiequivalenceHom (e : Biequivalence B C) : IsBiequivalence e.hom.toLax where
  essSurj := Biequivalence.EssentiallySurjective.hom e
  essFull := Biequivalence.EssentiallyFull.hom e
  fullFaith := Biequivalence.FullyFaithful.hom e

@[simp]
def BiequivalenceInv (e : Biequivalence B C) : IsBiequivalence e.inv.toLax where
  essSurj := Biequivalence.EssentiallySurjective.inv e
  essFull := Biequivalence.EssentiallyFull.inv e
  fullFaith := Biequivalence.FullyFaithful.inv e

namespace LaxSlice.incLaxTerminal

/-- This object will be an inc-lax terminal object in the lax slice `F ↓ X` for `F`
essentially surjective, essentially full, and fully faithful. 
Since `F` is essentially surjective, there is a choice of object `X' : B` and an invertible
1-cell `f_X' : FX' ⟶ X`. The object `(X', f_X')` then is our inc-lax terminal object. -/
@[simp]
noncomputable def obj (F : B ⥤ᴸ C) (x : C) [hF : IsBiequivalence F] :
    Comma.LaxSlice F x where
  left := _
  right := ⟨Discrete.mk PUnit.unit⟩
  hom := (Classical.choice (Classical.choose_spec (hF.essSurj _))).hom

/- It seems that I can't prove the `app_eq_id_self` condition for this construction,
so I am using it as a helper to construct something that will work. -/
@[simp]
noncomputable def underlyingCone (F : B ⥤ᴸ C) (x : C) [hF : IsBiequivalence F] :
    Lax.LaxTrans (LaxFunctor.id (Comma.LaxSlice F x))
    (const (Comma.LaxSlice F x) (obj F x)) := by
  let x' := Classical.choose (hF.essSurj x)
  let fx' := Classical.choice (Classical.choose_spec (hF.essSurj x))
  let p (z : Comma.LaxSlice F x) := Classical.choose (hF.essFull (z.hom ≫ fx'.inv))
  let pIso (z : Comma.LaxSlice F x) := Classical.choice (Classical.choose_spec (hF.essFull
    (z.hom ≫ fx'.inv)))
  let imageCell {a b : Comma.LaxSlice F x} (m : a ⟶ b) := (pIso _).hom ≫
    (whiskerRightIso (by simpa using (ρ_ _).symm) _).hom ≫ m.f ▷ _ ≫ (α_ _ _ _).hom ≫
    (whiskerLeftIso _ (pIso _).symm).hom ≫ F.mapComp m.left (p _)
  let natBase {a b : Comma.LaxSlice F x} (m : a ⟶ b) := Classical.choose
    ((hF.fullFaith (p _) (m.left ≫ p _)).2 (imageCell m))
  let natBase_spec {a b : Comma.LaxSlice F x} (m : a ⟶ b) := Classical.choose_spec
    ((hF.fullFaith (p _) (m.left ≫ p _)).2 (imageCell m))
  exact ⟨fun z => {
      left := p z
      right := 𝟙 _
      f := id (ρ_ _).hom ≫ (whiskerRightIso (pIso z) _ ≪≫ α_ _ _ _ ≪≫
        whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).inv },
    fun {a _} f => {
      left := (ρ_ _).hom ≫ natBase f
      right := 𝟙 _
      icc := by
        have {a b : Comma.LaxSlice F x} (m : a ⟶ b) :=
          congrArg (fun η => η ▷ fx'.hom) (natBase_spec m)
        dsimp only [Comma.LaxSlice, const.fromPUnit.eq_1, Pseudofunctor.toOplax_toPrelaxFunctor,
          const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj,
          const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map, id_eq, whiskerRightIso_hom,
          Iso.symm_hom, whiskerLeftIso_hom, natBase, imageCell] at this
        simp only [const.fromPUnit.eq_1, Comma.LaxSlice, Comma.inst.eq_1,
          Comma.instCategoryHom.eq_1, LaxFunctor.id_toPrelaxFunctor,
          PrelaxFunctor.id_toPrelaxFunctorStruct, PrelaxFunctorStruct.id_toPrefunctor,
          Prefunctor.id_obj, Pseudofunctor.toOplax_toPrelaxFunctor, obj,
          Pseudofunctor.toLax_toPrelaxFunctor,
          const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj,
          const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map, id_eq, Iso.trans_inv,
          whiskerLeftIso_inv, whiskerRightIso_inv, Comma.id_def, Comma.comp_def, Comma.comp₁_right,
          Comma.id₁_right, Prefunctor.id_map, Comma.comp₁_left, Comma.id₁_left, Comma.comp₁_f,
          Pseudofunctor.toOplax_mapComp, const_mapComp, Iso.symm_hom, whiskerLeft_rightUnitor_inv,
          assoc, Iso.hom_inv_id_assoc, whiskerRight_id, Comma.id₁_f, Pseudofunctor.toOplax_mapId,
          const_mapId, Iso.refl_hom, whiskerLeft_id, id_comp, whiskerLeft_comp,
          whiskerLeft_rightUnitor, Iso.inv_hom_id_assoc, PrelaxFunctor.map₂_comp, comp_whiskerRight,
          const_toPrelaxFunctor_toPrelaxFunctorStruct_map₂]
        rw [this]
        have : _ ◁ F.mapId x' ≫ F.mapComp (p a) (𝟙 x') ≫ F.map₂ (ρ_ _).hom = (ρ_ _).hom := by
          simpa using (F.map₂_rightUnitor_hom (p a)).symm
        have := congrArg (fun η => (α_ _ _ _).inv ≫ η ▷ fx'.hom) this
        simp only [const.fromPUnit.eq_1, comp_whiskerRight, whisker_assoc, assoc,
          Iso.inv_hom_id_assoc] at this
        have : _ ◁ (λ_ _).inv ≫ _ ◁ F.mapId x' ▷ _ ≫ (α_ _ _ _).inv ≫ F.mapComp (p a) (𝟙 x') ▷ _ ≫
            F.map₂ (ρ_ _).hom ▷ fx'.hom = 𝟙 _ := by
          rw [this]
          bicategory
        have := congrArg (fun η => _ ◁ fx'.counit.inv ≫ (α_ _ _ _).inv ≫ (pIso _).inv ▷ _ ≫ η ≫
          ((pIso _).hom ≫ (ρ_ _).inv ▷ _ ≫ f.f ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ (pIso _).inv ≫
          F.mapComp f.left (p _)) ▷ _) this
        simp only [const.fromPUnit.eq_1, Pseudofunctor.toOplax_toPrelaxFunctor,
          const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj,
          const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map, assoc] at this
        rw [this, id_comp]
        simp only [comp_whiskerRight, whisker_assoc, assoc, inv_hom_whiskerRight_assoc]
        have {z : C} {r s : z ⟶ x} (β : r ⟶ s) : ((β ▷ _) ▷ _) ≫
            (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).hom =
            (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).hom ≫ β := by
          calc
           _ = (α_ _ _ _).hom ≫ β ▷ _ ≫ _ ◁ fx'.counit.hom ≫ (ρ_ _).hom := by simp
           _ = (α_ _ _ _).hom ≫ _ ◁ fx'.counit.hom ≫ β ▷ _ ≫ (ρ_ _).hom := by
             rw [whisker_exchange_assoc]
           _ = _ := by simp
        have {z : C} {r s : z ⟶ x} (β : r ⟶ s) :
            (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).inv ≫ ((β ▷ _) ▷ _) =
            β ≫ (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).inv := by
          simpa using congrArg (fun t => (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).inv ≫ t ≫
          (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).inv) (this β)
        have : (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).inv ≫ (f.f ▷ _) ▷ _ =
            f.f ≫ (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).inv := by simpa using this f.f
        simpa using congrArg (fun η => η ≫ (α_ _ _ _).hom ▷ fx'.hom ≫ (α_ _ _ _).hom ≫
          _ ◁ (pIso _).inv ▷ _ ≫ (α_ _ _ _).inv ≫ F.mapComp f.left (p _) ▷ _) this },
    fun {a b f g} η => by
      simp only [Comma.LaxSlice, const.fromPUnit.eq_1, Comma.inst.eq_1, Comma.instCategoryHom.eq_1,
        LaxFunctor.id_toPrelaxFunctor, PrelaxFunctor.id_toPrelaxFunctorStruct,
        PrelaxFunctorStruct.id_toPrefunctor, Prefunctor.id_obj, obj,
        Pseudofunctor.toLax_toPrelaxFunctor,
        const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj,
        Pseudofunctor.toOplax_toPrelaxFunctor,
        const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map, id_eq, Comma.id_def,
        Comma.comp_def, Prefunctor.id_map, Comma.comp₁_left, Comma.id₁_left, Comma.comp₁_right,
        Comma.id₁_right, PrelaxFunctorStruct.id_map₂,
        const_toPrelaxFunctor_toPrelaxFunctorStruct_map₂]
      ext
      · simp only [Comma.comp₁_left, Comma.id₁_left, Comma.comp₂_left, Comma.whiskerRight_left,
          assoc, Comma.whiskerLeft_left, Comma.id₂_left, whiskerLeft_id, id_comp,
          Iso.cancel_iso_hom_left]
        apply (hF.fullFaith (p _) (_ ≫ p _)).1
        simp only [const.fromPUnit.eq_1, PrelaxFunctor.map₂_comp]
        have : imageCell _ ≫ F.map₂ (η.left ▷ p _) = imageCell _ := by
          simp only [const.fromPUnit.eq_1, Pseudofunctor.toOplax_toPrelaxFunctor,
            const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj, Comma.LaxSlice,
            const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map, id_eq,
            whiskerRightIso_hom, Iso.symm_hom, whiskerLeftIso_hom, assoc,
            LaxFunctor.mapComp_naturality_left, Iso.cancel_iso_hom_left, imageCell]
          have h₁ : _ ◁ (pIso _).inv ≫ F.map₂ η.left ▷ _ =
              F.map₂ η.left ▷ _ ≫ _ ◁ (pIso _).inv := by
            simpa using whisker_exchange (F.map₂ η.left) (pIso _).inv
          have h₂ : f.f ▷ _ ≫ (α_ _ _ _).hom ≫ F.map₂ η.left ▷ _ =
              (_ ◁ (const.fromPUnit x).toOplax.map₂ η.right) ▷ _ ≫ g.f ▷ fx'.inv ≫
              (α_ _ _ _).hom := by
            simpa using congrArg (fun θ => θ ▷ fx'.inv ≫ (α_ _ _ _).hom) η.icc
          calc
           _ = (ρ_ _).inv ▷ _ ≫ f.f ▷ _ ≫ (α_ _ _ _).hom ≫ F.map₂ η.left ▷ _ ≫ _ ◁ (pIso _).inv ≫
               F.mapComp g.left (p _) := by
             simpa using congrArg (fun θ => (ρ_ _).inv ▷ _ ≫ f.f ▷ _ ≫ (α_ _ _ _).hom ≫ θ ≫
               F.mapComp g.left (p _)) h₁
           _ = (ρ_ a.hom).inv ▷ _ ≫ ((_ ◁ (const.fromPUnit x).toOplax.map₂ η.right) ▷ _ ≫ g.f ▷ _ ≫
               (α_ _ _ _).hom) ≫ _ ◁ (pIso _).inv ≫ F.mapComp g.left (p _) := by
             simpa using congrArg (fun θ => (ρ_ _).inv ▷ _ ≫ θ ≫ _ ◁ (pIso _).inv ≫
               F.mapComp g.left (p b)) h₂
           _ = _ := by simp
        change F.map₂ (natBase f) ≫ F.map₂ (η.left ▷ p b) = F.map₂ (natBase g)
        simp only [Comma.LaxSlice, const.fromPUnit.eq_1] at natBase_spec
        rw [natBase_spec f, this, natBase_spec g]
      · rfl,
      fun a => by
        simp only [Comma.LaxSlice, const.fromPUnit.eq_1, Comma.inst.eq_1,
          Comma.instCategoryHom.eq_1, LaxFunctor.id_toPrelaxFunctor,
          PrelaxFunctor.id_toPrelaxFunctorStruct, PrelaxFunctorStruct.id_toPrefunctor,
          Prefunctor.id_obj, obj, Pseudofunctor.toLax_toPrelaxFunctor,
          const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj,
          Pseudofunctor.toOplax_toPrelaxFunctor,
          const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map, id_eq, Comma.id_def,
          Comma.comp_def, Prefunctor.id_map, Pseudofunctor.toLax_mapId, const_mapId, Iso.refl_inv,
          Comma.comp₁_left, Comma.id₁_left, Comma.comp₁_right, Comma.id₁_right,
          Comma.rightUnitor_hom, Comma.leftUnitor_inv, LaxFunctor.id_mapId]
        ext
        · simp only [Comma.comp₁_left, Comma.id₁_left, Comma.comp₂_left, Comma.whiskerLeft_left,
            Comma.id₂_left, whiskerLeft_id, id_comp, Comma.rightUnitorHom_left,
            Comma.leftUnitorInv_left, Comma.whiskerRight_left, id_whiskerRight, comp_id,
            Iso.cancel_iso_hom_left]
          apply (hF.fullFaith (p _) ((𝟙 _) ≫ p _)).1
          simp only [const.fromPUnit.eq_1, LaxFunctor.map₂_leftUnitor]
          calc
           _ = imageCell (Comma.id₁ a) := by simpa using Classical.choose_spec ((hF.fullFaith (p _)
             ((Comma.id₁ _).left ≫ p _)).2 (imageCell (Comma.id₁ _)))
           _ = _ := by
             dsimp [imageCell]
             have : (pIso _).hom ≫ (λ_ _).inv ≫ (α_ _ _ _).inv ≫ F.mapId a.left ▷ _ ▷ _ ≫
                 (α_ _ _ _).hom ≫ F.map (𝟙 _) ◁ (pIso _).inv = (λ_ _).inv ≫ F.mapId a.left ▷ _ := by
               have : (pIso _).hom ≫ (λ_ _).inv = (λ_ _).inv ≫ 𝟙 _ ◁ (pIso a).hom := by simp
               rw [←assoc (pIso a).hom, this]
               have : _ ◁ (pIso _).hom ≫ (α_ _ _ _).inv ≫ F.mapId a.left ▷ _ ▷ _ ≫ (α_ _ _ _).hom ≫
                   _ ◁ (pIso _).inv = F.mapId a.left ▷ _ := by
                 simpa using congrArg (fun θ => θ ≫ _ ◁ (pIso _).inv)
                   (whisker_exchange (F.mapId a.left) (pIso a).hom)
               rw [assoc, this]
             simpa using congrArg (fun θ => θ ≫ F.mapComp (𝟙 a.left) (p a)) this
        · rfl,
      fun {_ b _} f g => by
        simp only [Comma.LaxSlice, const.fromPUnit.eq_1, Comma.inst.eq_1,
          Comma.instCategoryHom.eq_1, LaxFunctor.id_toPrelaxFunctor,
          PrelaxFunctor.id_toPrelaxFunctorStruct, PrelaxFunctorStruct.id_toPrefunctor,
          Prefunctor.id_obj, obj, Pseudofunctor.toLax_toPrelaxFunctor,
          const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj,
          Pseudofunctor.toOplax_toPrelaxFunctor,
          const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map, id_eq, Comma.id_def,
          Comma.comp_def, Prefunctor.id_map, Pseudofunctor.toLax_mapComp, const_mapComp,
          Iso.symm_inv, Comma.rightUnitor_hom, Comma.comp₁_left, Comma.id₁_left, Comma.comp₁_right,
          Comma.id₁_right, Comma.associator_inv, Comma.associator_hom, LaxFunctor.id_mapComp]
        ext
        · simp only [Comma.comp₁_left, Comma.id₁_left, Comma.comp₂_left, Comma.whiskerLeft_left,
            Comma.rightUnitorHom_left, whiskerLeft_rightUnitor, assoc, Comma.associatorInv_left,
            Comma.whiskerRight_left, whiskerRight_id, Comma.associatorHom_left, whiskerLeft_comp,
            Comma.id₂_left, id_whiskerRight, comp_id, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
            Iso.cancel_iso_inv_left, Iso.cancel_iso_hom_left]
          apply (hF.fullFaith (p _) (_ ≫ p _)).1
          simp only [const.fromPUnit.eq_1, Comma.comp₁_left, PrelaxFunctor.map₂_comp]
          have : F.map₂ (natBase (Comma.comp₁ f g)) = imageCell (Comma.comp₁ f g) :=
            natBase_spec (Comma.comp₁ f g)
          rw [this]
          have h₁ : imageCell (Comma.comp₁ f g) =
              F.map₂ (natBase f ≫_ ◁ natBase g ≫ (α_ _ _ _).inv) := by
            simp only [const.fromPUnit.eq_1, Pseudofunctor.toOplax_toPrelaxFunctor,
            const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj, Comma.comp₁_left,
            Comma.LaxSlice, const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map, id_eq,
            whiskerRightIso_hom, Iso.symm_hom, whiskerLeftIso_hom, Comma.comp₁_f,
            Pseudofunctor.toOplax_mapComp, const_mapComp, whiskerLeft_rightUnitor_inv,
            whiskerRight_id, assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, comp_whiskerRight,
            whisker_assoc, PrelaxFunctor.map₂_comp, imageCell]
            simp only [Comma.LaxSlice, const.fromPUnit.eq_1] at natBase_spec
            have h₁ : F.mapComp f.left (p _) ≫ F.map₂ (_ ◁ natBase g) =
                _ ◁ imageCell g ≫ F.mapComp f.left (g.left ≫ p _) := by
              rw [F.mapComp_naturality_right f.left (natBase g), natBase_spec g]
            have h₂ : _ ◁ F.mapComp g.left (p _) ≫ F.mapComp f.left (g.left ≫ p _) ≫
                F.map₂ (α_ _ _ _).inv = (α_ _ _ _).inv ≫ F.mapComp f.left g.left ▷ _ ≫
                F.mapComp (f.left ≫ g.left) (p _) := by
              have := congrArg (fun η => (α_ _ _ _).inv ≫ η ≫ F.map₂ (α_ _ _ _).inv)
                (F.map₂_associator f.left g.left (p _))
              simp only [const.fromPUnit.eq_1, assoc, Iso.inv_hom_id_assoc, ←F.map₂_comp] at this
              rw [Iso.hom_inv_id] at this
              simp only [PrelaxFunctor.map₂_id, comp_id] at this
              exact this.symm
            rw [natBase_spec f]
            symm
            calc
             _ = (pIso _).hom ≫ (ρ_ _).inv ▷ _ ≫ f.f ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ (pIso _).inv ≫
                 F.mapComp f.left (p _) ≫ F.map₂ (_ ◁ natBase g) ≫ F.map₂ (α_ _ _ _).inv := by
               simp [imageCell]
             _ = _ := by
               have := congrArg (fun θ => (pIso _).hom ≫ (ρ_ _).inv ▷ _ ≫ f.f ▷ _ ≫ (α_ _ _ _).hom ≫
                 _ ◁ (pIso _).inv ≫ θ ≫ F.map₂ (α_ _ _ _).inv) h₁
               simp only [const.fromPUnit.eq_1, assoc] at this
               rw [this]
               have : (α_ _ _ _).hom ≫ _ ◁ (pIso _).inv ≫ F.map f.left ◁ imageCell g =
                 (ρ_ _).inv ▷ _ ≫ (α_ _ _ _).hom ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ g.f ▷ _ ≫
                 (α_ _ _ _).inv ≫ (α_ _ _ _).inv ▷ _ ≫ (α_ _ _ _).hom ≫ (α_ _ _ _).hom ≫
                 _ ◁ _ ◁ (pIso _).inv ≫ _ ◁ F.mapComp g.left (p _) := by
                 simp only [const.fromPUnit.eq_1, Pseudofunctor.toOplax_toPrelaxFunctor,
                   const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj,
                   Comma.LaxSlice,const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map,
                   id_eq, whiskerRightIso_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerLeft_comp,
                   whiskerLeft_inv_hom_assoc, pentagon_inv_hom_hom_hom_hom_assoc,
                   Iso.inv_hom_id_assoc, imageCell]
                 have : (α_ _ b.hom _).hom ≫ F.map f.left ◁ (ρ_ _).inv ▷ _ =
                     (ρ_ _).inv ▷ _ ≫ (α_ _ _ _).hom ▷ fx'.inv ≫ (α_ _ _ _).hom := by
                   rw [←associator_naturality_middle]
                   have : (ρ_ _).inv ▷ fx'.inv ≫ (α_ _ _ _).hom ▷ _ =
                     (F.map f.left ◁ (ρ_ b.hom).inv) ▷ _ := by bicategory
                   rw [←this]
                   simp
                 rw [←assoc (α_ (F.map _) _ _).hom, this]
                 simp
               have := congrArg (fun η => (pIso _).hom ≫ (ρ_ _).inv ▷ _ ≫ f.f ▷ _ ≫  η ≫
                 F.mapComp f.left (g.left ≫ p _) ≫ F.map₂ (α_ _ _ _).inv) this
               simp only [const.fromPUnit.eq_1, assoc] at this
               rw [this]
               simp only [const.fromPUnit.eq_1, Pseudofunctor.toOplax_toPrelaxFunctor,
                 const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj,
                 const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map,
                 pentagon_inv_hom_hom_hom_hom_assoc, Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
               have := congrArg (fun θ => (ρ_ _).inv ▷ _ ≫ f.f ▷ _ ≫ (ρ_ _).inv ▷ _ ≫
                 (α_ _ _ _).hom ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ g.f ▷ _ ≫ _ ◁ (α_ _ _ _).hom ≫
                 _ ◁ _ ◁ (pIso _).inv ≫ θ) h₂
               simp only [const.fromPUnit.eq_1, Pseudofunctor.toOplax_toPrelaxFunctor,
                 const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj] at this
               rw [this]
               have : _ ◁ _ ◁ (pIso _).inv ≫ (α_ _ _ _).inv ≫ F.mapComp f.left g.left ▷ _ =
                   (α_ _ _ _).inv ≫ F.mapComp f.left g.left ▷ _ ≫ _ ◁ (pIso _).inv := by
                 simpa using congrArg (fun θ => (α_ _ _ _).inv ≫ θ)
                   (whisker_exchange (F.mapComp f.left g.left) (pIso _).inv)
               have : _ ◁ (α_ _ _ _).hom ≫_ ◁ _ ◁ (pIso _).inv ≫ (α_ _ _ _).inv ≫
                   F.mapComp f.left g.left ▷ _ ≫ F.mapComp (f.left ≫ g.left) (p _) =
                   (α_ _ _ _).inv ≫ (α_ _ _ _).inv ▷ _ ≫ F.mapComp f.left g.left ▷ _ ▷ _ ≫
                   (α_ _ _ _).hom ≫ _ ◁ (pIso _).inv ≫ F.mapComp (f.left ≫ g.left) (p _) := by
                 simpa using congrArg (fun θ => _ ◁ (α_ _ _ _ ).hom ≫ θ ≫
                   F.mapComp (f.left ≫ g.left) (p _)) this
               rw [this]
          rw [h₁]
          simp
        · rfl⟩

@[simp]
noncomputable def app_isInitial (F : B ⥤ᴸ C) (x : C) [hF : IsBiequivalence F]
    (X : Comma.LaxSlice F x) : Limits.IsInitial ((underlyingCone F x).app X) := by
  let x' := Classical.choose (hF.essSurj x)
  let fx' := Classical.choice (Classical.choose_spec (hF.essSurj x))
  let p (z : Comma.LaxSlice F x) := Classical.choose (hF.essFull (z.hom ≫ fx'.inv))
  let pIso (z : Comma.LaxSlice F x) := Classical.choice (Classical.choose_spec (hF.essFull
    (z.hom ≫ fx'.inv)))
  let imageCell {z : Comma.LaxSlice F x} (Y : z ⟶ obj F x) :=
    (pIso z).hom ≫ (ρ_ z.hom).inv ▷ _ ≫ Y.f ▷ _ ≫ (α_ _ _ _).hom ≫ (whiskerLeftIso _ fx'.unit).inv ≫
    (ρ_ _).hom
  let lift {z : Comma.LaxSlice F x} (Y : z ⟶ obj F x) := Classical.choose
    ((hF.fullFaith (p _) Y.left).2 (imageCell Y))
  let lift_spec {z : Comma.LaxSlice F x} (Y : z ⟶ obj F x) := Classical.choose_spec
    ((hF.fullFaith (p _) Y.left).2 (imageCell Y))
  let preIso := whiskerLeftIso _ fx'.counit.symm ≪≫ (α_ _ _ _).symm
    ≪≫ whiskerRightIso (pIso X).symm _ 
  have h (Y : X ⟶ obj F x) : (preIso).hom ≫ imageCell Y ▷ _ = Y.f := by
    have : (α_ (F.map Y.left) _ _).hom ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ fx'.unit.inv ▷ _ ≫
        _ ◁ (λ_ _).hom = (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).hom := by
      simp only [const.fromPUnit.eq_1, obj, Pseudofunctor.toOplax_toPrelaxFunctor,
        const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj, Iso.trans_hom,
        whiskerLeftIso_hom, comp_whiskerLeft, assoc]
      have : whiskerLeftIso (F.map Y.left) (leftZigzagIso fx'.unit fx'.counit) =
          whiskerLeftIso _ (λ_ _ ≪≫ (ρ_ _).symm) := by
        simpa using congrArg (fun η => whiskerLeftIso _ η) fx'.left_triangle
      have : (whiskerRightIso (α_ (F.map Y.left) _ _) _ ≪≫ α_ _ _ _ ≪≫
          whiskerLeftIso _ (whiskerRightIso fx'.unit.symm _) ≪≫ whiskerLeftIso _ (λ_ _)).symm =
          (α_ _ _ _ ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso _ (whiskerLeftIso _ fx'.counit) ≪≫
          (α_ _ _ _).symm ≪≫ ρ_ _).symm := by
        ext
        have := congrArg Iso.hom this
        simp only [const.fromPUnit.eq_1,  obj, Pseudofunctor.toOplax_toPrelaxFunctor,
          const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj,  bicategoricalIsoComp,
          BicategoricalCoherence.assoc_iso, BicategoricalCoherence.whiskerRight_iso,
          BicategoricalCoherence.refl_iso, Iso.trans_assoc, whiskerLeftIso_hom, Iso.trans_hom,
          whiskerRightIso_hom, Iso.refl_hom, whiskerRight_comp, id_whiskerRight, id_comp,
          Iso.inv_hom_id, whiskerLeft_comp, Iso.symm_hom, whiskerLeft_rightUnitor_inv] at this
        simp only [const.fromPUnit.eq_1,  obj, Pseudofunctor.toOplax_toPrelaxFunctor,
          const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj, Iso.trans_symm,
          Iso.trans_assoc, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_inv, whiskerRightIso_inv,
          Iso.symm_inv, Iso.symm_symm_eq]
        calc
          _ = _ ◁ (λ_ _).inv ≫ (_ ◁ fx'.unit.hom ▷ _ ≫ _ ◁ (α_ _ _ _).hom ≫
            _ ◁ _ ◁ fx'.counit.hom) ≫ _ ◁ _ ◁ fx'.counit.inv ≫ (α_ _ _ _).inv ≫
            (α_ _ _ _).inv := by simp
          _ = _ ◁ (λ_ _).inv ≫ (_ ◁ (λ_ _).hom ≫ (ρ_ _).inv ≫ (α_ _ _ _).hom) ≫
            _ ◁ _ ◁ fx'.counit.inv ≫ (α_ _ _ _).inv ≫ (α_ _ _ _).inv := by rw [this]
          _ = _ := by simp
      have : whiskerRightIso (α_ (F.map Y.left) _ _) _ ≪≫ α_ _ _ _ ≪≫
          whiskerLeftIso _ (whiskerRightIso fx'.unit.symm _) ≪≫ whiskerLeftIso _ (λ_ _) =
          α_ _ _ _ ≪≫ α_ _ fx'.hom (fx'.inv ≫ fx'.hom) ≪≫
          whiskerLeftIso _ (whiskerLeftIso _ fx'.counit) ≪≫ (α_ _ _ _).symm ≪≫ ρ_ _ := by
        simpa using congrArg Iso.symm this
      exact congrArg Iso.hom this
    simp only [const.fromPUnit.eq_1, Pseudofunctor.toOplax_toPrelaxFunctor,
      const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj, obj, Iso.trans_hom,
      whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom, Comma.LaxSlice,
      const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map, whiskerLeftIso_inv,
      comp_whiskerRight, whisker_assoc, assoc, triangle_assoc_comp_right,
      inv_hom_whiskerRight_assoc, preIso, imageCell]
    rw [this]
    have : _ ◁ fx'.counit.inv ≫ (α_ X.hom _ _).inv ≫ (ρ_ _).inv ▷ _ ▷ _ =
       (ρ_ _).hom ≫ (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).inv ≫
       (ρ_ _).inv ▷ _ ▷ _ := by simp
    have := congrArg (fun η => η ≫ Y.f ▷ _ ▷ _ ≫
      (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).hom) this
    simp only [const.fromPUnit.eq_1,  obj, Pseudofunctor.toOplax_toPrelaxFunctor,
      const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj,
      const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map, assoc] at this
    rw [this]
    have {z : C} {r s : z ⟶ x} (β : r ⟶ s) : (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).inv ≫
        ((β ▷ _) ▷ _) ≫ (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).hom = β := by
      have : (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).inv ≫ ((β ▷ _) ▷ _) =
          β ≫ (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).inv := by
        have : ((β ▷ _) ▷ _) ≫ (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).hom =
            (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).hom ≫ β := by
          simp only [Iso.trans_hom, whiskerLeftIso_hom, assoc]
          rw [associator_naturality_left_assoc, ←whisker_exchange_assoc, rightUnitor_naturality]
        have := congrArg (fun η => (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).inv ≫ η ≫
          (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).inv) this
        simp only [assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, comp_id] at this
        exact this
      simpa using congrArg (fun η => η ≫ (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).hom) this
    have : (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).inv ≫ (((ρ_ _).inv ≫ Y.f) ▷ _ ▷ _) ≫
        (α_ _ _ _ ≪≫ whiskerLeftIso _ fx'.counit ≪≫ ρ_ _).hom = (ρ_ _).inv ≫ Y.f := by
      simpa using this ((ρ_ _).inv ≫ Y.f)
    simpa using congrArg (fun η => (ρ_ _).hom ≫ η) this
  refine Limits.IsInitial.ofUniqueHom ?_ ?_
  --want to just exact here but for some reason it doesn't like that.
  · intro Y
    exact {
      left := lift Y
      right := 𝟙 _
      icc := by
        simp only [Comma.LaxSlice, const.fromPUnit.eq_1, obj, Pseudofunctor.toOplax_toPrelaxFunctor,
          const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj] at lift_spec
        rw [lift_spec Y]
        simpa [preIso] using h Y }
  · intro Y m
    have h₁ : preIso.hom ≫ F.map₂ m.left ▷ _ = Y.f := by simpa [preIso] using m.icc
    have h₂ : F.map₂ m.left ▷ _ = imageCell Y ▷ fx'.hom := by
      calc
       _ = preIso.inv ≫ Y.f := by simpa using congrArg (fun η => preIso.inv ≫ η) h₁
       _ = _ := by simpa using (congrArg (fun η => preIso.inv ≫ η) (h Y)).symm
    simp only [Comma.LaxSlice, const.fromPUnit.eq_1, Comma.inst.eq_1, Comma.instCategoryHom.eq_1,
      LaxFunctor.id_toPrelaxFunctor, PrelaxFunctor.id_toPrelaxFunctorStruct,
      PrelaxFunctorStruct.id_toPrefunctor, Prefunctor.id_obj, obj,
      Pseudofunctor.toOplax_toPrelaxFunctor,
      const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj,
      Pseudofunctor.toLax_toPrelaxFunctor, underlyingCone,
      const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map, id_eq, Iso.trans_inv,
      whiskerLeftIso_inv, whiskerRightIso_inv, Comma.id_def, Comma.comp_def, Prefunctor.id_map,
      Comma.comp₁_left, Comma.id₁_left, whiskerRightIso_hom, Iso.symm_hom, whiskerLeftIso_hom,
      Comma.comp₁_right, Comma.id₁_right]
    ext
    · apply (hF.fullFaith _ _).1
      exact ((Equivalence.whiskerRightEquiv _ _ _).injective h₂).trans (lift_spec Y).symm
    · rfl

@[simp]
noncomputable def app (F : B ⥤ᴸ C) (x : C) [hF : IsBiequivalence F]
    (z : Comma.LaxSlice F x) : z ⟶ obj F x := by
  classical
  exact if h : z = obj F x then by
    subst h
    exact 𝟙 (obj F x)
  else (underlyingCone F x).app z

/- Note that here I am now assuming that `F` is a pseudofunctor. It seems to me that we need
`mapId` to be invertible for this to make sense. I don't know how Johnson-Yau seem to do this
with just a lax functor, but to me it seems that pseudofunctoriality is necessary. -/
@[simp]
noncomputable def appSelfIso (F : B ⥤ᵖ C) (x : C) [hF : IsBiequivalence F.toLax] :
    (underlyingCone F.toLax x).app (obj F.toLax x) ≅ 𝟙 (obj F.toLax x) := by
  let fx' : F.toLax.obj (obj F.toLax _).left ≌ _ := by
    simpa using (Classical.choice (Classical.choose_spec (hF.essSurj x)))
  let p := Classical.choose (hF.essFull ((obj F.toLax _).hom ≫
    (Classical.choice (Classical.choose_spec (hF.essSurj x))).inv))
  let pIso : F.toLax.map _ ≅ (obj F.toLax _).hom ≫ fx'.inv := by
    simpa using Classical.choice (Classical.choose_spec (hF.essFull ((obj F.toLax _).hom ≫
    (Classical.choice (Classical.choose_spec (hF.essSurj _))).inv)))
  --pseudofunctoriality used here
  let iF := pIso ≪≫ fx'.unit.symm ≪≫ (F.mapId (obj F.toLax _).left).symm
  let ihom := Classical.choose ((hF.fullFaith _ _).2 iF.hom)
  have ihom_spec : F.toLax.map₂ ihom = iF.hom := by
    simpa using Classical.choose_spec ((hF.fullFaith _ _).2 iF.hom)
  let iinv := Classical.choose ((hF.fullFaith _ _).2 iF.inv)
  have iinv_spec : F.toLax.map₂ iinv = iF.inv := by
    simpa using Classical.choose_spec ((hF.fullFaith _ _).2 iF.inv)
  let ileft : _ ≅ _ := {
    hom := ihom 
    inv := iinv
    hom_inv_id := by
      apply (hF.fullFaith _ _).1
      simp only [const.fromPUnit.eq_1, obj, Pseudofunctor.toOplax_toPrelaxFunctor,
        const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj, PrelaxFunctor.map₂_comp,
        PrelaxFunctor.map₂_id, ihom_spec, iinv_spec, Iso.hom_inv_id]
    inv_hom_id := by
      apply (hF.fullFaith _ _).1
      simp only [const.fromPUnit.eq_1, obj, Pseudofunctor.toOplax_toPrelaxFunctor,
        const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj, PrelaxFunctor.map₂_comp,
        PrelaxFunctor.map₂_id, iinv_spec, ihom_spec, Iso.inv_hom_id] }
  exact {
    hom := {
      left := by simpa using ileft.hom
      right := 𝟙 _
      icc := by
        simp only [const.fromPUnit.eq_1, Comma.LaxSlice, Comma.inst.eq_1,
          Comma.instCategoryHom.eq_1, LaxFunctor.id_toPrelaxFunctor,
          PrelaxFunctor.id_toPrelaxFunctorStruct, PrelaxFunctorStruct.id_toPrefunctor, obj,
          Pseudofunctor.toOplax_toPrelaxFunctor,
          const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj, Prefunctor.id_obj,
          underlyingCone, const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map, id_eq,
          Iso.trans_inv, whiskerLeftIso_inv, whiskerRightIso_inv, Comma.id_def, Comma.comp_def,
          Prefunctor.id_map, Comma.comp₁_left, Comma.id₁_left, whiskerRightIso_hom, Iso.symm_hom,
          whiskerLeftIso_hom, Pseudofunctor.toLax_mapComp, Comma.comp₁_right, Comma.id₁_right,
          assoc, Iso.hom_inv_id_assoc, eq_mpr_eq_cast, cast_eq,
          const_toPrelaxFunctor_toPrelaxFunctorStruct_map₂, whiskerLeft_id, Comma.id₁_f,
          Pseudofunctor.toOplax_mapId, const_mapId, Iso.refl_hom, Pseudofunctor.toLax_mapId,
          id_comp]
        rw [ihom_spec]
        simp only [Pseudofunctor.toLax_toPrelaxFunctor,
          const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj, const.fromPUnit.eq_1, obj,
          Pseudofunctor.toOplax_toPrelaxFunctor, id_eq, Iso.trans_hom, Iso.symm_hom,
          comp_whiskerRight, inv_hom_whiskerRight_assoc, iF, pIso]
        have : _ ◁ fx'.counit.inv ≫ (α_ _ _ _).inv ≫ fx'.unit.inv ▷ _ =
            (ρ_ _).hom ≫ (λ_ _).inv := by
          simpa [bicategoricalIsoComp] using congrArg (fun I => I.inv) fx'.left_triangle
        simpa using congrArg (fun η => η ≫ (F.mapId _).inv ▷ _) this }
    inv := {
      left := by simpa using ileft.inv
      right := 𝟙 _
      icc := by
        simp only [const.fromPUnit.eq_1, Comma.LaxSlice, Comma.inst.eq_1,
          Comma.instCategoryHom.eq_1, LaxFunctor.id_toPrelaxFunctor,
          PrelaxFunctor.id_toPrelaxFunctorStruct, PrelaxFunctorStruct.id_toPrefunctor, obj,
          Pseudofunctor.toOplax_toPrelaxFunctor,
          const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj, Prefunctor.id_obj,
          Comma.id_def, Comma.id₁_right,
          const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map, underlyingCone, id_eq,
          Iso.trans_inv, whiskerLeftIso_inv, whiskerRightIso_inv, Comma.comp_def, Prefunctor.id_map,
          Comma.comp₁_left, Comma.id₁_left, whiskerRightIso_hom, Iso.symm_hom, whiskerLeftIso_hom,
          Pseudofunctor.toLax_mapComp, Comma.comp₁_right, Comma.id₁_f, Pseudofunctor.toOplax_mapId,
          const_mapId, Iso.refl_hom, whiskerLeft_id, Pseudofunctor.toLax_mapId, id_comp,
          eq_mpr_eq_cast, cast_eq, assoc, const_toPrelaxFunctor_toPrelaxFunctorStruct_map₂,
          Iso.hom_inv_id_assoc]
        rw [iinv_spec]
        simp only [Pseudofunctor.toLax_toPrelaxFunctor,
          const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj, const.fromPUnit.eq_1, obj,
          Pseudofunctor.toOplax_toPrelaxFunctor, id_eq, Iso.trans_inv, Iso.symm_inv, assoc,
          comp_whiskerRight, inv_hom_whiskerRight_assoc, iF, pIso]
        have : _ ◁ fx'.counit.inv ≫ (α_ _ _ _).inv ≫ fx'.unit.inv ▷ _ =
            (ρ_ _).hom ≫ (λ_ _).inv := by
          simpa [bicategoricalIsoComp] using congrArg (fun I => I.inv) fx'.left_triangle
        simpa using congrArg (fun η => η ≫ fx'.unit.hom ▷ _ ≫ _ ▷ _) this.symm }
    hom_inv_id := by
      simp only [Comma.LaxSlice, const.fromPUnit.eq_1, Comma.inst.eq_1, Comma.instCategoryHom.eq_1,
        LaxFunctor.id_toPrelaxFunctor, PrelaxFunctor.id_toPrelaxFunctorStruct,
        PrelaxFunctorStruct.id_toPrefunctor, obj, Pseudofunctor.toLax_toPrelaxFunctor,
        Pseudofunctor.toOplax_toPrelaxFunctor,
        const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj, Prefunctor.id_obj,
        underlyingCone, const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map, id_eq,
        Iso.trans_inv, whiskerLeftIso_inv, whiskerRightIso_inv, Comma.id_def, Comma.comp_def,
        Prefunctor.id_map, Comma.comp₁_left, Comma.id₁_left, whiskerRightIso_hom, Iso.symm_hom,
        whiskerLeftIso_hom, Pseudofunctor.toLax_mapComp, Comma.comp₁_right, Comma.id₁_right,
        eq_mpr_eq_cast, cast_eq]
      ext
      · simp
      · rfl
    inv_hom_id := by
      simp only [Comma.LaxSlice, const.fromPUnit.eq_1, Comma.inst.eq_1, Comma.instCategoryHom.eq_1,
        LaxFunctor.id_toPrelaxFunctor, PrelaxFunctor.id_toPrelaxFunctorStruct,
        PrelaxFunctorStruct.id_toPrefunctor, obj, Pseudofunctor.toLax_toPrelaxFunctor,
        Pseudofunctor.toOplax_toPrelaxFunctor,
        const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj, Prefunctor.id_obj,
        Comma.id_def, underlyingCone, const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map,
        id_eq, Iso.trans_inv, whiskerLeftIso_inv, whiskerRightIso_inv, Comma.comp_def,
        Prefunctor.id_map, Comma.comp₁_left, Comma.id₁_left, whiskerRightIso_hom, Iso.symm_hom,
        whiskerLeftIso_hom, Pseudofunctor.toLax_mapComp, Comma.comp₁_right, Comma.id₁_right,
        eq_mpr_eq_cast, cast_eq]
      ext
      · simp
      · rfl }

@[simp]
noncomputable def isInitial (F : B ⥤ᵖ C) (x : C) [hF : IsBiequivalence F.toLax]
    (z : Comma.LaxSlice F.toLax x) : Limits.IsInitial (app F.toLax x z) := by
  by_cases hz : z = obj F.toLax x
  · subst z
    simpa using Limits.IsInitial.ofIso (app_isInitial F.toLax x (obj F.toLax x)) (appSelfIso F x)
  · unfold app
    simpa only [hz] using app_isInitial F.toLax x z

/-- The cone witnessing the lax terminal object. -/
@[simp]
noncomputable def cone (F : B ⥤ᵖ C) (x : C) [hF : IsBiequivalence F.toLax] :
    Lax.LaxTrans (LaxFunctor.id (Comma.LaxSlice F.toLax x))
    (const (Comma.LaxSlice F.toLax x) (obj F.toLax x)) := by
  have h {a b : Comma.LaxSlice F.toLax x} (f : a ⟶ b) :
      Limits.IsInitial
      (app F.toLax x a ≫ (const (Comma.LaxSlice F.toLax x) (obj F.toLax x)).toLax.map f) := by
    have : app F.toLax x a ≫ (const (Comma.LaxSlice F.toLax x) (obj F.toLax x)).toLax.map f ≅
        app F.toLax x a := by
      simpa using (ρ_ (app F.toLax x a))
    exact Limits.IsInitial.ofIso (isInitial F x a) this.symm
  have hcomp {a b c : Comma.LaxSlice F.toLax x} (f : a ⟶ b) (g : b ⟶ c) :
      Limits.IsInitial
      (app F.toLax x a ≫ (const (Comma.LaxSlice F.toLax x) (obj F.toLax x)).toLax.map f ≫
      (const (Comma.LaxSlice F.toLax x) (obj F.toLax x)).toLax.map g) := by
    have : app F.toLax x a ≫ (const (Comma.LaxSlice F.toLax x) (obj F.toLax x)).toLax.map f ≫
        (const (Comma.LaxSlice F.toLax x) (obj F.toLax x)).toLax.map g ≅ app F.toLax x a :=
      (α_ _ _ _).symm ≪≫ whiskerRightIso (by simpa using (ρ_ (app F.toLax x a)))
        ((const (Comma.LaxSlice F.toLax x) (obj F.toLax x)).toLax.map g) ≪≫
        (by simpa using ρ_ (app F.toLax x a))
    exact Limits.IsInitial.ofIso (isInitial F x a) this.symm
  exact ⟨
    fun _ => app _ _ _,
    fun _ => (h _).to ((LaxFunctor.id _).map _ ≫ _),
    fun _ => by apply (h _).hom_ext,
    fun _ => by apply (h (𝟙 _)).hom_ext,
    fun _ _ => by apply (hcomp _ _).hom_ext⟩

@[simp]
theorem cone_app_self (F : B ⥤ᵖ C) (x : C) [hF : IsBiequivalence F.toLax] :
    (cone F x).app (obj F.toLax x) = 𝟙 (obj F.toLax x) := by simp

end LaxSlice.incLaxTerminal

/-- The lax slice `F ↓ X` has an inc-lax terminal object for `F` essentially surjective,
essentially full, and fully faithful. -/
@[simp]
noncomputable def LaxSlice.incLaxTerminal (F : B ⥤ᵖ C) (x : C) [hF : IsBiequivalence F.toLax] :
    IncLaxTerminal (LaxSlice.incLaxTerminal.obj F.toLax x) where
  cone := LaxSlice.incLaxTerminal.cone F x
  inc := ⟨fun X => by simpa using LaxSlice.incLaxTerminal.isInitial F x X⟩
  app_self_eq_id := LaxSlice.incLaxTerminal.cone_app_self F x

end IsBiequivalence
