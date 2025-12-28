/-
Copyright (c) 2025 Judah Towery. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judah Towery
-/

import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Lax
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/-!

# The oplax comma bicategory for a lax functor `F : A ⥤ᴸ T` and an oplax functor `G : B ⥤ᵒᵖᴸ T`.

* objects are triples `(a : A, b : B, φ : Fa ⟶ Gb)`;
* 1-cells are triples `(p : a₀ ⟶ a₁, q : b₀ ⟶ b₁, θ : Gq φ₀ ⟶ φ₁ Fp)`;
* 2-cells are pairs `(α : p ⟶ p', β : q ⟶ q')` that satisfy the generalized ice cream 
* cone condition.

Provides change-of-leg strict pseudofunctors. 
For lax functors `F H : A ⥤ᴸ T` with a lax natural transformation `η : H ⟶ F`, 
and oplax `G : B ⥤ᵒᵖᴸ T`,  the change-of-left-leg strict pseudofunctor 
`mapLeft.functor : Comma F G ⥤ᵖ Comma H G` is given

* on objects by `(a, b, φ) ↦ (a, b, φη(a))`;
* on 1-cells by `(p, q, θ) ↦ (p, q, θ')`,
* where `θ'` is given by the composite
* `Gq(φ₀η(a₀)) ⟶ (Gq φ₀)η(a₀) ⟶ (φ₁Fp)η(a₀) ⟶ φ₁(Fp η(a₀)) ⟶ φ₁(η(a₁)Hp) ⟶ (φ₁η(a₁))Hp`;
* on 2-cells by `(α, β) ↦ (α, β)`.

For a lax functor `F : A ⥤ᴸ T` and oplax `G H : B ⥤ᵒᵖᴸ T` with a lax natural transformation 
`η : G ⟶ H`, the change-of-right-leg strict pseudofunctor 
`mapRight.functor : Comma F G ⥤ᵖ Comma F H` is given

* on objects by `(a, b, φ : Fa ⟶ Gb) ↦ (a, b, η(b)φ)`;
* on 1-cells by `(p, q, θ) ↦ (p, q, θ')`,
* where `θ'` is given by the composite
* `Hq(η(b₀)φ₀) ⟶ (Hq η(b₀))φ₀ ⟶ (η(b₁)Gp)φ₀ ⟶ η(b₁)(Gp φ₀) ⟶ η(b₁)(φ₁Fp) ⟶ (η(b₁)φ₁)Fp`;
* on 2-cells by `(α, β) ↦ (α, β)`.

Specializes to the lax slice bicategory. For some `x : T`, with constant pseudofunctor `Δₓ`, 
the lax slice bicategory is `Comma F Δₓ`. Similarly the lax coslice bicategory is `Comma Δₓ G`.
Note that this lax slice not definitionally equal to the lax slice construction in Johnson-Yau
(e.g. the objects in Comma F Δₓ are triples, not pairs), but `Comma F Δₓ` and the Johnson-Yau
lax slice are still biequivalent (this is not proven here).

Specializes as well to the arrow bicategory: `Comma (𝟙 T) (𝟙 T)`.

Provides forgetful projection strict pseudofunctors from the oplax comma bicategory:
`projLeft : Comma F G ⥤ᵖ A` given

*on objects by `(a, b, φ) ↦ a`;
*on 1-cells by `(p, q, θ) ↦ p`;
*on 2-cells by `(α, β) ↦ α`.

Similarly `projRight : Comma F G ⥤ᵖ B` given

*on objects by `(a, b, φ) ↦ b`;
*on 1-cells by `(p, q, θ) ↦ q`;
*on 2-cells by `(α, β) ↦ β`.

If `F` and `G` are pseudofunctors, then we have an arrow projection pseudofunctor 
`projArrow : Comma F G ⥤ᵖ Arrow T` given

*on objects by `(a, b, φ) ↦ (Fa, Gb, φ)`;
*on 1-cells by `(p, q, θ) ↦ (Fp, Gq, θ)`;
*on 2-cells by `(α, β) ↦ (Fα, Gβ)`.

This is specialized from lax and oplax arrow projections for if only one of `F` or `G` are 
pseudofunctors: `laxProjArrow : Comma F G ⥤ᴸ Arrow T`, `oplaxProjArrow : Comma F G ⥤ᵒᵖᴸ Arrow T`.

-/

namespace CategoryTheory.Bicategory

open Category Bicategory

universe w w₁ w₂ w₃ v v₁ v₂ v₃

variable {A B T : Type*} [Bicategory.{w₁, v₁} A] [Bicategory.{w₂, v₂} B] [Bicategory.{w₃, v₃} T]

/-- Objects. -/
@[ext]
structure Comma (F : A ⥤ᴸ T) (G : B ⥤ᵒᵖᴸ T) where
  left : A
  right : B
  hom : F.obj left ⟶ G.obj right

namespace Comma

variable {F : A ⥤ᴸ T} {G : B ⥤ᵒᵖᴸ T}

/-- 1-cells. -/
@[ext]
structure Hom₁ (X Y : Comma F G) where
  left : X.left ⟶ Y.left
  right : X.right ⟶ Y.right
  f : X.hom ≫ G.map right ⟶ F.map left ≫ Y.hom

/-- For an object `(a, b, φ)`, the identity 1-cell is
`(𝟙a, 𝟙b, θ₁)` where `θ₁ : G(𝟙b) φ ⟶ φ F(𝟙a)` is given by the canonical composite
`G(𝟙b) φ ⟶ 𝟙(Gb) φ ⟶ φ ⟶ φ 𝟙(Fa) ⟶ φ F(𝟙a)`. -/
@[simps]
def id₁ (X : Comma F G) : Hom₁ X X where
  left := 𝟙 X.left
  right := 𝟙 X.right
  f := _ ◁ (G.mapId _) ≫ (ρ_ _).hom ≫ (λ_ _).inv ≫ (F.mapId _) ▷ _

/-- For two 1-cells `(p, q, θ) : (a₀, b₀, φ₀) ⟶ (a₁, b₁, φ₁)`,
`(p', q', θ') : (a₁, b₁, φ₁) ⟶ (a₂, b₂, φ₂)`, the composition `(p', q', θ) ∘ (p, q, θ)`
is given by `(p'p, q'q, θ'')`, where `θ'' : G(q'q)φ₀ ⟶ φ₂F(p'p)` is given by the canonical composite
`G(q'q)φ₀ ⟶ (Gq'Gq)φ₀ ⟶ Gq'(Gqφ₀) ⟶ Gq'(φ₁Fp) ⟶ (Gq'φ₁)Fp ⟶ (φ₂Fp')Fp ⟶ φ₂(Fp'Fp) ⟶ φ₂(Fp'p)`. -/
@[simps]
def comp₁ {X Y Z : Comma F G} (P : Hom₁ X Y) (Q : Hom₁ Y Z) : Hom₁ X Z where
  left := P.left ≫ Q.left
  right := P.right ≫ Q.right
  f := _ ◁ (G.mapComp _ _) ≫ (α_ _ _ _).inv ≫ P.f ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ Q.f ≫ (α_ _ _ _).inv ≫ 
    (F.mapComp _ _) ▷ _

/-- Underlying 1-CategoryStruct. -/
@[simps]
instance : CategoryStruct (Comma F G) where
  Hom X Y := Hom₁ X Y
  id X := id₁ X
  comp P Q := comp₁ P Q

/-- 2-cells. -/
@[ext]
structure Hom₂ {X Y : Comma F G} (P Q : X ⟶ Y) where
  left : P.left ⟶ Q.left
  right : P.right ⟶ Q.right
  icc : P.f ≫ (F.map₂ left ▷ Y.hom) = (X.hom ◁ G.map₂ right) ≫ Q.f := by cat_disch

/-- For a 1-cell `(p, q, θ)`, the identity 2-cell is `(𝟙p, 𝟙q)`. -/
@[simps]
def id₂ {X Y : Comma F G} (P : X ⟶ Y) : Hom₂ P P where
  left := 𝟙 _
  right := 𝟙 _

/- For two 2-cells `(α₀, β₀)`, (α₁, β₁)`, their composition is `(α₁α₀, β₁β₀)`. -/
@[simps]
def comp₂ {X Y : Comma F G} {P Q R : X ⟶ Y} (η : Hom₂ P Q) (θ : Hom₂ Q R) :
    Hom₂ P R where
  left := _ ≫ _
  right := _ ≫ _
  icc := by simp only [PrelaxFunctor.map₂_comp, comp_whiskerRight, whiskerLeft_comp, assoc]
            rw [←assoc, η.icc, ←θ.icc, assoc]

/-- Hom category on 1-cells. -/
@[simp]
instance {X Y : Comma F G} : Category (X ⟶ Y) where
  Hom P Q := Hom₂ P Q
  id P := id₂ P
  comp P Q := comp₂ P Q

/-- Left whiskering, given directly by the left whiskering on the base categories. -/
@[simps]
def whiskerLeft {X Y Z : Comma F G} (P : X ⟶ Y) {Q R : Y ⟶ Z} (η : Q ⟶ R) : P ≫ Q ⟶ P ≫ R where
  left := _ ◁ η.left
  right := _ ◁ _
  icc := by simp only [comp_def, comp₁_right, comp₁_left, comp₁_f, assoc]
            rw [←comp_whiskerRight]
            simp only [LaxFunctor.mapComp_naturality_right, comp_whiskerRight, whisker_assoc,
              assoc, Iso.inv_hom_id_assoc]
            rw [←assoc (F.map P.left ◁ Q.f), ←whiskerLeft_comp]
            simp only [η.icc, whiskerLeft_comp, assoc]
            rw [←assoc (X.hom ◁ G.map₂ (P.right ◁ η.right)), ←whiskerLeft_comp]
            simp only [OplaxFunctor.mapComp_naturality_right, whiskerLeft_comp, assoc]
            rw [←assoc (X.hom ◁ G.map P.right ◁ G.map₂ η.right), associator_inv_naturality_right,
              ←assoc ((α_ (F.map P.left) Y.hom (G.map Q.right)).hom), ←associator_naturality_right,
              assoc, assoc, ←assoc ((X.hom ≫ G.map P.right) ◁ G.map₂ η.right), whisker_exchange]
            simp

/-- Right whiskering, given directly by the right whiskering on the base categories. -/
@[simps]
def whiskerRight {X Y Z : Comma F G} {P Q : X ⟶ Y} (η : P ⟶ Q) (R : Y ⟶ Z) : P ≫ R ⟶ Q ≫ R where
  left := η.left ▷ _
  right := _ ▷ _
  icc := by simp only [comp_def, comp₁_right, comp₁_left, comp₁_f, assoc]
            rw [←comp_whiskerRight]
            simp only [LaxFunctor.mapComp_naturality_left, comp_whiskerRight]
            rw [←assoc ((α_ (F.map P.left) (F.map R.left) Z.hom).inv),
              ←associator_inv_naturality_left, ←assoc (X.hom ◁ G.map₂ (η.right ▷ R.right)),
              ←whiskerLeft_comp, OplaxFunctor.mapComp_naturality_left, whiskerLeft_comp, assoc,
              assoc, whisker_assoc_symm, assoc, assoc,
              ←assoc ((α_ X.hom (G.map Q.right) (G.map R.right)).hom), Iso.hom_inv_id, id_comp,
              ←assoc ((X.hom ◁ G.map₂ η.right) ▷ G.map R.right ), ←comp_whiskerRight, ←η.icc,
              comp_whiskerRight, assoc, ←assoc (F.map₂ η.left ▷ Y.hom ▷ G.map R.right),
              associator_naturality_left, ←assoc (F.map P.left ◁ R.f), whisker_exchange]
            simp

@[simps]
def associatorHom {X Y Z W : Comma F G} (P : X ⟶ Y) (Q : Y ⟶ Z) (R : Z ⟶ W) : 
    (P ≫ Q) ≫ R ⟶ P ≫ Q ≫ R where
  left := (α_ _ _ _).hom
  right := (α_ _ _ _).hom
  icc := by simp only [comp_def, comp₁_right, comp₁_left, comp₁_f, comp_whiskerRight, 
              whisker_assoc, assoc, Iso.inv_hom_id_assoc, whiskerLeft_comp]
            rw [←assoc (X.hom ◁ G.mapComp (P.right ≫ Q.right) R.right), ←whiskerLeft_comp, 
              OplaxFunctor.mapComp_assoc_left]
            simp only [whiskerLeft_comp, assoc, pentagon_inv_assoc]
            rw [←assoc (X.hom ◁ G.map P.right ◁ G.mapComp Q.right R.right), 
              associator_inv_naturality_right, assoc, 
              ←assoc ((α_ (X.hom ≫ G.map P.right) (G.map Q.right) (G.map R.right)).inv), 
              ←associator_inv_naturality_left, assoc, 
              ←assoc ((X.hom ≫ G.map P.right) ◁ G.mapComp Q.right R.right), whisker_exchange]
            simp only [comp_whiskerLeft, pentagon_inv_hom_hom_hom_inv_assoc, assoc, 
              Iso.inv_hom_id_assoc]
            rw [←assoc (F.mapComp P.left Q.left ▷ Z.hom ▷ G.map R.right), 
              associator_naturality_left, assoc, 
              ←assoc ((α_ (F.map P.left) (F.map Q.left ≫ Z.hom) (G.map R.right)).inv), 
              ←assoc ((α_ (F.map P.left) (F.map Q.left ≫ Z.hom) (G.map R.right)).inv ≫ 
               (α_ (F.map P.left) (F.map Q.left) Z.hom).inv ▷ G.map R.right), 
               assoc ((α_ (F.map P.left) (F.map Q.left ≫ Z.hom) (G.map R.right)).inv), 
               pentagon_inv_inv_hom_hom_inv, assoc, 
               ←assoc (F.mapComp P.left Q.left ▷ (Z.hom ≫ G.map R.right)), ←whisker_exchange]
            simp only [comp_whiskerLeft, whiskerRight_comp, assoc, Iso.hom_inv_id_assoc, 
              Iso.inv_hom_id_assoc]
            rw [←comp_whiskerRight, ←comp_whiskerRight]
            simp

@[simps]
def associatorInv {X Y Z W : Comma F G} (P : X ⟶ Y) (Q : Y ⟶ Z) (R : Z ⟶ W) :
    P ≫ Q ≫ R ⟶ (P ≫ Q) ≫ R where
  left := (α_ _ _ _).inv
  right := (α_ _ _ _).inv
  icc := by simp only [comp_def, comp₁_right, comp₁_left, comp₁_f, whiskerLeft_comp, assoc, 
              comp_whiskerRight, whisker_assoc, Iso.inv_hom_id_assoc]
            rw [←assoc (X.hom ◁ G.mapComp (P.right ≫ Q.right) R.right), ←whiskerLeft_comp, 
              OplaxFunctor.mapComp_assoc_left, 
              ←assoc (X.hom ◁ G.map₂ (α_ P.right Q.right R.right).inv), ←whiskerLeft_comp, 
              ←assoc (G.map₂ (α_ P.right Q.right R.right).inv), ←PrelaxFunctor.map₂_comp]
            simp only [Iso.inv_hom_id, PrelaxFunctor.map₂_id, id_comp, whiskerLeft_comp, 
              assoc, pentagon_inv_assoc]
            rw [←assoc (X.hom ◁ G.map P.right ◁ G.mapComp Q.right R.right), 
              associator_inv_naturality_right, assoc, 
              ←assoc (α_ (X.hom ≫ G.map P.right) (G.map Q.right) (G.map R.right)).inv, 
              ←associator_inv_naturality_left, 
              ←assoc ((α_ (F.map P.left) Y.hom (G.map (Q.right ≫ R.right))).hom),
              ←associator_naturality_right, assoc, ←assoc (P.f ▷ G.map (Q.right ≫ R.right)), 
              ←whisker_exchange]
            simp only [comp_whiskerLeft, whiskerRight_comp, assoc, 
              pentagon_hom_hom_inv_hom_hom_assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, comp_id]
            rw [←assoc (F.mapComp P.left Q.left ▷ Z.hom ▷ G.map R.right), 
              associator_naturality_left, assoc, 
              ←assoc ((α_ (F.map P.left) (F.map Q.left ≫ Z.hom) (G.map R.right)).inv), 
              ←assoc (((α_ (F.map P.left) (F.map Q.left ≫ Z.hom) (G.map R.right)).inv ≫ 
              (α_ (F.map P.left) (F.map Q.left) Z.hom).inv ▷ G.map R.right)), 
              assoc ((α_ (F.map P.left) (F.map Q.left ≫ Z.hom) (G.map R.right)).inv), 
              pentagon_inv_inv_hom_hom_inv, assoc, 
              ←assoc (F.mapComp P.left Q.left ▷ (Z.hom ≫ G.map R.right)), ←whisker_exchange]
            simp only [comp_whiskerLeft, whiskerRight_comp, assoc, Iso.hom_inv_id_assoc, 
              Iso.inv_hom_id_assoc]
            rw [←assoc ((α_ (F.map P.left ≫ F.map Q.left) (F.map R.left) W.hom).inv), 
              ←associator_inv_naturality_left, assoc, 
              ←assoc (F.map P.left ◁ F.mapComp Q.left R.left ▷ W.hom), 
              associator_inv_naturality_middle, assoc, 
              ←assoc ((F.map P.left ◁ F.mapComp Q.left R.left) ▷ W.hom), ←comp_whiskerRight, 
              LaxFunctor.mapComp_assoc_right, comp_whiskerRight, assoc, ←comp_whiskerRight, 
              assoc, assoc, ←PrelaxFunctor.map₂_comp]
            simp
            
/-- Associator, given directly by the associator on the base categories. -/
@[simps]
def associator {X Y Z W : Comma F G} (P : X ⟶ Y) (Q : Y ⟶ Z) (R : Z ⟶ W) : 
    (P ≫ Q) ≫ R ≅ P ≫ Q ≫ R where
  hom := associatorHom P Q R
  inv := associatorInv P Q R

@[simps]
def leftUnitorHom {X Y : Comma F G} (P : X ⟶ Y) : 𝟙 X ≫ P ⟶ P where
  left := _
  right := (λ_ _).hom
  icc := by simp only [id_def, comp_def, comp₁_right, id₁_right, comp₁_left, id₁_left, comp₁_f, 
              id₁_f, comp_whiskerRight, whisker_assoc, leftUnitor_inv_whiskerRight, assoc, 
              triangle_assoc_comp_right_assoc, Iso.inv_hom_id_assoc, OplaxFunctor.map₂_leftUnitor, 
              whiskerLeft_comp]
            rw [←assoc (F.mapId X.left ▷ X.hom ▷ G.map P.right), associator_naturality_left, assoc, 
              ←assoc ((α_ (𝟙 (F.obj X.left)) X.hom (G.map P.right)).inv), Iso.inv_hom_id, id_comp, 
              ←assoc (F.mapId X.left ▷ (X.hom ≫ G.map P.right)), ←whisker_exchange]
            simp only [id_whiskerLeft, whiskerRight_comp, assoc, Iso.hom_inv_id_assoc, 
              Iso.inv_hom_id_assoc]
            rw [←comp_whiskerRight, ←comp_whiskerRight, ←LaxFunctor.map₂_leftUnitor_hom]
            simp

@[simps]
def leftUnitorInv {X Y : Comma F G} (P : X ⟶ Y) : P ⟶ 𝟙 X ≫ P where
  left := (λ_ _).inv
  right := _
  icc := by simp only [id_def, comp_def, comp₁_left, id₁_left, LaxFunctor.map₂_leftUnitor, 
              comp_whiskerRight, leftUnitor_inv_whiskerRight, assoc, comp₁_right, id₁_right, 
              comp₁_f, id₁_f, whisker_assoc, triangle_assoc_comp_right_assoc, Iso.inv_hom_id_assoc]
            rw [←assoc (F.mapId X.left ▷ X.hom ▷ G.map P.right), associator_naturality_left, assoc, 
              ←assoc ((α_ (𝟙 (F.obj X.left)) X.hom (G.map P.right)).inv), Iso.inv_hom_id, id_comp, 
              ←assoc (F.mapId X.left ▷ (X.hom ≫ G.map P.right)), ←whisker_exchange]
            simp only [id_whiskerLeft, whiskerRight_comp, assoc, Iso.hom_inv_id_assoc, 
              Iso.inv_hom_id_assoc]
            rw [←assoc (X.hom ◁ G.mapComp (𝟙 X.right) P.right), ←whiskerLeft_comp, 
              ←assoc (X.hom ◁ (G.mapComp (𝟙 X.right) P.right ≫ G.mapId X.right ▷ G.map P.right)), 
              ←whiskerLeft_comp, assoc, ←OplaxFunctor.map₂_leftUnitor, 
              ←assoc (X.hom ◁ G.map₂ (λ_ P.right).inv), ←whiskerLeft_comp, ←PrelaxFunctor.map₂_comp]
            simp
            
/-- Left unitor, given directly by the left unitor on the base categories. -/
@[simps]
def leftUnitor {X Y : Comma F G} (P : X ⟶ Y) : 𝟙 X ≫ P ≅ P where
  hom := leftUnitorHom P
  inv := leftUnitorInv P

@[simps]
def rightUnitorHom {X Y : Comma F G} (P : X ⟶ Y) : P ≫ 𝟙 Y ⟶ P where
  left := _
  right := (ρ_ _).hom
  icc := by simp only [id_def, comp_def, comp₁_right, id₁_right, comp₁_left, id₁_left, comp₁_f, 
              id₁_f, whiskerLeft_comp, whiskerLeft_rightUnitor, assoc, 
              OplaxFunctor.map₂_rightUnitor]
            rw [←assoc (F.map P.left ◁ Y.hom ◁ G.mapId Y.right), associator_inv_naturality_right, 
              assoc, ←assoc ((α_ (F.map P.left) Y.hom (G.map (𝟙 Y.right))).hom), Iso.hom_inv_id, 
              id_comp, ←assoc (P.f ▷ G.map (𝟙 Y.right)), ←whisker_exchange]
            simp only [comp_whiskerLeft, whiskerRight_id, assoc, Iso.inv_hom_id_assoc]
            rw [←assoc (F.map P.left ◁ F.mapId Y.left ▷ Y.hom), associator_inv_naturality_middle, 
            assoc, ←comp_whiskerRight, ←comp_whiskerRight, ←LaxFunctor.map₂_rightUnitor_hom]
            simp

@[simps]
def rightUnitorInv {X Y : Comma F G} (P : X ⟶ Y) : P ⟶ P ≫ 𝟙 Y where
  left := (ρ_ _).inv
  right := _
  icc := by simp only [id_def, comp_def, comp₁_left, id₁_left, LaxFunctor.map₂_rightUnitor, 
              comp_whiskerRight, whisker_assoc, assoc, triangle_assoc_comp_right_inv_assoc, 
              comp₁_right, id₁_right, comp₁_f, id₁_f, whiskerLeft_comp, whiskerLeft_rightUnitor]
            rw [←assoc (F.map P.left ◁ Y.hom ◁ G.mapId Y.right), associator_inv_naturality_right, 
              assoc, ←assoc ((α_ (F.map P.left) Y.hom (G.map (𝟙 Y.right))).hom), Iso.hom_inv_id, 
              id_comp, ←assoc (P.f ▷ G.map (𝟙 Y.right)), ←whisker_exchange]
            simp only [comp_whiskerLeft, whiskerRight_id, assoc, Iso.inv_hom_id_assoc]
            rw [rightUnitor_comp, assoc, 
              ←assoc ((α_ X.hom (G.map P.right) (𝟙 (G.obj Y.right))).inv), Iso.inv_hom_id, id_comp, 
              ←assoc (X.hom ◁ G.mapComp P.right (𝟙 Y.right)), ←whiskerLeft_comp, 
              ←assoc (X.hom ◁ (G.mapComp P.right (𝟙 Y.right) ≫ G.map P.right ◁ G.mapId Y.right)), 
              ←whiskerLeft_comp, assoc, ←OplaxFunctor.map₂_rightUnitor, 
              ←assoc (X.hom ◁ G.map₂ (ρ_ P.right).inv), ←whiskerLeft_comp, ←PrelaxFunctor.map₂_comp]
            simp 

/-- Right unitor, given directly by the right unitor on the base categories. -/
@[simps]
def rightUnitor {X Y : Comma F G} (P : X ⟶ Y) : P ≫ 𝟙 Y ≅ P where
  hom := rightUnitorHom P
  inv := rightUnitorInv P

/-- Comma bicategory. -/
@[simp]
instance : Bicategory (Comma F G) where
  whiskerLeft P _ _ η := whiskerLeft P η
  whiskerRight η R := whiskerRight η R
  associator P Q R := associator P Q R
  leftUnitor P := leftUnitor P
  rightUnitor P := rightUnitor P
  whisker_exchange η θ := by simp only [instCategoryHom, comp_def]
                             ext
                             all_goals simp [whisker_exchange]

@[simp]
lemma eqToHom_left {X Y : Comma F G} {P Q : X ⟶ Y} (e : P = Q) : 
    (eqToHom e).left = eqToHom (congrArg Hom₁.left e) := by
  cases e
  simp

@[simp]
lemma eqToHom_right {X Y : Comma F G} {P Q : X ⟶ Y} (e : P = Q) : 
    (eqToHom e).right = eqToHom (congrArg Hom₁.right e) := by
  cases e
  simp

namespace mapLeft

variable {H : A ⥤ᴸ T} (η : Lax.LaxTrans H F)

/-- Action of the change-of-left-leg functor on objects. -/
@[simps]
def obj (X : Comma F G) : Comma H G where 
  left := X.left 
  right := X.right 
  hom := η.app _ ≫ X.hom

/-- Action of the change-of-left-leg functor on 1-cells. -/
@[simps]
def map {X Y : Comma F G} (P : X ⟶ Y) : obj η X ⟶ obj η Y where 
  left := P.left 
  right := P.right 
  f := (α_ _ _ _).hom ≫ _ ◁ P.f ≫ (α_ _ _ _).inv ≫ η.naturality _ ▷ _ ≫ (α_ _ _ _).hom

/-- Action of the change-of-left-leg functor on 2-cells. -/
@[simps]
def map₂ {X Y : Comma F G} {P Q : X ⟶ Y} (θ : P ⟶ Q) : map η P ⟶ map η Q where 
  left := θ.left 
  right := θ.right 
  icc := by simp only [obj_left, obj_right, obj_hom, map_right, map_left, map_f, whiskerRight_comp, 
              assoc, Iso.hom_inv_id_assoc, comp_whiskerLeft, Iso.inv_hom_id_assoc, 
              Iso.cancel_iso_hom_left]
            rw [←assoc (η.naturality P.left ▷ Y.hom), ←comp_whiskerRight, 
              Lax.LaxTrans.naturality_naturality]
            simp only [comp_whiskerRight, whisker_assoc, assoc, Iso.inv_hom_id_assoc]
            rw [←assoc (η.app X.left ◁ P.f), ←whiskerLeft_comp, θ.icc] 
            simp

@[simp]
theorem map_id (X : Comma F G) : map η (𝟙 X) = 𝟙 (obj η X) := by
  simp only [id_def]
  apply Hom₁.ext
  all_goals simp only [obj_left, obj_right, obj_hom, map_right, id₁_right, map_left, 
    id₁_left, map_f, id₁_f, whiskerLeft_comp, whiskerLeft_rightUnitor, assoc, 
    comp_whiskerLeft, whiskerRight_comp, heq_eq_eq, Iso.cancel_iso_hom_left]
  rw [←assoc (η.app X.left ◁ F.mapId X.left ▷ X.hom), associator_inv_naturality_middle, assoc, 
    ←assoc ((η.app X.left ◁ F.mapId X.left) ▷ X.hom), ←comp_whiskerRight, 
    Lax.LaxTrans.naturality_id]
  simp

@[simp]
theorem map_comp {X Y Z : Comma F G} (P : X ⟶ Y) (Q : Y ⟶ Z) : 
    map η (P ≫ Q) = map η P ≫ map η Q := by
  simp only [Comma.comp_def]
  apply Hom₁.ext
  all_goals simp only [obj_left, obj_right, obj_hom, map_right, comp₁_right, map_left, 
    comp₁_left, map_f, comp₁_f, whiskerLeft_comp, assoc, comp_whiskerLeft, 
    comp_whiskerRight, whisker_assoc, whiskerRight_comp,
    pentagon_hom_inv_inv_inv_inv_assoc, pentagon_assoc, pentagon_inv_hom_hom_hom_inv_assoc, 
    Iso.inv_hom_id_assoc, heq_eq_eq, Iso.cancel_iso_hom_left]
  rw [←assoc (η.app X.left ◁ F.mapComp P.left Q.left ▷ Z.hom), associator_inv_naturality_middle, 
    assoc, ←assoc ((η.app X.left ◁ F.mapComp P.left Q.left) ▷ Z.hom), ←comp_whiskerRight, 
    Lax.LaxTrans.naturality_comp]
  simp only [comp_whiskerRight, whisker_assoc, assoc, pentagon_inv_assoc]
  rw [←assoc (η.app X.left ◁ F.map P.left ◁ Q.f), associator_inv_naturality_right, assoc, 
    ←assoc (η.naturality P.left ▷ Y.hom ▷ G.map Q.right), 
    associator_naturality_left (η.naturality P.left), assoc, 
    ←assoc ((α_ (η.app X.left) (F.map P.left ≫ Y.hom) (G.map Q.right)).inv), 
    ←assoc ((α_ (η.app X.left) (F.map P.left ≫ Y.hom) (G.map Q.right)).inv ≫ 
    (α_ (η.app X.left) (F.map P.left) Y.hom).inv ▷ G.map Q.right), 
    assoc ((α_ (η.app X.left) (F.map P.left ≫ Y.hom) (G.map Q.right)).inv), 
    pentagon_inv_inv_hom_hom_inv, assoc, 
    ←assoc ((α_ (η.app X.left ≫ F.map P.left) (F.map Q.left) Z.hom).inv), 
    ←associator_inv_naturality_left, assoc, ←assoc ((η.app X.left ≫ F.map P.left) ◁ Q.f), 
    whisker_exchange]
  simp

@[simps]
def core : StrictPseudofunctorCore (Comma F G) (Comma H G) where
  obj := obj η
  map := map η
  map₂ := map₂ η
  map_id := map_id η
  map_comp := map_comp η

end mapLeft

/-- The change-of-left-leg strict pseudofunctor. -/
@[simps!]
def mapLeft {H : A ⥤ᴸ T} (η : Lax.LaxTrans H F) : StrictPseudofunctor (Comma F G) (Comma H G) := 
  StrictPseudofunctor.mk' (mapLeft.core η)

namespace mapRight

variable {H : B ⥤ᵒᵖᴸ T} (η : Oplax.LaxTrans G H)

/-- Action of the change-of-right-leg functor on objects. -/
@[simps]
def obj (X : Comma F G) : Comma F H where 
  left := X.left 
  right := X.right 
  hom := X.hom ≫ η.app _

/-- Action of the change-of-right-leg functor on 1-cells. -/
@[simps]
def map {X Y : Comma F G} (P : X ⟶ Y) : obj η X ⟶ obj η Y where 
  left := P.left 
  right := P.right 
  f := (α_ _ _ _).hom ≫ _ ◁ η.naturality _ ≫ (α_ _ _ _).inv ≫ P.f ▷ _ ≫ (α_ _ _ _).hom

/-- Action of the change-of-right-leg functor on 2-cells. -/
@[simps]
def map₂ {X Y : Comma F G} {P Q : X ⟶ Y} (θ : P ⟶ Q) : map η P ⟶ map η Q where 
  left := θ.left 
  right := θ.right 
  icc := by simp only [obj_left, obj_right, obj_hom, map_right, map_left, map_f, whiskerRight_comp, 
              assoc, Iso.hom_inv_id_assoc, comp_whiskerLeft, Iso.inv_hom_id_assoc, 
              Iso.cancel_iso_hom_left]
            rw [←assoc (X.hom ◁ η.app X.right ◁ H.map₂ θ.right), ←whiskerLeft_comp, 
              ←Oplax.LaxTrans.naturality_naturality, whiskerLeft_comp, assoc, 
              ←assoc (X.hom ◁ G.map₂ θ.right ▷ η.app Y.right), associator_inv_naturality_middle, 
              assoc, ←assoc (P.f ▷ η.app Y.right), ←comp_whiskerRight, θ.icc]
            simp

@[simp]
theorem map_id (X : Comma F G) : map η (𝟙 X) = 𝟙 (obj η X) := by
  simp only [id_def]
  apply Hom₁.ext
  all_goals simp only [obj_left, obj_right, obj_hom, map_right, id₁_right, map_left, id₁_left, 
    map_f, id₁_f, comp_whiskerRight, whisker_assoc, leftUnitor_inv_whiskerRight, assoc, 
    triangle_assoc_comp_right_assoc, Iso.inv_hom_id_assoc, comp_whiskerLeft, whiskerRight_comp, 
    heq_eq_eq, Iso.cancel_iso_hom_left]
  rw [←assoc (X.hom ◁ η.naturality (𝟙 X.right)), ←whiskerLeft_comp, Oplax.LaxTrans.naturality_id]
  simp

@[simp]
theorem map_comp {X Y Z : Comma F G} (P : X ⟶ Y) (Q : Y ⟶ Z) : 
    map η (P ≫ Q) = map η P ≫ map η Q := by
  simp only [comp_def]
  apply Hom₁.ext
  all_goals simp only [obj_left, obj_right, obj_hom, map_right, comp₁_right, map_left, comp₁_left, 
    map_f, comp₁_f, comp_whiskerRight, whisker_assoc, assoc, Iso.inv_hom_id_assoc, 
    comp_whiskerLeft, whiskerLeft_comp, whiskerRight_comp, pentagon_hom_inv_inv_inv_inv_assoc, 
    pentagon_assoc, pentagon_inv_hom_hom_hom_inv_assoc, heq_eq_eq, Iso.cancel_iso_hom_left]
  rw [←assoc (X.hom ◁ η.naturality (P.right ≫ Q.right)), ←whiskerLeft_comp, 
    Oplax.LaxTrans.naturality_comp]
  simp only [whiskerLeft_comp, assoc, pentagon_inv_assoc]
  rw [←assoc (X.hom ◁ G.map P.right ◁ η.naturality Q.right), associator_inv_naturality_right, 
    assoc, ←assoc (P.f ▷ η.app Y.right ▷ H.map Q.right), associator_naturality_left P.f, assoc, 
    ←assoc ((α_ X.hom (G.map P.right ≫ η.app Y.right) (H.map Q.right)).inv), 
    ←assoc ((α_ X.hom (G.map P.right ≫ η.app Y.right) (H.map Q.right)).inv ≫ 
    (α_ X.hom (G.map P.right) (η.app Y.right)).inv ▷ H.map Q.right), 
    assoc ((α_ X.hom (G.map P.right ≫ η.app Y.right) (H.map Q.right)).inv), 
    pentagon_inv_inv_hom_hom_inv, assoc, 
    ←assoc ((α_ (X.hom ≫ G.map P.right) (G.map Q.right) (η.app Z.right)).inv), 
    ←associator_inv_naturality_left, assoc, 
    ←assoc ((X.hom ≫ G.map P.right) ◁ η.naturality Q.right), whisker_exchange]
  simp

@[simps]
def core : StrictPseudofunctorCore (Comma F G) (Comma F H) where
  obj := obj η
  map := map η
  map₂ := map₂ η
  map_id := map_id η
  map_comp := map_comp η

end mapRight

/-- The change-of-right-leg strict pseudofunctor -/
@[simps!]
def mapRight {H : B ⥤ᵒᵖᴸ T} (η : Oplax.LaxTrans G H) : StrictPseudofunctor (Comma F G) (Comma F H) 
    := StrictPseudofunctor.mk' (mapRight.core η)

/- 
@[simps!]
abbrev mapLeftMapRight {H : A ⥤ᴸ T} {K : B ⥤ᵒᵖᴸ T} (η : Lax.LaxTrans H F)
    (θ : Oplax.LaxTrans G K) : Pseudofunctor (Comma F G) (Comma H K) := 
  ((mapLeft η).comp (mapRight θ)).toPseudofunctor

@[simps!]
abbrev mapRightMapLeft {H : A ⥤ᴸ T} {K : B ⥤ᵒᵖᴸ T} (θ : Oplax.LaxTrans G K)
    (η : Lax.LaxTrans H F) : Pseudofunctor (Comma F G) (Comma H K) :=
  ((mapRight θ).comp (mapLeft η)).toPseudofunctor

namespace mapLeftMapRight

variable {H : A ⥤ᴸ T} {K : B ⥤ᵒᵖᴸ T} (η : Lax.LaxTrans H F) (θ : Oplax.LaxTrans G K)

open scoped Pseudofunctor.StrongTrans

@[simps]
def interchangeHom : mapLeftMapRight η θ ⟶ mapRightMapLeft θ η where
  app X := {
    left := 𝟙 _
    right := 𝟙 _
    f := _ ◁ (K.mapId _) ≫ (ρ_ _).hom ≫ (α_ _ _ _).hom ≫ (λ_ _).inv ≫ (H.mapId _) ▷ _ }
  naturality {X Y} P := {
    hom := {
      left := (ρ_ _).hom ≫ (λ_ _).inv
      right := (ρ_ _).hom ≫ (λ_ _).inv
      icc := by sorry }  -- yikes!
    inv := {
      left := (λ_ _).hom ≫ (ρ_ _).inv
      right := (λ_ _).hom ≫ (ρ_ _).inv
      icc := by sorry } }

@[simps]
def interchangeInv : mapRightMapLeft θ η ⟶ mapLeftMapRight η θ where
  app X := {
    left := 𝟙 X.left
    right := 𝟙 X.right
    f := _ ◁ (K.mapId _) ≫ (ρ_ _).hom ≫ (α_ _ _ _).inv ≫ (λ_ _).inv ≫ (H.mapId _) ▷ _ }
  naturality P := {
    hom := {
      left := (ρ_ _).hom ≫ (λ_ _).inv
      right := (ρ_ _).hom ≫ (λ_ _).inv
      icc := by sorry }
    inv := {
      left := (λ_ _).hom ≫ (ρ_ _).inv
      right := (λ_ _).hom ≫ (ρ_ _).inv
      icc := by sorry } }

def interchangeUnit : 𝟙 (mapLeftMapRight η θ) ≅ interchangeHom η θ ≫ interchangeInv η θ where
  hom := {
    as := {
      app X := {
        left := (ρ_ _).inv
        right := (ρ_ _).inv
        icc := by sorry } } }
  inv := {
    as := {
      app X := {
        left := (ρ_ _).hom
        right := (ρ_ _).hom
        icc := by sorry } } }

def interchangeCounit : interchangeInv η θ ≫ interchangeHom η θ ≅ 𝟙 (mapRightMapLeft θ η) where
  hom := {
    as := {
      app X := {
        left := (ρ_ _).hom
        right := (ρ_ _).hom
        icc := by sorry } } }
  inv := {
    as := {
      app X := {
        left := (ρ_ _).inv
        right := (ρ_ _).inv
        icc := by sorry } } }

/-- The middle four interchange between the change-of-left-leg and change-of-right-leg. -/
def interchange : mapLeftMapRight η θ ≌ mapRightMapLeft θ η := 
  Equivalence.mkOfAdjointifyCounit (interchangeUnit η θ) (interchangeCounit η θ)

end mapLeftMapRight -/

/-- Constant pseudofunctor at `x`. 
Refactor this with a separate `const` functor like on 1-categories. -/
@[simps]
def fromPUnit (x : T) : Pseudofunctor (LocallyDiscrete (Discrete PUnit)) T where
  obj := _
  map _ := _
  map₂ _ := _
  mapId _ := Iso.refl _
  mapComp _ _ := (ρ_ _).symm

/-- A 1-cell `f : x ⟶ y` in `T` induces a strong natural transformation
`fromPUnit x ⟶ fromPUnit y`. -/
@[simps]
def homStrongTrans {x y : T} (f : x ⟶ y) : 
    Pseudofunctor.StrongTrans (fromPUnit x) (fromPUnit y) where
  app := _
  naturality _ := (λ_ _) ≪≫ (ρ_ f).symm

/-- The lax slice bicategory. -/
@[simp]
abbrev LaxSlice (x : T) := Comma F (fromPUnit x).toOplax

/-- The lax coslice bicategory. -/
@[simp]
abbrev LaxCoslice (x : T) := Comma (fromPUnit x).toLax G

/-- The underlying lax natural transformation of an oplax strong natural transformation 
(can go to NaturalTransformation/Oplax.lean) -/
@[simps]
def toLax {F G : A ⥤ᵒᵖᴸ B} (η : Oplax.StrongTrans F G) : Oplax.LaxTrans F G where
  app := _
  naturality _ := (η.naturality _).inv
  naturality_naturality _ := by simp [←Iso.cancel_iso_hom_right _ _ (η.naturality _)]
  naturality_id _ := by simp [←Iso.cancel_iso_hom_left (η.naturality _) _ _]
  naturality_comp _ _ := by simp [←Iso.cancel_iso_hom_left (η.naturality _) _ _]

/-- The strong transformation of lax functors induced by a strong transformation of
pseudofunctors. 
(can go to NaturalTransformation/Pseudo.lean) -/
@[simps]
def toLax₂ {F G : A ⥤ᵖ B} (η : Pseudofunctor.StrongTrans F G) : 
    Lax.StrongTrans F.toLax G.toLax where
  app := _
  naturality _ := (η.naturality _).symm
  naturality_naturality _ := by simp [←Iso.cancel_iso_hom_right _ _ (η.naturality _)]
  naturality_id _ := by simp [←Iso.cancel_iso_hom_left (whiskerLeftIso (η.app _) (G.mapId _)) _ _, 
    ←Iso.cancel_iso_hom_left (η.naturality _) _ _]
  naturality_comp _ _ := by simp 
    [←Iso.cancel_iso_hom_right _ _ (whiskerLeftIso (η.app _) (G.mapComp _ _)), 
    ←Iso.cancel_iso_hom_right _ _ (η.naturality _)]

/-- The change-of-slice strict pseudofunctor. -/
@[simps!]
abbrev mapRightSlice {x y : T} (f : x ⟶ y) : 
    StrictPseudofunctor (LaxSlice (F := F) x) (LaxSlice (F := F) y) := 
  mapRight (toLax (homStrongTrans f).toOplax)

/-- The change-of-coslice strict pseudofunctor. -/
@[simps!]
abbrev mapLeftCoslice {x y : T} (f : y ⟶ x) :
    StrictPseudofunctor (LaxCoslice (G := G) x) (LaxCoslice (G := G) y) := 
  mapLeft (toLax₂ (homStrongTrans f)).toLax

/-- The arrow bicategory. -/
@[simp]
abbrev Arrow (B : Type*) [Bicategory.{w, v} B] := Comma (LaxFunctor.id B) (OplaxFunctor.id B)

@[simps]
def projLeftCore : StrictPseudofunctorCore (Comma F G) A where
  obj := _
  map := _
  map₂ η := η.left

/-- The left projection strict pseudofunctor. -/
@[simps!]
def projLeft : StrictPseudofunctor (Comma F G) A := StrictPseudofunctor.mk' projLeftCore

@[simps]
def projRightCore : StrictPseudofunctorCore (Comma F G) B where
  obj := _
  map := _
  map₂ η := η.right

/-- The right projection strict pseudofunctor. -/
@[simps!]
def projRight : StrictPseudofunctor (Comma F G) B := StrictPseudofunctor.mk' projRightCore

/-- The arrow projection lax functor, for `G` a pseudofunctor. 
Note that we need at least `G` to be a pseudofunctor for this to make sense.
e.g. for `mapId`, we need the right 2-cell component to be `𝟙 (G.obj X.right) ⟶ G.map (𝟙 X.right)`, which is the opposite mapping from `G` if it were merely oplax. -/
@[simps]
def laxProjArrow {G : B ⥤ᵖ T} : Comma F G.toOplax ⥤ᴸ Arrow T where
  obj X := {
    left := F.obj X.left
    right := G.obj X.right
    hom := X.hom }
  map P := {
    left := F.map P.left
    right := G.map P.right
    f := P.f }
  map₂ η := {
    left := F.map₂ η.left
    right := G.map₂ η.right
    icc := by simp [η.icc] }
  mapId X := {
    left := F.mapId _
    right := (G.mapId _).inv }
  mapComp P Q := {
    left := F.mapComp _ _
    right := (G.mapComp _ _).inv }
  map₂_leftUnitor P := by simp
                          ext
                          all_goals simp
                          have := G.map₂_left_unitor P.right
                          

end Comma
