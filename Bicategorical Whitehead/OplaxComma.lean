/-
Copyright (c) 2025 Judah Towery. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judah Towery
-/

import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Lax
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Oplax
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor

/-!

# The oplax comma bicategory for a lax functor `F : A ⥤ᴸ T` and an oplax functor `G : B ⥤ᵒᵖᴸ T`.

* objects are triples `(a : A, b : B, φ : Fa ⟶ Gb)`
* 1-cells are triples `(p : a₀ ⟶ a₁, q : b₀ ⟶ b₁, θ : Gq φ₀ ⟶ φ₁ Fp)`
* 2-cells are pairs `(α : p ⟶ p', β : q ⟶ q')` that satisfy the generalized ice cream 
* cone condition.

Provides as well change-of-leg strict pseudofunctors. 
For lax functors `F H : A ⥤ᴸ T` with a lax natural transformation `η : H ⟶ F`, 
and oplax `G : B ⥤ᵒᵖᴸ T`,  the change-of-left-leg strict pseudofunctor `Comma F G ⥤ᵖ Comma H G` 
is given

* on objects by `(a, b, φ) ↦ (a, b, φη(a))`
* on 1-cells by `(p, q, θ) ↦ (p, q, θ')`,
* where `θ'` is given by the composite
* `Gq(φ₀η(a₀)) ⟶ (Gq φ₀)η(a₀) ⟶ (φ₁Fp)η(a₀) ⟶ φ₁(Fp η(a₀)) ⟶ φ₁(η(a₁)Hp) ⟶ (φ₁η(a₁))Hp`
* on 2-cells by `(α, β) ↦ (α, β)`.

For a lax functor `F : A ⥤ᴸ T` and oplax `G H : B ⥤ᵒᵖᴸ T` with a lax natural transformation 
`η : G ⟶ H`, the change-of-right-leg strict pseudofunctor `Comma F G ⥤ᵖ Comma F H` is given

* on objects by `(a, b, φ : Fa ⟶ Gb) ↦ (a, b, η(b)φ)`
* on 1-cells by `(p, q, θ) ↦ (p, q, θ')`,
* where `θ'` is given by the composite
* `Hq(η(b₀)φ₀) ⟶ (Hq η(b₀))φ₀ ⟶ (η(b₁)Gp)φ₀ ⟶ η(b₁)(Gp φ₀) ⟶ η(b₁)(φ₁Fp) ⟶ (η(b₁)φ₁)Fp`
* on 2-cells by `(α, β) ↦ (α, β)`.

-/

namespace CategoryTheory.Bicategory

open Category Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃

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
  f := X.hom ◁ (G.mapId X.right) ≫ (ρ_ X.hom).hom ≫ (λ_ X.hom).inv ≫ (F.mapId X.left) ▷ X.hom

/-- For two 1-cells `(p, q, θ) : (a₀, b₀, φ₀) ⟶ (a₁, b₁, φ₁)`,
`(p', q', θ') : (a₁, b₁, φ₁) ⟶ (a₂, b₂, φ₂)`, the composition `(p', q', θ) ∘ (p, q, θ)`
is given by `(p'p, q'q, θ'')`, where `θ'' : G(q'q)φ₀ ⟶ φ₂F(p'p)` is given by the canonical composite
`G(q'q)φ₀ ⟶ (Gq'Gq)φ₀ ⟶ Gq'(Gqφ₀) ⟶ Gq'(φ₁Fp) ⟶ (Gq'φ₁)Fp ⟶ (φ₂Fp')Fp ⟶ φ₂(Fp'Fp) ⟶ φ₂(Fp'p)`. -/
@[simps]
def comp₁ {X Y Z : Comma F G} (P : Hom₁ X Y) (Q : Hom₁ Y Z) : Hom₁ X Z where
  left := P.left ≫ Q.left
  right := P.right ≫ Q.right
  f := X.hom ◁ (G.mapComp P.right Q.right) ≫ (α_ X.hom (G.map P.right) (G.map Q.right)).inv
         ≫ P.f ▷ (G.map Q.right) ≫ (α_ (F.map P.left) Y.hom (G.map Q.right)).hom 
         ≫ (F.map P.left) ◁ Q.f ≫ (α_ (F.map P.left) (F.map Q.left) Z.hom).inv 
         ≫ (F.mapComp P.left Q.left) ▷ Z.hom

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
  left := 𝟙 P.left
  right := 𝟙 P.right

/- For two 2-cells `(α₀, β₀)`, (α₁, β₁)`, their composition is `(α₁α₀, β₁β₀)`. -/
@[simps]
def comp₂ {X Y : Comma F G} {P Q R : X ⟶ Y} (η : Hom₂ P Q) (θ : Hom₂ Q R) :
    Hom₂ P R where
  left := η.left ≫ θ.left
  right := η.right ≫ θ.right
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
  left := P.left ◁ η.left
  right := P.right ◁ η.right
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
  left := η.left ▷ R.left
  right := η.right ▷ R.right
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
  left := (α_ P.left Q.left R.left).hom
  right := (α_ P.right Q.right R.right).hom
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
  left := (α_ P.left Q.left R.left).inv
  right := (α_ P.right Q.right R.right).inv
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
  left := (λ_ P.left).hom
  right := (λ_ P.right).hom
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
  left := (λ_ P.left).inv
  right := (λ_ P.right).inv
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
  left := (ρ_ P.left).hom
  right := (ρ_ P.right).hom
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
  left := (ρ_ P.left).inv
  right := (ρ_ P.right).inv
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
                             · simp only [comp₁_left, comp₂_left, whiskerLeft_left, 
                               whiskerRight_left]
                               rw [whisker_exchange]
                             simp only [comp₁_right, comp₂_right, whiskerLeft_right, 
                               whiskerRight_right]
                             rw [whisker_exchange]

@[simp]
theorem eqToHom_left {X Y : Comma F G} {P Q : X ⟶ Y} (e : P = Q) : 
    (eqToHom e).left = eqToHom (congrArg Hom₁.left e) := by
  cases e
  simp

@[simp]
theorem eqToHom_right {X Y : Comma F G} {P Q : X ⟶ Y} (e : P = Q) : 
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
  hom := (η.app X.left ≫ X.hom)

/-- Action of the change-of-left-leg functor on 1-cells. -/
@[simps]
def map {X Y : Comma F G} (P : X ⟶ Y) : (obj η X ⟶ obj η Y) where 
  left := P.left 
  right := P.right 
  f := ((α_ (η.app X.left) X.hom (G.map P.right)).hom ≫ (η.app X.left) ◁ P.f ≫ 
    (α_ (η.app X.left) (F.map P.left) Y.hom).inv ≫ (η.naturality P.left) ▷ Y.hom ≫ 
    (α_ (H.map P.left) (η.app Y.left) Y.hom).hom)

/-- Action of the change-of-left-leg functor on 2-cells. -/
@[simps]
def map₂ {X Y : Comma F G} {P Q : X ⟶ Y} (θ : P ⟶ Q) : (map η P ⟶ map η Q) where 
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
  all_goals simp only [obj_left, obj_right, obj_hom, map_right, Comma.id₁_right, map_left, 
    Comma.id₁_left, map_f, Comma.id₁_f, whiskerLeft_comp, whiskerLeft_rightUnitor, assoc, 
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
  all_goals simp only [obj_left, obj_right, obj_hom, map_right, Comma.comp₁_right, map_left, 
    Comma.comp₁_left, map_f, Comma.comp₁_f, whiskerLeft_comp, assoc, comp_whiskerLeft, 
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

@[simp]
theorem map₂_whisker_left {X Y Z : Comma F G} (P : X ⟶ Y) {Q R : Y ⟶ Z} (θ : Q ⟶ R) : 
    map₂ η (P ◁ θ) = eqToHom (map_comp η P Q) ≫ map η P ◁ map₂ η θ 
    ≫ eqToHom (map_comp η P R).symm := by
  simp only [Comma.instCategoryHom, Comma.inst, Comma.comp_def]
  ext
  · simp only [obj_left, map_left, Comma.comp₁_left, map₂_left, Comma.whiskerLeft_left, 
      Comma.comp₂_left]
    rw [Comma.eqToHom_left, Comma.eqToHom_left]
    simp
  simp only [obj_right, map_right, Comma.comp₁_right, map₂_right, Comma.whiskerLeft_right, 
    Comma.comp₂_right]
  rw [Comma.eqToHom_right, Comma.eqToHom_right]
  simp
  
@[simp]
theorem map₂_whisker_right {X Y Z : Comma F G} {P Q : X ⟶ Y} (θ : P ⟶ Q) (R : Y ⟶ Z) : 
    map₂ η (θ ▷ R) = eqToHom (map_comp η P R) ≫ map₂ η θ ▷ map η R 
    ≫ eqToHom (map_comp η Q R).symm := by
  simp only [Comma.instCategoryHom, Comma.inst, Comma.comp_def]
  ext
  · simp only [obj_left, map_left, Comma.comp₁_left, map₂_left, Comma.whiskerRight_left, 
      Comma.comp₂_left]
    rw [Comma.eqToHom_left, Comma.eqToHom_left]
    simp
  simp only [obj_right, map_right, Comma.comp₁_right, map₂_right, Comma.whiskerRight_right, 
    Comma.comp₂_right]
  rw [Comma.eqToHom_right, Comma.eqToHom_right]
  simp

@[simp]
theorem map₂_left_unitor {X Y : Comma F G} (P : X ⟶ Y) : 
    map₂ η (λ_ P).hom = eqToHom (by rw [map_comp η (𝟙 X) P, map_id η X]) ≫ (λ_ (map η P)).hom := by
  simp only [Comma.instCategoryHom, Comma.inst, Comma.id_def, Comma.comp_def, 
    Comma.leftUnitor_hom]
  ext
  · simp only [obj_left, map_left, Comma.comp₁_left, Comma.id₁_left, map₂_left, 
      Comma.leftUnitorHom_left, Comma.comp₂_left]
    rw [Comma.eqToHom_left]
    simp
  simp only [obj_right, map_right, Comma.comp₁_right, Comma.id₁_right, map₂_right, 
    Comma.leftUnitorHom_right, Comma.comp₂_right]
  rw [Comma.eqToHom_right]
  simp

@[simp]
theorem map₂_right_unitor {X Y : Comma F G} (P : X ⟶ Y) : 
    map₂ η (ρ_ P).hom = eqToHom (by rw [map_comp η P (𝟙 Y), map_id η Y]) ≫ (ρ_ (map η P)).hom := by
  simp only [Comma.instCategoryHom, Comma.inst, Comma.id_def, Comma.comp_def, 
    Comma.rightUnitor_hom]
  ext
  · simp only [obj_left, map_left, Comma.comp₁_left, Comma.id₁_left, map₂_left, 
      Comma.rightUnitorHom_left, Comma.comp₂_left]
    rw [Comma.eqToHom_left]
    simp
  simp only [obj_right, map_right, Comma.comp₁_right, Comma.id₁_right, map₂_right, 
    Comma.rightUnitorHom_right, Comma.comp₂_right]
  rw [Comma.eqToHom_right]
  simp

@[simp]
theorem map₂_associator {X Y Z W : Comma F G} (P : X ⟶ Y) (Q : Y ⟶ Z) (R : Z ⟶ W) : 
    map₂ η (α_ P Q R).hom = eqToHom (by simp only [map_comp]) ≫ 
    (α_ (map η P) (map η Q) (map η R)).hom ≫ eqToHom (by simp only [map_comp]) := by
  simp only [Comma.instCategoryHom, Comma.inst, Comma.comp_def, Comma.associator_hom]
  ext
  · simp only [obj_left, map_left, Comma.comp₁_left, map₂_left, Comma.associatorHom_left, 
    Comma.comp₂_left]
    rw [Comma.eqToHom_left, Comma.eqToHom_left]
    simp
  simp only [obj_right, map_right, Comma.comp₁_right, map₂_right, Comma.associatorHom_right, 
    Comma.comp₂_right]
  rw [Comma.eqToHom_right, Comma.eqToHom_right]
  simp

@[simps]
def core : StrictPseudofunctorCore (Comma F G) (Comma H G) where
  obj := obj η
  map := map η
  map₂ := map₂ η
  map_id := map_id η
  map_comp := map_comp η
  map₂_whisker_left := map₂_whisker_left η
  map₂_whisker_right := map₂_whisker_right η
  map₂_left_unitor := map₂_left_unitor η
  map₂_right_unitor := map₂_right_unitor η
  map₂_associator := map₂_associator η

/-- The change of left leg strict pseudofunctor. -/
@[simps!]
def functor : StrictPseudofunctor (Comma F G) (Comma H G) := StrictPseudofunctor.mk' (core η)

end mapLeft 

namespace mapRight

variable {H : B ⥤ᵒᵖᴸ T} (η : Oplax.LaxTrans G H)

end mapRight
