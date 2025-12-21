/-
Copyright (c) 2025 Judah Towery. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judah Towery
-/

import Mathlib.CategoryTheory.Bicategory.Functor.Lax
import Mathlib.CategoryTheory.Bicategory.Functor.Oplax

/-!

# The oplax comma bicategory for a lax functor `F : A ⥤ᴸ T` and an oplax functor `G : B ⥤ᵒᵖᴸ T`.

* objects are triples `(a : A, b : B, φ : Fa ⟶ Gb)`
* 1-cells are triples `(p : a₀ ⟶ a₁, q : b₀ ⟶ b₁, θ : Gq φ₀ ⟶ φ₁ Fp)`
* 2-cells are pairs `(α : p ⟶ p', β : q ⟶ q')` that satisfy the generalized ice cream 
cone condition.

-/

namespace CategoryTheory.Bicategory

open Category Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃

variable {A B T : Type*} [Bicategory.{w₁, v₁} A] [Bicategory.{w₂, v₂} B] [Bicategory.{w₃, v₃} T]

/-- The objects of the oplax comma bicategory are triples `(a, b, φ)`
with `a ∈ A`, `b ∈ B`, `φ : Fa → Gb` a 1-cell in `T`. -/
@[ext]
structure Comma (F : A ⥤ᴸ T) (G : B ⥤ᵒᵖᴸ T) where
  left : A
  right : B
  hom : F.obj left ⟶ G.obj right

namespace Comma

variable {F : A ⥤ᴸ T} {G : B ⥤ᵒᵖᴸ T}

/-- The 1-cells of the oplax comma bicategory are triples
`(p, q, θ) : (a₀, b₀, φ₀) ⟶ (a₁, b₁, φ₁) with
`p : a₀ ⟶ a₁` in `A`
`q : b₀ ⟶ b₁` in `B`
`θ : Gq φ₀ ⟶ φ₁ Fp` a 2-cell in `T`. -/
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
  ≫ P.f ▷ (G.map Q.right) ≫ (α_ (F.map P.left) Y.hom (G.map Q.right)).hom ≫ (F.map P.left) ◁ Q.f
  ≫ (α_ (F.map P.left) (F.map Q.left) Z.hom).inv ≫ (F.mapComp P.left Q.left) ▷ Z.hom

/-- Underlying 1-CategoryStruct. -/
@[simps]
instance : CategoryStruct (Comma F G) where
  Hom X Y := Hom₁ X Y
  id X := id₁ X
  comp P Q := comp₁ P Q

/-- The 2-cells of the oplax comma bicategory are pairs
`(α, β) : (p, q, θ) ⟶ (p', q', θ')` with
`α : p ⟶ p'` in `A`
`β : q ⟶ q'` in `B`
satisfying the generalized ice cream cone condition. -/
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

/- For two 2-cells `(α₀, β₀)`, (α₁, β₁)`, their composition is `(α₁ ∘ α₀, β₁ ∘ β₀)`. -/
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

/-- Left whiskering, given directly by the left whiskering on the base category. -/
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

/-- Right whiskering, given directly by the right whiskering on the base category. -/
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
            
/-- Associator, given directly by the associator on the base category. -/
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
            
/-- Left unitor, given directly by the left unitor on the base category. -/
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

/-- Right unitor, given directly by the right unitor on the base category. -/
@[simps]
def rightUnitor {X Y : Comma F G} (P : X ⟶ Y) : P ≫ 𝟙 Y ≅ P where
  hom := rightUnitorHom P
  inv := rightUnitorInv P

/-- Comma bicategory. -/
instance : Bicategory (Comma F G) where
  whiskerLeft P _ _ η := whiskerLeft P η
  whiskerRight η R := whiskerRight η R
  associator P Q R := associator P Q R
  leftUnitor P := leftUnitor P
  rightUnitor P := rightUnitor P
  whisker_exchange η θ := by simp only [Hom_def, instCategoryHom, comp_def]
                             ext
                             · simp only [comp₁_left, comp₂_left, whiskerLeft_left, 
                               whiskerRight_left]
                               rw [whisker_exchange]
                             simp only [comp₁_right, comp₂_right, whiskerLeft_right, 
                               whiskerRight_right]
                             rw [whisker_exchange]
