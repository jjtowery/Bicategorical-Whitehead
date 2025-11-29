/-
  Copyright (c) 2025 Judah Towery. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Judah Towery
-/

import Mathlib.CategoryTheory.Bicategory.Functor.Lax

/-!

# The lax slice bicategory F ↓ X of a lax functor F : B ⥤ᴸ C over an object X : C

* objects are pairs (A : B, f_A : FA ⟶ X) 
* 1-cells are pairs (p : A₀ ⟶ A₁, θ_p : f₀ ⟶ f₁(Fp) in C
* 2-cells are 2-cells α : p₀ ⟶ p₁ in B with Fα subject to the ice cream cone condition.

Provides a change-of-slice strict pseudofunctor for a 1-cell u : X ⟶ Y,
F ↓ u : (F ↓ X) ⥤ᵖ (F ↓ Y)

## References
* [Niles Johnson, Donald Yau, *2-Dimensional Categories*](https://arxiv.org/abs/2002.06055),
section 7.1
-/

namespace CategoryTheory

open Category Bicategory

universe w₁ w₂ v₁ v₂

namespace LaxSlice

variable {B C : Type*} [Bicategory.{w₁, v₁} B] [Bicategory.{w₂, v₂} C]

variable (F : B ⥤ᴸ C) (X : C)

/-- Objects of the lax slice bicategory `F ↓ X`. -/
@[ext]
structure Obj where
  A : B
  f : F.obj A ⟶ X

scoped notation F " ↓ " X => Obj F X

/-- 1-cells in `F ↓ X`
A 1-cell `(A₀, f₀) ⟶ (A₁, f₁)` is a pair `(p, θ_p)` with 
`p : A₀ ⟶ A₁` in `B`, and `θ_p : f₀ ⟶ f₁(Fp)` in `C`.
This is depicted as a triangle
```
FA₀-----Fp----->FA₁
|               |
|    ⇒⇒θ_p⇒⇒    |
|               |
|--f₀-->X<--f₁--| 
``` -/
@[ext]
structure Hom₁ (A₀ A₁ : F ↓ X) where
  p : A₀.A ⟶ A₁.A
  θ : A₀.f ⟶ F.map p ≫ A₁.f

/-- Identity 1-cell 
For an object `(A, f)`, the identity 1-cell is `(1_A, r')`, with `r'` from this pasting diagram:
```
|-------F1_A------|
|        ⇑        |
|      F^0_A      |
|        ⇑        ↓
FA------1_FA----->FA
|                 |
|     ⇒⇒r^-1⇒⇒    |
|                 |
|--f_A-->X<--f_A--| 
``` -/
@[simps]
def id₁ (A : F ↓ X) : Hom₁ F X A A where
  p := 𝟙 A.A
  θ := (λ_ A.f).inv ≫ (F.mapId A.A ▷ A.f)

/-- Composition of 1-cells.
For 1-cells `(p₀, θ₀) : (A₀, f₀) ⟶ (A₁, f₁), (p₁, θ₁) : (A₁, f₁) ⟶ (A₂, f₂)`, their composite is
`(p₁p₀, θ')`, where `θ'` is formed from the composite of the pasting diagram:
```
|-------F(p₁p₀)-------|          
|          ⇑          |
|       F^2_{p₁,p₀}   |
|          ⇑          ↓
FA₀--Fp₀-->FA₁--Fp₁-->FA₂
|          |          |
|  ⇒⇒θ₀⇒⇒  f₁ ⇒⇒θ₁⇒⇒  |
|          ↓          |
|----f₀--->X<---f₂----| 
``` -/
@[simps]
def comp₁ {A₀ A₁ A₂ : F ↓ X} (p₀ : Hom₁ F X A₀ A₁) (p₁ : Hom₁ F X A₁ A₂) : Hom₁ F X A₀ A₂ where
  p := p₀.p ≫ p₁.p
  θ := p₀.θ ≫ (F.map p₀.p ◁ p₁.θ) ≫ (α_ (F.map p₀.p) (F.map p₁.p) A₂.f).inv 
       ≫ (F.mapComp p₀.p p₁.p ▷ A₂.f)

/-- Underlying CategoryStruct on objects. -/
@[simps]
instance : CategoryStruct (F ↓ X) where
  Hom A₀ A₁ := Hom₁ F X A₀ A₁
  id A := id₁ F X A
  comp A₀ A₁ := comp₁ F X A₀ A₁

/-- 2-cells in `F ↓ X`
A 2-cell `(p₀, θ₀) ⟶ (p₁, θ₁)` is a 2-cell `α : p₀ ⟶ p₁` in `B` such that
`Fα` satisfies the ice cream cone condition:
```        
|-------Fp₁-----|     FA₀-----Fp₁---->FA₁
|        ⇑      |     |               |
|       Fα      |     |               |
|        ⇑      ↓     |               |
FA₀-----Fp₀---->FA₁ = |     ⇒⇒θ₁⇒⇒    |                
|               |     |               |
|     ⇒⇒θ₀⇒⇒    |     |               |
|               |     |               |
|--f₀-->X<--f₁--|     |--f₀-->X<--f₁--| 
``` -/
@[ext]
structure Hom₂ {A₀ A₁ : F ↓ X} (p₀ : A₀ ⟶ A₁) (p₁ : A₀ ⟶ A₁) where
  α : p₀.p ⟶ p₁.p
  icc : p₀.θ ≫ (F.map₂ α ▷ A₁.f) = p₁.θ

/-- Identity 2-cell.
For a 1-cell `(p, θ)`, the identity 2-cell is `1_p` -/
@[simps]
def id₂ {A₀ A₁ : F ↓ X} (p : A₀ ⟶ A₁) : Hom₂ F X p p where
  α := 𝟙 p.p
  icc := by simp 

/-- Vertical composition of 2-cells.
For 1-cells `(p, θ), (p', θ'), (p'', θ'') : (A₀, F₀) ⟶ (A₁, F₁)`
and 2-cells `α : (p, θ) ⟶ (p', θ'), α' : (p', θ') ⟶ (p'', θ'')`,
their vertical composite is the composite `α'α : (p, θ) ⟶ (p'', θ'')`. -/
@[simps]
def comp₂ {A₀ A₁ : F ↓ X} {p p' p'' : A₀ ⟶ A₁} (α : Hom₂ F X p p') (α' : Hom₂ F X p' p'') : 
    Hom₂ F X p p'' where
  α := α.α ≫ α'.α
  icc := by simp [←α.icc, ←α'.icc]

/-- Category structure on 1-cells with vertical composition. -/
@[simps!]
instance (A₀ A₁ : F ↓ X) : Category (A₀ ⟶ A₁) where
  Hom p₀ p₁ := Hom₂ F X p₀ p₁
  id p := id₂ F X p
  comp α₀ α₁ := comp₂ F X α₀ α₁

/-- Whisker a 2-cell on the left by a 1-cell.
Comes precisely from the whiskering on `B`. -/
@[simps]
def whiskerLeft₂ {A₀ A₁ A₂ : F ↓ X} (p₀ : A₀ ⟶ A₁) {p₁ p₂ : A₁ ⟶ A₂} (α : p₁ ⟶ p₂) : 
    (p₀ ≫ p₁) ⟶ (p₀ ≫ p₂) where
  α := p₀.p ◁ α.α
  icc := by simp [←α.icc, ←comp_whiskerRight]
            simp

/-- Whisker a 2-cell on the right by a 1-cell.
Comes precisely from the whiskering on `B`. -/
@[simps]
def whiskerRight₂ {A₀ A₁ A₂ : F ↓ X} {p₀ p₁ : A₀ ⟶ A₁} (α : p₀ ⟶ p₁) (p₂ : A₁ ⟶ A₂) : 
    (p₀ ≫ p₂) ⟶ (p₁ ≫ p₂) where
  α := α.α ▷ p₂.p
  icc := by simp [←α.icc, ←assoc (F.map₂ α.α ▷ A₁.f), ←whisker_exchange, ←comp_whiskerRight]

/- Associator forward direction. -/
@[simps]
def associator₂Hom {A₀ A₁ A₂ A₃ : F ↓ X} (p₀ : A₀ ⟶ A₁) (p₁ : A₁ ⟶ A₂) (p₂ : A₂ ⟶ A₃) : 
    (p₀ ≫ p₁) ≫ p₂ ⟶ p₀ ≫ p₁ ≫ p₂ where
  α := by simpa using (α_ p₀.p p₁.p p₂.p).hom
  icc := by simp [←assoc (F.mapComp p₀.p p₁.p ▷ A₂.f), ←whisker_exchange, ←comp_whiskerRight]
            rw [whisker_assoc_symm]
            simp
            
/- Associator reverse direction -/
@[simps]
def associator₂Inv {A₀ A₁ A₂ A₃ : F ↓ X} (p₀ : A₀ ⟶ A₁) (p₁ : A₁ ⟶ A₂) (p₂ : A₂ ⟶ A₃) :
    p₀ ≫ p₁ ≫ p₂ ⟶ (p₀ ≫ p₁) ≫ p₂ where
  α := by simpa using (α_ p₀.p p₁.p p₂.p).inv
  icc := by simp [←assoc (F.mapComp p₀.p p₁.p ▷ A₂.f), ←whisker_exchange]
            rw [←assoc ((α_ (F.map p₀.p) (F.map p₁.p) (F.map p₂.p ≫ A₃.f)).inv), ←pentagon_inv, 
                assoc, whisker_assoc_symm, assoc, assoc, 
                ←assoc ((α_ (F.map p₀.p) (F.map (p₁.p ≫ p₂.p)) A₃.f).hom), Iso.hom_inv_id, 
                id_comp, ←comp_whiskerRight, ←comp_whiskerRight, ←comp_whiskerRight, assoc,
                ←comp_whiskerRight, LaxFunctor.mapComp_assoc_left]
            simp

/- Associator isomorphism part 1 -/
@[simp]
theorem associator₂_hom_inv_id {A₀ A₁ A₂ A₃ : F ↓ X} (p₀ : A₀ ⟶ A₁) (p₁ : A₁ ⟶ A₂) (p₂ : A₂ ⟶ A₃) : 
    associator₂Hom F X p₀ p₁ p₂ ≫ associator₂Inv F X p₀ p₁ p₂ = 𝟙 ((p₀ ≫ p₁) ≫ p₂) := by
  refine Hom₂.ext ?_
  change (associator₂Hom F X p₀ p₁ p₂).α ≫
         (associator₂Inv F X p₀ p₁ p₂).α
         = 𝟙 _
  simp

/- Associator isomorphism part 2 -/
@[simp]
theorem associator₂_inv_hom_id {A₀ A₁ A₂ A₃ : F ↓ X} (p₀ : A₀ ⟶ A₁) (p₁ : A₁ ⟶ A₂) (p₂ : A₂ ⟶ A₃) : 
    associator₂Inv F X p₀ p₁ p₂ ≫ associator₂Hom F X p₀ p₁ p₂ = 𝟙 (p₀ ≫ p₁ ≫ p₂) := by 
  refine Hom₂.ext ?_
  change (associator₂Inv F X p₀ p₁ p₂).α ≫
         (associator₂Hom F X p₀ p₁ p₂).α
         = 𝟙 _
  simp

/-- Associator 2-cell.
For a composable triple of 1-cells `(p₀, θ₀) : (A₀, f₀) ⟶ (A₁, f₁), (p₁, θ₁) : (A₁, f₁) ⟶ (A₂, f₂)`,
`(p₂, θ₂) : (A₂, f₂) ⟶ (A₃, f₃)`, the associator `α_B` in `B` is the associator in `F ↓ X`: 
`α_B : ((p₂, θ₂)(p₁, θ₁))(p₀, θ₀) ⟶ (p₂, θ₂)((p₁, θ₁)(p₀, θ₀))` -/
@[simps]
def associator₂ {A₀ A₁ A₂ A₃ : F ↓ X} (p₀ : A₀ ⟶ A₁) (p₁ : A₁ ⟶ A₂) (p₂ : A₂ ⟶ A₃) : 
    (p₀ ≫ p₁) ≫ p₂ ≅ p₀ ≫ p₁ ≫ p₂ where
  hom := associator₂Hom F X p₀ p₁ p₂
  inv := associator₂Inv F X p₀ p₁ p₂
  hom_inv_id := associator₂_hom_inv_id F X p₀ p₁ p₂
  inv_hom_id := associator₂_inv_hom_id F X p₀ p₁ p₂

/- Left unitor forward direction -/
@[simps]
def leftUnitor₂Hom {A₀ A₁ : F ↓ X} (p : A₀ ⟶ A₁) : (𝟙 A₀) ≫ p ⟶ p where
  α := by simpa using (λ_ p.p).hom
  icc := by simp [←assoc (F.mapId A₀.A ▷ A₀.f), ←whisker_exchange, ←comp_whiskerRight, 
                  ←LaxFunctor.map₂_leftUnitor_hom]

/- Left unitor reverse direction -/
@[simps]
def leftUnitor₂Inv {A₀ A₁ : F ↓ X} (p : A₀ ⟶ A₁) : p ⟶ (𝟙 A₀) ≫ p where
  α := by simpa using (λ_ p.p).inv
  icc := by simp [←assoc (F.mapId A₀.A ▷ A₀.f), ←whisker_exchange]

/- Left unitor isomorphism part 1 -/
@[simp]
theorem leftUnitor₂_hom_inv_id {A₀ A₁ : F ↓ X} (p : A₀ ⟶ A₁) : 
    leftUnitor₂Hom F X p ≫ leftUnitor₂Inv F X p = 𝟙 (𝟙 A₀ ≫ p) := by
  refine Hom₂.ext ?_
  change (leftUnitor₂Hom F X p).α ≫
         (leftUnitor₂Inv F X p).α
         = 𝟙 _
  simp

/- Left unitor isomorphism part 2 -/
@[simp]
theorem leftUnitor₂_inv_hom_id {A₀ A₁ : F ↓ X} (p : A₀ ⟶ A₁) : 
    leftUnitor₂Inv F X p ≫ leftUnitor₂Hom F X p = 𝟙 p := by
  refine Hom₂.ext ?_
  change (leftUnitor₂Inv F X p).α ≫
         (leftUnitor₂Hom F X p).α
         = 𝟙 _
  simp

/-- Left unitor 2-cell. 
Given a 1-cell `(p, θ) : (A₀, f₀) ⟶ (A₁, f₁)`, the left unitor `ℓ_B` in `B` is the left unitor in 
`F ↓ X`: `ℓ_B : (1_{A₁}, r')(p, θ) ⟶ (p, θ)`. -/
@[simps]
def leftUnitor₂ {A₀ A₁ : F ↓ X} (p : A₀ ⟶ A₁) : (𝟙 A₀) ≫ p ≅ p where
  hom := leftUnitor₂Hom F X p
  inv := leftUnitor₂Inv F X p
  hom_inv_id := leftUnitor₂_hom_inv_id F X p
  inv_hom_id := leftUnitor₂_inv_hom_id F X p

def rightUnitor₂Hom {A₀ A₁ : F ↓ X} (p : A₀ ⟶ A₁) : p ≫ (𝟙 A₁) ⟶ p where
  α := by simpa using (ρ_ p.p).hom
  icc := by simp [←comp_whiskerRight]
            sorry

/-- Right unitor 2-cell.
Given a 1-cell `(p, θ) : (A₀, f₀) ⟶ (A₁, f₁)`, the right unitor `r_B` in `B` is the right unitor in
`F ↓ X`: `r_B : (p, θ)(1_{A_0}, r') ⟶ (p, θ)`. -/
@[simps]
def rightUnitor₂ {A₀ A₁ : F ↓ X} (p : A₀ ⟶ A₁) : p ≫ (𝟙 A₁) ≅ p where
  hom := sorry
  inv := sorry

@[simp]
instance : Bicategory (F ↓ X) where
  whiskerLeft p₀ _ _ α := whiskerLeft₂ F X p₀ α
  whiskerRight p₀ α := whiskerRight₂ F X p₀ α
  associator p₀ p₁ p₂ := associator₂ F X p₀ p₁ p₂
  leftUnitor p := leftUnitor₂ F X p
  rightUnitor p := rightUnitor₂ F X p
