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
def whiskerLeft {A₀ A₁ A₂ : F ↓ X} (p₀ : A₀ ⟶ A₁) {p₁ p₂ : A₁ ⟶ A₂} (α : p₁ ⟶ p₂) : 
    (p₀ ≫ p₁) ⟶ (p₀ ≫ p₂) where
  α := p₀.p ◁ α.α
  icc := by simp [←α.icc, ←comp_whiskerRight]
            simp

@[simp]
theorem whiskerLeft_id {A₀ A₁ A₂ : F ↓ X} (p₀ : A₀ ⟶ A₁) (p₁ : A₁ ⟶ A₂) : 
    whiskerLeft F X p₀ (𝟙 p₁) = 𝟙 (p₀ ≫ p₁) := by
  refine Hom₂.ext ?_
  change p₀.p ◁ 𝟙 p₁.p = 𝟙 _
  simp

@[simp]
theorem whiskerLeft_comp {A₀ A₁ A₂ : F ↓ X} (p₀ : A₀ ⟶ A₁) {p₁ p₂ p₃ : A₁ ⟶ A₂} (α₀ : p₁ ⟶ p₂) 
    (α₁ : p₂ ⟶ p₃) : 
    whiskerLeft F X p₀ (α₀ ≫ α₁) = whiskerLeft F X p₀ α₀ ≫ whiskerLeft F X p₀ α₁ := by
  refine Hom₂.ext ?_
  change p₀.p ◁ (α₀.α ≫ α₁.α) = _ ≫ _ 
  simp

/-- Whisker a 2-cell on the right by a 1-cell.
Comes precisely from the whiskering on `B`. -/
@[simps]
def whiskerRight {A₀ A₁ A₂ : F ↓ X} {p₀ p₁ : A₀ ⟶ A₁} (α : p₀ ⟶ p₁) (p₂ : A₁ ⟶ A₂) : 
    (p₀ ≫ p₂) ⟶ (p₁ ≫ p₂) where
  α := α.α ▷ p₂.p
  icc := by simp [←α.icc, ←assoc (F.map₂ α.α ▷ A₁.f), ←whisker_exchange, ←comp_whiskerRight]

@[simp]
theorem id_whiskerRight {A₀ A₁ A₂ : F ↓ X} (p₀ : A₀ ⟶ A₁) (p₁ : A₁ ⟶ A₂) : 
    whiskerRight F X (𝟙 p₀) p₁ = 𝟙 (p₀ ≫ p₁) := by
  refine Hom₂.ext ?_
  change (𝟙 p₀.p) ▷ p₁.p = 𝟙 _
  simp


@[simp]
theorem comp_whiskerRight {A₀ A₁ A₂ : F ↓ X} {p₀ p₁ p₂ : A₀ ⟶ A₁} (α₀ : p₀ ⟶ p₁) (α₁ : p₁ ⟶ p₂) 
    (p₃ : A₁ ⟶ A₂) : whiskerRight F X (α₀ ≫ α₁) p₃ = 
    whiskerRight F X α₀ p₃ ≫ whiskerRight F X α₁ p₃ := by
  refine Hom₂.ext ?_
  change (α₀.α ≫ α₁.α) ▷ p₃.p = _ ≫ _
  simp

/- Associator forward direction. -/
@[simps]
def associatorHom {A₀ A₁ A₂ A₃ : F ↓ X} (p₀ : A₀ ⟶ A₁) (p₁ : A₁ ⟶ A₂) (p₂ : A₂ ⟶ A₃) : 
    (p₀ ≫ p₁) ≫ p₂ ⟶ p₀ ≫ p₁ ≫ p₂ where
  α := by simpa using (α_ p₀.p p₁.p p₂.p).hom
  icc := by simp [←assoc (F.mapComp p₀.p p₁.p ▷ A₂.f), ←whisker_exchange, 
                  ←Bicategory.comp_whiskerRight]
            rw [whisker_assoc_symm]
            simp

/- Associator reverse direction -/
@[simps]
def associatorInv {A₀ A₁ A₂ A₃ : F ↓ X} (p₀ : A₀ ⟶ A₁) (p₁ : A₁ ⟶ A₂) (p₂ : A₂ ⟶ A₃) :
    p₀ ≫ p₁ ≫ p₂ ⟶ (p₀ ≫ p₁) ≫ p₂ where
  α := by simpa using (α_ p₀.p p₁.p p₂.p).inv
  icc := by simp [←assoc (F.mapComp p₀.p p₁.p ▷ A₂.f), ←whisker_exchange]
            rw [←assoc ((α_ (F.map p₀.p) (F.map p₁.p) (F.map p₂.p ≫ A₃.f)).inv), ←pentagon_inv, 
                assoc, whisker_assoc_symm, assoc, assoc, 
                ←assoc ((α_ (F.map p₀.p) (F.map (p₁.p ≫ p₂.p)) A₃.f).hom), Iso.hom_inv_id, 
                id_comp, ←Bicategory.comp_whiskerRight, ←Bicategory.comp_whiskerRight,
                assoc, ←Bicategory.comp_whiskerRight, LaxFunctor.mapComp_assoc_left]
            simp

/- Associator isomorphism part 1 -/
@[simp]
theorem associator_hom_inv_id {A₀ A₁ A₂ A₃ : F ↓ X} (p₀ : A₀ ⟶ A₁) (p₁ : A₁ ⟶ A₂) (p₂ : A₂ ⟶ A₃) : 
    associatorHom F X p₀ p₁ p₂ ≫ associatorInv F X p₀ p₁ p₂ = 𝟙 ((p₀ ≫ p₁) ≫ p₂) := by
  refine Hom₂.ext ?_
  change _ ≫ _ = 𝟙 _
  simp

/- Associator isomorphism part 2 -/
@[simp]
theorem associator_inv_hom_id {A₀ A₁ A₂ A₃ : F ↓ X} (p₀ : A₀ ⟶ A₁) (p₁ : A₁ ⟶ A₂) (p₂ : A₂ ⟶ A₃) : 
    associatorInv F X p₀ p₁ p₂ ≫ associatorHom F X p₀ p₁ p₂ = 𝟙 (p₀ ≫ p₁ ≫ p₂) := by 
  refine Hom₂.ext ?_
  change _ ≫ _ = 𝟙 _
  simp

/-- Associator 2-cell.
For a composable triple of 1-cells `(p₀, θ₀) : (A₀, f₀) ⟶ (A₁, f₁), (p₁, θ₁) : (A₁, f₁) ⟶ (A₂, f₂)`,
`(p₂, θ₂) : (A₂, f₂) ⟶ (A₃, f₃)`, the associator `α_B` in `B` is the associator in `F ↓ X`: 
`α_B : ((p₂, θ₂)(p₁, θ₁))(p₀, θ₀) ⟶ (p₂, θ₂)((p₁, θ₁)(p₀, θ₀))` -/
@[simps]
def associator {A₀ A₁ A₂ A₃ : F ↓ X} (p₀ : A₀ ⟶ A₁) (p₁ : A₁ ⟶ A₂) (p₂ : A₂ ⟶ A₃) : 
    (p₀ ≫ p₁) ≫ p₂ ≅ p₀ ≫ p₁ ≫ p₂ where
  hom := associatorHom F X p₀ p₁ p₂
  inv := associatorInv F X p₀ p₁ p₂
  hom_inv_id := associator_hom_inv_id F X p₀ p₁ p₂
  inv_hom_id := associator_inv_hom_id F X p₀ p₁ p₂

@[simp]
theorem comp_whiskerLeft {A₀ A₁ A₂ A₃ : F ↓ X} (p₀ : A₀ ⟶ A₁) (p₁ : A₁ ⟶ A₂) {p₂ p₃ : A₂ ⟶ A₃} 
    (α : p₂ ⟶ p₃) : whiskerLeft F X (p₀ ≫ p₁) α =
    (associator F X p₀ p₁ p₂).hom ≫ whiskerLeft F X p₀ (whiskerLeft F X p₁ α) ≫ 
    (associator F X p₀ p₁ p₃).inv := by
  refine Hom₂.ext ?_
  change _ = _ ≫ _ ≫ _
  simp

@[simp]
theorem whiskerRight_comp {A₀ A₁ A₂ A₃ : F ↓ X} {p₀ p₁ : A₀ ⟶ A₁} (α : p₀ ⟶ p₁) (p₂ : A₁ ⟶ A₂) 
    (p₃ : A₂ ⟶ A₃) : whiskerRight F X α (p₂ ≫ p₃) = 
    (associator F X p₀ p₂ p₃).inv ≫ whiskerRight F X (whiskerRight F X α p₂) p₃ ≫ 
    (associator F X p₁ p₂ p₃).hom := by
  refine Hom₂.ext ?_
  change _ = _ ≫ _ ≫ _
  simp

@[simp]
theorem whisker_assoc {A₀ A₁ A₂ A₃ : F ↓ X} (p₀ : A₀ ⟶ A₁) {p₁ p₂ : A₁ ⟶ A₂} (α : p₁ ⟶ p₂) 
    (p₃ : A₂ ⟶ A₃) : whiskerRight F X (whiskerLeft F X p₀ α) p₃ = 
    (associator F X p₀ p₁ p₃).hom ≫ whiskerLeft F X p₀ (whiskerRight F X α p₃) ≫ 
    (associator F X p₀ p₂ p₃).inv := by
  refine Hom₂.ext ?_
  change _ = _ ≫ _ ≫ _
  simp

@[simp]
theorem whisker_exchange {A₀ A₁ A₂ : F ↓ X} {p₀ p₁ : A₀ ⟶ A₁} {p₂ p₃ : A₁ ⟶ A₂} (α₀ : p₀ ⟶ p₁) 
    (α₁ : p₂ ⟶ p₃) : whiskerLeft F X p₀ α₁ ≫ whiskerRight F X α₀ p₃ = 
    whiskerRight F X α₀ p₂ ≫ whiskerLeft F X p₁ α₁ := by
  refine Hom₂.ext ?_
  change _ ≫ _ = _ ≫ _
  simp [Bicategory.whisker_exchange]

@[simp]
theorem pentagon {A₀ A₁ A₂ A₃ A₄ : F ↓ X} (p₀ : A₀ ⟶ A₁) (p₁ : A₁ ⟶ A₂) (p₂ : A₂ ⟶ A₃) 
  (p₃ : A₃ ⟶ A₄) : whiskerRight F X (associator F X p₀ p₁ p₂).hom p₃ ≫ 
  (associator F X p₀ (p₁ ≫ p₂) p₃).hom ≫ whiskerLeft F X p₀ (associator F X p₁ p₂ p₃).hom = 
  (associator F X (p₀ ≫ p₁) p₂ p₃).hom ≫ (associator F X p₀ p₁ (p₂ ≫ p₃)).hom := by
  refine Hom₂.ext ?_
  change _ ≫ _ ≫ _ = _ ≫ _
  simp

/- Left unitor forward direction -/
@[simps]
def leftUnitorHom {A₀ A₁ : F ↓ X} (p : A₀ ⟶ A₁) : (𝟙 A₀) ≫ p ⟶ p where
  α := by simpa using (λ_ p.p).hom
  icc := by simp [←assoc (F.mapId A₀.A ▷ A₀.f), ←Bicategory.whisker_exchange, 
                  ←Bicategory.comp_whiskerRight, ←LaxFunctor.map₂_leftUnitor_hom]

/- Left unitor reverse direction -/
@[simps]
def leftUnitorInv {A₀ A₁ : F ↓ X} (p : A₀ ⟶ A₁) : p ⟶ (𝟙 A₀) ≫ p where
  α := by simpa using (λ_ p.p).inv
  icc := by simp [←assoc (F.mapId A₀.A ▷ A₀.f), ←Bicategory.whisker_exchange]

/- Left unitor isomorphism part 1 -/
@[simp]
theorem leftUnitor_hom_inv_id {A₀ A₁ : F ↓ X} (p : A₀ ⟶ A₁) : 
    leftUnitorHom F X p ≫ leftUnitorInv F X p = 𝟙 (𝟙 A₀ ≫ p) := by
  refine Hom₂.ext ?_
  change _ ≫ _ = 𝟙 _
  simp

/- Left unitor isomorphism part 2 -/
@[simp]
theorem leftUnitor_inv_hom_id {A₀ A₁ : F ↓ X} (p : A₀ ⟶ A₁) : 
    leftUnitorInv F X p ≫ leftUnitorHom F X p = 𝟙 p := by
  refine Hom₂.ext ?_
  change _ ≫ _ = 𝟙 _
  simp

/-- Left unitor 2-cell. 
Given a 1-cell `(p, θ) : (A₀, f₀) ⟶ (A₁, f₁)`, the left unitor `ℓ_B` in `B` is the left unitor in 
`F ↓ X`: `ℓ_B : (1_{A₁}, r')(p, θ) ⟶ (p, θ)`. -/
@[simps]
def leftUnitor {A₀ A₁ : F ↓ X} (p : A₀ ⟶ A₁) : (𝟙 A₀) ≫ p ≅ p where
  hom := leftUnitorHom F X p
  inv := leftUnitorInv F X p
  hom_inv_id := leftUnitor_hom_inv_id F X p
  inv_hom_id := leftUnitor_inv_hom_id F X p

@[simp]
theorem id_whiskerLeft {A₀ A₁ : F ↓ X} {p₀ p₁ : A₀ ⟶ A₁} (α : p₀ ⟶ p₁) : 
    whiskerLeft F X (𝟙 A₀) α = (leftUnitor F X p₀).hom ≫ α ≫ (leftUnitor F X p₁).inv := by
  refine Hom₂.ext ?_
  change _ = _ ≫ _ ≫ _
  simp

/- Right unitor forward direction -/
@[simps]
def rightUnitorHom {A₀ A₁ : F ↓ X} (p : A₀ ⟶ A₁) : p ≫ (𝟙 A₁) ⟶ p where
  α := by simpa using (ρ_ p.p).hom
  icc := by simp [←Bicategory.comp_whiskerRight]
            rw [←assoc (F.map p.p ◁ F.mapId A₁.A ▷ A₁.f), whisker_assoc_symm, assoc, assoc, assoc,
                ←assoc (α_ (F.map p.p) (F.map (𝟙 A₁.A)) A₁.f).hom, Iso.hom_inv_id, id_comp, 
                ←Bicategory.comp_whiskerRight, ←LaxFunctor.map₂_rightUnitor_hom]
            simp

/- Right unitor reverse direction -/
@[simps]
def rightUnitorInv {A₀ A₁ : F ↓ X} (p : A₀ ⟶ A₁) : p ⟶ p ≫ (𝟙 A₁) where
  α := by simpa using (ρ_ p.p).inv
  icc := by simp

/- Right unitor isomorphism part 1 -/
@[simp]
theorem rightUnitor_hom_inv_id {A₀ A₁ : F ↓ X} (p : A₀ ⟶ A₁) : 
    rightUnitorHom F X p ≫ rightUnitorInv F X p = 𝟙 (p ≫ 𝟙 A₁) := by
  refine Hom₂.ext ?_
  change _ ≫ _ = 𝟙 _
  simp

/- Right unitor isomorphism part 2 -/
@[simp]
theorem rightUnitor_inv_hom_id {A₀ A₁ : F ↓ X} (p : A₀ ⟶ A₁) : 
    rightUnitorInv F X p ≫ rightUnitorHom F X p = 𝟙 p := by
  refine Hom₂.ext ?_
  change _ ≫ _ = 𝟙 _
  simp

/-- Right unitor 2-cell.
Given a 1-cell `(p, θ) : (A₀, f₀) ⟶ (A₁, f₁)`, the right unitor `r_B` in `B` is the right unitor in
`F ↓ X`: `r_B : (p, θ)(1_{A_0}, r') ⟶ (p, θ)`. -/
@[simps]
def rightUnitor {A₀ A₁ : F ↓ X} (p : A₀ ⟶ A₁) : p ≫ (𝟙 A₁) ≅ p where
  hom := rightUnitorHom F X p
  inv := rightUnitorInv F X p
  hom_inv_id := rightUnitor_hom_inv_id F X p
  inv_hom_id := rightUnitor_inv_hom_id F X p

@[simp]
theorem whiskerRight_id {A₀ A₁ : F ↓ X} {p₀ p₁ : A₀ ⟶ A₁} (α : p₀ ⟶ p₁) : 
    whiskerRight F X α (𝟙 A₁) = (rightUnitor F X p₀).hom ≫ α ≫ (rightUnitor F X p₁).inv := by
  refine Hom₂.ext ?_
  change _ = _ ≫ _ ≫ _
  simp

@[simp]
theorem triangle {A₀ A₁ A₂ : F ↓ X} (p₀ : A₀ ⟶ A₁) (p₁ : A₁ ⟶ A₂) : 
    (associator F X p₀ (𝟙 A₁) p₁).hom ≫ whiskerLeft F X p₀ (leftUnitor F X p₁).hom = 
    whiskerRight F X (rightUnitor F X p₀).hom p₁ := by
  refine Hom₂.ext ?_
  change _ ≫ _ = _
  simp


@[simp]
instance : Bicategory (F ↓ X) where
  whiskerLeft p₀ _ _ α := whiskerLeft F X p₀ α
  whiskerRight p₀ α := whiskerRight F X p₀ α
  associator p₀ p₁ p₂ := associator F X p₀ p₁ p₂
  leftUnitor p := leftUnitor F X p
  rightUnitor p := rightUnitor F X p
  whiskerLeft_id p₀ p₁ := whiskerLeft_id F X p₀ p₁
  whiskerLeft_comp p _ _ _ α₀ α₁ := whiskerLeft_comp F X p α₀ α₁
  id_whiskerLeft α := id_whiskerLeft F X α
  comp_whiskerLeft p₀ p₁ _ _ α := comp_whiskerLeft F X p₀ p₁ α
  id_whiskerRight p₀ p₁ := id_whiskerRight F X p₀ p₁
  comp_whiskerRight α₀ α₁ p := comp_whiskerRight F X α₀ α₁ p
  whiskerRight_id α := whiskerRight_id F X α
  whiskerRight_comp α p₀ p₁ := whiskerRight_comp F X α p₀ p₁
  whisker_assoc p₀ _ _ α p₁ := whisker_assoc F X p₀ α p₁
  whisker_exchange α₀ α₁ := whisker_exchange F X α₀ α₁
  pentagon p₀ p₁ p₂ p₃ := pentagon F X p₀ p₁ p₂ p₃
  triangle p₀ p₁ := triangle F X p₀ p₁
