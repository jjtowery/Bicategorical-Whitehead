/-
  Copyright (c) 2025 Judah Towery. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Judah Towery
-/

import Mathlib.CategoryTheory.Bicategory.Functor.Lax

/-
## References
* [Niles Johnson, Donald Yau, *2-Dimensional Categories*](https://arxiv.org/abs/2002.06055),
section 7.1.
-/

namespace CategoryTheory

open Category Bicategory

universe w₁ w₂ v₁ v₂

namespace LaxSlice

variable {B C : Type*} [Bicategory.{w₁, v₁} B] [Bicategory.{w₂, v₂} C]

variable (F : B ⥤ᴸ C) (X : C)

/- 
  Objects of the lax slice bicategory F ↓ X.
  Pairs (A, f_A) with A ∈ B and f_A : F A ⟶ X in C.
-/
@[ext]
structure Obj where
  A : B
  f : F.obj A ⟶ X

scoped notation F " ↓ " X => Obj F X

/- 
  1-cells in F ↓ X 
  A 1-cell (A₀, f₀) ⟶ (A₁, f₁) is a pair (p, θ_p) with 
  p : A₀ ⟶ A₁ in B, and θ_p : f₀ ⟶ f₁(Fp) in C.
  This is depicted as a triangle

  FA₀-----Fp----->FA₁
  |               |
  |    ⇒⇒θ_p⇒⇒    |
  |               |
  |--f₀-->X<--f₁--|

-/
@[ext]
structure Hom₁ (A₀ A₁ : F ↓ X) where
  p : A₀.A ⟶ A₁.A
  θ : A₀.f ⟶ F.map p ≫ A₁.f

/-
  2-cells in F ↓ X
  A 2-cell (p₀, θ₀) ⟶ (p₁, θ₁) is a 2-cell α : p₀ ⟶ p₁ in B such that
  Fα satisfies the ice cream cone condition:
            
  |-------Fp₁-----|     FA₀-----Fp₁---->FA₁
  |        ⇑      |     |               |
  |       Fα      |     |               |
  |        ⇑      ↓     |               |
  FA₀-----Fp₀---->FA₁ = |     ⇒⇒θ₁⇒⇒    |                
  |               |     |               |
  |     ⇒⇒θ₀⇒⇒    |     |               |
  |               |     |               |
  |--f₀-->X<--f₁--|     |--f₀-->X<--f₁--|
                
-/
@[ext]
structure Hom₂ {A₀ A₁ : F ↓ X} (p₀ : Hom₁ F X A₀ A₁) (p₁ : Hom₁ F X A₀ A₁) where
  α : p₀.p ⟶ p₁.p
  icc : p₀.θ ≫ (F.map₂ α ▷ A₁.f) = p₁.θ

/- 
  Identity 1-cell 
  For an object (A, f), the identity 1-cell is (1_A, r'), with r' from this pasting diagram:
   
  |-------F1_A------|
  |        ⇑        |
  |      F^0_A      |
  |        ⇑        ↓
  FA------1_FA----->FA
  |                 |
  |     ⇒⇒r^-1⇒⇒    |
  |                 |
  |--f_A-->X<--f_A--|

-/
@[simps]
def id₁ (A : F ↓ X) : Hom₁ F X A A where
  p := 𝟙 A.A
  θ := (λ_ A.f).inv ≫ (F.mapId A.A ▷ A.f)

/-
  Identity 2-cell.
  For a 1-cell (p, θ), the identity 2-cell is 1_p.
-/
@[simps]
def id₂ {A₀ A₁ : F ↓ X} (p : Hom₁ F X A₀ A₁) : Hom₂ F X p p where
  α := 𝟙 p.p
  icc := by simp only [PrelaxFunctor.map₂_id, id_whiskerRight, comp_id]

/- 
  Horizontal composition of 1-cells.
  For 1-cells (p₀, θ₀) : (A₀, f₀) ⟶ (A₁, f₁), (p₁, θ₁) : (A₁, f₁) ⟶ (A₂, f₂), their composite is
  (p₁p₀, θ'), where θ' is formed from the composite of the pasting diagram:

  |-------F(p₁p₀)-------|          
  |          ⇑          |
  |       F^2_{p₁,p₀}   |
  |          ⇑          ↓
  FA₀--Fp₀-->FA₁--Fp₁-->FA₂
  |          |          |
  |  ⇒⇒θ₀⇒⇒  f₁ ⇒⇒θ₁⇒⇒  |
  |          ↓          |
  |----f₀--->X<---f₂----|

-/
@[simps]
def comp₁ {A₀ A₁ A₂ : F ↓ X} (p₀ : Hom₁ F X A₀ A₁) (p₁ : Hom₁ F X A₁ A₂) : Hom₁ F X A₀ A₂ where
  p := p₀.p ≫ p₁.p
  θ := p₀.θ ≫ (F.map p₀.p ◁ p₁.θ) ≫ (α_ (F.map p₀.p) (F.map p₁.p) A₂.f).inv 
        ≫ (F.mapComp p₀.p p₁.p ▷ A₂.f)

/-
  Vertical composition of 2-cells.
  For 1-cells (p, θ), (p', θ'), (p'', θ'') : (A₀, F₀) ⟶ (A₁, F₁)
  and 2-cells α : (p, θ) ⟶ (p', θ'), α' : (p', θ') ⟶ (p'', θ''),
  their vertical composite is the composite α'α : (p, θ) ⟶ (p'', θ'').
-/
@[simps]
def vcomp₂ {A₀ A₁ : F ↓ X} {p p' p'' : Hom₁ F X A₀ A₁} (α : Hom₂ F X p p') (α' : Hom₂ F X p' p'') : 
    Hom₂ F X p p'' where
  α := α.α ≫ α'.α
  icc := by simp only [PrelaxFunctor.map₂_comp, comp_whiskerRight, ←α.icc, ←α'.icc, assoc]

/- 
  Category structure on 1-morphisms with vertical composition.
-/
@[simps]
instance (A₀ A₁ : F ↓ X) : Category (Hom₁ F X A₀ A₁) where
  Hom p₀ p₁ := Hom₂ F X p₀ p₁
  id p := id₂ F X p
  comp α₀ α₁ := vcomp₂ F X α₀ α₁

instance : Bicategory (F ↓ X) where
  Hom A₀ A₁ := Hom₁ F X A₀ A₁
  id A := id₁ F X A
  comp p₀ p₁ := comp₁ F X p₀ p₁
