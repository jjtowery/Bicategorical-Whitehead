/-
Copyright (c) 2025 Judah Towery. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judah Towery
-/

import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/-!

# Constant pseudofunctors between bicategories.

For any `x : C`, the constant pseudofunctor `Δₓ : B ⥤ᵖ C` is given

* on objects by `b ↦ x`;
* on 1-cells by `f ↦ 𝟙 x`;
* on 2-cells by `η ↦ 𝟙 (𝟙 x)`.

Provides the specialization to where the domain is the singleton bicategory:
`fromPUnit x : LocallyDiscrete (Discrete PUnit) ⥤ᵖ B`.

Provides the natural transformation induced from a 1-cell `f : x ⟶ y` in `C`
`homStrongTrans : fromPUnit x ⟶ fromPUnit y`.

-/

namespace CategoryTheory.Bicategory

open Category Bicategory

universe w₁ w₂ v₁ v₂

variable {C : Type*} [Bicategory.{w₂, v₂} C]

/-- The constant pseudofunctor at `x`. -/
@[simps]
def const (B : Type*) [Bicategory.{w₁, v₁} B] (x : C) : B ⥤ᵖ C where
  obj _ := _
  map _ := _
  map₂ _ := _
  mapId _ := Iso.refl _
  mapComp _ _ := (ρ_ _).symm

namespace const

/-- Constant pseudofunctor with domain the singleton bicategory. -/
@[simps!]
abbrev fromPUnit (x : C) := const (LocallyDiscrete (Discrete PUnit)) x

/-- Natural transformation induced from a 1-cell. -/
@[simps]
def homStrongTrans {x y : C} (f : x ⟶ y) : 
    Pseudofunctor.StrongTrans (fromPUnit x) (fromPUnit y) where
  app := _
  naturality _ := (λ_ _) ≪≫ (ρ_ f).symm

end const
