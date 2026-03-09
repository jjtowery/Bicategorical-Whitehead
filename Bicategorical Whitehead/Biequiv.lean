/-
Copyright (c) 2026 Judah Towery. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judah Towery
-/

import «Bicategorical Whitehead».LaxTerminal
import «Bicategorical Whitehead».OplaxComma
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

/-!
# Biequivalences of bicategories.

Defines pre-biequivalences as usual pseudo-inverses, and then defines biequivalences
as biadjoint biequivalences, with a strictification result that upgrades
pre-biequivalences to biadjoint biequivalences.

Defines essentially surjective, essentially full, and fully faithful lax functors.

Proves the bicategorical whitehead theorem: A pseudofunctor is a biequivalence if and only if
it is essentially surjective, essentially full, and fully faithful.

-/

namespace CategoryTheory.Bicategory

open Category Bicategory

universe w₁ w₂ v₁ v₂

open scoped Pseudofunctor.StrongTrans

/-- A pre-biequivalence. 
A pseudofunctor `F : B ⥤ᵖ C` is a pre-biequivalence if there is a pseudofunctor `G : C ⥤ᵖ B` 
with internal equivalences `𝟙 B ≌ GF` and `FG ≌ 𝟙 C` in their respective pseudofunctor bicategories.

The internal equivalence `FG ≌ 𝟙 C` entails the following data:
Strong transformations `ε : FG ⟶ 𝟙 C` and `ε' : 𝟙 C ⟶ FG`;
Invertible modifications `Γ : 𝟙 (𝟙 C) ≅ εε'` and `Γ' : ε'ε ≅ 𝟙 (FG)`.

The internal equivalence `𝟙 B ≌ GF` entails the following data:
Strong transformations `η : 𝟙 B ⟶ GF` and `η' : GF ⟶ 𝟙 B`;
Invertible modifications `θ : 𝟙 (𝟙 B) ≅ ηη'` and `θ' : ηη' ≅ 𝟙 (GF)`.

This is taken as the definition of biequivalence in Johnson-Yau, but in 
analogy with the 1-category API, we want to consider biadjoint biequivalence as the definition 
of biequivalence, which pre-biequivalences can strictify to. -/
structure PreBiequivalence (B C : Type*) [Bicategory.{w₁, v₁ B}] [Bicategory.{w₂, v₂} C] where
  hom : B ⥤ᵖ C
  inv : C ⥤ᵖ B
  unit : Pseudofunctor.id B ≌ hom.comp inv
  counit : inv.comp hom ≌ Pseudofunctor.id C

variable {B C : Type*} [Bicategory.{w₁, v₁} B] [Bicategory.{w₂, v₂} C]
