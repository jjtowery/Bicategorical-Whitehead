/-
Copyright (c) 2026 Judah Towery. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judah Towery
-/

import «Bicategorical Whitehead».Const
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Lax
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Lax terminal objects and inc-lax (initial-component-lax) transformations.

Defines lax terminal objects, inc-lax transformations, inc-lax terminal objects, and
initial component preserving lax functors.

Provides as well the partial functoriality of initial component preservation.

-/

namespace CategoryTheory.Bicategory

open Category Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃

variable {B C D : Type*} [Bicategory.{w₁, v₁} B] [Bicategory.{w₂, v₂} C] [Bicategory.{w₃, v₃} D]

/-- Lax terminal objects. 
An object `t : C` is lax terminal if there is a lax transformation `k : 𝟙 C ⟶ Δₜ`.
The 1-cells of such a transformation are of the form `k_X : X ⟶ t` for `X ∈ C`,
and 2-cells
```    
       u
    X ---> Y
    |      |
    |  kᵤ  |
k_X |  ⇒   | k_Y
    ↓      ↓
    t ---> t
      𝟙 t
``` -/
structure LaxTerminal (t : C) where
  cone : Lax.LaxTrans (LaxFunctor.id C) (const C t)

/-- Inc-lax transformations.
For lax functors `F, G : B ⥤ᴸ C`, a lax tranformation `k : F ⟶ G` is inc-lax if each component
`k_X : FX ⟶ GX` is initial in the category `C(FX, GX)`. -/
structure IncLax {F G : B ⥤ᴸ C} (k : Lax.LaxTrans F G) where
  app_isInitial (X : B) : Limits.IsInitial (k.app X) := by cat_disch

/-- Inc-lax terminal objects. 
If `t : C` is lax terminal with lax transformation `k : 𝟙 C ⟶ Δₜ`, `t` is an inc-lax
terminal object if `k` is inc-lax, and the component `kₜ` is the identity 1-cell `𝟙 t`. -/
structure IncLaxTerminal (t : C) extends LaxTerminal t where
  inc : IncLax cone
  app_self_eq_id : cone.app t = 𝟙 t := by cat_disch

attribute [simp] IncLaxTerminal.app_self_eq_id

/-- Lax functor that preserves initial components. 
If `B, C` have inc-lax terminal objects `(t, k), (t', k')` respectively, a lax functor 
`F : B ⥤ᴸ C` preserves initial components if the composite 
```  
     Fk_X      k'_(Ft)
FX -------> Ft -------> t'
```
is initial in `C(FX, t')`. -/
structure PreservesInitialComponents {t : B} {t' : C} (F : B ⥤ᴸ C)
    (h : IncLaxTerminal t) (h' : IncLaxTerminal t') where
  comp_isInitial (X : B) : Limits.IsInitial (F.map (h.cone.app X) ≫ h'.cone.app (F.obj t)) := 
    by cat_disch

namespace PreservesInitialComponents

/-- If `F : B ⥤ᴸ C` preserves initial components, and `f : X ⟶ t` is an initial 1-cell in 
`B(X, t)`, then
``` 
    Ff        k'_{Ft}
FX -----> Ft --------> t'
```
is initial in `C(FX, t')`. -/
@[simp]
def comp_isInitial_of_isInitial {t : B} {t' : C} {F : B ⥤ᴸ C} {h : IncLaxTerminal t}
    {h' : IncLaxTerminal t'} (hF : PreservesInitialComponents F h h') {X : B} {f : X ⟶ t}
    (hf : Limits.IsInitial f) :
    Limits.IsInitial (F.map f ≫ h'.cone.app (F.obj t)) := 
  Limits.IsInitial.ofIso (hF.comp_isInitial _) 
    (whiskerRightIso (PrelaxFunctor.map₂Iso F.toPrelaxFunctor 
    (Limits.IsInitial.uniqueUpToIso hf (h.inc.app_isInitial _))) _).symm

/-- Identity preserves initial components. -/
@[simp]
def id {t : B} (h : IncLaxTerminal t) : PreservesInitialComponents (LaxFunctor.id B) h h where
  comp_isInitial X := by simp only [LaxFunctor.id_toPrelaxFunctor, 
                           PrelaxFunctor.id_toPrelaxFunctorStruct,
                           PrelaxFunctorStruct.id_toPrefunctor, Prefunctor.id_obj, 
                           Pseudofunctor.toLax_toPrelaxFunctor, 
                           const_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj, 
                           Prefunctor.id_map, IncLaxTerminal.app_self_eq_id]
                         exact Limits.IsInitial.ofIso (h.inc.app_isInitial _) 
                           (ρ_ _).symm

/-- Composite of initial component preserving functors preserves initial components.
Note though that we need at least `G` a pseudofunctor for this to work. -/
@[simp]
def comp {t : B} {t' : C} {t'' : D}
    {F : B ⥤ᴸ C} {G : C ⥤ᵖ D}
    {h : IncLaxTerminal t} {h' : IncLaxTerminal t'} {h'' : IncLaxTerminal t''}
    (hF : PreservesInitialComponents F h h') (hG : PreservesInitialComponents G h' h'') :
    PreservesInitialComponents (F.comp G) h h'' where
  comp_isInitial _ := Limits.IsInitial.ofIso (comp_isInitial_of_isInitial hG (hF.comp_isInitial _))
                        ((whiskerRightIso (G.mapComp (F.map _) _) _ ≪≫ (α_ _ _ _)) ≪≫ 
                        (whiskerLeftIso _) (Limits.IsInitial.uniqueUpToIso (hG.comp_isInitial _) 
                        (h''.inc.app_isInitial _)))

end PreservesInitialComponents
