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

An object `t ∈ C` is lax terminal if there is a lax transformation `k : Id_C ⟶ Δₜ`.
The 1-cells of such a transformation are of the form `k_X : X ⟶ t` for `X ∈ C`,
and 2-cells
```    
       u
    X ---> Y
    |      |
    | k_u  |
k_X |  ⇒   | k_Y
    ↓      ↓
    t ---> t
       1ₜ
```

For lax functors `F, G : B ⥤ᴸ C`, a lax tranformation `k : F ⟶ G` is inc-lax if each component
`k_X : FX ⟶ GX` is initial in the category `C(FX, GX)`.

If `t ∈ C` is lax terminal with lax transformation `k : Id_C ⟶ Δₜ`, `t` is an inc-lax
terminal object if `k` is inc-lax, and the component `kₜ` is the identity 1-cell `1ₜ`.

If `B, C` have inc-lax terminal objects `(t, k), (t', k')` respectively, a lax functor 
`F : B ⥤ᴸ C` preserves initial components if the composite 
```  
     Fk_X      k'_(Ft)
FX -------> Ft -------> t'
```
is initial in `C(FX, t')`.

-/

namespace CategoryTheory.Bicategory

open Category Bicategory

universe w₁ w₂ v₁ v₂

variable {B C : Type*} [Bicategory.{w₁, v₁} B] [Bicategory.{w₂, v₂} C]

/-- Lax terminal objects. -/
structure LaxTerminal (t : C) where
  cone : Lax.LaxTrans (LaxFunctor.id C) (const C t)

/-- Inc-lax transformations. -/
structure IncLax {F G : B ⥤ᴸ C} (k : Lax.LaxTrans F G) where
  app_isInitial (X : B) : Limits.IsInitial (k.app X)

/-- Inc-lax terminal objects. -/
structure IncLaxTerminal (t : C) extends LaxTerminal t where
  inc : IncLax cone
  app_self_eq_id : cone.app t = 𝟙 t

/-- Lax functor that preserves initial components. -/
structure PreservesInitialComponents {t : B} {t' : C} (F : B ⥤ᴸ C)
    (h : IncLaxTerminal t) (h' : IncLaxTerminal t') where
  comp_isInitial (X : B) : Limits.IsInitial (F.map (h.cone.app X) ≫ h'.cone.app (F.obj t))

namespace PreservesInitialComponents

/-- If `F : B ⥤ᴸ C` preserves initial components, and `f : X ⟶ t` is an initial 1-cell in 
`B(X, t)`, then
``` 
    Ff        k'_{Ft}
FX -----> Ft --------> t
```
is initial in `C(FX, t)`. -/
def comp_isInitial_of_isInitial {t : B} {t' : C} {F : B ⥤ᴸ C} {h : IncLaxTerminal t}
    {h' : IncLaxTerminal t'} (hF : PreservesInitialComponents F h h') {X : B} {f : X ⟶ t}
    (hf : Limits.IsInitial f) :
    Limits.IsInitial (F.map f ≫ h'.cone.app (F.obj t)) := 
  Limits.IsInitial.ofIso (hF.comp_isInitial X) 
  (whiskerRightIso (PrelaxFunctor.map₂Iso F.toPrelaxFunctor 
  (Limits.IsInitial.uniqueUpToIso hf (h.inc.app_isInitial X)))
  (h'.cone.app (F.obj t))).symm

end PreservesInitialComponents
