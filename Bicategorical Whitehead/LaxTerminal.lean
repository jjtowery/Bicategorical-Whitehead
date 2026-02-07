/-
Copyright (c) 2026 Judah Towery. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judah Towery
-/

import «Bicategorical Whitehead».Const
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Lax
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-
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

For lax functors `F, G : B ⟶ C`, a lax tranformation `k : F ⟶ G` is inc-lax if each component
`k_X : FX ⟶ GX` is initial in the category `C(FX, GX)`.

If `t ∈ C` is lax terminal with lax transformation `k : Id_C ⟶ Δₜ`, `t` is an inc-lax
terminal object if `k` is inc-lax, and the component `kₜ` is the identity 1-cell `1ₜ`.

If `B, C` have inc-lax terminal objects `(t, k), (t', k')` respectively, a lax functor `F : B → C`
preserves initial components if the composite
    
```  
     Fk_X      k'_(Ft)
FX -------> Ft -------> t'
```
is initial in `C(FX, t)`.

-/

namespace CategoryTheory.Bicategory

open Category Bicategory

universe w₁ w₂ v₁ v₂

variable {B C : Type*} [Bicategory.{w₁, v₁} B] [Bicategory.{w₂, v₂} C]

@[simp]
abbrev LaxTerminalData (t : C) : Type _ := Lax.LaxTrans (LaxFunctor.id C) (const C t)

/-- Lax terminal objects. -/
class IsLaxTerminal (t : C) : Prop where
  exists_laxTerminalData : Nonempty (LaxTerminalData t)

namespace LaxTerminal

noncomputable def choose (t : C) [h : IsLaxTerminal t] : LaxTerminalData t := 
  Classical.choice h.exists_laxTerminalData

end LaxTerminal

/-- Inc-lax transformation. -/
class IsIncLax {F G : B ⥤ᴸ C} (k : Lax.LaxTrans F G) : Type _ where
  app_isInitial (X : B) : Limits.IsInitial (k.app X)
