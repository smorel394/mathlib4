/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Preadditive.FreydCategory.RightFreyd
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Tactic.ApplyFun

/-!

# Functoriality of the right Freyd category

-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits Arrow Preadditive RightFreyd

variable {V : Type*} [Category* V] [Preadditive V] {W : Type*} [Category* W] [Preadditive W]
  (G : V ⥤ W) [G.Additive]
  {C : Type*} [Category* C] [Preadditive C] [HasCokernels C] (F : V ⥤ C) [F.Additive]

namespace CategoryTheory

namespace Functor

set_option backward.isDefEq.respectTransparency false in
@[simps!]
def mapRightFreyd : RightFreyd V ⥤ RightFreyd W :=
  Quotient.lift (rightHomotopic V) (G.mapArrow ⋙ quotient W)
  (fun _ _ _ _ ⟨h⟩ ↦ (eq_of_rightHomotopy _ _ ⟨G.map h.hom, by simp [← G.map_sub, h.comm]; rfl⟩))

def mapRightFreydFunctor : (V ⥤+ W) ⥤ (RightFreyd V ⥤ RightFreyd W) where
  obj F := Functor.mapRightFreyd F.1
  map {F G} α := by
    refine Quotient.natTransLift _ ?_
    refine (Quotient.lift.isLift _ _ _).hom ≫ ?_ ≫ (Quotient.lift.isLift _ _ _).inv
  map_id := sorry
  map_comp := sorry

end Functor

end CategoryTheory
