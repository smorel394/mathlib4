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

variable {V₁ : Type*} [Category* V₁] [Preadditive V₁] {V₂ : Type*} [Category* V₂] [Preadditive V₂]
  (G : V₁ ⥤ V₂) [G.Additive]
  {C : Type*} [Category* C] [Preadditive C] [HasCokernels C] (F : V₁ ⥤ C) [F.Additive]

namespace CategoryTheory

namespace Functor

set_option backward.isDefEq.respectTransparency false in
@[simps!]
def mapRightFreyd : RightFreyd V₁ ⥤ RightFreyd V₂ :=
  Quotient.lift (rightHomotopic V₁) (G.mapArrow ⋙ quotient V₂)
  (fun _ _ _ _ ⟨h⟩ ↦ (eq_of_rightHomotopy _ _ ⟨G.map h.hom, by simp [← G.map_sub, h.comm]; rfl⟩))

set_option backward.isDefEq.respectTransparency false in
@[simps!]
def mapRightFreyd_id : (𝟭 V₁).mapRightFreyd ≅ 𝟭 (RightFreyd V₁) :=
  Quotient.natIsoLift _ (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp; rfl))

variable {V₃ : Type*} [Category* V₃] [Preadditive V₃] (H : V₂ ⥤ V₃) [H.Additive]

set_option backward.isDefEq.respectTransparency false in
@[simps!]
def mapRightFreyd_comp : (G ⋙ H).mapRightFreyd ≅ G.mapRightFreyd ⋙ H.mapRightFreyd :=
  Quotient.natIsoLift _ (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp; rfl))

variable [HasZeroObject V₁] [HasZeroObject V₂] in
def functorMapRightFreydIso : functor V₁ ⋙ G.mapRightFreyd ≅ G ⋙ functor V₂ :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Quotient.lift.isLift _ _ _) ≪≫
  Functor.isoWhiskerRight (rightFunctorMapArrowIso G) (quotient V₂)

-- `G.mapRightFreyd` preserves cokernels.

end Functor

namespace NatTrans

variable {G} {G' G'' : V₁ ⥤ V₂} [G'.Additive] [G''.Additive] (α : G ⟶ G')

def mapRightFreyd : G.mapRightFreyd ⟶ G'.mapRightFreyd :=
  Quotient.natTransLift _ ((Quotient.lift.isLift _ _ _).hom ≫ Functor.whiskerRight
  ((Functor.mapArrowFunctor V₁ V₂).map α) (quotient V₂) ≫ (Quotient.lift.isLift _ _ _).inv)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma mapRightFreyd_app (a : RightFreyd V₁) : α.mapRightFreyd.app a =
    (quotient V₂).map (homMk (α.app a.as.left) (α.app a.as.right) (α.naturality a.as.hom).symm):=
  (id_comp _).trans (comp_id _)

@[simp]
lemma mapRightFreyd_id : NatTrans.mapRightFreyd (𝟙 G) = 𝟙 G.mapRightFreyd := by cat_disch

@[simp]
lemma mapRightFreyd_comp (β : G' ⟶ G'') :
    (α ≫ β).mapRightFreyd = α.mapRightFreyd ≫ β.mapRightFreyd := by cat_disch

end NatTrans

namespace Functor

@[simps]
def mapRightFreydFunctor : (V₁ ⥤+ V₂) ⥤ (RightFreyd V₁ ⥤ RightFreyd V₂) where
  obj F := Functor.mapRightFreyd F.1
  map {F G} α := α.hom.mapRightFreyd

end Functor

end CategoryTheory
