/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.Homology.FreydCategory.ArrowHomotopy

/-!
# Homotopies in the arrow category

We define left and right homotopies between arrows.
-/

@[expose] public section

--universe v u

noncomputable section

open CategoryTheory Category Limits HomologicalComplex Arrow

variable (V : Type*) [Category* V] [Preadditive V]

namespace CategoryTheory

/-- If `V` is a preadditive category, then `RightFreyd V` is the category of arrows in `V`,
with morphisms identified when they are right homotopic. -/
def RightFreyd :=
  CategoryTheory.Quotient (rightHomotopic V)

instance : Category (RightFreyd V) :=
  inferInstanceAs <| Category (CategoryTheory.Quotient (rightHomotopic V))

namespace RightFreyd

instance : Preadditive (CategoryTheory.Quotient (rightHomotopic V)) :=
  Quotient.preadditive _ (by
    rintro _ _ _ _ _ _ ⟨h⟩ ⟨h'⟩
    exact ⟨RightHomotopy.add h h'⟩)

instance : Preadditive (RightFreyd V) :=
  inferInstanceAs <| Preadditive (CategoryTheory.Quotient (rightHomotopic V))

/-- The quotient functor from complexes to the homotopy category. -/
def quotient : Arrow V ⥤ RightFreyd V :=
  CategoryTheory.Quotient.functor _

instance : (quotient V).Full := Quotient.full_functor _

instance : (quotient V).EssSurj := Quotient.essSurj_functor _

instance : (quotient V).Additive where

instance : Functor.Additive (Quotient.functor (rightHomotopic V)) where

variable {V}

-- Is this used?
lemma quotient_obj_surjective (X : RightFreyd V) :
    ∃ (u : Arrow V), (quotient _).obj u = X :=
  ⟨_, rfl⟩

/-- If two morphisms in `Arrow V` are right homotopic, then they become equal in the right
Freyd category. -/
theorem eq_of_rightHomotopy {u v : Arrow V} (f g : u ⟶ v) (h : RightHomotopy f g) :
    (quotient V).map f = (quotient V).map g :=
  CategoryTheory.Quotient.sound _ ⟨h⟩

/-- If two morphisms of `Arrow V` become equal in the right Freyd category,
then they are right homotopic. -/
def homotopyOfEq {u v : Arrow V} (f g : u ⟶ v)
    (w : (quotient V).map f = (quotient V).map g) : RightHomotopy f g :=
  ((Quotient.functor_map_eq_iff _ _ _).mp w).some

variable {u v : Arrow V} (f : u ⟶ v)

lemma quotient_map_eq_zero_iff : (quotient V).map f = 0 ↔ Nonempty (RightHomotopy f 0) :=
  ⟨fun h ↦ ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ ↦ by simpa using eq_of_rightHomotopy _ _ h⟩

/--
If `f` is a morphism of `Arrow V` such that `f.right` is an isomorphism, then the image of `f`
in the right Freyd category is an epimorphism. -/
lemma isEpi_of_right_iso [IsIso f.right] : Epi ((quotient V).map f) where
  left_cancellation g₁ g₂ eq := by
    obtain ⟨g₁, rfl⟩ := (quotient V).map_surjective g₁
    obtain ⟨g₂, rfl⟩ := (quotient V).map_surjective g₂
    apply eq_of_rightHomotopy
    erw [← (quotient V).map_comp, ← (quotient V).map_comp] at eq
    set h := homotopyOfEq _ _ eq
    exact ⟨inv f.right ≫ h.hom, by simp [← h.comm]⟩

end RightFreyd



end CategoryTheory
