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

noncomputable section

open CategoryTheory Category Limits HomologicalComplex Arrow

variable (V : Type*) [Category* V] [Preadditive V]

namespace CategoryTheory.Preadditive

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

/-- The quotient functor from `Arrow V` to `RightFreyd V`. -/
def quotient : Arrow V ⥤ RightFreyd V :=
  CategoryTheory.Quotient.functor _

instance : (quotient V).Full := Quotient.full_functor _

instance : (quotient V).EssSurj := Quotient.essSurj_functor _

instance : (quotient V).Additive where

--instance : Functor.Additive (Quotient.functor (rightHomotopic V)) where

variable {V}

/-
-- Is this used?
lemma quotient_obj_surjective (X : RightFreyd V) :
    ∃ (u : Arrow V), (quotient _).obj u = X :=
  ⟨_, rfl⟩
-/

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
    set h : RightHomotopy (f ≫ g₁) (f ≫ g₂) := homotopyOfEq _ _ eq
    exact ⟨inv f.right ≫ h.hom, by simp [dsimp% h.comm]⟩

end RightFreyd

/-- If `V` is a preadditive category, then `LeftFreyd V` is the category of arrows in `V`,
with morphisms identified when they are left homotopic. -/
def LeftFreyd :=
  CategoryTheory.Quotient (leftHomotopic V)

instance : Category (LeftFreyd V) :=
  inferInstanceAs <| Category (CategoryTheory.Quotient (leftHomotopic V))

namespace LeftFreyd

instance : Preadditive (CategoryTheory.Quotient (leftHomotopic V)) :=
  Quotient.preadditive _ (by
    rintro _ _ _ _ _ _ ⟨h⟩ ⟨h'⟩
    exact ⟨LeftHomotopy.add h h'⟩)

instance : Preadditive (LeftFreyd V) :=
  inferInstanceAs <| Preadditive (CategoryTheory.Quotient (leftHomotopic V))

/-- The quotient functor from `Arrow V` to `LeftFreyd V`. -/
def quotient : Arrow V ⥤ LeftFreyd V :=
  CategoryTheory.Quotient.functor _

instance : (quotient V).Full := Quotient.full_functor _

instance : (quotient V).EssSurj := Quotient.essSurj_functor _

instance : (quotient V).Additive where

--instance : Functor.Additive (Quotient.functor (leftHomotopic V)) where

variable {V}

/-
-- Is this used?
lemma quotient_obj_surjective (X : LeftFreyd V) :
    ∃ (u : Arrow V), (quotient _).obj u = X :=
  ⟨_, rfl⟩
-/

/-- If two morphisms in `Arrow V` are left homotopic, then they become equal in the left
Freyd category. -/
theorem eq_of_leftHomotopy {u v : Arrow V} (f g : u ⟶ v) (h : LeftHomotopy f g) :
    (quotient V).map f = (quotient V).map g :=
  CategoryTheory.Quotient.sound _ ⟨h⟩

/-- If two morphisms of `Arrow V` become equal in the left Freyd category,
then they are rleft homotopic. -/
def homotopyOfEq {u v : Arrow V} (f g : u ⟶ v)
    (w : (quotient V).map f = (quotient V).map g) : LeftHomotopy f g :=
  ((Quotient.functor_map_eq_iff _ _ _).mp w).some

variable {u v : Arrow V} (f : u ⟶ v)

lemma quotient_map_eq_zero_iff : (quotient V).map f = 0 ↔ Nonempty (LeftHomotopy f 0) :=
  ⟨fun h ↦ ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ ↦ by simpa using eq_of_leftHomotopy _ _ h⟩

/--
If `f` is a morphism of `Arrow V` such that `f.left` is an isomorphism, then the image of `f`
in the right Freyd category is a monomorphism. -/
lemma isMono_of_left_iso [IsIso f.left] : Mono ((quotient V).map f) where
  right_cancellation g₁ g₂ eq := by
    obtain ⟨g₁, rfl⟩ := (quotient V).map_surjective g₁
    obtain ⟨g₂, rfl⟩ := (quotient V).map_surjective g₂
    apply eq_of_leftHomotopy
    set h : LeftHomotopy (g₁ ≫ f) (g₂ ≫ f) := homotopyOfEq _ _ eq
    exact ⟨h.hom ≫ inv f.left, by simp [← cancel_mono f.left, dsimp% h.comm]⟩

end LeftFreyd

end CategoryTheory.Preadditive
