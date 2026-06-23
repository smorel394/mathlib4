/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Tactic.Abel
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Preadditive.Comma
public import Mathlib.CategoryTheory.Quotient.Preadditive

/-!
# Homotopies in the arrow category

We define left and right homotopies between arrows.
-/

@[expose] public section

universe v u

noncomputable section

open CategoryTheory Category Limits HomologicalComplex

variable {V : Type u} [Category.{v} V] [Preadditive V]

namespace CategoryTheory.Arrow

variable {u v w : Arrow V} (f g : u ⟶ v)

/-- A left homotopy on morphisms in the category of arrows of a preadditive category. -/
@[ext]
structure LeftHomotopy where
  hom : u.right ⟶ v.left
  comm : f.right - g.right = hom ≫ v.hom := by cat_disch

/-- A right homotopy on morphisms in the category of arrows of a preadditive category. -/
@[ext]
structure RightHomotopy where
  hom : u.right ⟶ v.left
  comm : f.left - g.left = u.hom ≫ hom := by cat_disch

variable {f g}

namespace RightHomotopy

/-- `f` is homotopic to `g` iff `f - g` is homotopic to `0`.
-/
def equivSubZero : RightHomotopy f g ≃ RightHomotopy (f - g) 0 where
  toFun h :=
    { hom := h.hom
      comm := by simp [← h.comm]}
  invFun h :=
    { hom := h.hom
      comm := by simp [← h.comm]}
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- Equal chain maps are homotopic. -/
@[simps]
def ofEq (h : f = g) : RightHomotopy f g where
  hom := 0

/-- Every chain map is homotopic to itself. -/
@[simps!, refl]
def refl (f : u ⟶ v) : RightHomotopy f f :=
  ofEq (rfl : f = f)

/-- `f` is homotopic to `g` iff `g` is homotopic to `f`. -/
@[simps!, symm]
def symm {f g : u ⟶ v} (h : RightHomotopy f g) : RightHomotopy g f where
  hom := -h.hom
  comm := by simp [← h.comm]

/-- homotopy is a transitive relation. -/
@[simps!, trans]
def trans {e f g : u ⟶ v} (h : RightHomotopy e f) (k : RightHomotopy f g) : RightHomotopy e g where
  hom := h.hom + k.hom
  comm := by simp [← h.comm, ← k.comm]

/-- the sum of two homotopies is a homotopy between the sum of the respective morphisms. -/
@[simps!]
def add {f₁ g₁ f₂ g₂ : u ⟶ v} (h₁ : RightHomotopy f₁ g₁) (h₂ : RightHomotopy f₂ g₂) :
    RightHomotopy (f₁ + f₂) (g₁ + g₂) where
  hom := h₁.hom + h₂.hom
  comm := by simp [← h₁.comm, ← h₂.comm, add_sub_add_comm]

/-- homotopy is closed under composition (on the right) -/
@[simps]
def compRight {e f : u ⟶ v} (h : RightHomotopy e f) (g : v ⟶ w) :
    RightHomotopy (e ≫ g) (f ≫ g) where
  hom := h.hom ≫ g.left
  comm := by simp [← reassoc_of% h.comm]

/-- homotopy is closed under composition (on the left) -/
@[simps]
def compLeft {f g : v ⟶ w} (h : RightHomotopy f g) (e : u ⟶ v) :
    RightHomotopy (e ≫ f) (e ≫ g) where
  hom := e.right ≫ h.hom
  comm := by simp [← reassoc_of% e.w, ← h.comm]

/-- homotopy is closed under composition -/
@[simps!]
def comp {f₁ g₁ : u ⟶ v} {f₂ g₂ : v ⟶ w}
    (h₁ : RightHomotopy f₁ g₁) (h₂ : RightHomotopy f₂ g₂) : RightHomotopy (f₁ ≫ f₂) (g₁ ≫ g₂) :=
  (h₁.compRight _).trans (h₂.compLeft _)

/-- a variant of `RightHomotopy.compRight` useful for dealing with homotopy equivalences. -/
@[simps!]
def compRightId {f : u ⟶ u} (h : RightHomotopy f (𝟙 u)) (g : u ⟶ v) : RightHomotopy (f ≫ g) g :=
  (h.compRight g).trans (ofEq <| id_comp _)

/-- a variant of `RightHomotopy.compLeft` useful for dealing with homotopy equivalences. -/
@[simps!]
def compLeftId {f : v ⟶ v} (h : RightHomotopy f (𝟙 v)) (g : u ⟶ v) : RightHomotopy (g ≫ f) g :=
  (h.compLeft g).trans (ofEq <| comp_id _)

end RightHomotopy

variable (V)

def rightHomotopic : HomRel (Arrow V) := fun _ _ f g => Nonempty (RightHomotopy f g)

instance rightHomotopy_congruence : Congruence (rightHomotopic V) where
  equivalence :=
    { refl := fun C => ⟨RightHomotopy.refl C⟩
      symm := fun ⟨w⟩ => ⟨w.symm⟩
      trans := fun ⟨w₁⟩ ⟨w₂⟩ => ⟨w₁.trans w₂⟩ }
  comp_left := fun _ _ _ ⟨i⟩ => ⟨i.compLeft _⟩
  comp_right := fun _ ⟨i⟩ => ⟨i.compRight _⟩

/-- `RightFreyd V` is the category of arrows in `V`,
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

open ZeroObject

instance [HasZeroObject V] : Inhabited (RightFreyd V) :=
  ⟨(quotient V).obj 0⟩

instance [HasZeroObject V] : HasZeroObject (RightFreyd V) :=
  ⟨(quotient V).obj 0, by
    rw [IsZero.iff_id_eq_zero, ← (quotient V c).map_id, id_zero, Functor.map_zero]⟩

end RightFreyd

end CategoryTheory.Arrow
