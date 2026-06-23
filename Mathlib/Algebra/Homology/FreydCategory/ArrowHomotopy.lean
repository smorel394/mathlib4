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

variable {u v : Arrow V} (f g : u ⟶ v)

/-- A left homotopy on morphisms in the category of arrows of a preadditive category. -/
@[ext]
structure LeftHomotopy where
  hom : u.right ⟶ v.left
  comm : f.right - g.right = hom ≫ v.hom := by cat_disch

/-- A right homotopy on morphisms in the category of arrows of a preadditive category. -/
@[ext]
structure RightHomotopy where
  hom : u.right ⟶ v.left
  comm : f.left - g.left = u.hom ≫ hom

variable {f g}

namespace RightHomotopy

/-- `f` is homotopic to `g` iff `f - g` is homotopic to `0`.
-/
def equivSubZero : RightHomotopy f g ≃ RightHomotopy (f - g) 0 where
  toFun h :=
    { hom := fun i j => h.hom i j
      zero := fun _ _ w => h.zero _ _ w
      comm := fun i => by simp [h.comm] }
  invFun h :=
    { hom := fun i j => h.hom i j
      zero := fun _ _ w => h.zero _ _ w
      comm := fun i => by simpa [sub_eq_iff_eq_add] using h.comm i }
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- Equal chain maps are homotopic. -/
@[simps]
def ofEq (h : f = g) : Homotopy f g where
  hom := 0
  zero _ _ _ := rfl

/-- Every chain map is homotopic to itself. -/
@[simps!, refl]
def refl (f : C ⟶ D) : Homotopy f f :=
  ofEq (rfl : f = f)

/-- `f` is homotopic to `g` iff `g` is homotopic to `f`. -/
@[simps!, symm]
def symm {f g : C ⟶ D} (h : Homotopy f g) : Homotopy g f where
  hom := -h.hom
  zero i j w := by rw [Pi.neg_apply, Pi.neg_apply, h.zero i j w, neg_zero]
  comm i := by
    rw [map_neg, map_neg, h.comm, ← neg_add, ← add_assoc, neg_add_cancel, zero_add]

/-- homotopy is a transitive relation. -/
@[simps!, trans]
def trans {e f g : C ⟶ D} (h : Homotopy e f) (k : Homotopy f g) : Homotopy e g where
  hom := h.hom + k.hom
  zero i j w := by rw [Pi.add_apply, Pi.add_apply, h.zero i j w, k.zero i j w, zero_add]
  comm i := by grind [Homotopy.comm]

/-- the sum of two homotopies is a homotopy between the sum of the respective morphisms. -/
@[simps!]
def add {f₁ g₁ f₂ g₂ : C ⟶ D} (h₁ : Homotopy f₁ g₁) (h₂ : Homotopy f₂ g₂) :
    Homotopy (f₁ + f₂) (g₁ + g₂) where
  hom := h₁.hom + h₂.hom
  zero i j hij := by rw [Pi.add_apply, Pi.add_apply, h₁.zero i j hij, h₂.zero i j hij, add_zero]
  comm i := by grind [HomologicalComplex.add_f_apply, Homotopy.comm]

set_option backward.defeqAttrib.useBackward true in
/-- the scalar multiplication of a homotopy -/
@[simps!]
def smul {R : Type*} [Semiring R] [Linear R V] (h : Homotopy f g) (a : R) :
    Homotopy (a • f) (a • g) where
  hom i j := a • h.hom i j
  zero i j hij := by
    rw [h.zero i j hij, smul_zero]
  comm i := by
    dsimp
    rw [h.comm]
    dsimp [fromNext, toPrev]
    simp only [smul_add, Linear.comp_smul, Linear.smul_comp]

/-- homotopy is closed under composition (on the right) -/
@[simps]
def compRight {e f : C ⟶ D} (h : Homotopy e f) (g : D ⟶ E) : Homotopy (e ≫ g) (f ≫ g) where
  hom i j := h.hom i j ≫ g.f j
  zero i j w := by rw [h.zero i j w, zero_comp]
  comm i := by rw [comp_f, h.comm i, dNext_comp_right, prevD_comp_right, Preadditive.add_comp,
    comp_f, Preadditive.add_comp]

/-- homotopy is closed under composition (on the left) -/
@[simps]
def compLeft {f g : D ⟶ E} (h : Homotopy f g) (e : C ⟶ D) : Homotopy (e ≫ f) (e ≫ g) where
  hom i j := e.f i ≫ h.hom i j
  zero i j w := by rw [h.zero i j w, comp_zero]
  comm i := by rw [comp_f, h.comm i, dNext_comp_left, prevD_comp_left, comp_f,
    Preadditive.comp_add, Preadditive.comp_add]

/-- homotopy is closed under composition -/
@[simps!]
def comp {C₁ C₂ C₃ : HomologicalComplex V c} {f₁ g₁ : C₁ ⟶ C₂} {f₂ g₂ : C₂ ⟶ C₃}
    (h₁ : Homotopy f₁ g₁) (h₂ : Homotopy f₂ g₂) : Homotopy (f₁ ≫ f₂) (g₁ ≫ g₂) :=
  (h₁.compRight _).trans (h₂.compLeft _)

/-- a variant of `Homotopy.compRight` useful for dealing with homotopy equivalences. -/
@[simps!]
def compRightId {f : C ⟶ C} (h : Homotopy f (𝟙 C)) (g : C ⟶ D) : Homotopy (f ≫ g) g :=
  (h.compRight g).trans (ofEq <| id_comp _)

/-- a variant of `Homotopy.compLeft` useful for dealing with homotopy equivalences. -/
@[simps!]
def compLeftId {f : D ⟶ D} (h : Homotopy f (𝟙 D)) (g : C ⟶ D) : Homotopy (g ≫ f) g :=
  (h.compLeft g).trans (ofEq <| comp_id _)

end RightHomotopy


end CategoryTheory.Arrow
