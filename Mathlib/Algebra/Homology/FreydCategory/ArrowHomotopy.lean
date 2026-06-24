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
public import Mathlib.CategoryTheory.Limits.Comma

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
  comm : f.left - g.left = u.hom ≫ hom := by cat_disch

/-- A right homotopy on morphisms in the category of arrows of a preadditive category. -/
@[ext]
structure RightHomotopy where
  hom : u.right ⟶ v.left
  comm : f.right - g.right = hom ≫ v.hom := by cat_disch

variable {f g}

namespace LeftHomotopy

/-- `f` is homotopic to `g` iff `f - g` is homotopic to `0`.
-/
def equivSubZero : LeftHomotopy f g ≃ LeftHomotopy (f - g) 0 where
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
def ofEq (h : f = g) : LeftHomotopy f g where
  hom := 0

/-- Every chain map is homotopic to itself. -/
@[simps!, refl]
def refl (f : u ⟶ v) : LeftHomotopy f f :=
  ofEq (rfl : f = f)

/-- `f` is homotopic to `g` iff `g` is homotopic to `f`. -/
@[simps!, symm]
def symm {f g : u ⟶ v} (h : LeftHomotopy f g) : LeftHomotopy g f where
  hom := -h.hom
  comm := by simp [← h.comm]

/-- homotopy is a transitive relation. -/
@[simps!, trans]
def trans {e f g : u ⟶ v} (h : LeftHomotopy e f) (k : LeftHomotopy f g) : LeftHomotopy e g where
  hom := h.hom + k.hom
  comm := by simp [← h.comm, ← k.comm]

/-- the sum of two homotopies is a homotopy between the sum of the respective morphisms. -/
@[simps!]
def add {f₁ g₁ f₂ g₂ : u ⟶ v} (h₁ : LeftHomotopy f₁ g₁) (h₂ : LeftHomotopy f₂ g₂) :
    LeftHomotopy (f₁ + f₂) (g₁ + g₂) where
  hom := h₁.hom + h₂.hom
  comm := by simp [← h₁.comm, ← h₂.comm, add_sub_add_comm]

/-- homotopy is closed under composition (on the right) -/
@[simps]
def compRight {e f : u ⟶ v} (h : LeftHomotopy e f) (g : v ⟶ w) :
    LeftHomotopy (e ≫ g) (f ≫ g) where
  hom := h.hom ≫ g.left
  comm := by simp [← reassoc_of% h.comm]

/-- homotopy is closed under composition (on the left) -/
@[simps]
def compLeft {f g : v ⟶ w} (h : LeftHomotopy f g) (e : u ⟶ v) :
    LeftHomotopy (e ≫ f) (e ≫ g) where
  hom := e.right ≫ h.hom
  comm := by simp [← reassoc_of% e.w, ← h.comm]

/-- homotopy is closed under composition -/
@[simps!]
def comp {f₁ g₁ : u ⟶ v} {f₂ g₂ : v ⟶ w}
    (h₁ : LeftHomotopy f₁ g₁) (h₂ : LeftHomotopy f₂ g₂) : LeftHomotopy (f₁ ≫ f₂) (g₁ ≫ g₂) :=
  (h₁.compRight _).trans (h₂.compLeft _)

/-- a variant of `LeftHomotopy.compRight` useful for dealing with homotopy equivalences. -/
@[simps!]
def compRightId {f : u ⟶ u} (h : LeftHomotopy f (𝟙 u)) (g : u ⟶ v) : LeftHomotopy (f ≫ g) g :=
  (h.compRight g).trans (ofEq <| id_comp _)

/-- a variant of `LeftHomotopy.compLeft` useful for dealing with homotopy equivalences. -/
@[simps!]
def compLeftId {f : v ⟶ v} (h : LeftHomotopy f (𝟙 v)) (g : u ⟶ v) : LeftHomotopy (g ≫ f) g :=
  (h.compLeft g).trans (ofEq <| comp_id _)

end LeftHomotopy

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
  comm := by simp [← h.comm]

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

variable {V}

-- Is this used?
lemma quotient_obj_surjective (X : RightFreyd V) :
    ∃ (u : Arrow V), (quotient _).obj u = X :=
  ⟨_, rfl⟩

theorem eq_of_homotopy {u v : Arrow V} (f g : u ⟶ v) (h : RightHomotopy f g) :
    (quotient V).map f = (quotient V).map g :=
  CategoryTheory.Quotient.sound _ ⟨h⟩

/-- If two morphisms of `Arrow V` become equal in the right Freyd category,
then they are right homotopic. -/
def homotopyOfEq {u v : Arrow V} (f g : u ⟶ v)
    (w : (quotient V).map f = (quotient V).map g) : RightHomotopy f g :=
  ((Quotient.functor_map_eq_iff _ _ _).mp w).some

lemma quotient_map_eq_zero_iff {u v : Arrow V} (f : u ⟶ v) :
    (quotient V).map f = 0 ↔ Nonempty (RightHomotopy f 0) :=
  ⟨fun h ↦ ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ ↦ by simpa using eq_of_homotopy _ _ h⟩

lemma isEpi_of_right_iso [IsIso f.right] : Epi ((quotient V).map f) where
  left_cancellation g₁ g₂ eq := by
    obtain ⟨g₁, rfl⟩ := (quotient V).map_surjective g₁
    obtain ⟨g₂, rfl⟩ := (quotient V).map_surjective g₂
    apply eq_of_homotopy
    erw [← (quotient V).map_comp, ← (quotient V).map_comp] at eq
    set h := homotopyOfEq _ _ eq
    exact ⟨inv f.right ≫ h.hom, by simp [← h.comm]⟩

section ZeroObject

open ZeroObject

variable [HasZeroObject V]

instance : Inhabited (RightFreyd V) := ⟨(quotient V).obj 0⟩

/--
If `V` has zero objects, so does `RightFreyd V`.
-/
instance : HasZeroObject (RightFreyd V) :=
  ⟨(quotient V).obj 0, by
    rw [IsZero.iff_id_eq_zero, ← (quotient V).map_id, id_zero, Functor.map_zero]⟩

end ZeroObject

section Cokernels

variable [HasBinaryBiproducts V]

namespace Candidate

variable {u v : Arrow V} (f : u ⟶ v)

def cokernel : Arrow V := Arrow.mk (biprod.desc v.hom f.right)

def π : v ⟶ cokernel f := by
  refine Arrow.homMk biprod.inl (𝟙 v.right) ?_
  simp only [cokernel, mk_hom]
  erw [biprod.inl_desc, Category.comp_id]

def condition : RightHomotopy (f ≫ π f) 0 where
  hom := biprod.inr
  comm := by
    simp only [cokernel, π, comp_right, homMk_right, Hom.zero_right, mk_hom]
    erw [Category.comp_id, biprod.inr_desc, sub_zero]

set_option backward.isDefEq.respectTransparency false in
instance isEpi_π : Epi ((quotient V).map (π f)) :=
  have : IsIso ((π f).right) := by simp only [π, homMk_right]; infer_instance
  isEpi_of_right_iso

variable {w : Arrow V} (g : v ⟶ w) (h : RightHomotopy (f ≫ g) 0)

def desc : cokernel f ⟶ w := by
  refine Arrow.homMk (biprod.desc g.left h.hom) g.right ?_
  simp only [cokernel, mk_hom]
  apply biprod.hom_ext'
  · erw [biprod.inl_desc_assoc, biprod.inl_desc_assoc]
    rw [g.w]
    rfl
  · erw [biprod.inr_desc_assoc, biprod.inr_desc_assoc]
    rw [← h.comm]
    simp only [comp_right, Hom.zero_right, sub_zero]
    rfl

@[reassoc]
lemma π_desc : π f ≫ desc f g h = g := by
  simp only [cokernel, π, desc]
  ext
  · simp only [comp_left, homMk_left]
    exact biprod.inl_desc _ _
  · simp only [comp_right, homMk_right]
    exact Category.id_comp _

variable {X : RightFreyd V} {a : (quotient V).obj v ⟶ X} (eq : (quotient V).map f ≫ a = 0)

def desc' : (quotient V).obj (cokernel f) ⟶ X := by
  rw [← ((quotient V).map_surjective a).choose_spec] at eq
  exact (quotient V).map (Candidate.desc _ _ (homotopyOfEq _ _ eq))

lemma π_desc' : (quotient V).map (π f) ≫ desc' f eq = a := by
  rw [← ((quotient V).map_surjective a).choose_spec] at eq
  conv_rhs => rw [← ((quotient V).map_surjective a).choose_spec,
                      ← Candidate.π_desc _ _ (homotopyOfEq _ _ eq)]
  rfl

end Candidate

variable (f)

def candidateCokernelCofork : Cocone (parallelPair ((quotient V).map f) 0) := by
  refine CokernelCofork.ofπ ((quotient V).map (Candidate.π f)) ?_
  rw [← (quotient V).map_comp]
  exact eq_of_homotopy _ _ (Candidate.condition f)

def candidateCokernelCoforkIsCokernel : IsColimit (candidateCokernelCofork f) where
  desc s := Candidate.desc' f (CokernelCofork.condition s)
  fac s j :=
    match j with
    | WalkingParallelPair.zero => by
      simp only [Cofork.app_zero_eq_comp_π_left, CokernelCofork.condition]
      exact zero_comp
    | WalkingParallelPair.one => Candidate.π_desc' f (CokernelCofork.condition s)
  uniq s m eq :=
    (cancel_epi ((quotient V).map (Candidate.π f))).mp ((eq WalkingParallelPair.one).trans
    (Candidate.π_desc' f (CokernelCofork.condition s)).symm)

instance : HasCokernels (RightFreyd V) where
  has_colimit {X Y} f := {
    exists_colimit := by
      obtain ⟨f, rfl⟩ := (quotient V).map_surjective f
      exact Nonempty.intro {
        cocone := candidateCokernelCofork f
        isColimit := candidateCokernelCoforkIsCokernel f}}

end Cokernels

end RightFreyd

end CategoryTheory.Arrow
