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
public import Mathlib.Algebra.Homology.FreydCategory.WeakProduct

/-!
# Homotopies in the arrow category

We define left and right homotopies between arrows.
-/

@[expose] public section

universe v u

noncomputable section

open CategoryTheory Category Limits HomologicalComplex Arrow

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

end Arrow

variable (V)

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

lemma isEpi_of_right_iso [IsIso f.right] : Epi ((quotient V).map f) where
  left_cancellation g₁ g₂ eq := by
    obtain ⟨g₁, rfl⟩ := (quotient V).map_surjective g₁
    obtain ⟨g₂, rfl⟩ := (quotient V).map_surjective g₂
    apply eq_of_rightHomotopy
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

variable [HasFiniteProducts V]

local instance : HasBinaryBiproducts V := HasBinaryBiproducts.of_hasBinaryProducts

namespace CandidateCokernel

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
  isEpi_of_right_iso _

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
  exact (quotient V).map (CandidateCokernel.desc _ _ (homotopyOfEq _ _ eq))

lemma π_desc' : (quotient V).map (π f) ≫ desc' f eq = a := by
  rw [← ((quotient V).map_surjective a).choose_spec] at eq
  conv_rhs => rw [← ((quotient V).map_surjective a).choose_spec,
                      ← CandidateCokernel.π_desc _ _ (homotopyOfEq _ _ eq)]
  rfl

end CandidateCokernel

def candidateCokernelCofork : Cocone (parallelPair ((quotient V).map f) 0) := by
  refine CokernelCofork.ofπ ((quotient V).map (CandidateCokernel.π f)) ?_
  rw [← (quotient V).map_comp]
  exact eq_of_rightHomotopy _ _ (CandidateCokernel.condition f)

def candidateCokernelCoforkIsCokernel : IsColimit (candidateCokernelCofork f) where
  desc s := CandidateCokernel.desc' f (CokernelCofork.condition s)
  fac s j :=
    match j with
    | WalkingParallelPair.zero => by
      simp only [Cofork.app_zero_eq_comp_π_left, CokernelCofork.condition]
      exact zero_comp
    | WalkingParallelPair.one => CandidateCokernel.π_desc' f (CokernelCofork.condition s)
  uniq s m eq :=
    (cancel_epi ((quotient V).map (CandidateCokernel.π f))).mp ((eq WalkingParallelPair.one).trans
    (CandidateCokernel.π_desc' f (CokernelCofork.condition s)).symm)

instance : HasCokernels (RightFreyd V) where
  has_colimit {X Y} f := {
    exists_colimit := by
      obtain ⟨f, rfl⟩ := (quotient V).map_surjective f
      exact Nonempty.intro {
        cocone := candidateCokernelCofork f
        isColimit := candidateCokernelCoforkIsCokernel f}}

end Cokernels

section Kernels

variable [HasBinaryProducts V] [HasWeakKernels V]

local instance : HasWeakEqualizers V := Preadditive.hasWeakEqualizers_of_hasWeakKernels

local instance : HasWeakPullbacks V := hasWeakPullbacks_of_hasBinaryProducts_of_hasWeakKernels V

namespace CandidateKernel

variable {u v : Arrow V} (f : u ⟶ v)

def kernel : Arrow V := Arrow.mk (weakPullback.fst (weakPullback.snd v.hom f.right) u.hom)

def ι : kernel f ⟶ u := by
  refine Arrow.homMk (weakPullback.snd _ _) (weakPullback.snd _ _) ?_
  simp only [kernel, mk_hom]
  erw [← weakPullback.condition]
  rfl

def condition : RightHomotopy (ι f ≫ f) 0 where
  hom := weakPullback.fst _ _
  comm := by
    simp only [ι, comp_right, homMk_right, Hom.zero_right, sub_zero]
    erw [weakPullback.condition]
    rfl

lemma isMono_of_witness_snd {X Y Z : V} (a : X ⟶ Z) (b : Y ⟶ Z) :
    Mono ((quotient V).map (Arrow.homMk (f := Arrow.mk (weakPullback.fst a b)) (g := Arrow.mk b)
    (weakPullback.snd _ _) a weakPullback.condition.symm )) where
  right_cancellation g₁ g₂ eq := by
    obtain ⟨g₁, rfl⟩ := (quotient V).map_surjective g₁
    obtain ⟨g₂, rfl⟩ := (quotient V).map_surjective g₂
    apply eq_of_rightHomotopy
    erw [← (quotient V).map_comp, ← (quotient V).map_comp] at eq
    set h := homotopyOfEq _ _ eq
    refine ⟨weakPullback.lift (g₁.right - g₂.right) h.hom ?_, ?_⟩
    · erw [Preadditive.sub_comp]
      exact h.comm
    · simp only [mk_hom]
      erw [weakPullback.lift_fst]

instance isMono_ι : Mono ((quotient V).map (ι f)) := isMono_of_witness_snd _ _

variable {w : Arrow V} (g : w ⟶ u) (h : RightHomotopy (g ≫ f) 0)

def lift : w ⟶ kernel f := by
  refine Arrow.homMk (weakPullback.lift (w.hom ≫ weakPullback.lift h.hom g.right
    (by simp [← h.comm])) g.left (by simp only [assoc, Arrow.w]; erw [weakPullback.lift_snd]))
    (weakPullback.lift h.hom g.right (by simp [← h.comm])) ?_
  simp only [kernel, mk_hom]
  erw [weakPullback.lift_fst]
  rfl

@[reassoc]
lemma lift_ι : lift f g h ≫ ι f = g := by
  simp only [kernel, lift, ι]
  ext
  · simp only [comp_left, homMk_left]
    erw [weakPullback.lift_snd]
  · simp only [comp_right, homMk_right]
    erw [weakPullback.lift_snd]

variable {X : RightFreyd V} {a : X ⟶ (quotient V).obj u} (eq : a ≫ (quotient V).map f = 0)

def lift' : X ⟶ (quotient V).obj (kernel f) := by
  rw [← ((quotient V).map_surjective a).choose_spec] at eq
  exact (quotient V).map (CandidateKernel.lift _ _ (homotopyOfEq _ _ eq))

lemma lift'_ι : lift' f eq ≫ (quotient V).map (ι f) = a := by
  rw [← ((quotient V).map_surjective a).choose_spec] at eq
  conv_rhs => rw [← ((quotient V).map_surjective a).choose_spec,
                      ← CandidateKernel.lift_ι _ _ (homotopyOfEq _ _ eq)]
  rfl

end CandidateKernel

def candidateKernelFork : Cone (parallelPair ((quotient V).map f) 0) := by
  refine KernelFork.ofι ((quotient V).map (CandidateKernel.ι f)) ?_
  rw [← (quotient V).map_comp]
  exact eq_of_rightHomotopy _ _ (CandidateKernel.condition f)

def candidateKernelForkIsKernel : IsLimit (candidateKernelFork f) where
  lift s := CandidateKernel.lift' f (KernelFork.condition s)
  fac s j :=
    match j with
    | WalkingParallelPair.zero => CandidateKernel.lift'_ι _ _
    | WalkingParallelPair.one => by simp
  uniq s m eq :=
    (cancel_mono ((quotient V).map (CandidateKernel.ι f))).mp ((eq WalkingParallelPair.zero).trans
    (CandidateKernel.lift'_ι f (KernelFork.condition s)).symm)

instance : HasKernels (RightFreyd V) where
  has_limit {X Y} f := {
    exists_limit := by
      obtain ⟨f, rfl⟩ := (quotient V).map_surjective f
      exact Nonempty.intro {
        cone := candidateKernelFork f
        isLimit := candidateKernelForkIsKernel f}}

end Kernels

namespace NormalMono

variable [HasFiniteProducts V]

local instance : HasBinaryBiproducts V := HasBinaryBiproducts.of_hasBinaryProducts

variable {w : Arrow V} (g : w ⟶ v) (h : RightHomotopy (g ≫ CandidateCokernel.π f) 0)

lemma comm' : Hom.right g = h.hom ≫ biprod.fst ≫ v.hom + h.hom ≫ biprod.snd ≫ Hom.right f := by
  have := h.comm
  simp only [CandidateCokernel.cokernel, CandidateCokernel.π, comp_right, homMk_right,
      Hom.zero_right, mk_hom, biprod.desc_eq] at this
  erw [comp_id, sub_zero, Preadditive.comp_add] at this
  exact this

variable [HasWeakKernels V]

local instance : HasWeakEqualizers V := Preadditive.hasWeakEqualizers_of_hasWeakKernels

local instance : HasWeakPullbacks V := hasWeakPullbacks_of_hasBinaryProducts_of_hasWeakKernels V

variable [Mono ((quotient V).map f)]

def rightHomotopyOfMono : RightHomotopy (CandidateKernel.ι f) 0 := by
  refine ((quotient_map_eq_zero_iff (CandidateKernel.ι f)).mp ?_).some
  rw [← cancel_mono ((quotient V).map f), ← (quotient V).map_comp, zero_comp,
    quotient_map_eq_zero_iff]
  exact Nonempty.intro (CandidateKernel.condition f)

def lift : w ⟶ u := by
  set r : w.right ⟶ u.right := h.hom ≫ biprod.snd
  set l : w.left ⟶ u.left := by
    refine ?_ ≫ (rightHomotopyOfMono f).hom
    refine weakPullback.lift (g.left - w.hom ≫ h.hom ≫ biprod.fst) (w.hom ≫ h.hom ≫ biprod.snd) ?_
    simp only [Preadditive.sub_comp, Arrow.w, assoc]
    rw [comm' f g h]
    erw [Preadditive.comp_add]
    rw [← add_sub]
    exact add_sub_cancel _ _
  refine Arrow.homMk l r ?_
  simp only [assoc, l, r]
  rw [← (rightHomotopyOfMono f).comm]
  simp only [CandidateKernel.ι, homMk_right, Hom.zero_right, sub_zero]
  exact weakPullback.lift_snd _ _ _

def lift_f : RightHomotopy (lift f g h ≫ f) g where
  hom := - h.hom ≫ biprod.fst
  comm := by
    simp only [lift, comp_right, homMk_right, assoc, Preadditive.neg_comp]
    rw [comm' f g h]
    simp

variable {X : RightFreyd V} {a : X ⟶ (quotient V).obj v}
  (eq : a ≫ (quotient V).map (CandidateCokernel.π f) = 0)

def lift' : X ⟶ (quotient V).obj u := by
  rw [← ((quotient V).map_surjective a).choose_spec] at eq
  exact (quotient V).map (lift _ _ (homotopyOfEq _ _ eq))

lemma lift'_f : lift' f eq ≫ (quotient V).map f = a := by
  rw [← ((quotient V).map_surjective a).choose_spec] at eq
  conv_rhs => rw [← ((quotient V).map_surjective a).choose_spec]
  simp only [lift']
  erw [← (quotient V).map_comp]
  exact eq_of_rightHomotopy _ _ (lift_f _ _ (homotopyOfEq _ _ eq))

@[reducible]
def normalMonoOfMono : NormalMono ((quotient V).map f) where
  Z := (quotient V).obj (CandidateCokernel.cokernel f)
  g := (quotient V).map (CandidateCokernel.π f)
  w := (quotient_map_eq_zero_iff _).mpr (Nonempty.intro (CandidateCokernel.condition f))
  isLimit := {
    lift s:= lift' f (KernelFork.condition s)
    fac s j := match j with
    | WalkingParallelPair.zero => lift'_f _ _
    | WalkingParallelPair.one => by
      simp only [parallelPair_obj_one, Fork.ofι_π_app, Fork.app_one_eq_ι_comp_left,
        KernelFork.condition]
      conv_lhs => congr; rfl; erw [← (quotient V).map_comp]
      rw [eq_of_rightHomotopy _ _ (CandidateCokernel.condition f)]
      simp only [Functor.map_zero]
      erw [comp_zero]
    uniq s m eq := by
      apply (cancel_mono ((quotient V).map f)).mp
      rw [lift'_f]
      exact eq WalkingParallelPair.zero
  }

set_option backward.isDefEq.respectTransparency false in
instance : IsNormalMonoCategory (RightFreyd V) where
  normalMonoOfMono f _ := by
    obtain ⟨f, rfl⟩ := (quotient V).map_surjective f
    exact Nonempty.intro (normalMonoOfMono f)

end NormalMono

namespace NormalEpi

variable [HasFiniteProducts V]

local instance : HasBinaryBiproducts V := HasBinaryBiproducts.of_hasBinaryProducts

variable [Epi ((quotient V).map f)]

def rightHomotopyOfEpi : RightHomotopy (CandidateCokernel.π f) 0 := by
  refine ((quotient_map_eq_zero_iff (CandidateCokernel.π f)).mp ?_).some
  rw [← cancel_epi ((quotient V).map f), ← (quotient V).map_comp, comp_zero,
    quotient_map_eq_zero_iff]
  exact Nonempty.intro (CandidateCokernel.condition f)

lemma comm' (f : u ⟶ v) [Epi ((quotient V).map f)] : 𝟙 v.right = (rightHomotopyOfEpi f).hom ≫
    biprod.fst ≫ v.hom + (rightHomotopyOfEpi f).hom ≫ biprod.snd ≫ Hom.right f:= by
  have := (rightHomotopyOfEpi f).comm
  simp only [CandidateCokernel.cokernel, CandidateCokernel.π, homMk_right, Hom.zero_right, mk_hom,
    biprod.desc_eq] at this
  erw [sub_zero, Preadditive.comp_add] at this
  exact this

variable [HasWeakKernels V]

local instance : HasWeakEqualizers V := Preadditive.hasWeakEqualizers_of_hasWeakKernels

local instance : HasWeakPullbacks V := hasWeakPullbacks_of_hasBinaryProducts_of_hasWeakKernels V

variable {w : Arrow V} (g : u ⟶ w) (h : RightHomotopy (CandidateKernel.ι f ≫ g) 0)

def desc : v ⟶ w := by
  set r : v.right ⟶ w.right := (rightHomotopyOfEpi f).hom ≫ biprod.snd ≫ g.right
  set l : v.left ⟶ w.left := by
    refine ?_ ≫ h.hom
    refine weakPullback.lift (𝟙 _ - v.hom ≫ (rightHomotopyOfEpi f).hom ≫ biprod.fst)
      (v.hom ≫ (rightHomotopyOfEpi f).hom ≫ biprod.snd) ?_
    simp only [Preadditive.sub_comp, id_comp, assoc]
    rw [sub_eq_iff_eq_add, ← Preadditive.comp_add, add_comm, ← comm' f, comp_id]
  refine Arrow.homMk l r ?_
  simp only [assoc, l, r]
  rw [← h.comm]
  simp only [CandidateKernel.ι, comp_right, homMk_right, Hom.zero_right, sub_zero]
  erw [weakPullback.lift_snd_assoc]
  simp

def f_desc : RightHomotopy (f ≫ desc f g h) g where
  hom := by
    refine - weakPullback.lift (f.right ≫ (rightHomotopyOfEpi f).hom ≫ biprod.fst)
      (𝟙 _ - f.right ≫ (rightHomotopyOfEpi f).hom ≫ biprod.snd) ?_ ≫ h.hom
    simp only [assoc, Preadditive.sub_comp, id_comp]
    rw [eq_sub_iff_add_eq, ← Preadditive.comp_add, ← comm' f, comp_id]
  comm := by
    simp only [comp_right, Preadditive.neg_comp, assoc]
    erw [← h.comm]
    simp only [desc, CandidateKernel.ι, homMk_right, comp_right, Hom.zero_right, sub_zero]
    erw [weakPullback.lift_snd_assoc]
    simp

variable {X : RightFreyd V} {a : (quotient V).obj u ⟶ X}
  (eq : (quotient V).map (CandidateKernel.ι f) ≫ a = 0)

def desc' : (quotient V).obj v ⟶ X := by
  rw [← ((quotient V).map_surjective a).choose_spec] at eq
  exact (quotient V).map (desc _ _ (homotopyOfEq _ _ eq))

lemma f_desc' : (quotient V).map f ≫ desc' f eq = a := by
  rw [← ((quotient V).map_surjective a).choose_spec] at eq
  conv_rhs => rw [← ((quotient V).map_surjective a).choose_spec]
  simp only [desc']
  erw [← (quotient V).map_comp]
  exact eq_of_rightHomotopy _ _ (f_desc _ _ (homotopyOfEq _ _ eq))

@[reducible]
def normalEpiOfEpi : NormalEpi ((quotient V).map f) where
  W := (quotient V).obj (CandidateKernel.kernel f)
  g := (quotient V).map (CandidateKernel.ι f)
  w := (quotient_map_eq_zero_iff _).mpr (Nonempty.intro (CandidateKernel.condition f))
  isColimit := {
    desc s:= desc' f (CokernelCofork.condition s)
    fac s j := match j with
    | WalkingParallelPair.zero => by
      simp only [parallelPair_obj_zero, Cofork.ofπ_ι_app, Cofork.app_zero_eq_comp_π_left,
        CokernelCofork.condition]
      conv_lhs => congr; erw [← (quotient V).map_comp]
                  rw [eq_of_rightHomotopy _ _ (CandidateKernel.condition f)]
      simp only [Functor.map_zero]
      erw [zero_comp]
    | WalkingParallelPair.one => f_desc' _ _
    uniq s m eq := by
      apply (cancel_epi ((quotient V).map f)).mp
      rw [f_desc']
      exact eq WalkingParallelPair.one
  }

set_option backward.isDefEq.respectTransparency false in
instance : IsNormalEpiCategory (RightFreyd V) where
  normalEpiOfEpi f _ := by
    obtain ⟨f, rfl⟩ := (quotient V).map_surjective f
    exact Nonempty.intro (normalEpiOfEpi f)

end NormalEpi

section Abelian

variable [HasFiniteProducts V]

instance : HasFiniteProducts (Arrow V) where
  out _ := inferInstance

instance : HasFiniteProducts (RightFreyd V) :=
  have : (quotient V).EssSurj := inferInstance
  (quotient V).hasFiniteProductsOfAdditiveEssSurj

variable [HasWeakKernels V]

instance : Abelian (RightFreyd V) where

end Abelian

end RightFreyd

end CategoryTheory
