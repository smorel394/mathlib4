/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.Homology.FreydCategory.Kernels
public import Mathlib.Algebra.Homology.FreydCategory.Cokernels

/-!
# Freyd categories are abelian

If `V` is a preadditive category with finite products and weak kernels, then `RightFreyd V`
is an abelian category.

-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex Arrow

variable {V : Type*} [Category* V] [Preadditive V]

namespace CategoryTheory.Preadditive

namespace RightFreyd

variable [HasFiniteProducts V]

local instance : HasBinaryBiproducts V := HasBinaryBiproducts.of_hasBinaryProducts

variable {u v : Arrow V} (f : u ⟶ v)

namespace NormalMono

variable {w : Arrow V} (g : w ⟶ v) (h : RightHomotopy (g ≫ CandidateCokernel.π f) 0)

/-- For `f : u ⟶ v` and `g : w ⟶ v` morphisms in `Arrow V` such that `g ≫ CandidateCokernel.π f`
and `0` are right homotopic, this is a more convenient expression of the right homotopy
condition. -/
lemma comm' : Hom.right g = h.hom ≫ biprod.fst ≫ v.hom + h.hom ≫ biprod.snd ≫ Hom.right f := by
  have := h.comm
  simp only [CandidateCokernel.cokernel, CandidateCokernel.π, comp_right, homMk_right,
      Hom.zero_right, mk_hom, biprod.desc_eq] at this
  refine Eq.trans ?_ (this.trans ?_)
  · rw [sub_zero]
    exact (comp_id _).symm
  · exact Preadditive.comp_add _ _ _ _ _ _

variable [HasWeakKernels V]

local instance : HasWeakEqualizers V := Preadditive.hasWeakEqualizers_of_hasWeakKernels

local instance : HasWeakPullbacks V := hasWeakPullbacks_of_hasBinaryProducts_of_hasWeakKernels V

variable [Mono ((quotient V).map f)]

/-- If `f` is a morphism of `Arrow V` whose image in `RightFreyd V` is a monomorphism, then
`CandidateKernel.ι f` is right homotopic to `0`. -/
def rightHomotopyOfMono : RightHomotopy (CandidateKernel.ι f) 0 := by
  refine ((quotient_map_eq_zero_iff (CandidateKernel.ι f)).mp ?_).some
  rw [← cancel_mono ((quotient V).map f), ← (quotient V).map_comp, zero_comp,
    quotient_map_eq_zero_iff]
  exact Nonempty.intro (CandidateKernel.condition f)

/-- Let `f : u ⟶ v` and `g : w ⟶ v` be morphisms in `Arrow V` such that
`g ≫ CandidateCokernel.π f` and `0` are right homotopic, and suppose that the
image of `f` in `RightFreyd V` is a monomorphism. In `RightFreyd V`, the image of
`g` should lift to a morphism to `(quotient V).obj u`. This is a candidate for this
lift, in `Arrow V`. -/
def lift : w ⟶ u := by
  set r : w.right ⟶ u.right := h.hom ≫ biprod.snd
  set l : w.left ⟶ u.left := by
    refine ?_ ≫ (rightHomotopyOfMono f).hom
    refine weakPullback.lift (g.left - w.hom ≫ h.hom ≫ biprod.fst) (w.hom ≫ h.hom ≫ biprod.snd) ?_
    simp only [Preadditive.sub_comp, Arrow.w, assoc]
    rw [comm' f g h, sub_eq_iff_eq_add, add_comm]
    exact Preadditive.comp_add _ _ _ _ _ _
  refine Arrow.homMk l r ?_
  simp only [assoc, l, r]
  rw [← (rightHomotopyOfMono f).comm]
  simp only [CandidateKernel.ι, homMk_right, Hom.zero_right, sub_zero]
  exact weakPullback.lift_snd _ _ _

/-- Let `f : u ⟶ v` and `g : w ⟶ v` be morphisms in `Arrow V` such that
`g ≫ CandidateCokernel.π f` and `0` are right homotopic, and suppose that the
image of `f` in `RightFreyd V` is a monomorphism. In `RightFreyd V`, the image of
`g` should lift to a morphism to `(quotient V).obj u`. In `lift`, we constructed
a candidate for this lift, in `Arrow V`. This gives the right homotopy from
`lift g ≫ f` to `g`, proving that the candidate works. -/
def lift_f : RightHomotopy (lift f g h ≫ f) g where
  hom := - h.hom ≫ biprod.fst
  comm := by
    simp only [lift, comp_right, homMk_right, assoc, Preadditive.neg_comp]
    rw [comm' f g h]
    simp

variable {X : RightFreyd V} {a : X ⟶ (quotient V).obj v}
  (eq : a ≫ (quotient V).map (CandidateCokernel.π f) = 0)

/-- Let `f : u ⟶ v` be a morphism in `Arrow V` such that the image of `f` in `RightFreyd V`
is a monomorphism. Let `a : X ⟶ (quotient V).obj v` be a morphism in `RightFreyd v` such
that `a ≫ cokernel f = 0`. This is a lift of `a` to a morphism `X ⟶ (quotient V).obj u`. -/
def lift' : X ⟶ (quotient V).obj u := by
  rw [← ((quotient V).map_surjective a).choose_spec] at eq
  exact (quotient V).map (lift _ _ (homotopyOfEq _ _ eq))

/-- Let `f : u ⟶ v` be a morphism in `Arrow V` such that the image of `f` in `RightFreyd V`
is a monomorphism. Let `a : X ⟶ (quotient V).obj v` be a morphism in `RightFreyd v` such
that `a ≫ cokernel f = 0`. Then the lift of `a` to a morphism `X ⟶ (quotient V).obj u` constucted
in `lift'` satisfies the lift condition. -/
lemma lift'_f : lift' f eq ≫ (quotient V).map f = a := by
  rw [← ((quotient V).map_surjective a).choose_spec] at eq
  conv_rhs => rw [← ((quotient V).map_surjective a).choose_spec]
  exact eq_of_rightHomotopy _ _ (lift_f _ _ (homotopyOfEq _ _ eq))

/-- If `f` is a morphism of `Arrow V` such that `(quotient V).map f` is a monomorphism, then
`(quotient V).map f` is a normal monomorphism. -/
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
      exact comp_zero
    uniq s m eq := by
      apply (cancel_mono ((quotient V).map f)).mp
      rw [lift'_f]
      exact eq WalkingParallelPair.zero
  }

set_option backward.isDefEq.respectTransparency false in
/-- If `V` has finite products and weak kernels, then `RightFreyd V` is a normal mono category. -/
instance : IsNormalMonoCategory (RightFreyd V) where
  normalMonoOfMono f _ := by
    obtain ⟨f, rfl⟩ := (quotient V).map_surjective f
    exact Nonempty.intro (normalMonoOfMono f)

end NormalMono

namespace NormalEpi

variable [Epi ((quotient V).map f)]

/-- If `f` is a morphism of `Arrow V` whose image in `RightFreyd V` is an epimorphism, then
`CandidateCokernel.ι f` is right homotopic to `0`. -/
def rightHomotopyOfEpi : RightHomotopy (CandidateCokernel.π f) 0 := by
  refine ((quotient_map_eq_zero_iff (CandidateCokernel.π f)).mp ?_).some
  rw [← cancel_epi ((quotient V).map f), ← (quotient V).map_comp, comp_zero,
    quotient_map_eq_zero_iff]
  exact Nonempty.intro (CandidateCokernel.condition f)

/-- This is more convenient form of the homotopy relation of `rightHomotopyOfEpi`. -/
lemma comm' (f : u ⟶ v) [Epi ((quotient V).map f)] : 𝟙 v.right = (rightHomotopyOfEpi f).hom ≫
    biprod.fst ≫ v.hom + (rightHomotopyOfEpi f).hom ≫ biprod.snd ≫ Hom.right f:= by
  have := (rightHomotopyOfEpi f).comm
  simp only [CandidateCokernel.cokernel, CandidateCokernel.π, homMk_right, Hom.zero_right, mk_hom,
    biprod.desc_eq] at this
  exact Eq.trans (sub_zero _).symm (this.trans (Preadditive.comp_add _ _ _ _ _ _))

variable [HasWeakKernels V]

local instance : HasWeakEqualizers V := Preadditive.hasWeakEqualizers_of_hasWeakKernels

local instance : HasWeakPullbacks V := hasWeakPullbacks_of_hasBinaryProducts_of_hasWeakKernels V

variable {w : Arrow V} (g : u ⟶ w) (h : RightHomotopy (CandidateKernel.ι f ≫ g) 0)

/-- Let `f : u ⟶ v` and `g : u ⟶ w` be morphisms in `Arrow V` such that
`CandidateKernel.ι f ≫ g` and `0` are right homotopic, and suppose that the
image of `f` in `RightFreyd V` is an epimorphism. In `RightFreyd V`, the image of
`g` should descend to a morphism from `(quotient V).obj v`. This is a candidate for this
descended morphism, in `Arrow V`. -/
def desc : v ⟶ w := by
  set r : v.right ⟶ w.right := (rightHomotopyOfEpi f).hom ≫ biprod.snd ≫ g.right
  set l : v.left ⟶ w.left := by
    refine ?_ ≫ h.hom
    refine (weakPullback.lift (𝟙 _ - v.hom ≫ (rightHomotopyOfEpi f).hom ≫ biprod.fst)
      (v.hom ≫ (rightHomotopyOfEpi f).hom ≫ biprod.snd) ?_)
    simp only [Preadditive.sub_comp, id_comp, assoc]
    rw [sub_eq_iff_eq_add, ← Preadditive.comp_add, add_comm, ← comm' f, comp_id]
  refine Arrow.homMk l r ?_
  simp only [assoc, l, r]
  rw [← h.comm]
  simp only [CandidateKernel.ι, comp_right, homMk_right, Hom.zero_right, sub_zero]
  refine (weakPullback.lift_snd_assoc _ _ _ _).trans (by simp)

/-- Let `f : u ⟶ v` and `g : u ⟶ w` be morphisms in `Arrow V` such that
`CandidateKernel.ι f ≫ g` and `0` are right homotopic, and suppose that the
image of `f` in `RightFreyd V` is an epimorphism. In `RightFreyd V`, the image of
`g` should descend to a morphism from `(quotient V).obj v`. In `desc`, we constructed
a candidate in `Arrow V` for this descent. This gives the right homotopy from
`f ≫ descent g` to `g`, proving that the candidate works. -/
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
    rw [sub_eq_iff_comm, sub_neg_eq_add, add_comm, ← eq_sub_iff_add_eq]
    exact (weakPullback.lift_snd_assoc _ _ _ _).trans (by simp)

variable {X : RightFreyd V} {a : (quotient V).obj u ⟶ X}
  (eq : (quotient V).map (CandidateKernel.ι f) ≫ a = 0)

/-- Let `f : u ⟶ v` be a morphism in `Arrow V` such that the image of `f` in `RightFreyd V`
is an epimorphism. Let `a : (quotient V).obj u ⟶ X` be a morphism in `RightFreyd v` such
that `kernel f ≫ a = 0`. Then `a` descends tio a morphism `(quotient V).obj u ⟶ X`. -/
def desc' : (quotient V).obj v ⟶ X := by
  rw [← ((quotient V).map_surjective a).choose_spec] at eq
  exact (quotient V).map (desc _ _ (homotopyOfEq _ _ eq))

/-- Let `f : u ⟶ v` be a morphism in `Arrow V` such that the image of `f` in `RightFreyd V`
is an epimorphism. Let `a : (quotient V).obj u ⟶ X` be a morphism in `RightFreyd v` such
that `kernel f ≫ a = 0`. Then the descent of `a` to a morphism `(quotient V).obj u ⟶ X` constucted
in `desc'` satisfies the descent condition. -/
lemma f_desc' : (quotient V).map f ≫ desc' f eq = a := by
  rw [← ((quotient V).map_surjective a).choose_spec] at eq
  conv_rhs => rw [← ((quotient V).map_surjective a).choose_spec]
  simp only [desc']
  erw [← (quotient V).map_comp]
  exact eq_of_rightHomotopy _ _ (f_desc _ _ (homotopyOfEq _ _ eq))

/-- If `f` is a morphism of `Arrow V` such that `(quotient V).map f` is an epimorphism, then
`(quotient V).map f` is a normal epimorphism. -/
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
      conv_lhs => congr; change (quotient V).map (CandidateKernel.ι f ≫ f)
                  rw [eq_of_rightHomotopy _ _ (CandidateKernel.condition f)]
      simp only [Functor.map_zero]
      exact zero_comp
    | WalkingParallelPair.one => f_desc' _ _
    uniq s m eq := by
      apply (cancel_epi ((quotient V).map f)).mp
      rw [f_desc']
      exact eq WalkingParallelPair.one
  }

set_option backward.isDefEq.respectTransparency false in
/-- If `V` has finite products and weak kernels, then `RightFreyd V` is a normal epi category. -/
instance : IsNormalEpiCategory (RightFreyd V) where
  normalEpiOfEpi f _ := by
    obtain ⟨f, rfl⟩ := (quotient V).map_surjective f
    exact Nonempty.intro (normalEpiOfEpi f)

end NormalEpi

section Abelian

instance : HasFiniteProducts (Arrow V) where
  out _ := inferInstance

instance : HasFiniteProducts (RightFreyd V) :=
  have : (quotient V).EssSurj := inferInstance
  (quotient V).hasFiniteProducts_of_additive_of_essSurj

variable [HasWeakKernels V]

/-- If `V` has finite products and weak kernels, then `RightFreyd V` is an abelian category. -/
instance : Abelian (RightFreyd V) where

end Abelian

end RightFreyd

end CategoryTheory.Preadditive
