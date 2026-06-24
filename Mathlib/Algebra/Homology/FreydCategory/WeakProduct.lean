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
# Weak kernels and weak products

-/

@[expose] public section

noncomputable section

universe u₁ v₁ u₂ v₂

open CategoryTheory Category Limits

variable {J : Type u₁} [Category.{v₁, u₁} J] {C : Type u₂} [Category.{v₂, u₂} C]
    {F : Functor J C}

namespace Limits

structure IsWeakLimit (t : Cone F) where
  /-- There is a morphism from any cone point to `t.pt` -/
  lift : ∀ s : Cone F, s.pt ⟶ t.pt
  /-- The map makes the triangle with the two natural transformations commute -/
  fac : ∀ (s : Cone F) (j : J), lift s ≫ t.π.app j = s.π.app j := by cat_disch

attribute [reassoc (attr := simp)] IsWeakLimit.fac

/-- `WeakLimitCone F` contains a cone over `F` together with the information that it is
a weak limit. -/
structure WeakLimitCone (F : J ⥤ C) where
  /-- The cone itself -/
  cone : Cone F
  /-- The proof that is the limit cone -/
  isWeakLimit : IsWeakLimit cone

/-- `HasWeakLimit F` represents the mere existence of a weak limit for `F`. -/
class HasWeakLimit (F : J ⥤ C) : Prop where mk' ::
  /-- There is some weak limit cone for `F` -/
  exists_weakLimit : Nonempty (WeakLimitCone F)

theorem WeakHasLimit.mk {F : J ⥤ C} (d : WeakLimitCone F) : HasWeakLimit F :=
  ⟨Nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `WeakLimitCone F` from `HasWeakLimit F`. -/
def getWeakLimitCone (F : J ⥤ C) [HasWeakLimit F] : WeakLimitCone F :=
  Classical.choice <| HasWeakLimit.exists_weakLimit

variable (J C) in
/-- `C` has weak limits of shape `J` if there exists a weak limit for every functor
`F : J ⥤ C`. -/
class HasWeakLimitsOfShape : Prop where
  /-- All functors `F : J ⥤ C` from `J` have weak limits -/
  has_weakLimit : ∀ F : J ⥤ C, HasWeakLimit F := by infer_instance

-- Interface to the `HasWeakLimit` class.
/-- An arbitrary choice of weak limit cone for a functor. -/
def weakLimit.cone (F : J ⥤ C) [HasWeakLimit F] : Cone F :=
  (getWeakLimitCone F).cone

/-- An arbitrary choice of weak limit object of a functor. -/
def weakLimit (F : J ⥤ C) [HasWeakLimit F] :=
  (weakLimit.cone F).pt

/-- The projection from the weak limit object to a value of the functor. -/
def weakLimit.π (F : J ⥤ C) [HasWeakLimit F] (j : J) : weakLimit F ⟶ F.obj j :=
  (weakLimit.cone F).π.app j

@[reassoc]
theorem weakLimit.π_comp_eqToHom (F : J ⥤ C) [HasWeakLimit F] {j j' : J} (hj : j = j') :
    weakLimit.π F j ≫ eqToHom (by subst hj; rfl) = weakLimit.π F j' := by
  subst hj
  simp

@[simp]
theorem weakLimit.cone_x {F : J ⥤ C} [HasWeakLimit F] :
    (weakLimit.cone F).pt = weakLimit F := rfl

@[simp]
theorem weakLimit.cone_π {F : J ⥤ C} [HasWeakLimit F] :
    (weakLimit.cone F).π.app = weakLimit.π _ := rfl

@[reassoc (attr := simp)]
theorem weakLimit.w (F : J ⥤ C) [HasWeakLimit F] {j j' : J} (f : j ⟶ j') :
    weakLimit.π F j ≫ F.map f = weakLimit.π F j' :=
  (weakLimit.cone F).w f

/-- Evidence that the arbitrary choice of cone provided by `weakLimit.cone F`
is a weak limit cone. -/
def weakLimit.isWeakLimit (F : J ⥤ C) [HasWeakLimit F] :
    IsWeakLimit (weakLimit.cone F) :=
  (getWeakLimitCone F).isWeakLimit

/-- A morphism from the cone point of any other cone to the weak limit object. -/
def weakLimit.lift (F : J ⥤ C) [HasWeakLimit F] (c : Cone F) :
    c.pt ⟶ weakLimit F :=
  (weakLimit.isWeakLimit F).lift c

@[simp]
theorem weakLimit.isWeakLimit_lift {F : J ⥤ C} [HasWeakLimit F] (c : Cone F) :
    (weakLimit.isWeakLimit F).lift c = weakLimit.lift F c :=
  rfl

@[reassoc (attr := simp)]
theorem weakLimit.lift_π {F : J ⥤ C} [HasWeakLimit F] (c : Cone F) (j : J) :
    weakLimit.lift F c ≫ weakLimit.π F j = c.π.app j :=
  IsWeakLimit.fac _ c j


namespace IsWeakLimit

/-- Transport evidence that a cone is a limit cone across an isomorphism of cones. -/
--@[to_dual
--/-- Transport evidence that a cocone is a colimit cocone across an isomorphism of cocones. -/]
def ofIsoWeakLimit {r t : Cone F} (P : IsWeakLimit r) (i : r ≅ t) : IsWeakLimit t where
  lift s := P.lift s ≫ i.hom.hom
  fac s j := by simp

--@[to_dual (attr := simp)]
theorem ofIsoWeakLimit_lift {r t : Cone F} (P : IsWeakLimit r) (i : r ≅ t) (s) :
    (P.ofIsoWeakLimit i).lift s = P.lift s ≫ i.hom.hom :=
  rfl

end IsWeakLimit

section WeakKErnel

variable [HasZeroMorphisms C]

/-- A morphism `f` has a weak kernel if the functor `ParallelPair f 0` has a weak limit. -/
abbrev HasWeakKernel {X Y : C} (f : X ⟶ Y) : Prop :=
  HasWeakLimit (parallelPair f 0)

variable (C) in
/-- `HasWeakKernels` represents the existence of weak kernels for every morphism. -/
class HasWeakKernels : Prop where
  has_weakLimit : ∀ {X Y : C} (f : X ⟶ Y), HasWeakKernel f := by infer_instance

section

variable {X Y : C} (f : X ⟶ Y) [HasWeakKernel f]

/-- The weak kernel of a morphism. -/
abbrev weakKernel : C :=
  weakLimit (parallelPair f 0)

/-- The map from `weakKernel f` into the source of `f`. -/
abbrev weakKernel.ι : weakKernel f ⟶ X :=
  weakLimit.π (parallelPair f 0) WalkingParallelPair.zero

@[reassoc (attr := simp)]
theorem weakKernel.condition : weakKernel.ι f ≫ f = 0 :=
  KernelFork.condition _

set_option backward.defeqAttrib.useBackward true in
/-- The weak kernel built from `weakKernel.ι f` is weakly limiting. -/
def weakKernelIsWeakKernel :
    IsWeakLimit (Fork.ofι (weakKernel.ι f) ((weakKernel.condition f).trans comp_zero.symm)) :=
  IsWeakLimit.ofIsoWeakLimit (weakLimit.isWeakLimit _) (Fork.ext (Iso.refl _) (by simp; rfl))

/-- Given any morphism `k : W ⟶ X` satisfying `k ≫ f = 0`, `k` factors through
`weakKernel.ι f` via `weakKernel.lift : W ⟶ weakKernel f`. -/
abbrev weakKernel.lift {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ weakKernel f :=
  (weakKernelIsWeakKernel f).lift (KernelFork.ofι k h)

@[reassoc (attr := simp)]
theorem weakKernel.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = 0) :
    weakKernel.lift f k h ≫ weakKernel.ι f = k :=
  (weakKernelIsWeakKernel f).fac (KernelFork.ofι k h) WalkingParallelPair.zero

/-- Any morphism `k : W ⟶ X` satisfying `k ≫ f = 0` induces a morphism `l : W ⟶ weakKernel f`
such that `l ≫ weakKernel.ι f = k`. -/
def weakKernel.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = 0) :
    { l : W ⟶ weakKernel f // l ≫ weakKernel.ι f = k } :=
  ⟨weakKernel.lift f k h, weakKernel.lift_ι _ _ _⟩

end

end WeakKErnel

section WeakPullback

variable {W X Y Z : C}

/-- Two morphisms `f : X ⟶ Z` and `g : Y ⟶ Z` have a weak pullback if the diagram
`cospan f g` has a weak limit. -/
abbrev HasWeakPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  HasWeakLimit (cospan f g)

/-- `weakPullback f g` computes the weak pullback of a pair of morphisms
with the same target. -/
abbrev weakPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :=
  weakLimit (cospan f g)

/-- The cone associated to the weak pullback of `f` and `g` -/
abbrev weakPullback.cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasWeakPullback f g] : PullbackCone f g :=
  weakLimit.cone (cospan f g)

/-- The first projection of the weak pullback of `f` and `g`. -/
abbrev weakPullback.fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :
    weakPullback f g ⟶ X :=
  weakLimit.π (cospan f g) WalkingCospan.left

/-- The second projection of the weak pullback of `f` and `g`. -/
abbrev weakPullback.snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :
    weakPullback f g ⟶ Y :=
  weakLimit.π (cospan f g) WalkingCospan.right

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
`weakPullback.lift : W ⟶ weakPullback f g`. -/
abbrev weakPullback.lift {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasWeakPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g := by cat_disch) : W ⟶ weakPullback f g :=
  weakLimit.lift _ (PullbackCone.mk h k w)

set_option backward.isDefEq.respectTransparency false in
lemma weakPullback.exists_lift {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g]
    (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g := by cat_disch) :
    ∃ (l : W ⟶ weakPullback f g),
    l ≫ weakPullback.fst f g = h ∧ l ≫ weakPullback.snd f g = k :=
  ⟨weakPullback.lift h k, by simp⟩

/-- The cone associated to a weak pullback is a weak limit cone. -/
abbrev weakPullback.isWeakLimit {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :
    IsWeakLimit (weakPullback.cone f g) :=
  weakLimit.isWeakLimit (cospan f g)

@[simp]
theorem WeakPullbackCone.fst_limit_cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasWeakLimit (cospan f g)] :
    PullbackCone.fst (weakLimit.cone (cospan f g)) = weakPullback.fst f g := rfl

@[simp]
theorem WeakPullbackCone.snd_limit_cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasWeakLimit (cospan f g)] :
    PullbackCone.snd (weakLimit.cone (cospan f g)) = weakPullback.snd f g := rfl

@[reassoc]
theorem weakPullback.lift_fst {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    [HasWeakPullback f g] (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    weakPullback.lift h k w ≫ weakPullback.fst f g = h :=
  weakLimit.lift_π _ _

@[reassoc]
theorem weakPullback.lift_snd {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    [HasWeakPullback f g] (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    weakPullback.lift h k w ≫ weakPullback.snd f g = k :=
  weakLimit.lift_π _ _

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
`l : W ⟶ weakPullback f g` such that `l ≫ weakPullback.fst = h` and `l ≫ weakPullback.snd = k`. -/
def weakPullback.lift' {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasWeakPullback f g]
    (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
      { l : W ⟶ weakPullback f g //
      l ≫ weakPullback.fst f g = h ∧ l ≫ weakPullback.snd f g = k } :=
  ⟨weakPullback.lift h k w, weakPullback.lift_fst _ _ _, weakPullback.lift_snd _ _ _⟩

@[reassoc]
theorem weakPullback.condition {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasWeakPullback f g] :
    weakPullback.fst f g ≫ f = weakPullback.snd f g ≫ g :=
  PullbackCone.condition _

/-- The pullback cone reconstructed using `PullbackCone.mk` from a pullback cone that is a
weak limit, is also a weak limit. -/
def PullbackCone.mkSelfIsWeakLimit {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {t : PullbackCone f g}
    (ht : IsWeakLimit t) : IsWeakLimit (PullbackCone.mk t.fst t.snd t.condition) :=
  IsWeakLimit.ofIsoWeakLimit ht (PullbackCone.eta t)

/-- The weak pullback cone built from the pullback projections is a weak pullback. -/
def weakPullbackIsWeakPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :
    IsWeakLimit (PullbackCone.mk (weakPullback.fst f g) (weakPullback.snd f g)
    weakPullback.condition) :=
  PullbackCone.mkSelfIsWeakLimit <| weakPullback.isWeakLimit f g

variable (C)

/-- A category `HasPullbacks` if it has all weak limits of shape `WalkingCospan`, i.e. if it
has a weak pullback for every pair of morphisms with the same codomain. -/
abbrev HasWeakPullbacks :=
  HasWeakLimitsOfShape WalkingCospan C

/-- If a category has all binary products and all equalizers, then it also has all pullbacks.
As usual, this is not an instance, since there may be a more direct way to construct
pullbacks. -/
theorem hasWeakPullbacks_of_hasBinaryProducts_of_hasWeakKernels [Preadditive C]
    [HasBinaryProducts C] [HasWeakKernels C] : HasWeakPullbacks C where
      has_weakLimit F := {
        exists_weakLimit := by
          refine Nonempty.intro ⟨?_, ?_⟩
          · set u : F.obj WalkingCospan.left ⨯ F.obj WalkingCospan.right
                ⟶ F.obj WalkingCospan.one :=
              prod.fst ≫ F.map WalkingCospan.Hom.inl - prod.snd ≫ F.map WalkingCospan.Hom.inr
            have : HasWeakKernel u := sorry
            refine PullbackCone.mk (W := weakKernel u) ?_ ?_ ?_ (f := F.map WalkingCospan.Hom.inl)
              (g := F.map WalkingCospan.Hom.inr)
          · sorry
      }


end WeakPullback

end Limits
