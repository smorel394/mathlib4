/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.Homology.FreydCategory.Quotient

/-!
# Kernels in Freyd categories

-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex Arrow

variable {V : Type*} [Category* V] [Preadditive V]

namespace CategoryTheory.Preadditive

namespace RightFreyd

variable [HasFiniteProducts V]

local instance : HasBinaryBiproducts V := HasBinaryBiproducts.of_hasBinaryProducts

variable [HasWeakKernels V]

local instance : HasWeakEqualizers V := Preadditive.hasWeakEqualizers_of_hasWeakKernels

local instance : HasWeakPullbacks V := hasWeakPullbacks_of_hasBinaryProducts_of_hasWeakKernels V

variable {u v : Arrow V} (f : u ⟶ v)

namespace CandidateKernel

/-- If `f` is a morphism of `Arrow V`, this is a "candidate kernel" of `f`, i.e. an object
in `Arrow V` whose image in `RightFreyd V` will be a kernel of the image of `f`. -/
abbrev kernel : Arrow V := Arrow.mk (weakPullback.fst (weakPullback.snd v.hom f.right) u.hom)

/-- For `f : u ⟶ v` a morphism in `Arrow V`, this is the morphism `kernel f ⟶ u` from the
"candidate kernel" of `f` to `u`, whose image in `RightFreyd V` will be the inclusion of
the kernel of the image of `f`. -/
def ι : kernel f ⟶ u :=
  Arrow.homMk (weakPullback.snd _ _) (weakPullback.snd _ _)
    ((weakPullback.condition).symm.trans rfl)

/-- The right homotopy expressing that `ι f ≫ f` is sent to `0` in `RightFreyd V`. -/
def condition : RightHomotopy (ι f ≫ f) 0 where
  hom := weakPullback.fst _ _
  comm := by
    simp only [ι, comp_right, homMk_right, Hom.zero_right, sub_zero]
    exact weakPullback.condition.symm

/-- Let `a` and `b` be morphisms in `V`. Consider the morphism from
`Arrow.mk (weakPullback.fst a b)` to `Arrow.mk b` in `Arrow V` whose left component
is `weakPullback.snd` and whose right component is `a`. Then the image of this morphism in
`RighFreyd V` is a monomorphism.
-/
lemma isMono_of_witness_snd {X Y Z : V} (a : X ⟶ Z) (b : Y ⟶ Z) :
    Mono ((quotient V).map (Arrow.homMk (f := Arrow.mk (weakPullback.fst a b)) (g := Arrow.mk b)
    (weakPullback.snd _ _) a weakPullback.condition.symm )) where
  right_cancellation g₁ g₂ eq := by
    obtain ⟨g₁, rfl⟩ := (quotient V).map_surjective g₁
    obtain ⟨g₂, rfl⟩ := (quotient V).map_surjective g₂
    apply eq_of_rightHomotopy
    set h := homotopyOfEq _ _ eq
    refine ⟨weakPullback.lift (g₁.right - g₂.right) h.hom ?_, ?_⟩
    · exact (Preadditive.sub_comp _ _ _).trans h.comm
    · exact (weakPullback.lift_fst _ _ _).symm

instance isMono_ι : Mono ((quotient V).map (ι f)) := isMono_of_witness_snd _ _

variable {w : Arrow V} (g : w ⟶ u) (h : RightHomotopy (g ≫ f) 0)

/--
If `f : u ⟶ v` and `g : w ⟶ u` are morphisms in `Arrow V` such that `g ≫ f` is right homotopic
to `0`, this is the morphism from `w` to the "candidate kernel" of `f` defined from the
right homotopy. -/
def lift : w ⟶ kernel f := by
  refine Arrow.homMk (weakPullback.lift (w.hom ≫ weakPullback.lift h.hom g.right
    (by simp [← h.comm])) g.left
    (by simp only [assoc, Arrow.w]; congr; exact weakPullback.lift_snd _ _ _))
    (weakPullback.lift h.hom g.right (by simp [← h.comm])) ((weakPullback.lift_fst _ _ _).trans rfl)

@[reassoc]
lemma lift_ι : lift f g h ≫ ι f = g := by
  simp only [kernel, lift, ι]
  ext
  · simp only [comp_left, homMk_left]
    erw [weakPullback.lift_snd]
  · simp only [comp_right, homMk_right]
    erw [weakPullback.lift_snd]

end CandidateKernel

variable {X : RightFreyd V} {a : X ⟶ (quotient V).obj u} (eq : a ≫ (quotient V).map f = 0)

/-- Let `f : u ⟶ v` be a morphism in `Arrow V`, and let `a : X ⟶ (quotient V).obj u` be
a morphism in `RightFreyd V` such that `a ≫ (quotient V).map f = 0`. This is the morphism
`X ⟶ (quotient V).obj (kernel f)` that will serve as `kernel.lift f`. -/
def lift' : X ⟶ (quotient V).obj (CandidateKernel.kernel f) := by
  rw [← ((quotient V).map_surjective a).choose_spec] at eq
  exact (quotient V).map (CandidateKernel.lift _ _ (homotopyOfEq _ _ eq))

lemma lift'_ι : lift' f eq ≫ (quotient V).map (CandidateKernel.ι f) = a := by
  rw [← ((quotient V).map_surjective a).choose_spec] at eq
  conv_rhs => rw [← ((quotient V).map_surjective a).choose_spec,
                      ← CandidateKernel.lift_ι _ _ (homotopyOfEq _ _ eq)]
  rfl

/-- For `f` a morphism in `Arrow V`, construct a kernel fork of `(quotient V).map f`. -/
def candidateKernelFork : Cone (parallelPair ((quotient V).map f) 0) := by
  refine KernelFork.ofι ((quotient V).map (CandidateKernel.ι f)) ?_
  rw [← (quotient V).map_comp]
  exact eq_of_rightHomotopy _ _ (CandidateKernel.condition f)

/-- For `f` a morphism in `Arrow V`, the kernel fork of `(quotient V).map f` constructed
in `candidateCokernelCofork` is a limit fork. -/
def candidateKernelForkIsKernel : IsLimit (candidateKernelFork f) where
  lift s := lift' f (KernelFork.condition s)
  fac s j :=
    match j with
    | WalkingParallelPair.zero => lift'_ι _ _
    | WalkingParallelPair.one => by simp
  uniq s m eq :=
    (cancel_mono ((quotient V).map (CandidateKernel.ι f))).mp ((eq WalkingParallelPair.zero).trans
    (lift'_ι f (KernelFork.condition s)).symm)

/-- The category `RightFreyd V` has all cokernels if `V` has finite products and weak kernels. -/
instance : HasKernels (RightFreyd V) where
  has_limit {X Y} f := {
    exists_limit := by
      obtain ⟨f, rfl⟩ := (quotient V).map_surjective f
      exact Nonempty.intro {
        cone := candidateKernelFork f
        isLimit := candidateKernelForkIsKernel f}}

end RightFreyd

end CategoryTheory.Preadditive
