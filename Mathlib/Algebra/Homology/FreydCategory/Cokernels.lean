/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.Homology.FreydCategory.Basic

/-!
# Cokernels in Freyd categories

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

namespace CandidateCokernel

/-- If `f` is a morphism of `Arrow V`, this is a "candidate cokernel" of `f`, i.e. an object
in `Arrow V` whose image in `RightFreyd V` will be a cokernel of the image of `f`. -/
abbrev cokernel : Arrow V := Arrow.mk (biprod.desc v.hom f.right)

/-- For `f : u ⟶ v` a morphism in `Arrow V`, this is the morphism `v ⟶ cokernel f` from `v` to
the "candidate cokernel" of `f`, whose image in `RightFreyd V` will be the projection to
the cokernel of the image of `f`. -/
def π : v ⟶ cokernel f :=
  Arrow.homMk biprod.inl (𝟙 v.right) ((biprod.inl_desc _ _).trans (comp_id _).symm)

/-- The right homotopy expressing that `f ≫ π f` is sent to `0` in `RightFreyd V`. -/
def condition : RightHomotopy (f ≫ π f) 0 where
  hom := biprod.inr
  comm := by
    simp only [π, comp_right, homMk_right, Hom.zero_right]
    refine Eq.trans ?_ (biprod.inr_desc _ _).symm
    rw [sub_zero]
    exact comp_id _

set_option backward.isDefEq.respectTransparency false in
instance isEpi_π : Epi ((quotient V).map (π f)) :=
  have : IsIso ((π f).right) := by simp only [π, homMk_right]; infer_instance
  isEpi_of_right_iso _

variable {w : Arrow V} (g : v ⟶ w) (h : RightHomotopy (f ≫ g) 0)

/--
If `f : u ⟶ v` and `g : v ⟶ w` are morphisms in `Arrow V` such that `f ≫ g` is right homotopic
to `0`, this is the morphism from the "candidate cokernel" of `f` to `w` defined from the
right homotopy. -/
def desc : cokernel f ⟶ w := by
  refine Arrow.homMk (biprod.desc g.left h.hom) g.right ?_
  simp only [mk_hom]
  apply biprod.hom_ext'
  · convert (biprod.inl_desc_assoc _ _ _).trans
      (Eq.trans g.w (biprod.inl_desc_assoc _ _ _).symm) <;> rfl
  · convert (biprod.inr_desc_assoc g.left h.hom w.hom).trans
      (Eq.trans (by simp [h.comm.symm]) (biprod.inr_desc_assoc v.hom f.right g.right).symm) <;> rfl

@[reassoc]
lemma π_desc : π f ≫ desc f g h = g := by
  simp only [cokernel, π, desc]
  ext
  · simp only [comp_left, homMk_left]
    exact biprod.inl_desc _ _
  · simp only [comp_right, homMk_right]
    exact Category.id_comp _

end CandidateCokernel

variable {X : RightFreyd V} {a : (quotient V).obj v ⟶ X} (eq : (quotient V).map f ≫ a = 0)

/-- Let `f : u ⟶ v` be a morphism in `Arrow V`, and let `a : (quotient V).obj v ⟶ X` be
a morphism in `RightFreyd V` such that `(quotient V).map f ≫ a = 0`. This is the morphism
`(quotient V).obj (cokernel f) ⟶ X` that will serve as `cokernel.desc f`. -/
def desc' : (quotient V).obj (CandidateCokernel.cokernel f) ⟶ X := by
  rw [← ((quotient V).map_surjective a).choose_spec] at eq
  exact (quotient V).map (CandidateCokernel.desc _ _ (homotopyOfEq _ _ eq))

lemma π_desc' : (quotient V).map (CandidateCokernel.π f) ≫ desc' f eq = a := by
  rw [← ((quotient V).map_surjective a).choose_spec] at eq
  conv_rhs => rw [← ((quotient V).map_surjective a).choose_spec,
                      ← CandidateCokernel.π_desc _ _ (homotopyOfEq _ _ eq)]
  rfl

/-- For `f` a morphism in `Arrow V`, construct a cokernel cofork of `(quotient V).map f`. -/
def candidateCokernelCofork : Cocone (parallelPair ((quotient V).map f) 0) := by
  refine CokernelCofork.ofπ ((quotient V).map (CandidateCokernel.π f)) ?_
  rw [← (quotient V).map_comp]
  exact eq_of_rightHomotopy _ _ (CandidateCokernel.condition f)

/-- For `f` a morphism in `Arrow V`, the cokernel cofork of `(quotient V).map f` constructed
in `candidateCokernelCofork` is a colimit cofork. -/
def candidateCokernelCoforkIsCokernel : IsColimit (candidateCokernelCofork f) where
  desc s := desc' f (CokernelCofork.condition s)
  fac s j :=
    match j with
    | WalkingParallelPair.zero => by
      simp only [Cofork.app_zero_eq_comp_π_left, CokernelCofork.condition]
      exact zero_comp
    | WalkingParallelPair.one => π_desc' f (CokernelCofork.condition s)
  uniq s m eq :=
    (cancel_epi ((quotient V).map (CandidateCokernel.π f))).mp ((eq WalkingParallelPair.one).trans
    (π_desc' f (CokernelCofork.condition s)).symm)

/-- The category `RightFreyd V` has all cokernels if `V` has finite products. -/
instance : HasCokernels (RightFreyd V) where
  has_colimit {X Y} f := {
    exists_colimit := by
      obtain ⟨f, rfl⟩ := (quotient V).map_surjective f
      exact Nonempty.intro {
        cocone := candidateCokernelCofork f
        isColimit := candidateCokernelCoforkIsCokernel f}}

section Functor

variable {C : Type*} [Category* C] [Preadditive C] [HasCokernels C] (F : V ⥤ C) [F.Additive]

variable {u v : Arrow V} (f : u ⟶ v)

set_option backward.isDefEq.respectTransparency false in
def pi : cokernel (F.map v.hom) ⟶ cokernel (F.map ((CandidateCokernel.cokernel f).hom)) := by
  refine cokernel.desc _ (cokernel.π (F.map ((CandidateCokernel.cokernel f).hom))) ?_
  have := (CandidateCokernel.π f).w
  dsimp [CandidateCokernel.π] at this
  simp only [Arrow.homMk_left, Arrow.homMk_right, comp_id] at this
  apply_fun F.map at this
  rw [← this, F.map_comp, assoc, cokernel.condition, comp_zero]

set_option backward.isDefEq.respectTransparency false in
instance : Epi (pi F f) := by
    refine epi_of_epi_fac (f := cokernel.π (F.map v.hom))
      (h := cokernel.π (F.map (CandidateCokernel.cokernel f).hom)) ?_
    simp [pi]

set_option backward.isDefEq.respectTransparency false in
def cc : CokernelCofork ((functorLift F).map ((quotient V).map f)) := by
  refine CokernelCofork.ofπ (pi F f) ?_
  rw [← cancel_epi (cokernel.π (F.map u.hom))]
  simp [pi, functorLift_spec_map, CandidateCokernel.cokernel]
  sorry

set_option backward.isDefEq.respectTransparency false in
def e₀ : (parallelPair ((quotient V).map f) 0 ⋙ functorLift F) ≅
    parallelPair ((functorLift F).map ((quotient V).map f)) 0 :=
  diagramIsoParallelPair (parallelPair ((quotient V).map f) 0 ⋙ functorLift F) ≪≫
  parallelPair.ext (Iso.refl _) (Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
def e : (functorLift F).mapCocone (candidateCokernelCofork f) ≅ (Cocone.precompose
    (e₀ F f).hom).obj (cc F f) := by
  refine Cocone.ext (Iso.refl _) (fun j ↦ ?_)
  match j with
  | WalkingParallelPair.zero => simp
  | WalkingParallelPair.one =>
    rw [← cancel_epi (cokernel.π _)]
    simp only [parallelPair_obj_one, e₀, Functor.comp_map, parallelPair_obj_zero,
      parallelPair_map_left, parallelPair_map_right, CandidateCokernel.cokernel,
      candidateCokernelCofork, CandidateCokernel.π, Functor.mapCocone_ι_app, Cofork.ofπ_ι_app,
      functorLift_spec_map, functorLiftAux_map, homMk_left, homMk_right, Functor.map_id,
      Iso.refl_hom, comp_id, Cocone.precompose_obj_ι, Iso.trans_hom, assoc, NatTrans.comp_app,
      diagramIsoParallelPair_hom_app, eqToHom_refl, parallelPair.ext_hom_app, id_comp]
    refine (cokernel.π_desc _ _ _).trans ?_
    rw [id_comp]
    exact (cokernel.π_desc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
def colim : IsColimit (cc F f) := by
  refine Cofork.IsColimit.mk' _ (fun s ↦ ⟨?_, ?_, ?_⟩)
  · refine cokernel.desc _ (cokernel.π _ ≫ Cofork.π s) ?_
    have : PreservesBinaryBiproducts F := sorry
    rw [← cancel_epi (F.mapBiprod v.left u.right).inv]
    simp only [biprod.uniqueUpToIso_inv, Functor.mapBinaryBicone_inl, BinaryBiproduct.bicone_inl,
      Functor.mapBinaryBicone_inr, BinaryBiproduct.bicone_inr, CandidateCokernel.cokernel, mk_hom,
      comp_zero]
    ext
    · simp only [biprod.inl_desc_assoc, comp_zero]
      rw [← F.map_comp_assoc, biprod.inl_desc]
      exact (cokernel.condition_assoc (F.map v.hom) _).trans zero_comp
    · simp only [biprod.inr_desc_assoc, comp_zero]
      rw [← F.map_comp_assoc, biprod.inr_desc, ← assoc]
      change (_ ≫ cokernel.π (F.map v.hom)) ≫ _ = _
      rw [← cokernel.π_desc (F.map u.hom) (F.map (Hom.right f) ≫ cokernel.π (F.map v.hom)) sorry]
      rw [assoc]
      convert comp_zero
      have := Cofork.condition s
      simp only [functorLift_spec_map, functorLiftAux_map, zero_comp] at this
      exact this
  · sorry
  · sorry

def iscolim : IsColimit ((functorLift F).mapCocone (candidateCokernelCofork f)) :=
  ((IsColimit.precomposeHomEquiv (e₀ F f) _).invFun (colim F f)).ofIsoColimit (e F f).symm

set_option backward.isDefEq.respectTransparency false in
def preservesCokernel_functorLift_aux {u v : Arrow V} (f : u ⟶ v) :
    IsColimit ((functorLift F).mapCocone (candidateCokernelCofork f)) := by
  set c := ((functorLift F).mapCocone (candidateCokernelCofork f))
  set p : (functorLift F).obj ((quotient V).obj v) ⟶ c.pt := c.ι.app WalkingParallelPair.one
  have : Epi p := by
    refine epi_of_epi_fac (f := cokernel.π (F.map v.hom))
      (h := cokernel.π (F.map (CandidateCokernel.cokernel f).hom)) ?_
    simp [p, c, candidateCokernelCofork, functorLift_spec_map, CandidateCokernel.π]
  set e := diagramIsoParallelPair (parallelPair ((quotient V).map f) 0 ⋙ functorLift F)
  apply (IsColimit.precomposeHomEquiv e.symm c).toFun
  refine Cofork.IsColimit.mk' _ (fun s ↦ ⟨?_, ?_, ?_⟩)
  · dsimp [e, c, candidateCokernelCofork]
    simp only [Cocone.precompose_obj_pt, Functor.mapCocone_pt, Cofork.ofπ_pt, functorLift_spec_obj,
      functorLiftAux_obj, mk_hom]
    refine cokernel.desc _ (cokernel.π _ ≫ Cofork.π s) ?_
    dsimp
    have : PreservesBinaryBiproducts F := sorry
    rw [← cancel_epi (F.mapBiprod _ _).inv]
    ext
    · simp only [biprod.uniqueUpToIso_inv, Functor.mapBinaryBicone_inl, BinaryBiproduct.bicone_inl,
      Functor.mapBinaryBicone_inr, BinaryBiproduct.bicone_inr, biprod.inl_desc_assoc,
      ← F.map_comp_assoc, biprod.inl_desc, comp_zero]
      exact (cokernel.condition_assoc (F.map v.hom) _).trans zero_comp
    · simp only [biprod.uniqueUpToIso_inv, Functor.mapBinaryBicone_inl, BinaryBiproduct.bicone_inl,
      Functor.mapBinaryBicone_inr, BinaryBiproduct.bicone_inr, biprod.inr_desc_assoc,
      ← F.map_comp_assoc, biprod.inr_desc, comp_zero]
      rw [← assoc]
      change (_ ≫ cokernel.π (F.map v.hom)) ≫ _ = _
      rw [← cokernel.π_desc (F.map u.hom) (F.map (Hom.right f) ≫ cokernel.π (F.map v.hom)) sorry]
      rw [assoc]
      convert comp_zero
      have := Cofork.condition s
      dsimp at this
      simp only [functorLift_spec_map, functorLiftAux_map, Functor.map_zero, zero_comp] at this
      exact this
  · simp
    rw [← cancel_epi (cokernel.π (F.map v.hom))]
    simp [e, c, candidateCokernelCofork]
  · sorry



def preservesCokernel_functorLift {u v : RightFreyd V} (f : u ⟶ v) {c : CokernelCofork f}
    (hc : IsColimit c) : IsColimit ((functorLift F).mapCocone c) := sorry

local instance : HasZeroObject V := hasZeroObject_of_hasTerminal_object

instance : PreservesFiniteColimits (functorLift F) := by
  have : HasBinaryBiproducts (RightFreyd V) := HasBinaryBiproducts.of_hasBinaryProducts
  have : HasFiniteBiproducts (RightFreyd V) := HasFiniteBiproducts.of_hasFiniteProducts
  have : HasCoequalizers (RightFreyd V) := Preadditive.hasCoequalizers_of_hasCokernels
  have : HasZeroObject C := F.hasZeroObject_of_additive
  have : ∀ {X Y : RightFreyd V} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) (functorLift F) :=
    fun f ↦ {preserves hc := Nonempty.intro (preservesCokernel_functorLift F f hc)}
  exact (functorLift F).preservesFiniteColimits_of_preservesCokernels

end Functor

end RightFreyd

end CategoryTheory.Preadditive
