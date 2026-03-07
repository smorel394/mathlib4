/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# API for the long exact sequence for sheaf cohomology

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w' w v u

namespace CategoryTheory

open Abelian

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace Sheaf

variable [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})] (n : ℕ)

variable {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact) (n₀ : ℕ)
    (n₁ : ℕ)

/-- The connecting homomorphism from `Hⁿ(S.X₃)` to `Hⁿ⁺¹(S.X₁)` -/
noncomputable def H.connectingHom (h : n₀ + 1 = n₁ := by omega) : H S.X₃ n₀ →+ H S.X₁ n₁ :=
  hS.extClass.postcomp _ h

lemma H.connectingHom_naturality {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁ := by lia)
    (c : S₁.X₃.H n₀) :
    H.map f.τ₁ n₁ (H.connectingHom h₁ n₀ n₁ h c) = H.connectingHom h₂ n₀ n₁ h (H.map f.τ₃ n₀ c) :=
  sorry

open AddCommGrpCat

namespace H

/-- The long exact sequence on sheaf cohomology. -/
noncomputable def longSequence (h : n₀ + 1 = n₁ := by omega) :
    ComposableArrows AddCommGrpCat.{w'} 5 := ComposableArrows.mk₅
  (ofHom (H.map S.f n₀))
  (ofHom (H.map S.g n₀))
  (ofHom (H.connectingHom hS n₀ n₁))
  (ofHom (H.map S.f n₁))
  (ofHom (H.map S.g n₁))

theorem longSequence_exact (h : n₀ + 1 = n₁ := by omega) : (longSequence hS n₀ n₁ h).Exact :=
  Ext.covariantSequence_exact _ hS n₀ n₁ h

lemma longSequence_exact₁' (h : n₀ + 1 = n₁ := by omega) :
    (ShortComplex.mk (ofHom (H.connectingHom hS n₀ n₁ h)) (ofHom (H.map S.f n₁)) (by
      convert ((longSequence_exact hS n₀ n₁ h).sc 2).zero)).Exact := by
  convert (longSequence_exact hS n₀ n₁ h).exact 2

lemma longSequence_exact₃' (h : n₀ + 1 = n₁ := by omega) :
    (ShortComplex.mk (ofHom (H.map S.g n₀)) (ofHom (H.connectingHom hS n₀ n₁ h)) (by
      convert ((longSequence_exact hS n₀ n₁ h).sc 1).zero)).Exact := by
  convert (longSequence_exact hS n₀ n₁ h).exact 1

lemma longSequence_exact₂' (n : ℕ) :
    (ShortComplex.mk (ofHom (H.map S.f n)) (ofHom (H.map S.g n)) (by
      convert ((longSequence_exact hS n (n + 1)).sc 0).zero)).Exact := by
  convert (longSequence_exact hS n (n + 1)).exact 0

include hS in
lemma longSequence_exact₂ (x₂ : H S.X₂ n) (hx₂ : H.map S.g n x₂ = 0) :
    ∃ x₁ : H S.X₁ n, H.map S.f n x₁ = x₂ := by
  have := longSequence_exact₂' hS n
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₂ hx₂

lemma longSequence_exact₃ (h : n₀ + 1 = n₁ := by omega) (x₃ : H S.X₃ n₀)
    (hx₃ : H.connectingHom hS n₀ n₁ h x₃ = 0) :
    ∃ x₂ : H S.X₂ n₀, H.map S.g n₀ x₂ = x₃ := by
  have := longSequence_exact₃' hS n₀ n₁ h
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₃ hx₃

lemma longSequence_exact₁ (h : n₀ + 1 = n₁ := by omega) (x₁ : H S.X₁ n₁)
    (hx₁ : H.map S.f n₁ x₁ = 0) :
    ∃ x₃ : H S.X₃ n₀, H.connectingHom hS n₀ n₁ h x₃ = x₁ := by
  have := longSequence_exact₁' hS n₀ n₁ h
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₁ hx₁

variable {T : C} (hT : Limits.IsTerminal T)

open Opposite

lemma longSequence_equiv₀_exact₃ (x₃ : S.X₃.val.obj (op T))
    (hx₃ : (H.connectingHom hS 0 1) ((H.equiv₀ S.X₃ hT).symm x₃) = 0) :
    ∃ x₂ : S.X₂.obj.obj (op T), S.g.hom.app (op T) x₂ = x₃ := by
  obtain ⟨x₂', hx₂'⟩ := longSequence_exact₃ hS 0 _ _ ((H.equiv₀ S.X₃ hT).symm x₃) hx₃
  use H.equiv₀ S.X₂ hT x₂'
  simp [H.equiv₀_naturality, hx₂']

end H

end Sheaf

end CategoryTheory
