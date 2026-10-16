/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE.
Authors: Mikhail Izhutkin (mashingaan)
-/
import Research.ProximityPrize.Frontier._IncidenceCircuitShortening

/-!
# Six-error rank obstruction

In rank four, independence of every four errors forces every active coordinate
to occur in at least three of six errors. Received-space shortening makes
this incompatible with the literal first-sponsor error budget.
-/

set_option autoImplicit false
attribute [local instance] Classical.propDecidable

namespace ProximityGap.IncidenceSixErrorRank

open ProximityGap.IncidenceDependencyArithmetic
open ProximityGap.IncidenceAnchorCubeUpper

/-- A nonzero coordinate in a rank-four six-vector family with every four
independent is nonzero on at least three of the six vectors. -/
theorem six_rank_four_coordinate_multiplicity
    {F Coord : Type} [Field F] [Fintype Coord]
    (e : Fin 6 → (Coord → F))
    (hLI : ∀ b : Fin 4 → Fin 6, Function.Injective b →
      LinearIndependent F (fun j => e (b j)))
    (hrank : Module.finrank F (Submodule.span F (Set.range e)) ≤ 4)
    (x : Coord) (hactive : ∃ j, e j x ≠ 0)
    (N : Finset (Fin 6)) (hNmem : ∀ j, j ∈ N ↔ e j x ≠ 0) :
    3 ≤ N.card := by
  classical
  by_contra hn
  let Z := {j : Fin 6 // e j x = 0}
  have hN : Fintype.card {j : Fin 6 // ¬ e j x = 0} ≤ 2 := by
    have he := Fintype.card_of_subtype N hNmem
    omega
  have hcomp := Fintype.card_subtype_compl (fun j : Fin 6 => e j x = 0)
  have hZle := Fintype.card_subtype_le (fun j : Fin 6 => e j x = 0)
  have hZcard : 4 ≤ Fintype.card Z := by
    simp only [Fintype.card_fin] at hcomp hZle
    dsimp [Z]
    omega
  let bz : Fin 4 → Z := fun j =>
    (Fintype.equivFin Z).symm (Fin.castLE hZcard j)
  let b : Fin 4 → Fin 6 := fun j => (bz j).val
  have hb : Function.Injective b := by
    intro i j hij
    have hs : bz i = bz j := Subtype.ext hij
    have hf : Fin.castLE hZcard i = Fin.castLE hZcard j :=
      (Fintype.equivFin Z).symm.injective hs
    apply Fin.ext
    exact congrArg (fun k : Fin (Fintype.card Z) => k.val) hf
  have hLIb := hLI b hb
  have hspan : Submodule.span F (Set.range (fun j => e (b j))) ≤
      Submodule.span F (Set.range e) := by
    apply Submodule.span_mono
    rintro z ⟨j, rfl⟩
    exact ⟨b j, rfl⟩
  have heq := Submodule.eq_of_le_of_finrank_le hspan (by
    rw [finrank_span_eq_card hLIb]
    simpa using hrank)
  let ev : (Coord → F) →ₗ[F] F :=
    LinearMap.proj (R := F) (φ := fun _ : Coord => F) x
  have hvan : Submodule.span F (Set.range (fun j => e (b j))) ≤
      LinearMap.ker ev := by
    apply Submodule.span_le.mpr
    rintro z ⟨j, rfl⟩
    exact (bz j).property
  obtain ⟨k, hk⟩ := hactive
  apply hk
  have hm : e k ∈ Submodule.span F (Set.range (fun j => e (b j))) := by
    rw [heq]
    exact Submodule.subset_span ⟨k, rfl⟩
  exact hvan hm

/-- The coordinate multiplicity forces three incidences per active coordinate,
even when the supplied supports include zero coordinates. -/
theorem six_rank_four_support_mass
    {F Coord : Type} [Field F] [Fintype Coord] [DecidableEq Coord]
    (e : Fin 6 → (Coord → F)) (Q : Fin 6 → Finset Coord)
    (hsupport : ∀ j, ∀ x ∉ Q j, e j x = 0)
    (hLI : ∀ b : Fin 4 → Fin 6, Function.Injective b →
      LinearIndependent F (fun j => e (b j)))
    (hrank : Module.finrank F (Submodule.span F (Set.range e)) ≤ 4) :
    3 * (Finset.univ.filter (fun x => ∃ j, e j x ≠ 0)).card ≤
      ∑ j, (Q j).card := by
  classical
  let S := Finset.univ.filter (fun x => ∃ j, e j x ≠ 0)
  have hpoint : ∀ x : Coord, (if x ∈ S then 3 else 0) ≤
      ∑ j : Fin 6, if x ∈ Q j then 1 else 0 := by
    intro x
    by_cases hx : x ∈ S
    · have hmul := six_rank_four_coordinate_multiplicity e hLI hrank x
        ((Finset.mem_filter.mp hx).2)
        (Finset.univ.filter (fun j => e j x ≠ 0)) (fun j => by simp)
      have hcount : (Finset.univ.filter (fun j => e j x ≠ 0)).card ≤
          ∑ j : Fin 6, if x ∈ Q j then 1 else 0 := by
        rw [Finset.card_filter]
        apply Finset.sum_le_sum
        intro j _
        by_cases he : e j x = 0
        · simp [he]
        · have hxQ : x ∈ Q j := by
            by_contra h
            exact he (hsupport j x h)
          simp [he, hxQ]
      simpa only [if_pos hx] using hmul.trans hcount
    · simp only [if_neg hx]
      exact Nat.zero_le _
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
  rw [Finset.sum_comm] at hs
  simpa [S, Finset.sum_ite, mul_comm] using hs

/-- Six distinct selected errors in a canonical overbudget family span at
least five dimensions. Rank four is excluded by support multiplicity. -/
theorem six_bad_errors_rank_at_least_five
    {F I Coord : Type} [Field F] [Fintype I] [DecidableEq I]
    [Fintype Coord] [DecidableEq Coord]
    (hlength : Fintype.card Coord = 1073741824)
    (gamma : I → F) (w : I → (Coord → F)) (hinj : Function.Injective gamma)
    (C : Submodule F (Coord → F)) (T : I → Finset Coord) (u0 u1 : Coord → F)
    (hsize : 1073741825 ≤ Fintype.card I)
    (hC : ∀ z ∈ C, (∃ B : Finset Coord, B.card ≤ 536870912 ∧
      ∀ x ∉ B, z x = 0) → z = 0)
    (hwC : ∀ i, w i ∈ C) (hcompl : ∀ i, (T i)ᶜ.card ≤ 221512374)
    (hwag : ∀ i, ∀ x ∈ T i, w i x = u0 x + gamma i • u1 x)
    (hno : ∀ i, ¬ ∃ f0 ∈ C, ∃ f1 ∈ C,
      ∀ x ∈ T i, f0 x = u0 x ∧ f1 x = u1 x)
    (a : Fin 6 → I) (ha : Function.Injective a) :
    5 ≤ Module.finrank F (Submodule.span F
      (Set.range (fun j => u0 + gamma (a j) • u1 - w (a j)))) := by
  classical
  let e : Fin 6 → (Coord → F) := fun j => u0 + gamma (a j) • u1 - w (a j)
  let Q : Fin 6 → Finset Coord := fun j => (T (a j))ᶜ
  let V := Submodule.span F (Set.range e)
  let P := Submodule.span F {u0, u1}
  let S := Finset.univ.filter (fun x => ∃ j, e j x ≠ 0)
  have hLI : ∀ b : Fin 4 → Fin 6, Function.Injective b →
      LinearIndependent F (fun j => e (b j)) := by
    intro b hb
    exact four_bad_errors_linearIndependent_in_overbudget_family hlength
      gamma w hinj C T u0 u1 hsize hC hwC hcompl hwag hno (a ∘ b) (ha.comp hb)
  have hspan : Submodule.span F
      (Set.range (fun j : Fin 4 => e j.castSucc.castSucc)) ≤ V := by
    apply Submodule.span_mono
    rintro z ⟨j, rfl⟩
    exact ⟨j.castSucc.castSucc, rfl⟩
  have hrank : 4 ≤ Module.finrank F V := by
    have hli := hLI (fun j => j.castSucc.castSucc)
      ((Fin.castSucc_injective 5).comp (Fin.castSucc_injective 4))
    have hm := Submodule.finrank_mono hspan
    rw [finrank_span_eq_card hli] at hm
    simpa using hm
  have heQ : ∀ j, ∀ x ∉ Q j, e j x = 0 := by
    intro j x hx
    have he := hwag (a j) x (by simpa [Q] using hx)
    change u0 x + gamma (a j) * u1 x - w (a j) x = 0
    exact sub_eq_zero.mpr (by simpa only [smul_eq_mul] using he.symm)
  have hVS : ∀ v ∈ V, ∀ x ∉ S, v x = 0 := by
    intro v hv x hx
    let ev : (Coord → F) →ₗ[F] F :=
      LinearMap.proj (R := F) (φ := fun _ : Coord => F) x
    have hle : V ≤ LinearMap.ker ev := by
      apply Submodule.span_le.mpr
      rintro z ⟨j, rfl⟩
      have hz : ∀ j, e j x = 0 := by simpa [S] using hx
      exact hz j
    exact hle hv
  have hP : Module.finrank F P ≤ 2 := by
    have h1 := finrank_span_le_card (R := F) ({u0, u1} : Set (Coord → F))
    have h2 : ({u0, u1} : Set (Coord → F)).toFinset.card ≤ 2 := by
      rw [Set.toFinset_insert, Set.toFinset_singleton]
      exact (Finset.card_insert_le _ _).trans (by simp)
    exact h1.trans h2
  have hVP : V ≤ C ⊔ P := by
    apply Submodule.span_le.mpr
    rintro z ⟨j, rfl⟩
    exact (C ⊔ P).sub_mem
      ((C ⊔ P).add_mem
        ((show P ≤ C ⊔ P from le_sup_right) (Submodule.subset_span (by simp)))
        ((C ⊔ P).smul_mem _
          ((show P ≤ C ⊔ P from le_sup_right) (Submodule.subset_span (by simp)))))
      ((show C ≤ C ⊔ P from le_sup_left) (hwC (a j)))
  have hdistance : ∀ z ∈ C, ∀ B : Finset Coord, B.card < 536870913 →
      (∀ x ∉ B, z x = 0) → z = 0 := by
    intro z hz B hB hs
    exact hC z hz ⟨B, by omega, hs⟩
  have hshort := received_space_shortening_bound C V P 536870913 (by norm_num)
    hVP hP S hVS (by omega) hdistance
  change 5 ≤ Module.finrank F V
  by_contra hn
  have hrankUpper : Module.finrank F V ≤ 4 := by omega
  have hmass := six_rank_four_support_mass e Q heQ hLI hrankUpper
  have hweight : (∑ j, (Q j).card) ≤ 6*221512374 := by
    have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hcompl (a j))
    simpa [Q] using hs
  change 3*S.card ≤ _ at hmass
  omega

/-- Two distinct errors cannot both be dependent extensions of the same four
selected errors. In particular two five-error full circuits cannot share four
errors in a canonical overbudget family. -/
theorem no_two_dependent_error_extensions
    {F I Coord : Type} [Field F] [Fintype I] [DecidableEq I]
    [Fintype Coord] [DecidableEq Coord]
    (hlength : Fintype.card Coord = 1073741824)
    (gamma : I → F) (w : I → (Coord → F)) (hinj : Function.Injective gamma)
    (C : Submodule F (Coord → F)) (T : I → Finset Coord) (u0 u1 : Coord → F)
    (hsize : 1073741825 ≤ Fintype.card I)
    (hC : ∀ z ∈ C, (∃ B : Finset Coord, B.card ≤ 536870912 ∧
      ∀ x ∉ B, z x = 0) → z = 0)
    (hwC : ∀ i, w i ∈ C) (hcompl : ∀ i, (T i)ᶜ.card ≤ 221512374)
    (hwag : ∀ i, ∀ x ∈ T i, w i x = u0 x + gamma i • u1 x)
    (hno : ∀ i, ¬ ∃ f0 ∈ C, ∃ f1 ∈ C,
      ∀ x ∈ T i, f0 x = u0 x ∧ f1 x = u1 x)
    (a : Fin 6 → I) (ha : Function.Injective a)
    (c d : Fin 4 → F) (alpha beta : F) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hrel1 : (∑ j : Fin 4, c j •
      (u0 + gamma (a j.castSucc.castSucc) • u1 - w (a j.castSucc.castSucc))) +
        alpha • (u0 + gamma (a 4) • u1 - w (a 4)) = 0)
    (hrel2 : (∑ j : Fin 4, d j •
      (u0 + gamma (a j.castSucc.castSucc) • u1 - w (a j.castSucc.castSucc))) +
        beta • (u0 + gamma (a 5) • u1 - w (a 5)) = 0) : False := by
  classical
  let e : Fin 6 → (Coord → F) := fun j => u0 + gamma (a j) • u1 - w (a j)
  let W := Submodule.span F (Set.range (fun j : Fin 4 => e j.castSucc.castSucc))
  have hsum : ∀ f : Fin 4 → F, (∑ j, f j • e j.castSucc.castSucc) ∈ W := by
    intro f
    apply Submodule.sum_mem
    intro j _
    exact W.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  have h4 : e 4 ∈ W := by
    have he : alpha • e 4 = -(∑ j : Fin 4, c j • e j.castSucc.castSucc) :=
      eq_neg_iff_add_eq_zero.mpr (by simpa only [e, add_comm] using hrel1)
    have hm : alpha • e 4 ∈ W := by
      rw [he]
      exact W.neg_mem (hsum c)
    have hi := W.smul_mem alpha⁻¹ hm
    simpa only [smul_smul, inv_mul_cancel₀ halpha, one_smul] using hi
  have h5 : e 5 ∈ W := by
    have he : beta • e 5 = -(∑ j : Fin 4, d j • e j.castSucc.castSucc) :=
      eq_neg_iff_add_eq_zero.mpr (by simpa only [e, add_comm] using hrel2)
    have hm : beta • e 5 ∈ W := by
      rw [he]
      exact W.neg_mem (hsum d)
    have hi := W.smul_mem beta⁻¹ hm
    simpa only [smul_smul, inv_mul_cancel₀ hbeta, one_smul] using hi
  have hspan : Submodule.span F (Set.range e) ≤ W := by
    apply Submodule.span_le.mpr
    rintro z ⟨j, rfl⟩
    fin_cases j
    · exact Submodule.subset_span ⟨0, rfl⟩
    · exact Submodule.subset_span ⟨1, rfl⟩
    · exact Submodule.subset_span ⟨2, rfl⟩
    · exact Submodule.subset_span ⟨3, rfl⟩
    · exact h4
    · exact h5
  have hLI := four_bad_errors_linearIndependent_in_overbudget_family hlength
    gamma w hinj C T u0 u1 hsize hC hwC hcompl hwag hno
    (fun j : Fin 4 => a j.castSucc.castSucc)
    (ha.comp ((Fin.castSucc_injective 5).comp (Fin.castSucc_injective 4)))
  have hdim : Module.finrank F W = 4 := by
    have hd := finrank_span_eq_card hLI
    simpa [W, e] using hd
  have hmono := Submodule.finrank_mono hspan
  have hlarge := six_bad_errors_rank_at_least_five hlength gamma w hinj C T u0 u1
    hsize hC hwC hcompl hwag hno a ha
  change 5 ≤ Module.finrank F (Submodule.span F (Set.range e)) at hlarge
  omega

end ProximityGap.IncidenceSixErrorRank

#print axioms ProximityGap.IncidenceSixErrorRank.six_rank_four_coordinate_multiplicity
#print axioms ProximityGap.IncidenceSixErrorRank.six_rank_four_support_mass
#print axioms ProximityGap.IncidenceSixErrorRank.six_bad_errors_rank_at_least_five
#print axioms ProximityGap.IncidenceSixErrorRank.no_two_dependent_error_extensions
