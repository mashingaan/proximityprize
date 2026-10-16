/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE.
Authors: Mikhail Izhutkin (mashingaan)
-/
import Research.ProximityPrize.Frontier._IncidenceAnchorCubeUpper

/-!
# Shared support of full error circuits

A relation with every coefficient nonzero removes exclusive coordinates from
every participating error. Four-error independence supplies the rank needed
by received-space shortening for a five-error circuit.
-/

set_option autoImplicit false

namespace ProximityGap.IncidenceCircuitShortening

open ProximityGap.IncidenceDependencyArithmetic
open ProximityGap.IncidenceAnchorCubeUpper

/-- Every vector in a full relation vanishes off the coordinates shared by at
least two of its supplied supports. -/
theorem full_relation_shared_support
    {F I Coord : Type} [Field F] [Fintype I] [DecidableEq I]
    [Fintype Coord] [DecidableEq Coord]
    (e : I → (Coord → F)) (Q : I → Finset Coord)
    (hsupport : ∀ i, ∀ x ∉ Q i, e i x = 0)
    (c : I → F) (hc : ∀ i, c i ≠ 0) (hrel : (∑ i, c i • e i) = 0) :
    ∀ i, ∀ x ∉ sharedSupport Q, e i x = 0 := by
  classical
  intro i x hx
  by_cases hxi : x ∈ Q i
  · have hother : ∀ j, j ≠ i → e j x = 0 := by
      intro j hji
      apply hsupport j x
      intro hxj
      apply hx
      simp only [sharedSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, j, Ne.symm hji, hxi, hxj⟩
    have he : (∑ j, c j * e j x) = c i * e i x := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [hother j hji, mul_zero]
      · simp
    have hz : (∑ j, c j * e j x) = 0 := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
        congrArg (fun f : Coord → F => f x) hrel
    exact (mul_eq_zero.mp (he.symm.trans hz)).resolve_left (hc i)
  · exact hsupport i x hxi

/-- A five-error full relation in an actual canonical overbudget family forces
at least D+1 shared error coordinates. Its rank activity is derived. -/
theorem five_bad_error_circuit_shared_support
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
    (a : Fin 5 → I) (ha : Function.Injective a)
    (c : Fin 5 → F) (hc : ∀ j, c j ≠ 0)
    (hrel : (∑ j, c j • (u0 + gamma (a j) • u1 - w (a j))) = 0) :
    536870914 ≤ (sharedSupport (fun j => (T (a j))ᶜ)).card := by
  classical
  let e : Fin 5 → (Coord → F) := fun j => u0 + gamma (a j) • u1 - w (a j)
  let Q : Fin 5 → Finset Coord := fun j => (T (a j))ᶜ
  let V := Submodule.span F (Set.range e)
  let P := Submodule.span F {u0, u1}
  have heQ : ∀ j, ∀ x ∉ Q j, e j x = 0 := by
    intro j x hx
    have he := hwag (a j) x (by simpa [Q] using hx)
    change u0 x + gamma (a j) * u1 x - w (a j) x = 0
    exact sub_eq_zero.mpr (by simpa only [smul_eq_mul] using he.symm)
  have heS := full_relation_shared_support e Q heQ c hc hrel
  have hVS : ∀ v ∈ V, ∀ x ∉ sharedSupport Q, v x = 0 := by
    intro v hv x hx
    let ev : (Coord → F) →ₗ[F] F :=
      LinearMap.proj (R := F) (φ := fun _ : Coord => F) x
    have hle : V ≤ LinearMap.ker ev := by
      apply Submodule.span_le.mpr
      rintro z ⟨j, rfl⟩
      exact heS j x hx
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
  let b : Fin 4 → I := fun j => a j.castSucc
  have hb : Function.Injective b := ha.comp (Fin.castSucc_injective 4)
  have hLI := four_bad_errors_linearIndependent_in_overbudget_family hlength
    gamma w hinj C T u0 u1 hsize hC hwC hcompl hwag hno b hb
  change LinearIndependent F (fun j : Fin 4 => e j.castSucc) at hLI
  have hspan : Submodule.span F (Set.range (fun j : Fin 4 => e j.castSucc)) ≤ V := by
    apply Submodule.span_mono
    rintro z ⟨j, rfl⟩
    exact ⟨j.castSucc, rfl⟩
  have hrank : 4 ≤ Module.finrank F V := by
    have hm := Submodule.finrank_mono hspan
    rw [finrank_span_eq_card hLI] at hm
    simpa using hm
  have hdistance : ∀ z ∈ C, ∀ B : Finset Coord, B.card < 536870913 →
      (∀ x ∉ B, z x = 0) → z = 0 := by
    intro z hz B hB hs
    exact hC z hz ⟨B, by omega, hs⟩
  have hshort := received_space_shortening_bound C V P 536870913 (by norm_num)
    hVP hP (sharedSupport Q) hVS (by omega) hdistance
  change 536870914 ≤ (sharedSupport Q).card
  omega

end ProximityGap.IncidenceCircuitShortening

#print axioms ProximityGap.IncidenceCircuitShortening.full_relation_shared_support
#print axioms ProximityGap.IncidenceCircuitShortening.five_bad_error_circuit_shared_support
