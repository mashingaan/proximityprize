/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE.
Authors: Mikhail Izhutkin (mashingaan)
-/
import Research.ProximityPrize.Frontier._IncidenceDependencyArithmetic
import Research.ProximityPrize.Frontier._IncidenceConstantLineCap

/-!
# No full four-error relation in a canonical bad-witness family

This combines the direct error-relation transfer with the global cap-three
theorem. The cap uses the whole family's size and its lack of joint explanations.
The conclusion only excludes relations with every coefficient nonzero.
-/

set_option autoImplicit false

namespace ProximityGap.IncidenceErrorCircuit

open ProximityGap.IncidenceDependencyArithmetic
open ProximityGap.IncidenceAffineLines
open ProximityGap.IncidenceConstantLineCap

theorem no_four_full_error_relation
    {F I Coord : Type} [Field F] [Fintype I] [DecidableEq I]
    [Fintype Coord] [DecidableEq Coord]
    (gamma : I → F) (w : I → (Coord → F)) (hinj : Function.Injective gamma)
    (C : Submodule F (Coord → F)) (d t : ℕ)
    (hsize : t+1 < Fintype.card I) (ht : 7*t < 3*(d+1))
    (hC : ∀ z ∈ C, (∃ B : Finset Coord, B.card ≤ d ∧
      ∀ x ∉ B, z x = 0) → z = 0)
    (T : I → Finset Coord) (u0 u1 : Coord → F)
    (hwC : ∀ i, w i ∈ C)
    (hcompl : ∀ i, (T i)ᶜ.card ≤ t)
    (hwag : ∀ i, ∀ x ∈ T i, w i x = u0 x + gamma i • u1 x)
    (hno : ∀ i, ¬ ∃ f0 ∈ C, ∃ f1 ∈ C,
      ∀ x ∈ T i, f0 x = u0 x ∧ f1 x = u1 x)
    (a : Fin 4 → I) (ha : Function.Injective a)
    (c : Fin 4 → F) (hc : ∀ i, c i ≠ 0) :
    (∑ i, c i • (u0 + gamma (a i) • u1 - w (a i))) ≠ 0 := by
  classical
  intro hrel
  have hdistance : ∀ v ∈ C, ∀ B : Finset Coord, B.card < d+1 →
      (∀ x ∉ B, v x = 0) → v = 0 := by
    intro v hv B hB hs
    exact hC v hv ⟨B, by omega, hs⟩
  obtain ⟨U, V, _, _, hline⟩ := affine_heads_of_small_error_relation
    C u0 u1 (fun i => w (a i)) (fun i => gamma (a i)) c
    (fun i => (T (a i))ᶜ) (d+1) t (fun i => hwC (a i)) hc
    (fun i x hx => by
      have hxin : x ∈ T (a i) := by simpa using hx
      simpa using hwag (a i) x hxin)
    (fun i => hcompl (a i))
    (by simp only [Fintype.card_fin]
        omega)
    hrel 0 1
    (fun h => (by decide : (0 : Fin 4) ≠ 1) (ha (hinj h))) hdistance
  have hcap := bad_witness_line_cap_three gamma w hinj Finset.univ C d t
    (by simpa using hsize) ht hC T u0 u1
    (fun i _ => hwC i) (fun i _ => hcompl i)
    (fun i _ => hwag i) (fun i _ => hno i) U V
  have hsub : Finset.univ.image a ⊆
      Finset.univ.filter (OnLine gamma w U V) := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hline j⟩
  have hfour := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ ha, Finset.card_univ,
    Fintype.card_fin] at hfour
  omega

end ProximityGap.IncidenceErrorCircuit

#print axioms ProximityGap.IncidenceErrorCircuit.no_four_full_error_relation
