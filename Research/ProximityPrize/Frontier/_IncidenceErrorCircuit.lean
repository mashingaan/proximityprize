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

/-- A bad head constrains every code-valued combination of the received rows. -/
theorem bad_head_received_coefficients {F Coord : Type} [Field F]
    (C : Submodule F (Coord → F)) (u0 u1 w : Coord → F) (gamma : F)
    (T : Set Coord) (hw : w ∈ C)
    (hag : ∀ x ∈ T, w x = u0 x + gamma * u1 x)
    (hno : ¬ ∃ f0 ∈ C, ∃ f1 ∈ C,
      ∀ x ∈ T, f0 x = u0 x ∧ f1 x = u1 x)
    (a b : F) (hz : a • u0 + b • u1 ∈ C) : b = a * gamma := by
  by_contra hne
  have hdne : a * gamma - b ≠ 0 := by
    intro h
    exact hne (sub_eq_zero.mp h).symm
  let V := (a * gamma - b)⁻¹ • (a • w - (a • u0 + b • u1))
  let U := w - gamma • V
  have hVC : V ∈ C := C.smul_mem _ (C.sub_mem (C.smul_mem a hw) hz)
  have hUC : U ∈ C := C.sub_mem hw (C.smul_mem gamma hVC)
  have hV : ∀ x ∈ T, V x = u1 x := by
    intro x hx
    have he : a * w x - (a * u0 x + b * u1 x) =
        (a * gamma - b) * u1 x := by
      rw [hag x hx]
      ring
    change (a * gamma - b)⁻¹ * (a * w x - (a * u0 x + b * u1 x)) = u1 x
    rw [he, ← mul_assoc, inv_mul_cancel₀ hdne, one_mul]
  apply hno
  refine ⟨U, hUC, V, hVC, ?_⟩
  intro x hx
  refine ⟨?_, hV x hx⟩
  change w x - gamma * V x = u0 x
  rw [hV x hx, hag x hx]
  ring

/-- Two distinct bad scalars force independence of received rows modulo C. -/
theorem received_quotient_independent_of_two_bad_heads
    {F I Coord : Type} [Field F]
    (C : Submodule F (Coord → F)) (u0 u1 : Coord → F)
    (w : I → (Coord → F)) (gamma : I → F) (T : I → Set Coord)
    (hw : ∀ i, w i ∈ C)
    (hag : ∀ i, ∀ x ∈ T i, w i x = u0 x + gamma i * u1 x)
    (hno : ∀ i, ¬ ∃ f0 ∈ C, ∃ f1 ∈ C,
      ∀ x ∈ T i, f0 x = u0 x ∧ f1 x = u1 x)
    (i j : I) (hgamma : gamma i ≠ gamma j)
    (a b : F) (hz : a • u0 + b • u1 ∈ C) : a = 0 ∧ b = 0 := by
  have hi := bad_head_received_coefficients C u0 u1 (w i) (gamma i) (T i)
    (hw i) (hag i) (hno i) a b hz
  have hj := bad_head_received_coefficients C u0 u1 (w j) (gamma j) (T j)
    (hw j) (hag j) (hno j) a b hz
  have he : a * (gamma i - gamma j) = 0 := by
    rw [mul_sub, ← hi, ← hj, sub_self]
  have ha : a = 0 := (mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hgamma)
  exact ⟨ha, by simpa [ha] using hi⟩

/-- Every error relation has vanishing scalar and scalar-parameter sums. -/
theorem error_relation_received_coefficients
    {F I Coord : Type} [Field F] [Fintype I]
    (C : Submodule F (Coord → F)) (u0 u1 : Coord → F)
    (w : I → (Coord → F)) (gamma : I → F) (T : I → Set Coord)
    (hw : ∀ i, w i ∈ C)
    (hag : ∀ i, ∀ x ∈ T i, w i x = u0 x + gamma i * u1 x)
    (hno : ∀ i, ¬ ∃ f0 ∈ C, ∃ f1 ∈ C,
      ∀ x ∈ T i, f0 x = u0 x ∧ f1 x = u1 x)
    (i j : I) (hgamma : gamma i ≠ gamma j) (c : I → F)
    (hrel : (∑ k, c k • (u0 + gamma k • u1 - w k)) = 0) :
    (∑ k, c k) = 0 ∧ (∑ k, c k * gamma k) = 0 := by
  have hc : (∑ k, c k) • u0 + (∑ k, c k * gamma k) • u1 ∈ C := by
    simp_rw [smul_sub, smul_add, smul_smul] at hrel
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_smul, ← Finset.sum_smul] at hrel
    rw [sub_eq_zero.mp hrel]
    exact C.sum_mem (fun k _ => C.smul_mem (c k) (hw k))
  exact received_quotient_independent_of_two_bad_heads C u0 u1 w gamma T
    hw hag hno i j hgamma _ _ hc

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
#print axioms ProximityGap.IncidenceErrorCircuit.bad_head_received_coefficients
#print axioms ProximityGap.IncidenceErrorCircuit.received_quotient_independent_of_two_bad_heads
#print axioms ProximityGap.IncidenceErrorCircuit.error_relation_received_coefficients
