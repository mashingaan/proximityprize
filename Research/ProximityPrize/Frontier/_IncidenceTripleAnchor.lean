/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE.
Authors: Mikhail Izhutkin (mashingaan)
-/
import Research.ProximityPrize.Frontier._IncidenceDependencyArithmetic

/-!
# Geometry and the two-region cube bound for a triple-line anchor

The overlap estimate uses a genuinely external code head. The cube theorem is
universal over nonnegative degrees and derives its bound from two degree sums.
Degree sums are double counted from the actual agreement sets. The final
uniform numerical transfer and the complementary cubic upper bound remain
separate obligations.
-/

set_option autoImplicit false

namespace ProximityGap.IncidenceTripleAnchor

open ProximityGap.IncidenceDependencyArithmetic

/-- An external head has limited error overlap with the affine error support. -/
theorem external_head_anchor_overlap
    {F Coord : Type} [Field F] [Fintype Coord] [DecidableEq Coord]
    (C : Submodule F (Coord → F)) (u0 u1 U V w : Coord → F) (gamma : F)
    (D t : ℕ) (E : Finset Coord)
    (hU : U ∈ C) (hV : V ∈ C) (hw : w ∈ C)
    (houtside : w ≠ U + gamma • V)
    (hag : ∀ x ∉ E, w x = u0 x + gamma * u1 x) (hweight : E.card ≤ t)
    (hdistance : ∀ v ∈ C, ∀ B : Finset Coord, B.card < D →
      (∀ x ∉ B, v x = 0) → v = 0) :
    D + (affineErrorSupport u0 u1 U V ∩ E).card ≤
      (affineErrorSupport u0 u1 U V).card + t := by
  classical
  let Q := affineErrorSupport u0 u1 U V
  let z := w - (U + gamma • V)
  have hzC : z ∈ C := C.sub_mem hw (C.add_mem hU (C.smul_mem gamma hV))
  have hz : z ≠ 0 := fun h => houtside (sub_eq_zero.mp h)
  have hs : ∀ x ∉ Q ∪ E, z x = 0 := by
    intro x hx
    have hp : x ∉ Q ∧ x ∉ E := by simpa using hx
    have hq : u0 x = U x ∧ u1 x = V x := by
      simpa [Q, affineErrorSupport, not_or] using hp.1
    change w x - (U x + gamma * V x) = 0
    rw [hag x hp.2, hq.1, hq.2, sub_self]
  have hD : D ≤ (Q ∪ E).card := by
    by_contra hn
    exact hz (hdistance z hzC (Q ∪ E) (by omega) hs)
  have hc := Finset.card_union_add_card_inter Q E
  change D + (Q ∩ E).card ≤ Q.card + t
  omega

/-- A two-region cubic tangent bound. The larger reference degree belongs to Q.
Only total agreement mass and agreement mass inside Q are needed. -/
theorem two_region_cube_lower
    {Coord : Type} [Fintype Coord] [DecidableEq Coord]
    (Q : Finset Coord) (d : Coord → ℝ) (mu nu : ℝ)
    (hd : ∀ x, 0 ≤ d x) (hnu : 0 ≤ nu) (horder : nu ≤ mu)
    (hinside : (Q.card : ℝ) * mu ≤ ∑ x ∈ Q, d x)
    (htotal : (Q.card : ℝ) * mu + (Qᶜ.card : ℝ) * nu ≤ ∑ x, d x) :
    (Q.card : ℝ) * mu^3 + (Qᶜ.card : ℝ) * nu^3 ≤ ∑ x, (d x)^3 := by
  classical
  have hmu : 0 ≤ mu := hnu.trans horder
  have htangent : ∀ x r, 0 ≤ r → 3*r^2*d x - 2*r^3 ≤ (d x)^3 := by
    intro x r hr
    have hp := mul_nonneg (sq_nonneg (d x-r))
      (add_nonneg (hd x) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr))
    nlinarith
  have hleft := Finset.sum_le_sum (fun x (_ : x ∈ Q) => htangent x mu hmu)
  have hright := Finset.sum_le_sum (fun x (_ : x ∈ Qᶜ) => htangent x nu hnu)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul] at hleft hright
  rw [← Finset.sum_add_sum_compl Q d] at htotal
  rw [← Finset.sum_add_sum_compl Q (fun x => (d x)^3)]
  have hsq : 0 ≤ mu^2 - nu^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr horder) (add_nonneg hmu hnu)]
  have hin := mul_nonneg hsq (sub_nonneg.mpr hinside)
  have hall := mul_nonneg (sq_nonneg nu) (sub_nonneg.mpr htotal)
  nlinarith

noncomputable def agreementDegree {I Coord : Type} [Fintype I]
    [DecidableEq Coord] (T : I → Finset Coord) (x : Coord) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => x ∈ T i)).card

/-- Agreement mass on a region is the sum of the individual regional counts. -/
theorem agreement_mass_on_region {I Coord : Type} [Fintype I]
    [DecidableEq Coord] (T : I → Finset Coord) (Q : Finset Coord) :
    (∑ x ∈ Q, agreementDegree T x) = ∑ i, (T i ∩ Q).card := by
  classical
  calc
    (∑ x ∈ Q, agreementDegree T x) =
        ∑ x ∈ Q, ∑ i, if x ∈ T i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.card_filter (fun i : I => x ∈ T i) Finset.univ
    _ = ∑ i, ∑ x ∈ Q, if x ∈ T i then 1 else 0 := Finset.sum_comm
    _ = ∑ i, (T i ∩ Q).card := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.card_filter]
      congr 1
      ext x
      simp [and_comm]

/-- The two-region cube lower bound for an actual finite agreement family. -/
theorem agreement_cube_lower_of_counts
    {I Coord : Type} [Fintype I] [Fintype Coord] [DecidableEq Coord]
    (T : I → Finset Coord) (Q : Finset Coord) (A B : ℕ) (mu nu : ℝ)
    (hinside : ∀ i, A ≤ (T i ∩ Q).card)
    (htotal : ∀ i, A+B ≤ (T i).card)
    (hmu : (Q.card : ℝ) * mu = (Fintype.card I : ℝ) * A)
    (hnu : (Qᶜ.card : ℝ) * nu = (Fintype.card I : ℝ) * B)
    (hnupos : 0 ≤ nu) (horder : nu ≤ mu) :
    (Q.card : ℝ) * mu^3 + (Qᶜ.card : ℝ) * nu^3 ≤
      ∑ x, (agreementDegree T x : ℝ)^3 := by
  classical
  have hinsNat : Fintype.card I * A ≤ ∑ x ∈ Q, agreementDegree T x := by
    rw [agreement_mass_on_region]
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hinside i)
  have htotNat : Fintype.card I * (A+B) ≤ ∑ x, agreementDegree T x := by
    have hm := agreement_mass_on_region T (Finset.univ : Finset Coord)
    simp only [Finset.inter_univ] at hm
    rw [hm]
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => htotal i)
  have hins : (Q.card : ℝ) * mu ≤ ∑ x ∈ Q, (agreementDegree T x : ℝ) := by
    rw [hmu]
    exact_mod_cast hinsNat
  have htot : (Q.card : ℝ) * mu + (Qᶜ.card : ℝ) * nu ≤
      ∑ x, (agreementDegree T x : ℝ) := by
    rw [hmu, hnu]
    have he : (Fintype.card I : ℝ) * (A+B) ≤
        ∑ x, (agreementDegree T x : ℝ) := by exact_mod_cast htotNat
    push_cast at he
    nlinarith
  exact two_region_cube_lower Q (fun x => (agreementDegree T x : ℝ)) mu nu
    (fun x => Nat.cast_nonneg _) hnupos horder hins htot

/-- Every external actual witness contributes the regional and total agreement
counts needed by the cube theorem. Only its individual error budget is assumed. -/
theorem external_family_two_region_cube
    {F I Coord : Type} [Field F] [Fintype I] [Fintype Coord] [DecidableEq Coord]
    (C : Submodule F (Coord → F)) (u0 u1 U V : Coord → F)
    (w : I → (Coord → F)) (gamma : I → F) (T : I → Finset Coord)
    (D t : ℕ) (htD : t ≤ D) (hDn : D ≤ Fintype.card Coord)
    (hU : U ∈ C) (hV : V ∈ C) (hw : ∀ i, w i ∈ C)
    (houtside : ∀ i, w i ≠ U + gamma i • V)
    (hag : ∀ i, ∀ x ∈ T i, w i x = u0 x + gamma i * u1 x)
    (hweight : ∀ i, (T i)ᶜ.card ≤ t)
    (hdistance : ∀ v ∈ C, ∀ B : Finset Coord, B.card < D →
      (∀ x ∉ B, v x = 0) → v = 0)
    (mu nu : ℝ) (hnupos : 0 ≤ nu) (horder : nu ≤ mu)
    (hmu : ((affineErrorSupport u0 u1 U V).card : ℝ) * mu =
      (Fintype.card I : ℝ) * ((D-t : ℕ) : ℝ))
    (hnu : ((affineErrorSupport u0 u1 U V)ᶜ.card : ℝ) * nu =
      (Fintype.card I : ℝ) * ((Fintype.card Coord-D : ℕ) : ℝ)) :
    ((affineErrorSupport u0 u1 U V).card : ℝ) * mu^3 +
      ((affineErrorSupport u0 u1 U V)ᶜ.card : ℝ) * nu^3 ≤
        ∑ x, (agreementDegree T x : ℝ)^3 := by
  classical
  let Q := affineErrorSupport u0 u1 U V
  have hinside : ∀ i, D-t ≤ (T i ∩ Q).card := by
    intro i
    have ho := external_head_anchor_overlap C u0 u1 U V (w i) (gamma i)
      D t (T i)ᶜ hU hV (hw i) (houtside i)
      (fun x hx => hag i x (by simpa using hx)) (hweight i) hdistance
    change D + (Q ∩ (T i)ᶜ).card ≤ Q.card + t at ho
    have hp := Finset.card_inter_add_card_sdiff Q (T i)
    rw [Finset.sdiff_eq_inter_compl, Finset.inter_comm Q (T i)] at hp
    omega
  have htotal : ∀ i, (D-t)+(Fintype.card Coord-D) ≤ (T i).card := by
    intro i
    have hc := Finset.card_compl_add_card (T i)
    have he := hweight i
    omega
  exact agreement_cube_lower_of_counts T Q (D-t) (Fintype.card Coord-D)
    mu nu hinside htotal hmu hnu hnupos horder

end ProximityGap.IncidenceTripleAnchor

#print axioms ProximityGap.IncidenceTripleAnchor.external_head_anchor_overlap
#print axioms ProximityGap.IncidenceTripleAnchor.two_region_cube_lower
#print axioms ProximityGap.IncidenceTripleAnchor.agreement_mass_on_region
#print axioms ProximityGap.IncidenceTripleAnchor.agreement_cube_lower_of_counts
#print axioms ProximityGap.IncidenceTripleAnchor.external_family_two_region_cube
