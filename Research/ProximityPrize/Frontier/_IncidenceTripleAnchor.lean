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
The canonical witness-degree counts and the final numerical transfer remain
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

end ProximityGap.IncidenceTripleAnchor

#print axioms ProximityGap.IncidenceTripleAnchor.external_head_anchor_overlap
#print axioms ProximityGap.IncidenceTripleAnchor.two_region_cube_lower
