/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE.
Authors: Mikhail Izhutkin (mashingaan)
-/
import Research.ProximityPrize.Frontier._IncidenceTripleAnchor
import Research.ProximityPrize.Frontier._IncidenceTripleMass
import Research.ProximityPrize.Frontier._IncidenceConstantLineCap

/-!
# Canonical upper cube for agreement degrees

The pair-union and noncollinear triple bounds and the cap on collinear triples
are derived from the actual bad-witness family. This is the weaker upper cube
with quadratic coefficient 4t, which suffices for excluding a triple anchor in
an overbudget family once joined to its uniform lower cube.
-/

set_option autoImplicit false

namespace ProximityGap.IncidenceAnchorCubeUpper

open ProximityGap.IncidenceTripleAnchor ProximityGap.IncidenceTripleMass
open ProximityGap.IncidenceAffineLines ProximityGap.IncidenceConstantLineCap

theorem canonical_agreement_cube_upper
    {F I Coord : Type} [Field F] [Fintype I] [DecidableEq I]
    [Fintype Coord] [DecidableEq Coord]
    (gamma : I → F) (w : I → (Coord → F)) (hinj : Function.Injective gamma)
    (C : Submodule F (Coord → F)) (d t : ℕ)
    (hsize : t+1 < Fintype.card I) (ht : 7*t < 3*(d+1))
    (hDn : d+1 ≤ Fintype.card Coord)
    (hC : ∀ z ∈ C, (∃ B : Finset Coord, B.card ≤ d ∧
      ∀ x ∉ B, z x = 0) → z = 0)
    (T : I → Finset Coord) (u0 u1 : Coord → F)
    (hwC : ∀ i, w i ∈ C) (hcompl : ∀ i, (T i)ᶜ.card ≤ t)
    (hwag : ∀ i, ∀ x ∈ T i, w i x = u0 x + gamma i • u1 x)
    (hno : ∀ i, ¬ ∃ f0 ∈ C, ∃ f1 ∈ C,
      ∀ x ∈ T i, f0 x = u0 x ∧ f1 x = u1 x) :
    (∑ x, (agreementDegree T x)^3) ≤
      (Fintype.card Coord-(d+1)) * (Fintype.card I)^3 +
        4*t*(Fintype.card I)^2 + (d+1)*Fintype.card I := by
  classical
  have hcap : ∀ U V, (Finset.univ.filter (OnLine gamma w U V)).card ≤ 3 := by
    intro U V
    exact bad_witness_line_cap_three gamma w hinj Finset.univ C d t
      (by simpa using hsize) ht hC T u0 u1
      (fun i _ => hwC i) (fun i _ => hcompl i)
      (fun i _ => hwag i) (fun i _ => hno i) U V
  have hcol := collinearTriples_card_le_square_of_line_cap_three
    gamma w hinj Finset.univ hcap
  have hpair : ∀ a ∈ (Finset.univ : Finset I), ∀ b ∈ Finset.univ,
      a ≠ b → d+1 ≤ ((T a)ᶜ ∪ (T b)ᶜ).card+t := by
    intro a ha b hb hab
    exact bad_witness_pair_union_distance gamma w hinj Finset.univ C d t
      (by simpa using hsize) hC T u0 u1
      (fun i _ => hwC i) (fun i _ => hcompl i)
      (fun i _ => hwag i) (fun i _ => hno i) ha hb hab
  have hlow := triple_mass_lower_of_pair_union gamma w Finset.univ
    (fun i => (T i)ᶜ) (d+1) t hpair
    (fun a _ b _ c _ hab _ _ hnc =>
      Nat.succ_le_of_lt (error_union_gt_of_noncollinear gamma w hinj C d hC T u0 u1 hab
        (hwC a) (hwC b) (hwC c) (hwag a) (hwag b) (hwag c) hnc))
  simp only [Finset.card_univ] at hcol hlow
  have hpoint : ∀ a b c,
      (T a ∩ T b ∩ T c).card + ((T a)ᶜ ∪ (T b)ᶜ ∪ (T c)ᶜ).card =
        Fintype.card Coord := by
    intro a b c
    have he : ((T a)ᶜ ∪ (T b)ᶜ ∪ (T c)ᶜ)ᶜ = T a ∩ T b ∩ T c := by
      ext x
      simp [not_or]
    have hc := Finset.card_compl_add_card ((T a)ᶜ ∪ (T b)ᶜ ∪ (T c)ᶜ)
    rwa [he] at hc
  have hinter := sum_card_triple_inter_eq_sum_degree_cube T
  change (∑ a, ∑ b, ∑ c, (T a ∩ T b ∩ T c).card) =
    ∑ x, (agreementDegree T x)^3 at hinter
  have hmass : (∑ x, (agreementDegree T x)^3) +
      (∑ a, ∑ b, ∑ c, ((T a)ᶜ ∪ (T b)ᶜ ∪ (T c)ᶜ).card) =
        Fintype.card Coord * (Fintype.card I)^3 := by
    rw [← hinter]
    simp_rw [← Finset.sum_add_distrib, hpoint]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  have hdist := Nat.sub_add_cancel hDn
  have hsplit : (Fintype.card Coord-(d+1)) * (Fintype.card I)^3 +
      (d+1)*(Fintype.card I)^3 = Fintype.card Coord * (Fintype.card I)^3 := by
    rw [← Nat.add_mul, hdist]
  nlinarith [Nat.mul_le_mul_left t hcol]

end ProximityGap.IncidenceAnchorCubeUpper

#print axioms ProximityGap.IncidenceAnchorCubeUpper.canonical_agreement_cube_upper
