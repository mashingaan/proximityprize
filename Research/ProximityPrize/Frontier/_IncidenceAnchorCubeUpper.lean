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
open ProximityGap.IncidenceDependencyArithmetic

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

/-- At the literal first-sponsor radius a three-head anchor cannot have an
external bad-witness family of size at least n-2. All moment bounds are derived. -/
theorem no_large_external_family_of_triple_anchor
    {F I Coord : Type} [Field F] [Fintype I] [DecidableEq I]
    [Fintype Coord] [DecidableEq Coord]
    (hlength : Fintype.card Coord = 1073741824)
    (gamma : I → F) (w : I → (Coord → F)) (hinj : Function.Injective gamma)
    (C : Submodule F (Coord → F)) (T : I → Finset Coord)
    (u0 u1 U V : Coord → F) (a : Fin 3 → F) (ha : Function.Injective a)
    (hheads : ∀ j, U + a j • V ∈ C)
    (hanchor : ∀ j, (ProximityGap.IncidenceDependencyArithmetic.affineHeadErrors
      u0 u1 U V (a j)).card ≤ 221512374)
    (hsize : 1073741822 ≤ Fintype.card I)
    (hC : ∀ z ∈ C, (∃ B : Finset Coord, B.card ≤ 536870912 ∧
      ∀ x ∉ B, z x = 0) → z = 0)
    (hwC : ∀ i, w i ∈ C) (hcompl : ∀ i, (T i)ᶜ.card ≤ 221512374)
    (hwag : ∀ i, ∀ x ∈ T i, w i x = u0 x + gamma i • u1 x)
    (hno : ∀ i, ¬ ∃ f0 ∈ C, ∃ f1 ∈ C,
      ∀ x ∈ T i, f0 x = u0 x ∧ f1 x = u1 x)
    (houtside : ∀ i, w i ≠ U + gamma i • V) : False := by
  classical
  obtain ⟨hU, hV⟩ := affine_parameters_mem_code C U V (a 0) (a 1)
    (fun h => (by decide : (0 : Fin 3) ≠ 1) (ha h)) (hheads 0) (hheads 1)
  let Q := ProximityGap.IncidenceDependencyArithmetic.affineErrorSupport u0 u1 U V
  have hbudget := ProximityGap.IncidenceDependencyArithmetic.three_head_support_budget
    u0 u1 U V a ha 221512374 hanchor
  have hq : Q.card ≤ 332268561 := by
    change 2*Q.card ≤ _ at hbudget
    omega
  have hdistance : ∀ z ∈ C, ∀ B : Finset Coord, B.card < 536870913 →
      (∀ x ∉ B, z x = 0) → z = 0 := by
    intro z hz B hB hs
    exact hC z hz ⟨B, by omega, hs⟩
  have hinside : ∀ i, 315358539 ≤ (T i ∩ Q).card := by
    intro i
    have ho := external_head_anchor_overlap C u0 u1 U V (w i) (gamma i)
      536870913 221512374 (T i)ᶜ hU hV (hwC i) (houtside i)
      (fun x hx => by simpa using hwag i x (by simpa using hx))
      (hcompl i) hdistance
    change 536870913 + (Q ∩ (T i)ᶜ).card ≤ Q.card + 221512374 at ho
    have hp := Finset.card_inter_add_card_sdiff Q (T i)
    rw [Finset.sdiff_eq_inter_compl, Finset.inter_comm Q (T i)] at hp
    omega
  have htotal : ∀ i, 315358539+536870911 ≤ (T i).card := by
    intro i
    have hc := Finset.card_compl_add_card (T i)
    rw [hlength] at hc
    have he := hcompl i
    omega
  let s : ℝ := Fintype.card I
  let r : ℝ := 315358539 / 332268561
  let v : ℝ := 536870911 / 741473263
  have hs : 0 ≤ s := Nat.cast_nonneg _
  have hv : 0 ≤ s*v := mul_nonneg hs (by norm_num [v])
  have horder : s*v ≤ s*r := mul_le_mul_of_nonneg_left (by norm_num [r, v]) hs
  have hmu : (332268561 : ℝ)*(s*r) = (Fintype.card I : ℝ)*315358539 := by
    dsimp [s, r]
    ring
  have hnu : ((Fintype.card Coord : ℝ)-332268561)*(s*v) =
      (Fintype.card I : ℝ)*536870911 := by
    rw [hlength]
    dsimp [s, v]
    ring
  have hlo := agreement_cube_lower_uniform_of_counts T Q 315358539 536870911
    332268561 (s*r) (s*v) hinside htotal (by exact_mod_cast hq) hmu hnu hv horder
  rw [hlength] at hlo
  norm_num only [Nat.cast_ofNat] at hlo
  have hnormal : (332268561 : ℝ)*(s*r)^3 +
      ((1073741824 : ℝ)-332268561)*(s*v)^3 =
      (332268561*r^3+741473263*v^3)*s^3 := by ring
  rw [hnormal] at hlo
  have hgain : (536870912 : ℝ) ≤ 332268561*r^3+741473263*v^3 := by
    norm_num [r, v]
  have hlow := (mul_le_mul_of_nonneg_right hgain (pow_nonneg hs 3)).trans hlo
  have hu := canonical_agreement_cube_upper gamma w hinj C 536870912 221512374
    (by omega) (by norm_num) (by omega) hC T u0 u1 hwC hcompl hwag hno
  rw [hlength] at hu
  norm_num at hu
  have hupper : (∑ x, (agreementDegree T x : ℝ)^3) ≤
      536870911*s^3 + 886049496*s^2 + 536870913*s := by exact_mod_cast hu
  have hslarge : (1073741822 : ℝ) ≤ s := by exact_mod_cast hsize
  have hspos : 0 < s := by linarith
  have hp : (886049497 : ℝ)*s ≤ s^2 := by
    have he := mul_le_mul_of_nonneg_right (show (886049497 : ℝ) ≤ s by linarith) hs
    nlinarith
  have hgap : 886049496*s + 536870913 < s^2 := by nlinarith
  have hgapS := mul_lt_mul_of_pos_right hgap hspos
  nlinarith

end ProximityGap.IncidenceAnchorCubeUpper

#print axioms ProximityGap.IncidenceAnchorCubeUpper.canonical_agreement_cube_upper
#print axioms ProximityGap.IncidenceAnchorCubeUpper.no_large_external_family_of_triple_anchor
