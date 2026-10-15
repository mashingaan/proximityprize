import Mathlib.Tactic

set_option autoImplicit false

namespace ProximityGap.IncidenceDependencyArithmetic

/-- Universal coordinate-count inequality for a minimal multi-line dependency. -/
theorem coordinate_count_bound (L a k : ℤ)
    (hL : 4 ≤ L) (ha : 1 ≤ a) (haL : a ≤ L)
    (hk : 0 ≤ k) (hka : k ≤ a) :
    2 * (3*L*(L-1)-3*(L-a)*(L-a-1)-k*(L-a)) ≤
      (5*L-7)*(3*a-k)+4*(if a=1 ∧ k=1 then 1 else 0) := by
  by_cases ha1 : a = 1
  · subst a
    by_cases hk1 : k = 1
    · subst k
      simp only [and_self, ↓reduceIte]
      nlinarith
    · have hk0 : k = 0 := by omega
      subst k
      norm_num
      nlinarith
  · have ha2 : 2 ≤ a := by omega
    have hfirst : 0 ≤ a*(a-2) := mul_nonneg (by omega) (by omega)
    have hsecond : 0 ≤ (3*L+2*a-7)*(a-k) :=
      mul_nonneg (by omega) (by omega)
    have hnot : ¬ (a=1 ∧ k=1) := by tauto
    simp only [if_neg hnot]
    nlinarith [hfirst, hsecond]

/-- Arithmetic transfer after codeword averaging and shared-support shortening.
The two structural inputs are explicit and are not proved by this declaration. -/
theorem dependency_necessary (L D t n E S : ℤ)
    (haverage : 6*L*(L-1)*D ≤ 3*L*(5*L-7)*t+4*E)
    (hshared : D+L-4 ≤ S) (hambient : E+S ≤ n) :
    (6*L*(L-1)+4)*D ≤ 3*L*(5*L-7)*t+4*(n-L+4) := by
  nlinarith

/-- Finite-coordinate ledger. Codeword-distance, error-budget and shortening
inputs remain explicit until the canonical witness construction is connected. -/
theorem dependency_from_coordinate_ledger {X : Type*} (U : Finset X)
    (L D t n E S : ℤ) (a k b : X → ℤ) (hL : 4 ≤ L)
    (hcoord : ∀ x ∈ U, 1 ≤ a x ∧ a x ≤ L ∧ 0 ≤ k x ∧ k x ≤ a x)
    (hcount : ∀ x ∈ U, b x ≤
      3*L*(L-1)-3*(L-a x)*(L-a x-1)-k x*(L-a x))
    (hdistance : 3*L*(L-1)*D ≤ ∑ x ∈ U, b x)
    (herrors : (∑ x ∈ U, (3*a x-k x)) ≤ 3*L*t)
    (hexclusive : (∑ x ∈ U, (if a x=1 ∧ k x=1 then (1 : ℤ) else 0)) ≤ E)
    (hshared : D+L-4 ≤ S) (hambient : E+S ≤ n) :
    (6*L*(L-1)+4)*D ≤ 3*L*(5*L-7)*t+4*(n-L+4) := by
  have hpoint : ∀ x ∈ U, 2*b x ≤
      (5*L-7)*(3*a x-k x)+4*(if a x=1 ∧ k x=1 then (1 : ℤ) else 0) := by
    intro x hx
    obtain ⟨ha, haL, hk, hka⟩ := hcoord x hx
    have hc := coordinate_count_bound L (a x) (k x) hL ha haL hk hka
    have hb := hcount x hx
    nlinarith
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have herrors' := mul_le_mul_of_nonneg_left herrors (show 0 ≤ 5*L-7 by omega)
  have havg : 6*L*(L-1)*D ≤ 3*L*(5*L-7)*t+4*E := by
    nlinarith [hdistance, herrors', hexclusive]
  exact dependency_necessary L D t n E S havg hshared hambient

/-- Literal integer exclusion, conditional on the necessary inequality above. -/
theorem literal_dependency_excluded (L : ℤ) (hlo : 4 ≤ L) (hhi : L ≤ 12) :
    ¬ ((6*L*(L-1)+4)*536870913 ≤
      3*L*(5*L-7)*221512373+4*(1073741824-L+4)) := by
  interval_cases L
  all_goals norm_num

end ProximityGap.IncidenceDependencyArithmetic

#print axioms ProximityGap.IncidenceDependencyArithmetic.coordinate_count_bound
#print axioms ProximityGap.IncidenceDependencyArithmetic.dependency_necessary
#print axioms ProximityGap.IncidenceDependencyArithmetic.dependency_from_coordinate_ledger
#print axioms ProximityGap.IncidenceDependencyArithmetic.literal_dependency_excluded
