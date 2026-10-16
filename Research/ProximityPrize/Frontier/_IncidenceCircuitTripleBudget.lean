/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE.
Authors: Mikhail Izhutkin (mashingaan)
-/
import Research.ProximityPrize.Frontier._IncidenceCircuitShortening

/-!
# Triple-union budgets for full error circuits

A full relation excludes coordinates of error degree one. On five or six
errors this improves the sum of triple unions enough to contradict the
literal first-sponsor distance and error budgets.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace ProximityGap.IncidenceCircuitTripleBudget

open ProximityGap.IncidenceDependencyArithmetic
open ProximityGap.IncidenceCircuitShortening
open ProximityGap.IncidenceAnchorCubeUpper
open ProximityGap.IncidenceAffineLines

def distinctTriples (m : ℕ) : Finset (Fin m × Fin m × Fin m) :=
  Finset.univ.filter (fun p => p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2)

def booleanDegree {m : ℕ} (b : Fin m → Bool) : ℕ :=
  ∑ i, if b i then 1 else 0

def booleanTripleMass {m : ℕ} (b : Fin m → Bool) : ℕ :=
  ∑ p ∈ distinctTriples m, if b p.1 || b p.2.1 || b p.2.2 then 1 else 0

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
theorem five_boolean_circuit_budget :
    ∀ b : Fin 5 → Bool, booleanDegree b ≠ 1 →
      booleanTripleMass b ≤ 27 * booleanDegree b := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
theorem six_boolean_circuit_budget :
    ∀ b : Fin 6 → Bool, booleanDegree b ≠ 1 →
      booleanTripleMass b ≤ 48 * booleanDegree b := by decide

/-- Exact supports in a full relation cannot contain a singleton incidence. -/
theorem full_relation_degree_ne_one
    {F Coord : Type} [Field F] [Fintype Coord] [DecidableEq Coord]
    {m : ℕ} (e : Fin m → (Coord → F)) (E : Fin m → Finset Coord)
    (hE : ∀ i x, x ∈ E i ↔ e i x ≠ 0)
    (c : Fin m → F) (hc : ∀ i, c i ≠ 0) (hrel : (∑ i, c i • e i) = 0)
    (x : Coord) : (Finset.univ.filter (fun i => x ∈ E i)).card ≠ 1 := by
  classical
  have hs := full_relation_shared_support e E
    (fun i y hy => by simpa only [hE, not_not] using hy) c hc hrel
  intro hone
  let N := Finset.univ.filter (fun i => x ∈ E i)
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
  have hix : x ∈ E i := by
    have hm : i ∈ N := by
      change i ∈ Finset.univ.filter (fun i => x ∈ E i)
      rw [hi]
      simp
    exact (Finset.mem_filter.mp hm).2
  have hnot : x ∉ sharedSupport E := by
    intro hx
    obtain ⟨j, k, hjk, hj, hk⟩ : ∃ j k, j ≠ k ∧ x ∈ E j ∧ x ∈ E k := by
      simpa [sharedSupport] using hx
    have hji : j = i := by
      have hm : j ∈ Finset.univ.filter (fun i => x ∈ E i) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
      rw [hi] at hm
      exact Finset.mem_singleton.mp hm
    have hki : k = i := by
      have hm : k ∈ Finset.univ.filter (fun i => x ∈ E i) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
      rw [hi] at hm
      exact Finset.mem_singleton.mp hm
    exact hjk (hji.trans hki.symm)
  exact (hE i x).mp hix (hs i x hnot)

/-- Double counting transfers the finite Boolean certificate to actual errors. -/
theorem full_relation_triple_mass_bound
    {F Coord : Type} [Field F] [Fintype Coord] [DecidableEq Coord]
    {m : ℕ} (k : ℕ)
    (hbool : ∀ b : Fin m → Bool, booleanDegree b ≠ 1 →
      booleanTripleMass b ≤ k * booleanDegree b)
    (e : Fin m → (Coord → F)) (E : Fin m → Finset Coord)
    (hE : ∀ i x, x ∈ E i ↔ e i x ≠ 0)
    (c : Fin m → F) (hc : ∀ i, c i ≠ 0) (hrel : (∑ i, c i • e i) = 0) :
    (∑ p ∈ distinctTriples m, ((E p.1 ∪ E p.2.1) ∪ E p.2.2).card) ≤
      k * ∑ i, (E i).card := by
  classical
  have hpoint : ∀ x : Coord,
      (∑ p ∈ distinctTriples m,
        if x ∈ (E p.1 ∪ E p.2.1) ∪ E p.2.2 then 1 else 0) ≤
      k * ∑ i, if x ∈ E i then 1 else 0 := by
    intro x
    let b : Fin m → Bool := fun i => decide (x ∈ E i)
    have hd : booleanDegree b = (Finset.univ.filter (fun i => x ∈ E i)).card := by
      unfold booleanDegree
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : x ∈ E i
      · simp [b, hi]
      · simp [b, hi]
    have hn : booleanDegree b ≠ 1 := by
      rw [hd]
      exact full_relation_degree_ne_one e E hE c hc hrel x
    have hb := hbool b hn
    simpa [booleanTripleMass, booleanDegree, b, Finset.mem_union, or_assoc] using hb
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
  have hleft : (∑ x, ∑ p ∈ distinctTriples m,
      if x ∈ (E p.1 ∪ E p.2.1) ∪ E p.2.2 then 1 else 0) =
      ∑ p ∈ distinctTriples m, ((E p.1 ∪ E p.2.1) ∪ E p.2.2).card := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    let S := (E p.1 ∪ E p.2.1) ∪ E p.2.2
    have hf : Finset.univ.filter (fun x => x ∈ S) = S := by
      ext x
      simp
    change (∑ x, if x ∈ S then 1 else 0) = S.card
    rw [← Finset.card_filter, hf]
  have hright : (∑ x, k * ∑ i, if x ∈ E i then 1 else 0) =
      k * ∑ i, (E i).card := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp [Finset.sum_ite]
  rwa [hleft, hright] at hs

/-- A full-relation obstruction and independence of every deletion imply
independence of the whole finite family. -/
theorem independent_of_full_relation_and_deletions
    {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {n : ℕ} (e : Fin (n+1) → V)
    (hfull : ∀ c : Fin (n+1) → F, (∀ j, c j ≠ 0) → (∑ j, c j • e j) ≠ 0)
    (hdelete : ∀ k : Fin (n+1), LinearIndependent F (fun j : Fin n => e (k.succAbove j))) :
    LinearIndependent F e := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hrel i
  by_cases hc : ∀ j, c j ≠ 0
  · exact False.elim (hfull c hc hrel)
  push Not at hc
  obtain ⟨k, hk⟩ := hc
  have hr : (∑ j : Fin n, c (k.succAbove j) • e (k.succAbove j)) = 0 := by
    rw [Fin.sum_univ_succAbove _ k] at hrel
    simpa [hk] using hrel
  have hz := Fintype.linearIndependent_iff.mp (hdelete k)
    (fun j => c (k.succAbove j)) hr
  by_cases hik : i = k
  · simpa [hik] using hk
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hik
    exact hz j

/-- The finite circuit budget contradicts the canonical distance constraints. -/
theorem no_full_bad_error_relation_of_triple_budget
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
    (m k : ℕ) (hbool : ∀ b : Fin m → Bool, booleanDegree b ≠ 1 →
      booleanTripleMass b ≤ k * booleanDegree b)
    (hgap : k*m*221512374 < (distinctTriples m).card*536870913)
    (a : Fin m → I) (ha : Function.Injective a)
    (c : Fin m → F) (hc : ∀ j, c j ≠ 0) :
    (∑ j, c j • (u0 + gamma (a j) • u1 - w (a j))) ≠ 0 := by
  classical
  intro hrel
  let e : Fin m → (Coord → F) := fun j => u0 + gamma (a j) • u1 - w (a j)
  let E : Fin m → Finset Coord := fun j => Finset.univ.filter (fun x => e j x ≠ 0)
  have hE : ∀ j x, x ∈ E j ↔ e j x ≠ 0 := by
    intro j x
    simp [E]
  have hweight : ∀ j, (E j).card ≤ 221512374 := by
    intro j
    apply (Finset.card_le_card (show E j ⊆ (T (a j))ᶜ from ?_)).trans (hcompl (a j))
    intro x hx
    apply Finset.mem_compl.mpr
    intro hxT
    have he := hwag (a j) x hxT
    apply (hE j x).mp hx
    change u0 x + gamma (a j) * u1 x - w (a j) x = 0
    exact sub_eq_zero.mpr (by simpa only [smul_eq_mul] using he.symm)
  have hag : ∀ j, ∀ x ∈ (E j)ᶜ, w (a j) x = u0 x + gamma (a j) • u1 x := by
    intro j x hx
    have hz : e j x = 0 := by simpa [E] using hx
    change u0 x + gamma (a j) * u1 x - w (a j) x = 0 at hz
    simpa only [smul_eq_mul] using (sub_eq_zero.mp hz).symm
  have hlower : ∀ p ∈ distinctTriples m,
      536870913 ≤ ((E p.1 ∪ E p.2.1) ∪ E p.2.2).card := by
    intro p hp
    obtain ⟨hab, hac, hbc⟩ := (Finset.mem_filter.mp hp).2
    let b : Fin 3 → Fin m := ![p.1, p.2.1, p.2.2]
    have hb : Function.Injective b := by
      intro i j hij
      fin_cases i
      · fin_cases j
        · rfl
        · exact False.elim (hab (by simpa [b] using hij))
        · exact False.elim (hac (by simpa [b] using hij))
      · fin_cases j
        · exact False.elim (hab (by simpa [b] using hij.symm))
        · rfl
        · exact False.elim (hbc (by simpa [b] using hij))
      · fin_cases j
        · exact False.elim (hac (by simpa [b] using hij.symm))
        · exact False.elim (hbc (by simpa [b] using hij.symm))
        · rfl
    have hnc : ¬ CollinearTriple (fun j => gamma (a j)) (fun j => w (a j))
        p.1 p.2.1 p.2.2 := by
      rintro ⟨U, V, h0, h1, h2⟩
      apply no_collinear_triple_in_overbudget_family hlength gamma w hinj C T u0 u1
        hsize hC hwC hcompl hwag hno (a ∘ b) (ha.comp hb)
      refine ⟨U, V, ?_⟩
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    have hu := error_union_gt_of_noncollinear (fun j => gamma (a j))
      (fun j => w (a j)) (hinj.comp ha) C 536870912 hC (fun j => (E j)ᶜ)
      u0 u1 hab (hwC (a p.1)) (hwC (a p.2.1)) (hwC (a p.2.2))
      (hag p.1) (hag p.2.1) (hag p.2.2) hnc
    simpa only [Finset.compl_compl] using Nat.succ_le_of_lt hu
  have hl := Finset.sum_le_sum hlower
  have hu := full_relation_triple_mass_bound k hbool e E hE c hc hrel
  have hw := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hweight j)
  have hcard : (∑ j, (E j).card) ≤ m*221512374 := by simpa using hw
  have hlow : (distinctTriples m).card*536870913 ≤
      ∑ p ∈ distinctTriples m, ((E p.1 ∪ E p.2.1) ∪ E p.2.2).card := by
    simpa using hl
  have hupper := hu.trans (Nat.mul_le_mul_left k hcard)
  omega

theorem five_bad_errors_linearIndependent
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
    (a : Fin 5 → I) (ha : Function.Injective a) :
    LinearIndependent F (fun j => u0 + gamma (a j) • u1 - w (a j)) := by
  apply independent_of_full_relation_and_deletions
  · exact no_full_bad_error_relation_of_triple_budget hlength gamma w hinj C T u0 u1
      hsize hC hwC hcompl hwag hno 5 27 five_boolean_circuit_budget (by decide) a ha
  · intro k
    exact four_bad_errors_linearIndependent_in_overbudget_family hlength gamma w hinj
      C T u0 u1 hsize hC hwC hcompl hwag hno (fun j => a (k.succAbove j))
      (ha.comp Fin.succAbove_right_injective)

theorem six_bad_errors_linearIndependent
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
    LinearIndependent F (fun j => u0 + gamma (a j) • u1 - w (a j)) := by
  apply independent_of_full_relation_and_deletions
  · exact no_full_bad_error_relation_of_triple_budget hlength gamma w hinj C T u0 u1
      hsize hC hwC hcompl hwag hno 6 48 six_boolean_circuit_budget (by decide) a ha
  · intro k
    exact five_bad_errors_linearIndependent hlength gamma w hinj C T u0 u1
      hsize hC hwC hcompl hwag hno (fun j => a (k.succAbove j))
      (ha.comp Fin.succAbove_right_injective)

end ProximityGap.IncidenceCircuitTripleBudget

#print axioms ProximityGap.IncidenceCircuitTripleBudget.five_boolean_circuit_budget
#print axioms ProximityGap.IncidenceCircuitTripleBudget.six_boolean_circuit_budget
#print axioms ProximityGap.IncidenceCircuitTripleBudget.full_relation_degree_ne_one
#print axioms ProximityGap.IncidenceCircuitTripleBudget.full_relation_triple_mass_bound
#print axioms ProximityGap.IncidenceCircuitTripleBudget.independent_of_full_relation_and_deletions
#print axioms ProximityGap.IncidenceCircuitTripleBudget.no_full_bad_error_relation_of_triple_budget
#print axioms ProximityGap.IncidenceCircuitTripleBudget.five_bad_errors_linearIndependent
#print axioms ProximityGap.IncidenceCircuitTripleBudget.six_bad_errors_linearIndependent
