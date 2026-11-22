import ChippingSupercondensation.Background
import ChippingSupercondensation.Coalescence

/-!
# Births of large piles

Adjusting the empty-window test on an empty mask makes a first large pile cost
nothing (`stationary_twoLargePilesProbability_le_competingBirthDamage`). A birth
between consecutive marks erases the product of its distances to them
(`competingBirthDamage_eq_gap_product`). At a selected macroscopic cutoff, chip
births within `R` sites of an existing mark are negligible when
`R² (R + 1) / N → 0`. The remaining whole-pile and distant chip births appear in
`stationary_twoLargePilesProbability_le_wholeAndDistantChipBirthDamage`; their
rates are not yet bounded.
-/

namespace Chipping

open Filter
open scoped BigOperators Topology

noncomputable section

private theorem emptyMaskWindowPotential_shift {L : ℕ} [NeZero L]
    (s : Fin L → Bool) (d : Fin L) :
    emptyMaskWindowPotential (fun j => s (j + d)) = emptyMaskWindowPotential s := by
  have hmass (r : ℕ) (j : Fin L) :
      maskWindowMass r (fun t => s (t + d)) j = maskWindowMass r s (j + d) := by
    unfold maskWindowMass
    apply Finset.sum_congr rfl
    intro t _
    congr 3
    abel_nf
  unfold emptyMaskWindowPotential
  apply Finset.sum_congr rfl
  intro r _
  unfold emptyMaskWindowCount emptyMaskWindowAt
  simp_rw [hmass]
  exact Equiv.sum_comp (Equiv.addRight d) (emptyMaskWindowAt (r + 1) s)

private theorem emptyMaskWindowPotential_singleton_eq {L : ℕ} [NeZero L] (i : Fin L) :
    emptyMaskWindowPotential (insertMask (fun _ : Fin L => false) i) =
      emptyMaskWindowPotential (insertMask (fun _ : Fin L => false) 0) := by
  let s := insertMask (fun _ : Fin L => false) i
  have hshift : (fun j => s (j + i)) = insertMask (fun _ : Fin L => false) 0 := by
    funext j
    have hiff : j + i = i ↔ j = 0 := by
      constructor
      · intro h
        exact add_right_cancel (h.trans (zero_add i).symm)
      · intro h
        simp [h]
    simp [s, insertMask, hiff]
  have h := emptyMaskWindowPotential_shift s i
  rw [hshift] at h
  exact h.symm

/-- A mask with no marked site. -/
def maskIsEmpty {L : ℕ} (s : Fin L → Bool) : Prop := ∀ j, s j = false

instance maskIsEmptyDecidable {L : ℕ} (s : Fin L → Bool) : Decidable (maskIsEmpty s) := by
  unfold maskIsEmpty
  infer_instance

private theorem mask_not_empty_iff {L : ℕ} {s : Fin L → Bool} :
    ¬maskIsEmpty s ↔ ∃ j, s j = true := by
  classical
  constructor
  · intro h
    by_contra h'
    apply h
    intro j
    cases hj : s j
    · rfl
    · exact (h' ⟨j, hj⟩).elim
  · rintro ⟨j, hj⟩ hs
    rw [hs j] at hj
    contradiction

private theorem maskIsEmpty_coalesce_iff {L : ℕ} (hL : 3 ≤ L) (s : Fin L → Bool) (i : Fin L) :
    maskIsEmpty (coalesceMask s i) ↔ maskIsEmpty s := by
  constructor
  · intro h
    classical
    by_contra hs
    obtain ⟨j, hj⟩ := mask_not_empty_iff.mp hs
    by_cases hji : j = i
    · subst j
      have hright : coalesceMask s i (right i) = true := by
        simp [coalesceMask, right_ne_self hL i, hj]
      rw [h (right i)] at hright
      contradiction
    · have hj' : coalesceMask s i j = true := by
        unfold coalesceMask
        rw [if_neg hji]
        split_ifs <;> simp [hj]
      rw [h j] at hj'
      contradiction
  · intro h
    rw [coalesceMask_eq_self_of_false s i (h i)]
    exact h

/-- The empty-window test with its value on an empty mask set equal to its
value on a singleton. A first mark does not change this test. -/
def competitiveEmptyWindowPotential {L : ℕ} [NeZero L] (s : Fin L → Bool) : ℝ := by
  classical
  exact if maskIsEmpty s then emptyMaskWindowPotential (insertMask (fun _ => false) (0 : Fin L))
    else emptyMaskWindowPotential s

theorem competitiveEmptyWindowPotential_antitone {L : ℕ} [NeZero L] {s t : Fin L → Bool}
    (h : ∀ j, s j = true → t j = true) : competitiveEmptyWindowPotential t ≤ competitiveEmptyWindowPotential s := by
  classical
  unfold competitiveEmptyWindowPotential
  by_cases hs : maskIsEmpty s
  · by_cases ht : maskIsEmpty t
    · rw [if_pos hs, if_pos ht]
    · rw [if_pos hs, if_neg ht]
      obtain ⟨j, hj⟩ := mask_not_empty_iff.mp ht
      rw [← emptyMaskWindowPotential_singleton_eq j]
      apply emptyMaskWindowPotential_antitone
      intro i hi
      by_cases hi' : i = j
      · simpa [hi'] using hj
      · simp [insertMask, hi'] at hi
  · have ht : ¬maskIsEmpty t := by
      obtain ⟨j, hj⟩ := mask_not_empty_iff.mp hs
      exact mask_not_empty_iff.mpr ⟨j, h j hj⟩
    rw [if_neg hs, if_neg ht]
    exact emptyMaskWindowPotential_antitone h

private theorem maskCoalescenceGenerator_competitive_empty_eq {L : ℕ} [NeZero L]
    (hL : 3 ≤ L) (s : Fin L → Bool) :
    maskCoalescenceGenerator competitiveEmptyWindowPotential s =
      maskCoalescenceGenerator emptyMaskWindowPotential s := by
  unfold maskCoalescenceGenerator
  apply Finset.sum_congr rfl
  intro i _
  have h := maskIsEmpty_coalesce_iff hL s i
  by_cases hs : maskIsEmpty s
  · rw [coalesceMask_eq_self_of_false s i (hs i)]
    simp
  · have h' := fun hp => hs (h.mp hp)
    simp only [competitiveEmptyWindowPotential, if_neg hs, if_neg h']

/-- Inserting the first large pile carries no birth damage for the adjusted test. -/
theorem competitiveEmptyWindowPotential_firstBirth_damage_eq_zero {L : ℕ} [NeZero L]
    (s : Fin L → Bool) (i : Fin L) (hs : maskIsEmpty s) :
    maskBirthDamage competitiveEmptyWindowPotential s i = 0 := by
  have ht : ¬maskIsEmpty (insertMask s i) := by
    intro h
    have hi := h i
    simp [insertMask] at hi
  have hfun : s = fun _ => false := funext hs
  unfold maskBirthDamage competitiveEmptyWindowPotential
  rw [if_pos hs, if_neg ht, hfun, emptyMaskWindowPotential_singleton_eq i, sub_self]

private theorem competitiveBirthDamageRate_eq_zero_of_empty {L N : ℕ} [NeZero L]
    (w : ℝ) (k : ℕ) (x : State L N) (hs : maskIsEmpty (largePileMask k x)) :
    maskBirthDamageRate competitiveEmptyWindowPotential w k x = 0 := by
  unfold maskBirthDamageRate
  simp_rw [competitiveEmptyWindowPotential_firstBirth_damage_eq_zero _ _ hs, mul_zero]
  simp

/-- The probability of two large piles anywhere on the ring is controlled
only by births that occur while another large pile is present. Each such
birth is weighted by the empty windows it erases. -/
theorem stationary_twoLargePilesProbability_le_competingBirthDamage {L N : ℕ} [NeZero L]
    (hL : 3 ≤ L) {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (k : ℕ) (hk : 1 ≤ k) :
    2 * twoLargePilesProbability μ k ≤
      ∑ x, if maskIsEmpty (largePileMask k x) then 0 else
        μ.weight x * maskBirthDamageRate competitiveEmptyWindowPotential w k x := by
  classical
  calc
    _ = ∑ x, μ.weight x * (if 2 ≤ maskCount (largePileMask k x) then 2 else 0) := by
      unfold twoLargePilesProbability
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> ring
    _ ≤ ∑ x, μ.weight x * maskCoalescenceGenerator competitiveEmptyWindowPotential (largePileMask k x) := by
      simp_rw [maskCoalescenceGenerator_competitive_empty_eq hL]
      exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
        (maskCoalescenceGenerator_emptyPotential_ge hL _) (μ.nonneg x))
    _ ≤ ∑ x, μ.weight x * maskBirthDamageRate competitiveEmptyWindowPotential w k x :=
      stationary_maskCoalescence_drift_le_birthDamage hL hw μ k hk competitiveEmptyWindowPotential
        (fun _ _ h => competitiveEmptyWindowPotential_antitone h)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs with hx
      · rw [competitiveBirthDamageRate_eq_zero_of_empty w k x hx, mul_zero]
      · rfl

private theorem maskWindowMass_insert_zero_iff {L : ℕ} [NeZero L]
    (s : Fin L → Bool) (r : ℕ) (i j : Fin L) :
    maskWindowMass r (insertMask s i) j = 0 ↔ maskWindowMass r s j = 0 ∧
      ¬∃ t : Fin r, j - (t.val : Fin L) = i := by
  unfold maskWindowMass
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity),
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)]
  simp only [Nat.cast_eq_zero]
  constructor
  · intro h
    constructor
    · intro t ht
      have ht' := h t ht
      by_cases hi : j - (t : Fin L) = i
      · simp [insertMask, hi, bitMass] at ht'
      · simpa only [insertMask, if_neg hi] using ht'
    · rintro ⟨t, hi⟩
      have ht' := h t.val (Finset.mem_range.mpr t.isLt)
      simp [insertMask, hi, bitMass] at ht'
  · rintro ⟨hzero, hnot⟩ t ht
    have hi : j - (t : Fin L) ≠ i := fun h => hnot ⟨⟨t, Finset.mem_range.mp ht⟩, h⟩
    simpa only [insertMask, if_neg hi] using hzero t ht

/-- With a large pile already present, the birth weight counts exactly the
proper empty windows that contain the new large pile's location. -/
theorem competingBirthDamage_eq_emptyContaining_count {L : ℕ} [NeZero L]
    (s : Fin L → Bool) (i : Fin L) (hs : ¬maskIsEmpty s) :
    maskBirthDamage competitiveEmptyWindowPotential s i =
      ∑ r ∈ Finset.range (L - 1), ∑ j, if maskWindowMass (r + 1) s j = 0 ∧
        (∃ t : Fin (r + 1), j - (t.val : Fin L) = i) then 1 else 0 := by
  classical
  have ht : ¬maskIsEmpty (insertMask s i) := by
    intro h
    have hi := h i
    simp [insertMask] at hi
  unfold maskBirthDamage competitiveEmptyWindowPotential
  rw [if_neg hs, if_neg ht]
  unfold emptyMaskWindowPotential emptyMaskWindowCount
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold emptyMaskWindowAt
  simp only [maskWindowMass_insert_zero_iff]
  by_cases hz : maskWindowMass (r + 1) s j = 0 <;>
    by_cases hcontains : ∃ t : Fin (r + 1), j - (t.val : Fin L) = i <;>
    simp [hz, hcontains]

private theorem maskWindowMass_zero_iff_unmarked {L : ℕ} [NeZero L]
    (s : Fin L → Bool) (r : ℕ) (j : Fin L) :
    maskWindowMass r s j = 0 ↔ ∀ t < r, s (j - (t : Fin L)) = false := by
  unfold maskWindowMass
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)]
  simp [bitMass]

private theorem emptyContaining_iff_in_gap {L : ℕ} [NeZero L]
    (s : Fin L → Bool) (i v : Fin L) (p q r : ℕ) (hr : r < L)
    (hp : s (i - (p : Fin L)) = true) (hq : s (i + (q : Fin L)) = true)
    (hleft : ∀ u < p, s (i - (u : Fin L)) = false)
    (hright : ∀ u < q, s (i + (u : Fin L)) = false) :
    (maskWindowMass (r + 1) s (i + v) = 0 ∧
      ∃ t : Fin (r + 1), i + v - (t.val : Fin L) = i) ↔
      v.val < q ∧ v.val ≤ r ∧ r < v.val + p := by
  rw [maskWindowMass_zero_iff_unmarked]
  constructor
  · rintro ⟨hz, t, ht⟩
    have he : v = (t.val : Fin L) := add_left_cancel (sub_eq_iff_eq_add.mp ht)
    have htL : t.val < L := by have := t.isLt; omega
    have hv := congrArg Fin.val he
    rw [Fin.val_natCast, Nat.mod_eq_of_lt htL] at hv
    have hvr : v.val ≤ r := by have := t.isLt; omega
    refine ⟨?_, hvr, ?_⟩
    · by_contra! h
      have hzero := hz (v.val - q) (by omega)
      rw [Nat.cast_sub h, Fin.cast_val_eq_self] at hzero
      have heq : i + v - (v - (q : Fin L)) = i + (q : Fin L) := by abel
      simp [heq, hq] at hzero
    · by_contra! h
      have hzero := hz (v.val + p) (by omega)
      rw [Nat.cast_add, Fin.cast_val_eq_self] at hzero
      have heq : i + v - (v + (p : Fin L)) = i - (p : Fin L) := by abel
      simp [heq, hp] at hzero
  · rintro ⟨hvq, hvr, hrp⟩
    refine ⟨?_, ⟨⟨v.val, by omega⟩, by simp⟩⟩
    intro t ht
    by_cases h : t ≤ v.val
    · have hz := hright (v.val - t) (by omega)
      rw [Nat.cast_sub h, Fin.cast_val_eq_self] at hz
      simpa only [add_sub_assoc] using hz
    · have hz := hleft (t - v.val) (by omega)
      rw [Nat.cast_sub (by omega : v.val ≤ t), Fin.cast_val_eq_self] at hz
      have heq : i + v - (t : Fin L) = i - ((t : Fin L) - v) := by abel
      rwa [heq]

/-- A competing birth in the gap between two consecutive marks erases exactly
the product of its distances to those marks. On a ring with just one mark,
the same mark bounds the gap from both sides. -/
theorem competingBirthDamage_eq_gap_product {L : ℕ} [NeZero L]
    (s : Fin L → Bool) (i : Fin L) (p q : ℕ) (hgap : p + q ≤ L)
    (hp : s (i - (p : Fin L)) = true) (hq : s (i + (q : Fin L)) = true)
    (hleft : ∀ u < p, s (i - (u : Fin L)) = false)
    (hright : ∀ u < q, s (i + (u : Fin L)) = false) :
    maskBirthDamage competitiveEmptyWindowPotential s i = (p : ℝ) * (q : ℝ) := by
  classical
  rw [competingBirthDamage_eq_emptyContaining_count s i (mask_not_empty_iff.mpr ⟨_, hp⟩)]
  have hlen (r : ℕ) (hr : r < L - 1) :
      (∑ j, if maskWindowMass (r + 1) s j = 0 ∧
        (∃ t : Fin (r + 1), j - (t.val : Fin L) = i) then (1 : ℝ) else 0) =
      ∑ v : Fin L, if v.val < q ∧ v.val ≤ r ∧ r < v.val + p then (1 : ℝ) else 0 := by
    rw [← Equiv.sum_comp (Equiv.addLeft i)]
    apply Finset.sum_congr rfl
    intro v _
    change (if maskWindowMass (r + 1) s (i + v) = 0 ∧
      (∃ t : Fin (r + 1), i + v - (t.val : Fin L) = i) then _ else _) = _
    simp only [emptyContaining_iff_in_gap s i v p q r (by omega) hp hq hleft hright]
  rw [Finset.sum_congr rfl (fun r hr => hlen r (Finset.mem_range.mp hr)), Finset.sum_comm]
  have hcount (v : ℕ) :
      (∑ r ∈ Finset.range (L - 1), if v < q ∧ v ≤ r ∧ r < v + p then (1 : ℝ) else 0) =
      if v < q then (p : ℝ) else 0 := by
    by_cases hv : v < q
    · simp only [hv, true_and, if_true]
      rw [← Finset.sum_filter]
      have heq : (Finset.range (L - 1)).filter (fun r => v ≤ r ∧ r < v + p) =
          Finset.Ico v (v + p) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      simp [heq, Nat.card_Ico]
    · simp [hv]
  simp_rw [hcount]
  rw [Fin.sum_univ_eq_sum_range (fun v => if v < q then (p : ℝ) else 0), ← Finset.sum_filter]
  have heq : (Finset.range L).filter (fun v => v < q) = Finset.range q := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  simp [heq, nsmul_eq_mul, mul_comm]

private theorem exists_bracketing_marks {L : ℕ} [NeZero L] (s : Fin L → Bool)
    (i : Fin L) (hs : ¬maskIsEmpty s) :
    ∃ p q : ℕ, p + q ≤ L ∧ s (i - (p : Fin L)) = true ∧ s (i + (q : Fin L)) = true ∧
      (∀ u < p, s (i - (u : Fin L)) = false) ∧ (∀ u < q, s (i + (u : Fin L)) = false) := by
  obtain ⟨j, hj⟩ := mask_not_empty_iff.mp hs
  have hb : ∃ n : ℕ, s (i - (n : Fin L)) = true :=
    ⟨(i - j).val, by simpa only [Fin.cast_val_eq_self, sub_sub_cancel] using hj⟩
  have hf : ∃ n : ℕ, s (i + (n : Fin L)) = true :=
    ⟨(j - i).val, by simpa only [Fin.cast_val_eq_self, add_sub_cancel] using hj⟩
  let p := Nat.find hb
  let q := Nat.find hf
  have hq : s (i + (q : Fin L)) = true := Nat.find_spec hf
  have hqL : q ≤ L := (Nat.find_min' hf (show s (i + ((j - i).val : Fin L)) = true by
    simpa only [Fin.cast_val_eq_self, add_sub_cancel] using hj)).trans (j - i).isLt.le
  have hwrap : s (i - ((L - q : ℕ) : Fin L)) = true := by
    simpa [Nat.cast_sub hqL, Fin.natCast_self] using hq
  have hpL : p ≤ L - q := Nat.find_min' hb hwrap
  exact ⟨p, q, by omega, Nat.find_spec hb, hq,
    fun u hu => Bool.eq_false_iff.mpr (Nat.find_min hb hu),
    fun u hu => Bool.eq_false_iff.mpr (Nat.find_min hf hu)⟩

/-- A birth within `d` steps of an existing mark in either direction erases at
most `d * (L - 1)` proper empty windows. -/
theorem competingBirthDamage_le_of_near_mark {L : ℕ} [NeZero L]
    (s : Fin L → Bool) (i : Fin L) (d : ℕ)
    (hm : s (i - (d : Fin L)) = true ∨ s (i + (d : Fin L)) = true) :
    maskBirthDamage competitiveEmptyWindowPotential s i ≤ (d : ℝ) * ((L - 1 : ℕ) : ℝ) := by
  have hs : ¬maskIsEmpty s := by
    rcases hm with h | h <;> exact mask_not_empty_iff.mpr ⟨_, h⟩
  obtain ⟨p, q, hgap, hp, hq, hleft, hright⟩ := exists_bracketing_marks s i hs
  rw [competingBirthDamage_eq_gap_product s i p q hgap hp hq hleft hright]
  by_cases hp0 : p = 0
  · rw [hp0, Nat.cast_zero, zero_mul]
    positivity
  by_cases hq0 : q = 0
  · rw [hq0, Nat.cast_zero, mul_zero]
    positivity
  rcases hm with h | h
  · have hpd : p ≤ d := by
      by_contra! hd
      rw [hleft d hd] at h
      contradiction
    exact_mod_cast Nat.mul_le_mul hpd (show q ≤ L - 1 by omega)
  · have hqd : q ≤ d := by
      by_contra! hd
      rw [hright d hd] at h
      contradiction
    rw [mul_comm]
    exact_mod_cast Nat.mul_le_mul hqd (show p ≤ L - 1 by omega)

/-- A birth next to an existing mark can erase at most one empty window of
each length. Its weight is at most `L - 1`. -/
theorem competingBirthDamage_le_of_marked_predecessor {L : ℕ} [NeZero L]
    (s : Fin L → Bool) (i : Fin L) (hmark : s (i - 1) = true) :
    maskBirthDamage competitiveEmptyWindowPotential s i ≤ ((L - 1 : ℕ) : ℝ) := by
  simpa using competingBirthDamage_le_of_near_mark s i 1 (Or.inl (by simpa using hmark))

private def isNearbyChipBirth {L N : ℕ} [NeZero L] (k R : ℕ)
    (x : State L N) (i : Fin L) : Prop :=
  1 ≤ occ x i ∧ occ x (right i) = k ∧ ∃ r : Fin R,
    k < occ x (right i - ((r.val + 1 : ℕ) : Fin L)) ∨
    k < occ x (right i + ((r.val + 1 : ℕ) : Fin L))

private def nearbyChipBirthDamageAt {L N : ℕ} [NeZero L] (k R : ℕ)
    (x : State L N) (i : Fin L) : ℝ := by
  classical
  exact if isNearbyChipBirth k R x i then
    maskBirthDamage competitiveEmptyWindowPotential (largePileMask k x) (right i) else 0

/-- The stationary chip-birth contribution to the empty-window bound from
destinations within `R` steps of a pre-existing large pile, in either direction.
A birth with several nearby marks is counted once. -/
def meanNearbyChipBirthDamage {L N : ℕ} [NeZero L] {w : ℝ}
    (μ : StationaryLaw L N w) (k R : ℕ) : ℝ :=
  ∑ x, μ.weight x * (w * ∑ i, nearbyChipBirthDamageAt k R x i)

private theorem nearbyChipBirthDamageAt_le {L N : ℕ} [NeZero L]
    (k R : ℕ) (x : State L N) (i : Fin L) :
    nearbyChipBirthDamageAt k R x i ≤
      ((R : ℝ) * (L : ℝ)) * (if occ x (right i) = k then 1 else 0) := by
  classical
  unfold nearbyChipBirthDamageAt
  split_ifs with h hk hk
  · obtain ⟨_, _, r, hr⟩ := h
    have hm : largePileMask k x (right i - ((r.val + 1 : ℕ) : Fin L)) = true ∨
        largePileMask k x (right i + ((r.val + 1 : ℕ) : Fin L)) = true := by
      simpa only [largePileMask, decide_eq_true_eq] using hr
    rw [mul_one]
    exact (competingBirthDamage_le_of_near_mark _ _ _ hm).trans
      (by exact_mod_cast Nat.mul_le_mul r.isLt (Nat.sub_le L 1))
  · exact (hk h.2.1).elim
  · positivity
  · simp

private theorem nearbyChipBirthDamage_band_le {L N : ℕ} [NeZero L]
    (a b R : ℕ) (ha : 0 < a) (x : State L N) :
    (∑ k ∈ Finset.Icc a b, ∑ i, nearbyChipBirthDamageAt k R x i) ≤
      (R : ℝ) * (L : ℝ) * ((N : ℝ) / (a : ℝ)) := by
  have hmass : (∑ i, (occ x (right i) : ℝ)) = (N : ℝ) := by
    simp only [right_eq_add_one]
    exact (Equiv.sum_comp (Equiv.addRight (1 : Fin L)) (fun i => (occ x i : ℝ))).trans
      (by exact_mod_cast x.property)
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i, (R : ℝ) * (L : ℝ) * ((occ x (right i) : ℝ) / (a : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      refine (Finset.sum_le_sum (fun k _ => nearbyChipBirthDamageAt_le k R x i)).trans ?_
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Nat.add_zero] using sum_threshold_hits_le a b (occ x (right i)) 0 ha
    _ = _ := by simp only [← Finset.mul_sum, div_eq_mul_inv, ← Finset.sum_mul, hmass]

/-- Across a band of positive cutoffs, a receiving site can have exactly the
cutoff mass only once. A nearby chip birth also requires a nearby pair already
at the lower edge of the band. -/
theorem stationary_nearbyChipBirthDamage_band_le {L N : ℕ} [NeZero L] {w : ℝ}
    (hw : 0 ≤ w) (μ : StationaryLaw L N w) (a b R : ℕ) (ha : 0 < a) :
    (∑ k ∈ Finset.Icc a b, meanNearbyChipBirthDamage μ k R) ≤
      w * ((R : ℝ) * (L : ℝ) * ((N : ℝ) / (a : ℝ))) * nearbyThresholdPairProbability μ a R := by
  classical
  unfold meanNearbyChipBirthDamage nearbyThresholdPairProbability
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  simp_rw [← Finset.mul_sum]
  split_ifs with hpair
  · rw [mul_comm _ (μ.weight x)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (nearbyChipBirthDamage_band_le a b R ha x) hw) (μ.nonneg x)
  · have hzero (k : ℕ) (hk : k ∈ Finset.Icc a b) (i : Fin L) :
        nearbyChipBirthDamageAt k R x i = 0 := by
      apply if_neg
      rintro ⟨_, hdest, r, hm | hm⟩ <;> apply hpair
      · refine ⟨r.val, Finset.mem_range.mpr r.isLt, _, ((Finset.mem_Icc.mp hk).1.trans hm.le), ?_⟩
        simpa only [sub_add_cancel, hdest] using (Finset.mem_Icc.mp hk).1
      · exact ⟨r.val, Finset.mem_range.mpr r.isLt, right i, hdest ▸ (Finset.mem_Icc.mp hk).1,
          (Finset.mem_Icc.mp hk).1.trans hm.le⟩
    rw [Finset.sum_eq_zero (fun k hk => Finset.sum_eq_zero (fun i _ => hzero k hk i))]
    simp

/-- One cutoff in the band has a nearby chip-birth error bounded by the
stationary probability of a nearby pair times the displayed prefactor. -/
theorem exists_threshold_nearbyChipBirthDamage_le {L N : ℕ} [NeZero L] {w : ℝ}
    (hw : 0 ≤ w) (μ : StationaryLaw L N w) (a b R : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ k ∈ Finset.Icc a b, meanNearbyChipBirthDamage μ k R ≤
      (w * ((R : ℝ) * (L : ℝ) * ((N : ℝ) / (a : ℝ))) /
        ((b + 1 - a : ℕ) : ℝ)) * nearbyThresholdPairProbability μ a R := by
  apply Finset.exists_le_of_sum_le ⟨a, Finset.mem_Icc.mpr ⟨le_rfl, hab⟩⟩
  have hc : ((b + 1 - a : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show b + 1 - a ≠ 0 by omega)
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, ← mul_assoc, mul_comm _ (_ / _),
    div_mul_cancel₀ _ hc]
  exact stationary_nearbyChipBirthDamage_band_le hw μ a b R ha

private theorem competitiveBirthDamage_nonneg {L : ℕ} [NeZero L]
    (s : Fin L → Bool) (j : Fin L) : 0 ≤ maskBirthDamage competitiveEmptyWindowPotential s j := by
  apply sub_nonneg.mpr
  apply competitiveEmptyWindowPotential_antitone
  intro i hi
  by_cases h : i = j <;> simp [insertMask, h, hi]

private theorem meanNearbyChipBirthDamage_nonneg {L N : ℕ} [NeZero L] {w : ℝ}
    (hw : 0 ≤ w) (μ : StationaryLaw L N w) (k R : ℕ) : 0 ≤ meanNearbyChipBirthDamage μ k R := by
  apply Finset.sum_nonneg
  intro x _
  refine mul_nonneg (μ.nonneg x) (mul_nonneg hw (Finset.sum_nonneg (fun i _ => ?_)))
  unfold nearbyChipBirthDamageAt
  split_ifs
  · exact competitiveBirthDamage_nonneg _ _
  · exact le_rfl

/-- For a band with lower edge at least `α N` and width at least `β N`, a
single cutoff controls all chip births within radius `R`, with their actual
empty-window weights. -/
theorem exists_threshold_nearbyChipBirthDamage_le_proportional {L N : ℕ} [NeZero L]
    {w α β : ℝ} (hw : 0 ≤ w) (hw' : w ≤ 1) (hα : 0 < α) (hβ : 0 < β)
    (hN : 0 < N) (μ : StationaryLaw L N w) (a b R : ℕ) (hab : a ≤ b) (hR : R < L)
    (halow : α * (N : ℝ) ≤ (a : ℝ)) (hwidth : β * (N : ℝ) ≤ ((b + 1 - a : ℕ) : ℝ)) :
    ∃ k ∈ Finset.Icc a b, meanNearbyChipBirthDamage μ k R ≤
      (w / (α ^ 3 * β)) * ((L : ℝ) / (N : ℝ)) * ((R : ℝ) ^ 2 * ((R : ℝ) + 1) / (N : ℝ)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have ha := (mul_pos hα hn).trans_le halow
  obtain ⟨k, hk, hd⟩ := exists_threshold_nearbyChipBirthDamage_le hw μ a b R (by exact_mod_cast ha) hab
  refine ⟨k, hk, hd.trans ?_⟩
  have hratio : (N : ℝ) / (a : ℝ) ≤ 1 / α := (div_le_div_iff₀ ha hα).mpr (by linarith)
  have hpre : w * ((R : ℝ) * L * (N / (a : ℝ))) / ((b + 1 - a : ℕ) : ℝ) ≤
      w * ((R : ℝ) * L * (1 / α)) / (β * N) := by
    apply (div_le_div_of_nonneg_left (by positivity) (mul_pos hβ hn) hwidth).trans
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hratio (by positivity)) hw) (mul_pos hβ hn).le
  have hfrac : α ≤ (a : ℝ) / (N : ℝ) := (le_div_iff₀ hn).mpr halow
  have hpair : nearbyThresholdPairProbability μ a R ≤
      ((R : ℝ) * ((R : ℝ) + 1) / N) / α ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hα)).mpr
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hα.le hfrac 2)
      (nearbyThresholdPairProbability_nonneg μ a R)).trans
      (nearbyThresholdPairProbability_mul_fraction_sq_le hw hw' μ a R hR)
  refine (mul_le_mul hpre hpair (nearbyThresholdPairProbability_nonneg μ a R) (by positivity)).trans_eq ?_
  field_simp [hα.ne', hβ.ne', hn.ne']
  ring

/-- At positive limiting density the nearby chip-birth part of the
two-pile estimate vanishes at a selected macroscopic cutoff whenever
`R² (R + 1) / N → 0`. -/
theorem exists_threshold_nearbyChipBirthDamage_tendsto_zero
    {L N a b R : ℕ → ℕ} [∀ n, NeZero (L n)] {w α β ρ : ℝ}
    (hw : 0 ≤ w) (hw' : w ≤ 1) (hα : 0 < α) (hβ : 0 < β) (hρ : 0 < ρ)
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w)
    (hdensity : Tendsto (fun n => (N n : ℝ) / (L n : ℝ)) atTop (𝓝 ρ))
    (hab : ∀ n, a n ≤ b n)
    (hband : ∀ᶠ n in atTop, R n < L n ∧ α * (N n : ℝ) ≤ (a n : ℝ) ∧
      β * (N n : ℝ) ≤ ((b n + 1 - a n : ℕ) : ℝ))
    (hscale : Tendsto (fun n => (R n : ℝ) ^ 2 * ((R n : ℝ) + 1) / (N n : ℝ)) atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, (∀ n, k n ∈ Finset.Icc (a n) (b n)) ∧
      Tendsto (fun n => meanNearbyChipBirthDamage (μ n) (k n) (R n)) atTop (𝓝 0) := by
  let bound (n : ℕ) := (w / (α ^ 3 * β)) * ((L n : ℝ) / (N n : ℝ)) *
    ((R n : ℝ) ^ 2 * ((R n : ℝ) + 1) / (N n : ℝ))
  have hinv : Tendsto (fun n => (L n : ℝ) / (N n : ℝ)) atTop (𝓝 ρ⁻¹) := by
    simpa only [inv_div] using hdensity.inv₀ hρ.ne'
  have hlim : Tendsto bound atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := w / (α ^ 3 * β))).mul hinv |>.mul hscale
  classical
  let k (n : ℕ) := if h : ∃ j ∈ Finset.Icc (a n) (b n),
      meanNearbyChipBirthDamage (μ n) j (R n) ≤ bound n then Classical.choose h else a n
  have hgood : ∀ᶠ n in atTop, ∃ j ∈ Finset.Icc (a n) (b n),
      meanNearbyChipBirthDamage (μ n) j (R n) ≤ bound n := by
    filter_upwards [eventually_pos_mass_of_tendsto_density hρ hdensity, hband] with n hn hb
    exact exists_threshold_nearbyChipBirthDamage_le_proportional hw hw' hα hβ hn
      (μ n) (a n) (b n) (R n) (hab n) hb.1 hb.2.1 hb.2.2
  refine ⟨k, fun n => ?_, tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun n => meanNearbyChipBirthDamage_nonneg hw (μ n) (k n) (R n))) ?_⟩
  · dsimp only [k]
    split_ifs with h
    · exact (Classical.choose_spec h).1
    · exact Finset.mem_Icc.mpr ⟨le_rfl, hab n⟩
  · exact hgood.mono (fun n h => by simpa only [k, dif_pos h] using (Classical.choose_spec h).2)

/-- The remaining weighted birth rate after removing nearby chip births:
whole-pile mergers across the cutoff and chips that cross it farther than
`R` from every existing mark. The weight at a first birth is zero. -/
def meanWholeAndDistantChipBirthDamage {L N : ℕ} [NeZero L] {w : ℝ}
    (μ : StationaryLaw L N w) (k R : ℕ) : ℝ := by
  classical
  exact ∑ x, μ.weight x * ∑ i,
    ((if 1 ≤ occ x i ∧ occ x (right i) = k ∧ ¬isNearbyChipBirth k R x i then w else 0) +
      wholeThresholdBirthAt k x i) *
      maskBirthDamage competitiveEmptyWindowPotential (largePileMask k x) (right i)

private theorem mean_competingBirthDamage_split {L N : ℕ} [NeZero L] {w : ℝ}
    (μ : StationaryLaw L N w) (k R : ℕ) :
    (∑ x, if maskIsEmpty (largePileMask k x) then 0 else
      μ.weight x * maskBirthDamageRate competitiveEmptyWindowPotential w k x) =
      meanWholeAndDistantChipBirthDamage μ k R + meanNearbyChipBirthDamage μ k R := by
  classical
  unfold meanWholeAndDistantChipBirthDamage meanNearbyChipBirthDamage
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hempty : (if maskIsEmpty (largePileMask k x) then 0 else
      μ.weight x * maskBirthDamageRate competitiveEmptyWindowPotential w k x) =
      μ.weight x * maskBirthDamageRate competitiveEmptyWindowPotential w k x := by
    split_ifs with h
    · rw [competitiveBirthDamageRate_eq_zero_of_empty w k x h, mul_zero]
    · rfl
  rw [hempty, ← mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply congrArg (μ.weight x * ·)
  unfold maskBirthDamageRate
  apply Finset.sum_congr rfl
  intro i _
  unfold nearbyChipBirthDamageAt
  by_cases hnear : isNearbyChipBirth k R x i
  · have hchip := And.intro hnear.1 hnear.2.1
    simp [hnear, hchip, add_mul, add_comm]
  · by_cases hchip : 1 ≤ occ x i ∧ occ x (right i) = k <;> simp [hnear, hchip, and_assoc]

private theorem twoLargePilesProbability_antitone {L N : ℕ} {w : ℝ}
    (μ : StationaryLaw L N w) {k b : ℕ} (hkb : k ≤ b) :
    twoLargePilesProbability μ b ≤ twoLargePilesProbability μ k := by
  unfold twoLargePilesProbability
  apply Finset.sum_le_sum
  intro x _
  have hc : maskCount (largePileMask b x) ≤ maskCount (largePileMask k x) := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hb : b < occ x i
    · simp [largePileMask, hb, hkb.trans_lt hb]
    · simp [largePileMask, hb, bitMass]
      split_ifs <;> norm_num
  split_ifs <;> first | exact le_rfl | exact μ.nonneg x | linarith

/-- Bound pairs above the *prescribed* upper edge of the macroscopic band.
At the selected cutoff only whole-pile births and distant chip births remain,
up to the explicit nearby chip error. -/
theorem stationary_twoLargePilesProbability_le_wholeAndDistantChipBirthDamage
    {L N : ℕ} [NeZero L] (hL : 3 ≤ L) {w α β : ℝ}
    (hw : 0 ≤ w) (hw' : w ≤ 1) (hα : 0 < α) (hβ : 0 < β)
    (hN : 0 < N) (μ : StationaryLaw L N w) (a b R : ℕ) (hab : a ≤ b) (hR : R < L)
    (halow : α * (N : ℝ) ≤ (a : ℝ)) (hwidth : β * (N : ℝ) ≤ ((b + 1 - a : ℕ) : ℝ)) :
    ∃ k ∈ Finset.Icc a b, 2 * twoLargePilesProbability μ b ≤
      meanWholeAndDistantChipBirthDamage μ k R +
        (w / (α ^ 3 * β)) * ((L : ℝ) / (N : ℝ)) * ((R : ℝ) ^ 2 * ((R : ℝ) + 1) / (N : ℝ)) := by
  obtain ⟨k, hk, hnear⟩ := exists_threshold_nearbyChipBirthDamage_le_proportional
    hw hw' hα hβ hN μ a b R hab hR halow hwidth
  have ha : 0 < a := by
    exact_mod_cast (mul_pos hα (by exact_mod_cast hN : (0 : ℝ) < N)).trans_le halow
  have h := stationary_twoLargePilesProbability_le_competingBirthDamage hL hw μ k
    (ha.trans_le (Finset.mem_Icc.mp hk).1)
  rw [mean_competingBirthDamage_split μ k R] at h
  exact ⟨k, hk, (mul_le_mul_of_nonneg_left (twoLargePilesProbability_antitone μ (Finset.mem_Icc.mp hk).2)
    (by norm_num : (0 : ℝ) ≤ 2)).trans (h.trans (add_le_add_left hnear _))⟩

end
end Chipping
