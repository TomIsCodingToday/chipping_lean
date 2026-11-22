import ChippingSupercondensation.Identities

/-!
# The largest pile

Whole-pile moves cannot reduce the largest mass, and at most one chip can. This
bounds the stationary mean mass just ahead of a largest pile by `w`, also above
any cutoff. A pile holding a majority is tracked through each jump
(`peakSite`). Tracking gives the flow of mass at successive offsets ahead of it,
the exact entry rate into the majority region above a cutoff, a cutoff with
small boundary weight in any band, and a level-crossing bound for the site
ahead of the peak.
-/

namespace Chipping

open Filter
open scoped BigOperators Topology

noncomputable section

/-- The largest pile mass as an observable for the generator. -/
def largestMass {L N : ℕ} (x : State L N) : ℝ := largest x

private theorem occ_le_largest {L N : ℕ} (x : State L N) (j : Fin L) :
    occ x j ≤ largest x :=
  Finset.le_sup (Finset.mem_univ j)

private theorem exists_occ_eq_largest {L N : ℕ} (hL : 0 < L) (x : State L N) :
    ∃ j : Fin L, occ x j = largest x := by
  have hs : (Finset.univ : Finset (Fin L)).Nonempty := ⟨⟨0, hL⟩, Finset.mem_univ _⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ hs (occ x)
  exact ⟨j, hj.symm⟩

private theorem occ_le_largest_move_of_ne {L N : ℕ} (x : State L N)
    (i j : Fin L) (k : ℕ) (hk : k ≤ occ x i) (hj : j ≠ i) :
    occ x j ≤ largest (move x i k hk) := by
  have hkeep : occ x j ≤ occ (move x i k hk) j := by
    simp [occ_move, transfer, hj]
  exact hkeep.trans (occ_le_largest _ j)

private theorem largest_le_largest_move_add {L N : ℕ} (x : State L N)
    (i : Fin L) (k : ℕ) (hk : k ≤ occ x i) :
    largest x ≤ largest (move x i k hk) + k := by
  apply Finset.sup_le
  intro j _
  by_cases hj : j = i
  · subst j
    have hsource : occ x i - k ≤ occ (move x i k hk) i := by
      simp [occ_move, transfer]
    calc
      occ x i = occ x i - k + k := (Nat.sub_add_cancel hk).symm
      _ ≤ occ (move x i k hk) i + k := Nat.add_le_add_right hsource k
      _ ≤ largest (move x i k hk) + k := Nat.add_le_add_right (occ_le_largest _ i) k
  · exact (occ_le_largest_move_of_ne x i j k hk hj).trans (Nat.le_add_right _ _)

private theorem largest_le_largest_whole_move {L N : ℕ} (hL : 3 ≤ L)
    (x : State L N) (i : Fin L) :
    largest x ≤ largest (move x i (occ x i) le_rfl) := by
  obtain ⟨j, hj⟩ := exists_occ_eq_largest (show 0 < L by omega) x
  rw [← hj]
  by_cases hji : j = i
  · subst j
    have hr := occ_le_largest (move x i (occ x i) le_rfl) (right i)
    rw [occ_move_right hL] at hr
    omega
  · exact occ_le_largest_move_of_ne x i j _ le_rfl hji

/-- An indicator for a site whose chip can reduce the largest mass. -/
def largestPileChipRiskAt {L N : ℕ} (x : State L N) (i : Fin L) : ℝ := by
  classical
  exact if 2 ≤ occ x i ∧ (∀ j : Fin L, j ≠ i → occ x j < occ x i) then 1 else 0

private theorem largestMass_chip_change_ge {L N : ℕ} (hL : 3 ≤ L)
    (x : State L N) (i : Fin L) (hm : 1 ≤ occ x i) :
    -largestPileChipRiskAt x i ≤ largestMass (move x i 1 hm) - largestMass x := by
  classical
  let y := move x i 1 hm
  by_cases hdrop : largest y < largest x
  · obtain ⟨j, hj⟩ := exists_occ_eq_largest (show 0 < L by omega) x
    have hji : j = i := by
      by_contra hne
      exact (not_le_of_gt hdrop) (hj ▸ occ_le_largest_move_of_ne x i j 1 hm hne)
    have hi : occ x i = largest x := by simpa [hji] using hj
    have hy : 1 ≤ largest y := by
      have hright := occ_le_largest y (right i)
      rw [show occ y (right i) = occ x (right i) + 1 from occ_move_right hL x i 1 hm] at hright
      omega
    have hm₂ : 2 ≤ occ x i := by omega
    have hstrict (j : Fin L) (hne : j ≠ i) : occ x j < occ x i := by
      rw [hi]
      exact (occ_le_largest_move_of_ne x i j 1 hm hne).trans_lt hdrop
    have hbound : (largest x : ℝ) ≤ (largest y : ℝ) + 1 := by
      exact_mod_cast largest_le_largest_move_add x i 1 hm
    have hrisk : largestPileChipRiskAt x i = 1 := by
      unfold largestPileChipRiskAt
      exact if_pos ⟨hm₂, hstrict⟩
    rw [hrisk]
    change -(1 : ℝ) ≤ (largest y : ℝ) - (largest x : ℝ)
    linarith
  · have hbound : (largest x : ℝ) ≤ (largest y : ℝ) := by
      exact_mod_cast le_of_not_gt hdrop
    unfold largestPileChipRiskAt largestMass
    change -_ ≤ (largest y : ℝ) - (largest x : ℝ)
    split_ifs <;> linarith

/-- The mass captured in a whole pile move whose source or destination is a
largest pile. When both are largest, the move is counted once. -/
def largestPileMergeGainAt {L N : ℕ} (x : State L N) (i : Fin L) : ℝ :=
  if 2 ≤ occ x i ∧ (occ x i = largest x ∨ occ x (right i) = largest x) then
    (min (occ x i) (occ x (right i)) : ℝ)
  else 0

private theorem whole_largest_change_ge {L N : ℕ} (hL : 3 ≤ L)
    (x : State L N) (i : Fin L) :
    largestPileMergeGainAt x i ≤
      (if 2 ≤ occ x i then largestMass (move x i (occ x i) le_rfl) - largestMass x else 0) := by
  by_cases hm : 2 ≤ occ x i
  · rw [if_pos hm]
    unfold largestPileMergeGainAt
    simp only [hm, true_and, largestMass]
    split_ifs with hpeak
    · have hright := occ_le_largest (move x i (occ x i) le_rfl) (right i)
      rw [occ_move_right hL] at hright
      have hgain : largest x + min (occ x i) (occ x (right i)) ≤
          largest (move x i (occ x i) le_rfl) := by
        rcases hpeak with ha | hb
        · have hmin := min_le_right (occ x i) (occ x (right i))
          omega
        · have hmin := min_le_left (occ x i) (occ x (right i))
          omega
      have hreal : (largest x : ℝ) + min (occ x i : ℝ) (occ x (right i) : ℝ) ≤
          (largest (move x i (occ x i) le_rfl) : ℝ) := by exact_mod_cast hgain
      linarith
    · apply sub_nonneg.mpr
      exact_mod_cast largest_le_largest_whole_move hL x i
  · simp [largestPileMergeGainAt, hm]

/-- Whole pile moves that touch a largest pile give positive drift. The only
negative drift comes from chipping a unique largest pile of size at least two. -/
theorem largestMass_generator_ge {L N : ℕ} (hL : 3 ≤ L) {w : ℝ} (hw : 0 ≤ w)
    (x : State L N) :
    (∑ i, largestPileMergeGainAt x i) - w * (∑ i, largestPileChipRiskAt x i) ≤
      generator w largestMass x := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  unfold generator
  apply Finset.sum_le_sum
  intro i _
  have hwhole := whole_largest_change_ge hL x i
  have hchip : -(w * largestPileChipRiskAt x i) ≤
      (if hm : 1 ≤ occ x i then w * (largestMass (move x i 1 hm) - largestMass x) else 0) := by
    split_ifs with hm
    · rw [← mul_neg]
      exact mul_le_mul_of_nonneg_left (largestMass_chip_change_ge hL x i hm) hw
    · have hm₂ : ¬ 2 ≤ occ x i := by omega
      simp [largestPileChipRiskAt, hm₂]
  unfold atSite
  linarith only [hwhole, hchip]

private theorem sum_largestPileChipRiskAt_le_one {L N : ℕ} (hL : 3 ≤ L) (x : State L N) :
    (∑ i, largestPileChipRiskAt x i) ≤ 1 := by
  classical
  obtain ⟨j, hj⟩ := exists_occ_eq_largest (show 0 < L by omega) x
  calc
    _ ≤ ∑ i, (if i = j then 1 else 0 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      unfold largestPileChipRiskAt
      split_ifs with hv heq
      · rfl
      · exact (not_lt_of_ge (hj ▸ occ_le_largest x i) (hv.2 j (Ne.symm heq))).elim
      · norm_num
      · rfl
    _ = 1 := by simp

/-- The expected merge gain at largest piles is bounded by the expected
decrease budget from vulnerable chip departures. -/
theorem stationary_largestPileMergeGain_le_chipRisk {L N : ℕ} (hL : 3 ≤ L) {w : ℝ}
    (hw : 0 ≤ w) (μ : StationaryLaw L N w) :
    (∑ x, μ.weight x * ∑ i, largestPileMergeGainAt x i) ≤
      w * (∑ x, μ.weight x * ∑ i, largestPileChipRiskAt x i) := by
  have h : (∑ x, μ.weight x * ((∑ i, largestPileMergeGainAt x i) -
      w * (∑ i, largestPileChipRiskAt x i))) ≤ 0 := by
    calc
      _ ≤ ∑ x, μ.weight x * generator w largestMass x :=
        Finset.sum_le_sum (fun x _ =>
          mul_le_mul_of_nonneg_left (largestMass_generator_ge hL hw x) (μ.nonneg x))
      _ = 0 := μ.invariant largestMass
  simp_rw [mul_sub, Finset.sum_sub_distrib, mul_left_comm _ w, ← Finset.mul_sum] at h
  exact sub_nonpos.mp h

/-- The stationary merge gain around largest piles is at most one chip rate. -/
theorem stationary_largestPileMergeGain_le {L N : ℕ} (hL : 3 ≤ L) {w : ℝ}
    (hw : 0 ≤ w) (μ : StationaryLaw L N w) :
    (∑ x, μ.weight x * ∑ i, largestPileMergeGainAt x i) ≤ w := by
  refine (stationary_largestPileMergeGain_le_chipRisk hL hw μ).trans ?_
  have h : (∑ x, μ.weight x * ∑ i, largestPileChipRiskAt x i) ≤ 1 := by
    calc
      _ ≤ ∑ x, μ.weight x * 1 :=
        Finset.sum_le_sum (fun x _ =>
          mul_le_mul_of_nonneg_left (sum_largestPileChipRiskAt_le_one hL x) (μ.nonneg x))
      _ = 1 := by simpa only [mul_one] using μ.normalized
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h hw

private theorem mass_ahead_of_largest_le_mergeGain {L N : ℕ} (x : State L N) (site : Fin L)
    (hpeak : occ x site = largest x) :
    (if 2 ≤ largest x then (occ x (right site) : ℝ) else 0) ≤ ∑ i, largestPileMergeGainAt x i := by
  have hnonneg (i : Fin L) : 0 ≤ largestPileMergeGainAt x i := by
    unfold largestPileMergeGainAt
    split_ifs
    · exact le_min (by positivity) (by positivity)
    · rfl
  by_cases hm : 2 ≤ largest x
  · rw [if_pos hm]
    have hsel :
        largestPileMergeGainAt x site = (occ x (right site) : ℝ) := by
      have hright : (occ x (right site) : ℝ) ≤ (largest x : ℝ) := by
        exact_mod_cast occ_le_largest x (right site)
      simp [largestPileMergeGainAt, hpeak, hm, min_eq_right hright]
    rw [← hsel]
    exact Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ site)
  · rw [if_neg hm]
    exact Finset.sum_nonneg (fun i _ => hnonneg i)

/-- The expected mass just ahead of any chosen largest pile of size at least
two is at most the chipping rate. The choice can depend on the configuration. -/
theorem stationary_mass_ahead_of_largest_le {L N : ℕ} (hL : 3 ≤ L) {w : ℝ}
    (hw : 0 ≤ w) (μ : StationaryLaw L N w) (peak : State L N → Fin L)
    (hpeak : ∀ x, occ x (peak x) = largest x) :
    (∑ x, μ.weight x * (if 2 ≤ largest x then (occ x (right (peak x)) : ℝ) else 0)) ≤ w := by
  refine le_trans ?_ (stationary_largestPileMergeGain_le hL hw μ)
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
    (mass_ahead_of_largest_le_mergeGain x (peak x) (hpeak x)) (μ.nonneg x))

/-- The mass of the largest pile above a specified cutoff. -/
def largestMassExcess {L N : ℕ} (t : ℕ) (x : State L N) : ℝ :=
  ((largest x - t : ℕ) : ℝ)

private theorem atSite_mono_of_change_le {L N : ℕ} {w : ℝ} (hw : 0 ≤ w)
    {f g : State L N → ℝ} (x : State L N)
    (h : ∀ y, f y - f x ≤ g y - g x) (i : Fin L) :
    atSite w f x i ≤ atSite w g x i := by
  unfold atSite
  apply add_le_add
  · split_ifs with hc
    · exact mul_le_mul_of_nonneg_left (h _) hw
    · rfl
  · split_ifs
    · exact h _
    · rfl

private theorem largestMassExcess_change_ge {L N : ℕ} (t : ℕ) (x y : State L N)
    (h : t < largest x) :
    largestMass y - largestMass x ≤ largestMassExcess t y - largestMassExcess t x := by
  unfold largestMass largestMassExcess
  rw [Nat.cast_sub h.le]
  by_cases hy : t ≤ largest y
  · rw [Nat.cast_sub hy]
    linarith
  · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hy), Nat.cast_zero]
    have hy' : (largest y : ℝ) ≤ (t : ℝ) := by exact_mod_cast le_of_not_ge hy
    linarith

/-- Above a cutoff, the excess retains the drift of the largest mass as a
lower bound. Below the cutoff its drift is nonnegative. -/
theorem largestMassExcess_generator_ge {L N : ℕ} (hL : 3 ≤ L) {w : ℝ}
    (hw : 0 ≤ w) (t : ℕ) (x : State L N) :
    (if t < largest x then
      (∑ i, largestPileMergeGainAt x i) - w * (∑ i, largestPileChipRiskAt x i)
    else 0) ≤ generator w (largestMassExcess t) x := by
  by_cases ht : t < largest x
  · rw [if_pos ht]
    refine (largestMass_generator_ge hL hw x).trans ?_
    unfold generator
    exact Finset.sum_le_sum (fun i _ =>
      atSite_mono_of_change_le hw x (fun y => largestMassExcess_change_ge t x y ht) i)
  · rw [if_neg ht]
    have hx : largestMassExcess t x = 0 := by
      simp [largestMassExcess, Nat.sub_eq_zero_of_le (le_of_not_gt ht)]
    unfold generator
    apply Finset.sum_nonneg
    intro i _
    unfold atSite
    rw [hx]
    have hy (y : State L N) : 0 ≤ largestMassExcess t y := by unfold largestMassExcess; positivity
    apply add_nonneg
    · split_ifs
      · exact mul_nonneg hw (by simpa only [sub_zero] using hy _)
      · rfl
    · split_ifs
      · simpa only [sub_zero] using hy _
      · rfl

/-- The same stationary budget for merge gains holds on the event that the
largest pile exceeds the cutoff, multiplied by the probability of that event. -/
theorem stationary_largestPileMergeGain_above_le {L N : ℕ} (hL : 3 ≤ L) {w : ℝ}
    (hw : 0 ≤ w) (μ : StationaryLaw L N w) (t : ℕ) :
    (∑ x, μ.weight x * (if t < largest x then ∑ i, largestPileMergeGainAt x i else 0)) ≤
      w * (∑ x, if t < largest x then μ.weight x else 0) := by
  have h : (∑ x, μ.weight x *
      (if t < largest x then (∑ i, largestPileMergeGainAt x i) -
        w * (∑ i, largestPileChipRiskAt x i) else 0)) ≤ 0 := by
    calc
      _ ≤ ∑ x, μ.weight x * generator w (largestMassExcess t) x :=
        Finset.sum_le_sum (fun x _ =>
          mul_le_mul_of_nonneg_left (largestMassExcess_generator_ge hL hw t x) (μ.nonneg x))
      _ = 0 := μ.invariant (largestMassExcess t)
  have hpoint (x : State L N) :
      μ.weight x * (if t < largest x then ∑ i, largestPileMergeGainAt x i else 0) -
        w * (if t < largest x then μ.weight x else 0) ≤
        μ.weight x * (if t < largest x then (∑ i, largestPileMergeGainAt x i) -
          w * (∑ i, largestPileChipRiskAt x i) else 0) := by
    split_ifs
    · have hrisk := mul_le_mul_of_nonneg_left (sum_largestPileChipRiskAt_le_one hL x)
        (mul_nonneg (μ.nonneg x) hw)
      nlinarith only [hrisk]
    · simp
  apply sub_nonpos.mp
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact (Finset.sum_le_sum (fun x _ => hpoint x)).trans h

/-- Conditional on the largest pile exceeding any positive cutoff, the mass
immediately ahead has mean at most `w`, expressed without division by the event
probability. -/
theorem stationary_mass_ahead_of_largest_above_le {L N : ℕ} (hL : 3 ≤ L) {w : ℝ}
    (hw : 0 ≤ w) (μ : StationaryLaw L N w) (t : ℕ) (ht : 1 ≤ t)
    (peak : State L N → Fin L) (hpeak : ∀ x, occ x (peak x) = largest x) :
    (∑ x, μ.weight x * (if t < largest x then (occ x (right (peak x)) : ℝ) else 0)) ≤
      w * (∑ x, if t < largest x then μ.weight x else 0) := by
  refine le_trans ?_ (stationary_largestPileMergeGain_above_le hL hw μ t)
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (μ.nonneg x)
  split_ifs with hx
  · have hsize : 2 ≤ largest x := by omega
    simpa only [if_pos hsize] using mass_ahead_of_largest_le_mergeGain x (peak x) (hpeak x)
  · rfl

/-- A conditional tail bound for the mass in front of a largest pile. -/
theorem stationary_mass_ahead_of_largest_tail_le {L N : ℕ} (hL : 3 ≤ L) {w : ℝ}
    (hw : 0 ≤ w) (μ : StationaryLaw L N w) (t : ℕ) (ht : 1 ≤ t)
    (peak : State L N → Fin L) (hpeak : ∀ x, occ x (peak x) = largest x) (a : ℕ) :
    (a : ℝ) * (∑ x, if t < largest x ∧ a ≤ occ x (right (peak x)) then μ.weight x else 0) ≤
      w * (∑ x, if t < largest x then μ.weight x else 0) := by
  refine le_trans ?_ (stationary_mass_ahead_of_largest_above_le hL hw μ t ht peak hpeak)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : t < largest x
  · by_cases ha : a ≤ occ x (right (peak x))
    · simp only [hx, ha, and_self, if_true, mul_comm (a : ℝ)]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast ha) (μ.nonneg x)
    · simp only [hx, ha, and_false, if_false, if_true, mul_zero]
      exact mul_nonneg (μ.nonneg x) (by positivity)
  · simp [hx]

/-- A site attaining the largest mass. In the majority region it is unique. -/
def peakSite {L N : ℕ} [NeZero L] (x : State L N) : Fin L :=
  (exists_occ_eq_largest (Nat.pos_of_ne_zero (NeZero.ne L)) x).choose

theorem occ_peakSite {L N : ℕ} [NeZero L] (x : State L N) :
    occ x (peakSite x) = largest x :=
  (exists_occ_eq_largest (Nat.pos_of_ne_zero (NeZero.ne L)) x).choose_spec

private theorem two_site_mass_le_total {L N : ℕ} (x : State L N) {i j : Fin L}
    (hne : i ≠ j) : occ x i + occ x j ≤ N := by
  classical
  calc
    _ = ∑ k ∈ ({i, j} : Finset (Fin L)), occ x k := by simp [hne]
    _ ≤ ∑ k, occ x k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => Nat.zero_le _)
    _ = N := x.property

theorem peakSite_eq_of_majority {L N : ℕ} [NeZero L] (x : State L N) (i : Fin L)
    (hi : N < 2 * occ x i) : peakSite x = i := by
  by_contra h
  have hsum := two_site_mass_le_total x h
  have hpeak : occ x i ≤ occ x (peakSite x) := (occ_peakSite x).symm ▸ occ_le_largest x i
  omega

theorem peakSite_chip_move {L N : ℕ} [NeZero L] (x : State L N)
    (hmargin : N + 2 < 2 * largest x) (i : Fin L) (hi : 1 ≤ occ x i) :
    peakSite (move x i 1 hi) = peakSite x := by
  apply peakSite_eq_of_majority
  have hmass : largest x - 1 ≤ occ (move x i 1 hi) (peakSite x) := by
    rw [← occ_peakSite x]
    by_cases h : peakSite x = i
    · simp [occ_move, transfer, h]
    · simp [occ_move, transfer, h, le_trans (Nat.sub_le _ _) (Nat.le_add_right _ _)]
  omega

theorem peakSite_whole_move {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    (x : State L N) (hmajority : N < 2 * largest x) (i : Fin L) :
    peakSite (move x i (occ x i) le_rfl) = if i = peakSite x then right i else peakSite x := by
  split_ifs with h
  · apply peakSite_eq_of_majority
    rw [occ_move_right hL, h, occ_peakSite]
    omega
  · apply peakSite_eq_of_majority
    have hmass : largest x ≤ occ (move x i (occ x i) le_rfl) (peakSite x) := by
      rw [← occ_peakSite x]
      simp [occ_move, transfer, Ne.symm h]
    omega

/-- Total mass in the next `r` sites clockwise of the selected largest pile. -/
def massAheadOfPeak {L N : ℕ} [NeZero L] (r : ℕ) (x : State L N) : ℝ :=
  windowMass r x (peakSite x + (r : Fin L))

private theorem windowMass_shift_one {L N : ℕ} [NeZero L] (r : ℕ)
    (x : State L N) (j : Fin L) :
    windowMass r x (j + 1) - windowMass r x j =
      (occ x (j + 1) : ℝ) - (occ x (j + 1 - (r : Fin L)) : ℝ) := by
  let f (s : ℕ) : ℝ := occ x (j + 1 - (s : Fin L))
  have hf (s : ℕ) : (occ x (j - (s : Fin L)) : ℝ) = f (s + 1) := by
    dsimp [f]
    congr 2
    push_cast
    abel
  unfold windowMass
  change (∑ s ∈ Finset.range r, f s) - (∑ s ∈ Finset.range r, (occ x (j - (s : Fin L)) : ℝ)) = _
  simp_rw [hf]
  rw [← neg_sub, ← Finset.sum_sub_distrib, sum_range_forward_diff f r]
  simp [f]

private theorem massAheadOfPeak_chip_change {L N : ℕ} [NeZero L]
    (r : ℕ) (x : State L N) (hmargin : N + 2 < 2 * largest x)
    (i : Fin L) (hi : 1 ≤ occ x i) :
    massAheadOfPeak r (move x i 1 hi) - massAheadOfPeak r x =
      (if i = peakSite x then (1 : ℝ) else 0) -
        (if i = peakSite x + (r : Fin L) then 1 else 0) := by
  unfold massAheadOfPeak
  rw [peakSite_chip_move x hmargin, windowMass_move]
  simp [eq_comm]

private theorem massAheadOfPeak_whole_change {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    (r : ℕ) (hr : r + 1 < L) (x : State L N) (hmajority : N < 2 * largest x) (i : Fin L) :
    massAheadOfPeak r (move x i (occ x i) le_rfl) - massAheadOfPeak r x =
      if i = peakSite x then
        (occ x (peakSite x + ((r + 1 : ℕ) : Fin L)) : ℝ) - (occ x (right (peakSite x)) : ℝ)
      else -(if i = peakSite x + (r : Fin L) then (occ x i : ℝ) else 0) := by
  unfold massAheadOfPeak
  rw [peakSite_whole_move hL x hmajority]
  by_cases hp : i = peakSite x
  · rw [if_pos hp, if_pos hp]
    let j := right i + (r : Fin L)
    change windowMass r (move x i (occ x i) le_rfl) j -
      windowMass r x (peakSite x + (r : Fin L)) = _
    have hj : j = i + ((r + 1 : ℕ) : Fin L) := by
      dsimp [j]
      simp only [right_eq_add_one, Nat.cast_add, Nat.cast_one]
      abel
    have hj₁ : j ≠ i + (r : Fin L) := by
      change right i + (r : Fin L) ≠ i + (r : Fin L)
      exact fun h => right_ne_self hL i (add_right_cancel h)
    have hj₂ : j ≠ i := by
      rw [hj]
      exact fun h => natCast_fin_ne_zero (by omega : 0 < r + 1) hr
        (add_left_cancel (h.trans (add_zero i).symm))
    have hs := windowMass_move r x i (occ x i) le_rfl j
    rw [if_neg hj₁, if_neg hj₂, sub_self, mul_zero, sub_eq_zero] at hs
    rw [hs]
    have hshift : j = (peakSite x + (r : Fin L)) + 1 := by
      rw [hj, hp, Nat.cast_add, Nat.cast_one, add_assoc]
    have hfirst : (peakSite x + (r : Fin L)) + 1 - (r : Fin L) = right (peakSite x) := by
      rw [right_eq_add_one]
      abel
    rw [hshift, windowMass_shift_one, hfirst, Nat.cast_add, Nat.cast_one, add_assoc]
  · rw [if_neg hp, if_neg hp, windowMass_move]
    have hp' : peakSite x ≠ i := Ne.symm hp
    simp [hp', eq_comm]
    split_ifs <;> ring

/-- Expected mass sent to the right per unit time by a site of mass `a`. -/
def departureMassRate (w : ℝ) (a : ℕ) : ℝ :=
  (if 1 ≤ a then w else 0) + (if 2 ≤ a then (a : ℝ) else 0)

/-- The exact drift of the mass ahead of a pile with a majority that survives
any single chip. The peak chips into the block, its whole moves shift the
frame, and the far end of the block sends mass out. -/
theorem generator_massAheadOfPeak_eq {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    (w : ℝ) (r : ℕ) (hr : 0 < r) (hrL : r + 1 < L)
    (x : State L N) (hmargin : N + 2 < 2 * largest x) :
    generator w (massAheadOfPeak r) x =
      w + ((occ x (peakSite x + ((r + 1 : ℕ) : Fin L)) : ℝ) -
        (occ x (right (peakSite x)) : ℝ)) -
      departureMassRate w (occ x (peakSite x + (r : Fin L))) := by
  let p := peakSite x
  let edge := p + (r : Fin L)
  let shift : ℝ := (occ x (p + ((r + 1 : ℕ) : Fin L)) : ℝ) - (occ x (right p) : ℝ)
  have hsep : edge ≠ p := by
    intro h
    exact natCast_fin_ne_zero hr (by omega : r < L) (add_left_cancel (h.trans (add_zero p).symm))
  have hp₂ : 2 ≤ occ x p := by
    change 2 ≤ occ x (peakSite x)
    rw [occ_peakSite]
    omega
  have hp₁ : 1 ≤ occ x p := by omega
  have hsite (i : Fin L) : atSite w (massAheadOfPeak r) x i =
      (if i = p then w + shift else 0) -
        (if i = edge then departureMassRate w (occ x i) else 0) := by
    unfold atSite
    simp_rw [massAheadOfPeak_chip_change r x hmargin,
      massAheadOfPeak_whole_change hL r hrL x (show N < 2 * largest x by omega)]
    change (if 1 ≤ occ x i then w * ((if i = p then 1 else 0) - (if i = edge then 1 else 0)) else 0) +
      (if 2 ≤ occ x i then (if i = p then shift else -(if i = edge then (occ x i : ℝ) else 0))
        else 0) = _
    by_cases hpeak : i = p
    · rw [hpeak]
      simp [hp₁, hp₂, Ne.symm hsep]
    · by_cases hfar : i = edge
      · simp only [hpeak, hfar, if_false, if_true, sub_zero]
        unfold departureMassRate
        split_ifs <;> ring
      · simp [hpeak, hfar]
  unfold generator
  simp_rw [hsite]
  simp [Finset.sum_sub_distrib, edge, shift, p]

theorem massAheadOfPeak_nonneg {L N : ℕ} [NeZero L] (r : ℕ) (x : State L N) :
    0 ≤ massAheadOfPeak r x := by
  unfold massAheadOfPeak windowMass
  exact Finset.sum_nonneg (fun _ _ => by positivity)

/-- Before wrapping around to the peak, the block is part of the background. -/
theorem massAheadOfPeak_le_background {L N : ℕ} [NeZero L] (r : ℕ) (hr : r < L)
    (x : State L N) : massAheadOfPeak r x ≤ (N : ℝ) - (largest x : ℝ) := by
  classical
  let f (s : ℕ) : Fin L := peakSite x + ((s + 1 : ℕ) : Fin L)
  have hlt (s : ℕ) (hs : s ∈ Finset.range r) : s + 1 < L := by
    have := Finset.mem_range.mp hs
    omega
  have hsub : (Finset.range r).image f ⊆ Finset.univ.erase (peakSite x) := by
    intro j hj
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hj
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro h
    exact natCast_fin_ne_zero (by omega : 0 < s + 1) (hlt s hs)
      (add_left_cancel (h.trans (add_zero (peakSite x)).symm))
  have hinj (s : ℕ) (hs : s ∈ Finset.range r) (t : ℕ) (ht : t ∈ Finset.range r)
      (he : f s = f t) : s = t := by
    have hv := congrArg Fin.val (add_left_cancel he)
    rw [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt (hlt s hs),
      Nat.mod_eq_of_lt (hlt t ht)] at hv
    omega
  have hmass : (∑ i, (occ x i : ℝ)) = (N : ℝ) := by exact_mod_cast x.property
  unfold massAheadOfPeak
  rw [windowMass_at_forward_end]
  change (∑ s ∈ Finset.range r, (occ x (f s) : ℝ)) ≤ _
  calc
    _ = ∑ j ∈ (Finset.range r).image f, (occ x j : ℝ) := (Finset.sum_image hinj).symm
    _ ≤ ∑ j ∈ Finset.univ.erase (peakSite x), (occ x j : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = _ := by rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), hmass, occ_peakSite]

/-- Observe `f` only while the largest pile exceeds `t`. -/
def largestCutoff {L N : ℕ} (t : ℕ) (f : State L N → ℝ) (x : State L N) : ℝ :=
  if t < largest x then f x else 0

private theorem chip_exit_cutoff_facts {L N : ℕ} [NeZero L] (t : ℕ) (x : State L N)
    (ht : t < largest x) (i : Fin L) (hi : 1 ≤ occ x i)
    (hy : largest (move x i 1 hi) ≤ t) :
    i = peakSite x ∧ largest x = t + 1 ∧ largest (move x i 1 hi) = t := by
  have hone := largest_le_largest_move_add x i 1 hi
  have hi_eq : i = peakSite x := by
    classical
    by_contra h
    have hkeep := occ_le_largest_move_of_ne x i (peakSite x) 1 hi (Ne.symm h)
    rw [occ_peakSite] at hkeep
    omega
  exact ⟨hi_eq, by omega, by omega⟩

private theorem largestCutoff_chip_lower {L N : ℕ} [NeZero L]
    (t : ℕ) (f : State L N → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hexit : ∀ y, largest y = t → f y ≤ b) (x : State L N) (ht : t < largest x)
    (i : Fin L) (hi : 1 ≤ occ x i) :
    f (move x i 1 hi) - (if i = peakSite x ∧ largest x = t + 1 then b else 0) ≤
      largestCutoff t f (move x i 1 hi) := by
  classical
  let y := move x i 1 hi
  have hpen : 0 ≤ (if i = peakSite x ∧ largest x = t + 1 then b else 0) := by
    split_ifs
    · exact hb
    · rfl
  by_cases hy : t < largest y
  · change f y - _ ≤ largestCutoff t f y
    rw [largestCutoff, if_pos hy]
    exact sub_le_self _ hpen
  · obtain ⟨hi_eq, hboundary, hy_eq⟩ := chip_exit_cutoff_facts t x ht i hi (le_of_not_gt hy)
    change f y - _ ≤ largestCutoff t f y
    rw [largestCutoff, if_neg hy, if_pos ⟨hi_eq, hboundary⟩]
    exact sub_nonpos.mpr (hexit y hy_eq)

/-- Truncation at a largest-mass cutoff loses drift only when a chip takes
the largest mass from `t + 1` to `t`. At most one site can do this. -/
theorem generator_largestCutoff_ge {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (t : ℕ) (f : State L N → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hnonneg : ∀ y, t < largest y → 0 ≤ f y) (hexit : ∀ y, largest y = t → f y ≤ b)
    (x : State L N) :
    (if t < largest x then generator w f x else 0) -
        (if largest x = t + 1 then w * b else 0) ≤ generator w (largestCutoff t f) x := by
  by_cases ht : t < largest x
  · rw [if_pos ht]
    have hx : largestCutoff t f x = f x := if_pos ht
    have hwhole (i : Fin L) :
        largestCutoff t f (move x i (occ x i) le_rfl) = f (move x i (occ x i) le_rfl) :=
      if_pos (ht.trans_le (largest_le_largest_whole_move hL x i))
    have hsite (i : Fin L) :
        atSite w f x i - (if i = peakSite x ∧ largest x = t + 1 then w * b else 0) ≤
          atSite w (largestCutoff t f) x i := by
      unfold atSite
      rw [hx, hwhole]
      by_cases hi : 1 ≤ occ x i
      · simp only [dif_pos hi]
        have hc := mul_le_mul_of_nonneg_left
          (largestCutoff_chip_lower t f hb hexit x ht i hi) hw
        by_cases hp : i = peakSite x ∧ largest x = t + 1
        · simp only [if_pos hp] at hc ⊢
          linarith only [hc]
        · simp only [if_neg hp, sub_zero] at hc ⊢
          linarith only [hc]
      · simp only [dif_neg hi, zero_add]
        apply sub_le_self
        split_ifs
        · exact mul_nonneg hw hb
        · exact le_rfl
    unfold generator
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hsite i)
    by_cases hb : largest x = t + 1
    · simpa [Finset.sum_sub_distrib, hb] using hsum
    · simpa [Finset.sum_sub_distrib, hb] using hsum
  · have hb : largest x ≠ t + 1 := by omega
    rw [if_neg ht, if_neg hb, sub_zero]
    have hx : largestCutoff t f x = 0 := if_neg ht
    have hy (y : State L N) : 0 ≤ largestCutoff t f y := by
      unfold largestCutoff
      split_ifs with hy
      · exact hnonneg y hy
      · rfl
    unfold generator
    apply Finset.sum_nonneg
    intro i _
    unfold atSite
    rw [hx]
    apply add_nonneg
    · split_ifs
      · exact mul_nonneg hw (by simpa only [sub_zero] using hy _)
      · rfl
    · split_ifs
      · simpa only [sub_zero] using hy _
      · rfl

private theorem stationary_largestCutoff_drift_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (t : ℕ) (f : State L N → ℝ)
    {b : ℝ} (hb : 0 ≤ b) (hnonneg : ∀ y, t < largest y → 0 ≤ f y)
    (hexit : ∀ y, largest y = t → f y ≤ b) :
    (∑ x, μ.weight x * (if t < largest x then generator w f x else 0)) ≤
      w * b * (∑ x, if largest x = t + 1 then μ.weight x else 0) := by
  have hpoint (x : State L N) :
      μ.weight x * (if t < largest x then generator w f x else 0) -
        w * b * (if largest x = t + 1 then μ.weight x else 0) ≤
        μ.weight x * generator w (largestCutoff t f) x := by
    have h := mul_le_mul_of_nonneg_left
      (generator_largestCutoff_ge hL hw t f hb hnonneg hexit x) (μ.nonneg x)
    by_cases he : largest x = t + 1
    · simpa only [if_pos he, mul_sub, mul_comm (μ.weight x) (w * b)] using h
    · simpa only [if_neg he, mul_zero, sub_zero] using h
  apply sub_nonpos.mp
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact (Finset.sum_le_sum (fun x _ => hpoint x)).trans_eq (μ.invariant (largestCutoff t f))

private theorem generator_const_sub {L N : ℕ} (w b : ℝ)
    (f : State L N → ℝ) (x : State L N) :
    generator w (fun y => b - f y) x = -generator w f x := by
  unfold generator
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold atSite
  split_ifs <;> ring

/-- A bounded observable has small mean drift on the cutoff region if few
configurations are one chip away from losing the cutoff. -/
theorem stationary_largestCutoff_abs_drift_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (t : ℕ) (f : State L N → ℝ)
    {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ y, t ≤ largest y → 0 ≤ f y ∧ f y ≤ b) :
    |∑ x, μ.weight x * (if t < largest x then generator w f x else 0)| ≤
      w * b * (∑ x, if largest x = t + 1 then μ.weight x else 0) := by
  apply abs_le.mpr
  constructor
  · have h := stationary_largestCutoff_drift_le hL hw μ t (fun y => b - f y) hb
      (fun y hy => sub_nonneg.mpr (hbound y hy.le).2)
      (fun y hy => sub_le_self _ (hbound y hy.ge).1)
    have hneg (x : State L N) :
        (if t < largest x then generator w (fun y => b - f y) x else 0) =
          -(if t < largest x then generator w f x else 0) := by
      rw [generator_const_sub]
      split_ifs <;> simp
    simp_rw [hneg, mul_neg, Finset.sum_neg_distrib] at h
    exact neg_le.mp h
  · exact stationary_largestCutoff_drift_le hL hw μ t f hb
      (fun y hy => (hbound y hy.le).1) (fun y hy => (hbound y hy.ge).2)

/-- The drift equation for a block ahead of the peak holds in stationary
expectation on the majority region, up to an error from crossing the cutoff. -/
theorem stationary_massAheadOfPeak_majority_drift_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w)
    (r t : ℕ) (hr : 0 < r) (hrL : r + 1 < L) (ht : N < 2 * t) (htN : t ≤ N) :
    |∑ x, μ.weight x * (if t < largest x then
      w + ((occ x (peakSite x + ((r + 1 : ℕ) : Fin L)) : ℝ) -
        (occ x (right (peakSite x)) : ℝ)) -
        departureMassRate w (occ x (peakSite x + (r : Fin L)))
      else 0)| ≤ w * ((N - t : ℕ) : ℝ) * (∑ x, if largest x = t + 1 then μ.weight x else 0) := by
  have hbound (x : State L N) (hx : t ≤ largest x) :
      0 ≤ massAheadOfPeak r x ∧ massAheadOfPeak r x ≤ ((N - t : ℕ) : ℝ) := by
    refine ⟨massAheadOfPeak_nonneg r x, (massAheadOfPeak_le_background r (by omega) x).trans ?_⟩
    rw [Nat.cast_sub htN]
    exact sub_le_sub_left (by exact_mod_cast hx) _
  have h := stationary_largestCutoff_abs_drift_le hL hw μ t (massAheadOfPeak r)
    (by positivity) hbound
  have hlocal (x : State L N) :
      (if t < largest x then generator w (massAheadOfPeak r) x else 0) =
        (if t < largest x then
          w + ((occ x (peakSite x + ((r + 1 : ℕ) : Fin L)) : ℝ) -
            (occ x (right (peakSite x)) : ℝ)) -
            departureMassRate w (occ x (peakSite x + (r : Fin L)))
        else 0) := by
    split_ifs with hx
    · exact generator_massAheadOfPeak_eq hL w r hr hrL x (by omega)
    · rfl
  simpa only [hlocal] using h

/-- Total mass outside a largest pile. -/
def backgroundMass {L N : ℕ} (x : State L N) : ℝ := (N : ℝ) - largestMass x

theorem occ_move_delta {L N : ℕ} (x : State L N) (i j : Fin L) (k : ℕ)
    (hk : k ≤ occ x i) :
    (occ (move x i k hk) j : ℝ) - (occ x j : ℝ) =
      (if j = right i then (k : ℝ) else 0) - (if j = i then (k : ℝ) else 0) := by
  have hsub : (if j = i then k else 0) ≤ occ x j := by
    by_cases h : j = i
    · simpa [h] using hk
    · simp [h]
  rw [occ_move]
  unfold transfer
  push_cast [Nat.cast_sub hsub]
  ring

/-- In the majority frame the background gains one particle per chip from
the peak and loses all mass the peak catches or receives from behind. -/
theorem generator_backgroundMass_majority_eq {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    (w : ℝ) (x : State L N) (hmargin : N + 2 < 2 * largest x) :
    generator w backgroundMass x =
      w - (occ x (right (peakSite x)) : ℝ) - departureMassRate w (occ x (peakSite x - 1)) := by
  change generator w (fun y => (N : ℝ) - largestMass y) x = _
  rw [generator_const_sub]
  let p := peakSite x
  let rear := p - 1
  have hrear (i : Fin L) : p = right i ↔ i = rear := by
    rw [right_eq_add_one, eq_comm, ← eq_sub_iff_add_eq]
  have hsep : rear ≠ p := by
    intro h
    have h' : right p = p := (hrear p).mpr h.symm |>.symm
    exact right_ne_self hL p h'
  have hchip (i : Fin L) (hi : 1 ≤ occ x i) :
      largestMass (move x i 1 hi) - largestMass x =
        (if i = rear then (1 : ℝ) else 0) - (if i = p then 1 else 0) := by
    unfold largestMass
    rw [← occ_peakSite (move x i 1 hi), peakSite_chip_move x hmargin, ← occ_peakSite x,
      occ_move_delta]
    change (if p = right i then (↑(1 : ℕ) : ℝ) else 0) - (if p = i then _ else 0) = _
    simp only [hrear, Nat.cast_one]
    simp [eq_comm]
  have hwhole (i : Fin L) :
      largestMass (move x i (occ x i) le_rfl) - largestMass x =
        if i = p then (occ x (right p) : ℝ) else (if i = rear then (occ x i : ℝ) else 0) := by
    unfold largestMass
    rw [← occ_peakSite (move x i (occ x i) le_rfl),
      peakSite_whole_move hL x (by omega : N < 2 * largest x)]
    change (occ (move x i (occ x i) le_rfl) (if i = p then right i else p) : ℝ) - _ = _
    by_cases hp : i = p
    · rw [if_pos hp, if_pos hp, occ_move_right hL, hp]
      simp [p, occ_peakSite]
    · rw [if_neg hp, if_neg hp, ← occ_peakSite x]
      change (occ (move x i (occ x i) le_rfl) p : ℝ) - (occ x p : ℝ) = _
      rw [occ_move_delta]
      simp [hrear, Ne.symm hp]
  have hp₂ : 2 ≤ occ x p := by dsimp [p]; rw [occ_peakSite]; omega
  have hp₁ : 1 ≤ occ x p := by omega
  have hsite (i : Fin L) : atSite w largestMass x i =
      (if i = p then (occ x (right p) : ℝ) - w else 0) +
        (if i = rear then departureMassRate w (occ x i) else 0) := by
    unfold atSite
    simp_rw [hchip, hwhole]
    by_cases hp : i = p
    · rw [hp]
      simp [hp₁, hp₂, Ne.symm hsep]
      ring
    · by_cases hb : i = rear
      · simp [hp, hb, hsep, departureMassRate]
      · simp [hp, hb]
  unfold generator
  simp_rw [hsite]
  simp [Finset.sum_add_distrib, p, rear]
  ring

/-- The same cutoff estimate for the total background balances the chip input
at the peak against the two ways particles are absorbed into it. -/
theorem stationary_backgroundMass_majority_drift_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (t : ℕ) (ht : N < 2 * t) (htN : t ≤ N) :
    |∑ x, μ.weight x * (if t < largest x then
      w - (occ x (right (peakSite x)) : ℝ) - departureMassRate w (occ x (peakSite x - 1))
      else 0)| ≤ w * ((N - t : ℕ) : ℝ) * (∑ x, if largest x = t + 1 then μ.weight x else 0) := by
  have hbound (x : State L N) (hx : t ≤ largest x) :
      0 ≤ backgroundMass x ∧ backgroundMass x ≤ ((N - t : ℕ) : ℝ) := by
    rw [Nat.cast_sub htN]
    have hfront := massAheadOfPeak_le_background 0 (by omega) x
    have hnonneg := massAheadOfPeak_nonneg 0 x
    have hmass : (t : ℝ) ≤ (largest x : ℝ) := by exact_mod_cast hx
    unfold backgroundMass largestMass
    constructor <;> linarith
  have h := stationary_largestCutoff_abs_drift_le hL hw μ t backgroundMass
    (by positivity) hbound
  have hlocal (x : State L N) :
      (if t < largest x then generator w backgroundMass x else 0) =
        (if t < largest x then
          w - (occ x (right (peakSite x)) : ℝ) - departureMassRate w (occ x (peakSite x - 1))
        else 0) := by
    split_ifs with hx
    · exact generator_backgroundMass_majority_eq hL w x (by omega)
    · rfl
  simpa only [hlocal] using h

private theorem generator_sub {L N : ℕ} (w : ℝ) (f g : State L N → ℝ) (x : State L N) :
    generator w (fun y => f y - g y) x = generator w f x - generator w g x := by
  unfold generator
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold atSite
  split_ifs <;> ring

/-- Successive sites in the majority frame satisfy a stationary flow balance.
Taking the difference between total background and front block mass removes
both the peak's chip input and the mass caught by its whole moves. -/
theorem stationary_majority_successive_flow_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w)
    (r t : ℕ) (hr : 0 < r) (hrL : r + 1 < L) (ht : N < 2 * t) (htN : t ≤ N) :
    |∑ x, μ.weight x * (if t < largest x then
      departureMassRate w (occ x (peakSite x + (r : Fin L))) -
        (occ x (peakSite x + ((r + 1 : ℕ) : Fin L)) : ℝ) -
        departureMassRate w (occ x (peakSite x - 1))
      else 0)| ≤ w * ((N - t : ℕ) : ℝ) * (∑ x, if largest x = t + 1 then μ.weight x else 0) := by
  let f (x : State L N) := backgroundMass x - massAheadOfPeak r x
  have hbound (x : State L N) (hx : t ≤ largest x) :
      0 ≤ f x ∧ f x ≤ ((N - t : ℕ) : ℝ) := by
    have hfront := massAheadOfPeak_le_background r (by omega) x
    have hmass : (t : ℝ) ≤ (largest x : ℝ) := by exact_mod_cast hx
    have hnonneg := massAheadOfPeak_nonneg r x
    rw [Nat.cast_sub htN]
    dsimp [f, backgroundMass, largestMass]
    constructor <;> linarith
  have h := stationary_largestCutoff_abs_drift_le hL hw μ t f (by positivity) hbound
  have hlocal (x : State L N) :
      (if t < largest x then generator w f x else 0) =
        (if t < largest x then
          departureMassRate w (occ x (peakSite x + (r : Fin L))) -
            (occ x (peakSite x + ((r + 1 : ℕ) : Fin L)) : ℝ) -
            departureMassRate w (occ x (peakSite x - 1))
          else 0) := by
    split_ifs with hx
    · have hmargin : N + 2 < 2 * largest x := by omega
      dsimp [f]
      rw [generator_sub, generator_backgroundMass_majority_eq hL w x hmargin,
        generator_massAheadOfPeak_eq hL w r hr hrL x hmargin]
      ring
    · rfl
  simpa only [hlocal] using h

private theorem chip_exits_majority_cutoff_iff {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    (t : ℕ) (hmajority : N < 2 * t) (x : State L N) (hx : t < largest x)
    (i : Fin L) (hi : 1 ≤ occ x i) :
    largest (move x i 1 hi) ≤ t ↔ i = peakSite x ∧ largest x = t + 1 := by
  constructor
  · intro hy
    obtain ⟨hpeak, hm, _⟩ := chip_exit_cutoff_facts t x hx i hi hy
    exact ⟨hpeak, hm⟩
  · rintro ⟨hpeak, hm⟩
    have hsource : occ x i = t + 1 := by rw [hpeak, occ_peakSite, hm]
    apply Finset.sup_le
    intro j _
    by_cases hji : j = i
    · subst j
      simp [occ_move, transfer, Ne.symm (right_ne_self hL i), hsource]
    · have hpair := two_site_mass_le_total x hji
      rw [hsource] at hpair
      rw [occ_move]
      unfold transfer
      simp only [if_neg hji, Nat.sub_zero]
      split_ifs <;> omega

private theorem largest_move_above_iff {L N : ℕ} (hL : 3 ≤ L)
    (t : ℕ) (x : State L N) (hx : largest x ≤ t) (i : Fin L) (k : ℕ)
    (hk : k ≤ occ x i) :
    t < largest (move x i k hk) ↔ t < occ x (right i) + k := by
  constructor
  · intro h
    by_contra! hdest
    apply (not_le_of_gt h)
    apply Finset.sup_le
    intro j _
    by_cases hj : j = right i
    · subst j
      simpa only [occ_move_right hL] using hdest
    · have hold := (occ_le_largest x j).trans hx
      rw [occ_move]
      unfold transfer
      simp only [if_neg hj, Nat.add_zero]
      exact (Nat.sub_le _ _).trans hold
  · intro h
    have hr := occ_le_largest (move x i k hk) (right i)
    rw [occ_move_right hL] at hr
    exact h.trans_le hr

/-- Total rate of jumps from a largest mass at most `t` to one above `t`.
The only possible entries are chips into a site of mass `t` and whole pile
merges with combined mass greater than `t`. -/
def largestCutoffEntryRate {L N : ℕ} (w : ℝ) (t : ℕ) (x : State L N) : ℝ :=
  if largest x ≤ t then
    ∑ i, ((if 1 ≤ occ x i ∧ occ x (right i) = t then w else 0) +
      (if 2 ≤ occ x i ∧ t < occ x i + occ x (right i) then 1 else 0))
  else 0

private theorem indicatorCutoff_generator_below_eq {L N : ℕ} (hL : 3 ≤ L)
    (w : ℝ) (t : ℕ) (x : State L N) (hx : largest x ≤ t) :
    generator w (largestCutoff t (fun _ => 1)) x = largestCutoffEntryRate w t x := by
  have hx' : ¬ t < largest x := not_lt_of_ge hx
  unfold generator largestCutoffEntryRate
  rw [if_pos hx]
  apply Finset.sum_congr rfl
  intro i _
  have hchip (hc : 1 ≤ occ x i) :
      t < largest (move x i 1 hc) ↔ occ x (right i) = t := by
    rw [largest_move_above_iff hL t x hx]
    have hright := (occ_le_largest x (right i)).trans hx
    omega
  have hwhole :
      t < largest (move x i (occ x i) le_rfl) ↔ t < occ x i + occ x (right i) := by
    rw [largest_move_above_iff hL t x hx, Nat.add_comm]
  unfold atSite largestCutoff
  by_cases hc : 1 ≤ occ x i
  · by_cases hm : 2 ≤ occ x i
    · by_cases hd : occ x (right i) = t <;> by_cases hs : t < occ x i + occ x (right i) <;>
        simp [hc, hm, hx', hchip hc, hwhole, hd, hs]
    · by_cases hd : occ x (right i) = t <;> simp [hc, hm, hx', hchip hc, hd]
  · have hm : ¬ 2 ≤ occ x i := by omega
    simp [hc, hm]

/-- For a majority cutoff, the only negative drift of its indicator is the
chip of the unique peak at mass `t + 1`. -/
theorem generator_majorityIndicator_eq {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    (w : ℝ) (t : ℕ) (ht : N < 2 * t) (x : State L N) :
    generator w (largestCutoff t (fun _ => 1)) x =
      largestCutoffEntryRate w t x - (if largest x = t + 1 then w else 0) := by
  by_cases hx : t < largest x
  · have hsite (i : Fin L) : atSite w (largestCutoff t (fun _ => 1)) x i =
        -(if i = peakSite x ∧ largest x = t + 1 then w else 0) := by
      have hwhole : t < largest (move x i (occ x i) le_rfl) :=
        hx.trans_le (largest_le_largest_whole_move hL x i)
      unfold atSite largestCutoff
      simp only [if_pos hx, if_pos hwhole, sub_self, ite_self, add_zero]
      by_cases hc : 1 ≤ occ x i
      · have heq := chip_exits_majority_cutoff_iff hL t ht x hx i hc
        by_cases hb : i = peakSite x ∧ largest x = t + 1
        · have hnot := not_lt_of_ge (heq.mpr hb)
          simp only [dif_pos hc, if_neg hnot, if_pos hb, zero_sub, mul_neg, mul_one]
        · have hpos := lt_of_not_ge (fun h => hb (heq.mp h))
          simp [hc, hb, hpos]
      · have hb : ¬(i = peakSite x ∧ largest x = t + 1) := by
          rintro ⟨hi, hmass⟩
          apply hc
          rw [hi, occ_peakSite, hmass]
          omega
        simp [hc, hb]
    unfold generator
    simp_rw [hsite]
    rw [Finset.sum_neg_distrib]
    by_cases hb : largest x = t + 1 <;> simp [largestCutoffEntryRate, not_le_of_gt hx, hb]
  · rw [indicatorCutoff_generator_below_eq hL w t x (le_of_not_gt hx)]
    have hne : largest x ≠ t + 1 := by omega
    simp [hne]

/-- Under stationarity, the rate of entry into a majority region equals the
rate of chips from the mass level immediately above its boundary. -/
theorem stationary_majority_cutoff_flow_eq {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (μ : StationaryLaw L N w) (t : ℕ) (ht : N < 2 * t) :
    (∑ x, μ.weight x * largestCutoffEntryRate w t x) =
      w * (∑ x, if largest x = t + 1 then μ.weight x else 0) := by
  have h := μ.invariant (largestCutoff t (fun _ => 1))
  have hterm (x : State L N) :
      μ.weight x * (if largest x = t + 1 then w else 0) =
        w * (if largest x = t + 1 then μ.weight x else 0) := by
    split_ifs <;> ring
  simp_rw [generator_majorityIndicator_eq hL w t ht, mul_sub, hterm,
    Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  exact sub_eq_zero.mp h

private theorem sum_cutoff_boundary_weights {L N : ℕ} {w : ℝ}
    (μ : StationaryLaw L N w) (a b : ℕ) :
    (∑ t ∈ Finset.Icc a b, ∑ x, if largest x = t + 1 then μ.weight x else 0) =
      ∑ x, if a < largest x ∧ largest x ≤ b + 1 then μ.weight x else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hm : largest x = 0
  · simp [hm]
  · have hcut (t : ℕ) : largest x = t + 1 ↔ t = largest x - 1 := by omega
    have hmem : largest x - 1 ∈ Finset.Icc a b ↔ a < largest x ∧ largest x ≤ b + 1 := by
      rw [Finset.mem_Icc]
      omega
    simp only [hcut, Finset.sum_ite_eq', hmem]

/-- Over a band of majority cutoffs, the total stationary entry flux is the
chip rate times the probability of the corresponding band of mass levels. -/
theorem stationary_majority_cutoff_band_flow_eq {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (μ : StationaryLaw L N w) (a b : ℕ) (ha : N < 2 * a) :
    (∑ t ∈ Finset.Icc a b, ∑ x, μ.weight x * largestCutoffEntryRate w t x) =
      w * (∑ x, if a < largest x ∧ largest x ≤ b + 1 then μ.weight x else 0) := by
  calc
    _ = ∑ t ∈ Finset.Icc a b,
        (w * (∑ x, if largest x = t + 1 then μ.weight x else 0)) := by
      apply Finset.sum_congr rfl
      intro t ht
      have hat := (Finset.mem_Icc.mp ht).1
      exact stationary_majority_cutoff_flow_eq hL μ t (by omega)
    _ = _ := by rw [← Finset.mul_sum, sum_cutoff_boundary_weights]

/-- Choose a cutoff whose boundary probability is at most the mean over the
band. The level at the boundary of cutoff `t` is `t + 1`. -/
theorem exists_cutoff_with_small_boundary {L N : ℕ} {w : ℝ}
    (μ : StationaryLaw L N w) (a b : ℕ) (hab : a ≤ b) :
    ∃ t ∈ Finset.Icc a b,
      (∑ x, if largest x = t + 1 then μ.weight x else 0) ≤
        (∑ x, if a < largest x ∧ largest x ≤ b + 1 then μ.weight x else 0) /
          ((b + 1 - a : ℕ) : ℝ) := by
  let p : ℝ := ∑ x, if a < largest x ∧ largest x ≤ b + 1 then μ.weight x else 0
  let c : ℝ := ((b + 1 - a : ℕ) : ℝ)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (show b + 1 - a ≠ 0 by omega)
  have hs : (Finset.Icc a b).Nonempty := ⟨a, Finset.mem_Icc.mpr ⟨le_rfl, hab⟩⟩
  have hsum :
      (∑ t ∈ Finset.Icc a b, ∑ x, if largest x = t + 1 then μ.weight x else 0) ≤
        ∑ _t ∈ Finset.Icc a b, p / c := by
    rw [sum_cutoff_boundary_weights, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    change p ≤ c * (p / c)
    field_simp [hc]
  exact Finset.exists_le_of_sum_le hs hsum

/-- One majority cutoff in any given band has both a small entry flux and
a small error bound for every moving-frame flow equation. -/
theorem exists_majority_cutoff_with_small_error {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (a b : ℕ)
    (ha : N < 2 * a) (hab : a ≤ b) :
    ∃ t ∈ Finset.Icc a b,
      (∑ x, μ.weight x * largestCutoffEntryRate w t x) ≤
        w * ((∑ x, if a < largest x ∧ largest x ≤ b + 1 then μ.weight x else 0) /
          ((b + 1 - a : ℕ) : ℝ)) ∧
      w * ((N - t : ℕ) : ℝ) * (∑ x, if largest x = t + 1 then μ.weight x else 0) ≤
        w * ((N - a : ℕ) : ℝ) *
          ((∑ x, if a < largest x ∧ largest x ≤ b + 1 then μ.weight x else 0) /
            ((b + 1 - a : ℕ) : ℝ)) := by
  obtain ⟨t, ht, hprob⟩ := exists_cutoff_with_small_boundary μ a b hab
  have hat := (Finset.mem_Icc.mp ht).1
  refine ⟨t, ht, ?_, ?_⟩
  · rw [stationary_majority_cutoff_flow_eq hL μ t (by omega)]
    exact mul_le_mul_of_nonneg_left hprob hw
  · have hnonneg : 0 ≤ ∑ x, if largest x = t + 1 then μ.weight x else 0 := by
      apply Finset.sum_nonneg
      intro x _
      split_ifs
      · exact μ.nonneg x
      · rfl
    have hmass : ((N - t : ℕ) : ℝ) ≤ ((N - a : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le_sub_left hat N
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass hw) hnonneg).trans
      (mul_le_mul_of_nonneg_left hprob (mul_nonneg hw (by positivity)))

/-- At any cutoff, chips from the next mass level bound the entry flux.
For majority cutoffs this is the equality above. -/
theorem stationary_cutoff_entry_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L) {w : ℝ}
    (hw : 0 ≤ w) (μ : StationaryLaw L N w) (t : ℕ) :
    (∑ x, μ.weight x * largestCutoffEntryRate w t x) ≤
      w * (∑ x, if largest x = t + 1 then μ.weight x else 0) := by
  have hpoint (x : State L N) :
      μ.weight x * largestCutoffEntryRate w t x - w * (if largest x = t + 1 then μ.weight x else 0) ≤
        μ.weight x * generator w (largestCutoff t (fun _ => 1)) x := by
    by_cases hx : t < largest x
    · have h := generator_largestCutoff_ge hL hw t
        (fun _ : State L N => (1 : ℝ)) (b := 1) zero_le_one
        (fun _ _ => zero_le_one) (fun _ _ => le_rfl) x
      have hzero : generator w (fun _ : State L N => 1) x = 0 := by
        unfold generator
        apply Finset.sum_eq_zero
        intro i _
        unfold atSite
        split_ifs <;> ring
      have hweighted := mul_le_mul_of_nonneg_left h (μ.nonneg x)
      by_cases hb : largest x = t + 1 <;>
        simpa [largestCutoffEntryRate, not_le_of_gt hx, hx, hzero, hb, mul_sub, mul_comm w]
          using hweighted
    · have hb : largest x ≠ t + 1 := by omega
      simp [hb, indicatorCutoff_generator_below_eq hL w t x (le_of_not_gt hx)]
  apply sub_nonpos.mp
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact (Finset.sum_le_sum (fun x _ => hpoint x)).trans_eq (μ.invariant _)

private theorem largestCutoffEntryRate_nonneg {L N : ℕ} {w : ℝ} (hw : 0 ≤ w)
    (t : ℕ) (x : State L N) : 0 ≤ largestCutoffEntryRate w t x := by
  unfold largestCutoffEntryRate
  split_ifs
  · apply Finset.sum_nonneg
    intro i _
    split_ifs <;> linarith
  · rfl

private theorem one_le_largestCutoffEntryRate_of_merge {L N : ℕ} {w : ℝ}
    (hw : 0 ≤ w) (t : ℕ) (x : State L N) (hx : largest x ≤ t) (i : Fin L)
    (hmerge : 2 ≤ occ x i ∧ t < occ x i + occ x (right i)) :
    1 ≤ largestCutoffEntryRate w t x := by
  unfold largestCutoffEntryRate
  rw [if_pos hx]
  let f (j : Fin L) : ℝ := (if 1 ≤ occ x j ∧ occ x (right j) = t then w else 0) +
    (if 2 ≤ occ x j ∧ t < occ x j + occ x (right j) then 1 else 0)
  have hnonneg (j : Fin L) : 0 ≤ f j := by
    dsimp [f]
    split_ifs <;> linarith
  have hi : 1 ≤ f i := by
    dsimp [f]
    rw [if_pos hmerge]
    split_ifs <;> linarith
  exact hi.trans (Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i))

/-- From level `m`, an immediate neighbour of mass at least `d` would allow
a whole pile jump above level `m + d - 1`. Its probability is bounded by
the chip rate times the stationary probability at level `m + d`. -/
theorem stationary_peak_neighbour_level_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (m d : ℕ) (hm : 2 ≤ m) (hd : 0 < d) :
    (∑ x, if largest x = m ∧ d ≤ occ x (right (peakSite x)) then μ.weight x else 0) ≤
      w * (∑ x, if largest x = m + d then μ.weight x else 0) := by
  let t := m + d - 1
  have ht : t + 1 = m + d := by omega
  have hflow := stationary_cutoff_entry_le hL hw μ t
  rw [ht] at hflow
  refine le_trans ?_ hflow
  apply Finset.sum_le_sum
  intro x _
  split_ifs with hx
  · have hpeak := occ_peakSite x
    have hentry : 1 ≤ largestCutoffEntryRate w t x :=
      one_le_largestCutoffEntryRate_of_merge hw t x (by dsimp [t]; omega) (peakSite x)
        ⟨by omega, by dsimp [t]; omega⟩
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hentry (μ.nonneg x)
  · exact mul_nonneg (μ.nonneg x) (largestCutoffEntryRate_nonneg hw t x)

end
end Chipping
