import ChippingSupercondensation.Identities

/-!
# Coalescence of large piles

The sites above a mass cutoff follow the rate-one clockwise coalescing update,
except for chips that cross the cutoff and mergers of two smaller piles. Summed
over a band of cutoffs the exception rate is controlled, so one cutoff in the
band has small mean coalescence drift for every bounded test. Under pure
coalescence the empty-window potential has drift at least two when two or more
sites are marked. `stationary_twoLargePilesProbability_le_birthDamage` then
bounds the probability of two large piles by births weighted by the empty
windows they erase.
-/

namespace Chipping

open Filter
open scoped BigOperators Topology

noncomputable section

private def chipThresholdCountAt {L N : ℕ} (k : ℕ) (x : State L N) (i : Fin L) : ℝ :=
  (if occ x i = k + 1 then 1 else 0) + (if occ x (right i) = k then 1 else 0)

def wholeThresholdBirthAt {L N : ℕ} (k : ℕ) (x : State L N) (i : Fin L) : ℝ :=
  if 2 ≤ occ x i ∧ occ x i ≤ k ∧ occ x (right i) ≤ k ∧
    k < occ x i + occ x (right i) then 1 else 0

/-- A rate bound for moves that change the set of sites above `k` in ways
other than whole-pile coalescence. Inactive chip clocks are included in the
bound, and a chip that changes both sites can be counted twice. -/
def thresholdExceptionRate {L N : ℕ} (w : ℝ) (k : ℕ) (x : State L N) : ℝ :=
  w * (∑ i, chipThresholdCountAt k x i) + ∑ i, wholeThresholdBirthAt k x i

theorem sum_threshold_hits_le (a b m s : ℕ) (ha : 0 < a) :
    (∑ k ∈ Finset.Icc a b, (if m = k + s then (1 : ℝ) else 0)) ≤ (m : ℝ) / (a : ℝ) := by
  by_cases hm : s ≤ m
  · have hiff (k : ℕ) : m = k + s ↔ k = m - s := by omega
    simp only [hiff, Finset.sum_ite_eq']
    split_ifs with h
    · have hmass : a ≤ m := by have := (Finset.mem_Icc.mp h).1; omega
      apply (le_div_iff₀ (by exact_mod_cast ha : (0 : ℝ) < (a : ℝ))).mpr
      simpa only [one_mul] using (show (a : ℝ) ≤ (m : ℝ) by exact_mod_cast hmass)
    · positivity
  · have hzero (k : ℕ) : m ≠ k + s := by omega
    simp [hzero]
    positivity

private theorem sum_wholeThresholdBirth_le (a b u v : ℕ) (ha : 0 < a) :
    (∑ k ∈ Finset.Icc a b, (if 2 ≤ u ∧ u ≤ k ∧ v ≤ k ∧ k < u + v then (1 : ℝ) else 0)) ≤
      (2 / (a : ℝ)) * (if 2 ≤ u then (u : ℝ) * (v : ℝ) else 0) := by
  classical
  let good (k : ℕ) := 2 ≤ u ∧ u ≤ k ∧ v ≤ k ∧ k < u + v
  change (∑ k ∈ Finset.Icc a b, if good k then (1 : ℝ) else 0) ≤ _
  by_cases he : ∃ k ∈ Finset.Icc a b, good k
  · obtain ⟨k, hk, hu, _, _, hsum⟩ := he
    have hlow : a ≤ u + v := ((Finset.mem_Icc.mp hk).1).trans hsum.le
    have hsubset : (Finset.Icc a b).filter good ⊆ Finset.Ico (max u v) (u + v) := by
      intro j hj
      obtain ⟨_, hj'⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_Ico.mpr ⟨max_le hj'.2.1 hj'.2.2.1, hj'.2.2.2⟩
    have hcount : (∑ j ∈ Finset.Icc a b, if good j then (1 : ℝ) else 0) ≤ (min u v : ℕ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hcard := Finset.card_le_card hsubset
      rw [Nat.card_Ico] at hcard
      have hmin : u + v - max u v = min u v := by omega
      rw [hmin] at hcard
      exact_mod_cast hcard
    refine hcount.trans ?_
    have hmul : (a : ℝ) * ((min u v : ℕ) : ℝ) ≤ 2 * ((u : ℝ) * (v : ℝ)) := by
      by_cases huv : u ≤ v
      · rw [min_eq_left huv]
        have hv : (a : ℝ) ≤ 2 * (v : ℝ) := by exact_mod_cast (show a ≤ 2 * v by omega)
        nlinarith only [mul_le_mul_of_nonneg_right hv (show 0 ≤ (u : ℝ) by positivity)]
      · rw [min_eq_right (le_of_not_ge huv)]
        have hu' : (a : ℝ) ≤ 2 * (u : ℝ) := by exact_mod_cast (show a ≤ 2 * u by omega)
        nlinarith only [mul_le_mul_of_nonneg_right hu' (show 0 ≤ (v : ℝ) by positivity)]
    rw [if_pos hu, div_mul_eq_mul_div]
    apply (le_div_iff₀ (by exact_mod_cast ha : (0 : ℝ) < (a : ℝ))).mpr
    simpa only [mul_comm _ (a : ℝ)] using hmul
  · have hzero : (∑ j ∈ Finset.Icc a b, if good j then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact if_neg (fun h => he ⟨j, hj, h⟩)
    rw [hzero]
    apply mul_nonneg (by positivity)
    split_ifs <;> positivity

private theorem thresholdExceptionRate_band_le {L N : ℕ} [NeZero L] {w : ℝ}
    (hw : 0 ≤ w) (a b : ℕ) (ha : 0 < a) (x : State L N) :
    (∑ k ∈ Finset.Icc a b, thresholdExceptionRate w k x) ≤
      w * (2 * (N : ℝ) / (a : ℝ)) + (2 / (a : ℝ)) * wholePileSquaredMassGain x := by
  have hmass : (∑ i, (occ x i : ℝ)) = (N : ℝ) := by exact_mod_cast x.property
  have hright : (∑ i, (occ x (right i) : ℝ)) = (N : ℝ) := by
    simp only [right_eq_add_one]
    exact (Equiv.sum_comp (Equiv.addRight (1 : Fin L)) (fun i => (occ x i : ℝ))).trans hmass
  have hchips : (∑ k ∈ Finset.Icc a b, ∑ i, chipThresholdCountAt k x i) ≤
      2 * (N : ℝ) / (a : ℝ) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ i, ((occ x i : ℝ) / (a : ℝ) + (occ x (right i) : ℝ) / (a : ℝ)) := by
        apply Finset.sum_le_sum
        intro i _
        unfold chipThresholdCountAt
        rw [Finset.sum_add_distrib]
        exact add_le_add (sum_threshold_hits_le a b (occ x i) 1 ha)
          (by simpa only [Nat.add_zero] using sum_threshold_hits_le a b (occ x (right i)) 0 ha)
      _ = _ := by
        simp only [Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.sum_mul, hmass, hright]
        ring
  have hwhole : (∑ k ∈ Finset.Icc a b, ∑ i, wholeThresholdBirthAt k x i) ≤
      (2 / (a : ℝ)) * wholePileSquaredMassGain x := by
    unfold wholePileSquaredMassGain
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => sum_wholeThresholdBirth_le a b (occ x i) (occ x (right i)) ha)
  unfold thresholdExceptionRate
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact add_le_add (mul_le_mul_of_nonneg_left hchips hw) hwhole

/-- The stationary mean rate bound at a given cutoff. -/
def meanThresholdExceptionRate {L N : ℕ} {w : ℝ}
    (μ : StationaryLaw L N w) (k : ℕ) : ℝ :=
  ∑ x, μ.weight x * thresholdExceptionRate w k x

/-- Summing over a cutoff band costs at most `4 * w * N / a`, regardless of
the number of cutoffs. The whole-pile term uses the stationary adjacent mass
product bound, rather than bounding the number of cutoff crossings separately. -/
theorem stationary_thresholdExceptionRate_band_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (a b : ℕ) (ha : 0 < a) :
    (∑ k ∈ Finset.Icc a b, meanThresholdExceptionRate μ k) ≤ 4 * w * (N : ℝ) / (a : ℝ) := by
  unfold meanThresholdExceptionRate
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ x, μ.weight x * (w * (2 * (N : ℝ) / (a : ℝ)) +
        (2 / (a : ℝ)) * wholePileSquaredMassGain x) := by
      exact Finset.sum_le_sum (fun x _ =>
        mul_le_mul_of_nonneg_left (thresholdExceptionRate_band_le hw a b ha x) (μ.nonneg x))
    _ = w * (2 * (N : ℝ) / (a : ℝ)) +
        (2 / (a : ℝ)) * ∑ x, μ.weight x * wholePileSquaredMassGain x := by
      simp_rw [mul_add, Finset.sum_add_distrib, mul_left_comm _ (2 / (a : ℝ)), ← Finset.mul_sum]
      rw [← Finset.sum_mul, μ.normalized, one_mul]
    _ ≤ w * (2 * (N : ℝ) / (a : ℝ)) + (2 / (a : ℝ)) * (w * (N : ℝ)) :=
      add_le_add_left (mul_le_mul_of_nonneg_left (stationary_wholePileSquaredMassGain_le hL hw μ)
        (by positivity)) _
    _ = _ := by ring

/-- In any positive cutoff band, some cutoff has a small rate of departures
from pure coalescence. For a band of macroscopic masses this rate is `O(1/N)`. -/
theorem exists_threshold_with_small_exceptionRate {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ k ∈ Finset.Icc a b, meanThresholdExceptionRate μ k ≤
      (4 * w * (N : ℝ) / (a : ℝ)) / ((b + 1 - a : ℕ) : ℝ) := by
  let c : ℝ := ((b + 1 - a : ℕ) : ℝ)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (show b + 1 - a ≠ 0 by omega)
  have hs : (Finset.Icc a b).Nonempty := ⟨a, Finset.mem_Icc.mpr ⟨le_rfl, hab⟩⟩
  apply Finset.exists_le_of_sum_le hs
  have hmean : (∑ _k ∈ Finset.Icc a b, (4 * w * (N : ℝ) / (a : ℝ)) / c) =
      4 * w * (N : ℝ) / (a : ℝ) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    change c * _ = _
    rw [mul_comm, div_mul_cancel₀ _ hc]
  rw [hmean]
  exact stationary_thresholdExceptionRate_band_le hL hw μ a b ha

/-- Keep only the locations of piles whose mass is strictly greater than `k`. -/
def largePileMask {L N : ℕ} (k : ℕ) (x : State L N) (j : Fin L) : Bool :=
  decide (k < occ x j)

/-- A rate-one coalescing walk sends the bit at `i` one site clockwise. If
that site is already occupied, the two bits merge. -/
def coalesceMask {L : ℕ} (s : Fin L → Bool) (i j : Fin L) : Bool :=
  if j = i then false else if j = right i then s i || s j else s j

private theorem largePileMask_chipOrStay_eq {L N : ℕ} (hL : 3 ≤ L)
    (k : ℕ) (x : State L N) (i : Fin L)
    (ha : occ x i ≠ k + 1) (hb : occ x (right i) ≠ k) :
    largePileMask k (chipOrStay x i) = largePileMask k x := by
  unfold chipOrStay
  by_cases hi : 1 ≤ occ x i
  · rw [dif_pos hi]
    funext j
    unfold largePileMask
    by_cases hj : j = i
    · subst j
      have hiff : k < occ x i - 1 ↔ k < occ x i := by omega
      simp [occ_move, transfer, Ne.symm (right_ne_self hL i), hiff]
    · by_cases hr : j = right i
      · subst j
        have hiff : k < occ x (right i) + 1 ↔ k < occ x (right i) := by omega
        simp [occ_move_right hL, hiff]
      · simp [occ_move, transfer, hj, hr]
  · rw [dif_neg hi]

private theorem largePileMask_wholePileOrStay_eq {L N : ℕ} (hL : 3 ≤ L)
    (k : ℕ) (hk : 1 ≤ k) (x : State L N) (i : Fin L)
    (hn : ¬(2 ≤ occ x i ∧ occ x i ≤ k ∧ occ x (right i) ≤ k ∧
      k < occ x i + occ x (right i))) :
    largePileMask k (wholePileOrStay x i) = coalesceMask (largePileMask k x) i := by
  unfold wholePileOrStay
  by_cases hm : 2 ≤ occ x i
  · rw [if_pos hm]
    funext j
    by_cases hj : j = i
    · subst j
      simp [largePileMask, coalesceMask, occ_move, transfer, Ne.symm (right_ne_self hL i)]
    · by_cases hr : j = right i
      · subst j
        have hiff : k < occ x i + occ x (right i) ↔ k < occ x i ∨ k < occ x (right i) := by
          omega
        simp [largePileMask, coalesceMask, hj, occ_move_right hL, Nat.add_comm (occ x (right i)), hiff]
      · simp [largePileMask, coalesceMask, occ_move, transfer, hj, hr]
  · rw [if_neg hm]
    have hsmall : ¬ k < occ x i := by omega
    funext j
    by_cases hj : j = i <;> by_cases hr : j = right i <;>
      simp [largePileMask, coalesceMask, hj, hr, hsmall, right_ne_self hL i]

/-- Generator of rate-one clockwise coalescence on sets of large sites. -/
def maskCoalescenceGenerator {L : ℕ} (f : (Fin L → Bool) → ℝ) (s : Fin L → Bool) : ℝ :=
  ∑ i, (f (coalesceMask s i) - f s)

private theorem thresholdMask_atSite_difference_le {L N : ℕ} (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (k : ℕ) (hk : 1 ≤ k) (f : (Fin L → Bool) → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ s t, |f s - f t| ≤ C) (x : State L N) (i : Fin L) :
    |atSite w (fun y => f (largePileMask k y)) x i -
      (f (coalesceMask (largePileMask k x) i) - f (largePileMask k x))| ≤
        C * (w * chipThresholdCountAt k x i + wholeThresholdBirthAt k x i) := by
  let g := fun y : State L N => f (largePileMask k y)
  let c := f (coalesceMask (largePileMask k x) i)
  change |atSite w g x i - (c - g x)| ≤ _
  have hg : atSite w g x i =
      w * (g (chipOrStay x i) - g x) + (g (wholePileOrStay x i) - g x) := by
    unfold atSite chipOrStay wholePileOrStay
    by_cases ha : 1 ≤ occ x i <;> by_cases hb : 2 ≤ occ x i <;> simp [ha, hb]
  have hc : |g (chipOrStay x i) - g x| ≤ C * chipThresholdCountAt k x i := by
    have h := hf (largePileMask k (chipOrStay x i)) (largePileMask k x)
    by_cases ha : occ x i = k + 1
    · by_cases hb : occ x (right i) = k
      · simp only [chipThresholdCountAt, if_pos ha, if_pos hb]
        dsimp [g]
        linarith
      · simpa only [g, chipThresholdCountAt, if_pos ha, if_neg hb, add_zero, mul_one] using h
    · by_cases hb : occ x (right i) = k
      · simpa only [g, chipThresholdCountAt, if_neg ha, if_pos hb, zero_add, mul_one] using h
      · simp [g, largePileMask_chipOrStay_eq hL k x i ha hb, chipThresholdCountAt, ha, hb]
  have hm : |g (wholePileOrStay x i) - c| ≤ C * wholeThresholdBirthAt k x i := by
    unfold wholeThresholdBirthAt
    split_ifs with h
    · simpa only [mul_one, g, c] using hf (largePileMask k (wholePileOrStay x i))
        (coalesceMask (largePileMask k x) i)
    · simp [g, c, largePileMask_wholePileOrStay_eq hL k hk x i h]
  rw [hg, show w * (g (chipOrStay x i) - g x) + (g (wholePileOrStay x i) - g x) - (c - g x) =
    w * (g (chipOrStay x i) - g x) + (g (wholePileOrStay x i) - c) by ring]
  calc
    _ ≤ |w * (g (chipOrStay x i) - g x)| + |g (wholePileOrStay x i) - c| := abs_add_le _ _
    _ ≤ w * (C * chipThresholdCountAt k x i) + C * wholeThresholdBirthAt k x i := by
      rw [abs_mul, abs_of_nonneg hw]
      exact add_le_add (mul_le_mul_of_nonneg_left hc hw) hm
    _ = _ := by ring

/-- Under a stationary chipping law, the large-pile mask has small mean drift
for the pure coalescing generator. Only threshold exceptions contribute. -/
theorem stationary_maskCoalescence_drift_abs_le {L N : ℕ} (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (k : ℕ) (hk : 1 ≤ k)
    (f : (Fin L → Bool) → ℝ) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ s t, |f s - f t| ≤ C) :
    |∑ x, μ.weight x * maskCoalescenceGenerator f (largePileMask k x)| ≤
      C * meanThresholdExceptionRate μ k := by
  let g := fun x : State L N => f (largePileMask k x)
  let q := fun x : State L N => maskCoalescenceGenerator f (largePileMask k x)
  change |∑ x, μ.weight x * q x| ≤ _
  have hpoint (x : State L N) : |generator w g x - q x| ≤ C * thresholdExceptionRate w k x := by
    unfold generator q maskCoalescenceGenerator
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, |atSite w g x i - (f (coalesceMask (largePileMask k x) i) - f (largePileMask k x))| :=
        Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ i, C * (w * chipThresholdCountAt k x i + wholeThresholdBirthAt k x i) :=
        Finset.sum_le_sum (fun i _ => thresholdMask_atSite_difference_le hL hw k hk f hC hf x i)
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, thresholdExceptionRate]
  have hdiff : (∑ x, μ.weight x * (generator w g x - q x)) = -(∑ x, μ.weight x * q x) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, μ.invariant g, zero_sub]
  calc
    _ = |∑ x, μ.weight x * (generator w g x - q x)| := by rw [hdiff, abs_neg]
    _ ≤ ∑ x, |μ.weight x * (generator w g x - q x)| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ x, μ.weight x * (C * thresholdExceptionRate w k x) := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul, abs_of_nonneg (μ.nonneg x)]
      exact mul_le_mul_of_nonneg_left (hpoint x) (μ.nonneg x)
    _ = _ := by
      unfold meanThresholdExceptionRate
      simp_rw [mul_left_comm _ C, ← Finset.mul_sum]

/-- A single chosen cutoff makes every bounded test on the large-pile mask
approximately invariant for rate-one coalescence. -/
theorem exists_threshold_maskCoalescence_small_drift {L N : ℕ} [NeZero L]
    (hL : 3 ≤ L) {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w)
    (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ k ∈ Finset.Icc a b, ∀ (f : (Fin L → Bool) → ℝ) (C : ℝ), 0 ≤ C →
      (∀ s t, |f s - f t| ≤ C) →
        |∑ x, μ.weight x * maskCoalescenceGenerator f (largePileMask k x)| ≤
          C * ((4 * w * (N : ℝ) / (a : ℝ)) / ((b + 1 - a : ℕ) : ℝ)) := by
  obtain ⟨k, hk, hrate⟩ := exists_threshold_with_small_exceptionRate hL hw μ a b ha hab
  have hak := (Finset.mem_Icc.mp hk).1
  refine ⟨k, hk, fun f C hC hf => ?_⟩
  exact (stationary_maskCoalescence_drift_abs_le hL hw μ k (by omega) f hC hf).trans
    (mul_le_mul_of_nonneg_left hrate hC)

/-- At a cutoff chosen from a band whose lower end and width are both
proportional to the total mass, the coalescence drift error is inverse in mass. -/
theorem exists_macroscopic_threshold_maskCoalescence_small_drift {L N : ℕ} [NeZero L]
    (hL : 3 ≤ L) {w α β : ℝ} (hw : 0 ≤ w) (hN : 0 < N) (hα : 0 < α) (hβ : 0 < β)
    (μ : StationaryLaw L N w) (a b : ℕ) (hab : a ≤ b)
    (halow : α * (N : ℝ) ≤ (a : ℝ)) (hwidth : β * (N : ℝ) ≤ ((b + 1 - a : ℕ) : ℝ)) :
    ∃ k ∈ Finset.Icc a b, ∀ (f : (Fin L → Bool) → ℝ) (C : ℝ), 0 ≤ C →
      (∀ s t, |f s - f t| ≤ C) →
        |∑ x, μ.weight x * maskCoalescenceGenerator f (largePileMask k x)| ≤
          C * (4 * w / (α * β * (N : ℝ))) := by
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have halo : (0 : ℝ) < (a : ℝ) := (mul_pos hα hNreal).trans_le halow
  have ha : 0 < a := by exact_mod_cast halo
  obtain ⟨k, hk, h⟩ := exists_threshold_maskCoalescence_small_drift hL hw μ a b ha hab
  have hscale : (4 * w * (N : ℝ) / (a : ℝ)) / ((b + 1 - a : ℕ) : ℝ) ≤
      4 * w / (α * β * (N : ℝ)) := by
    have hpos : 0 < (α * (N : ℝ)) * (β * (N : ℝ)) :=
      mul_pos (mul_pos hα hNreal) (mul_pos hβ hNreal)
    rw [div_div]
    calc
      _ ≤ 4 * w * (N : ℝ) / ((α * (N : ℝ)) * (β * (N : ℝ))) :=
        div_le_div_of_nonneg_left (by positivity) hpos
          (mul_le_mul halow hwidth (by positivity) (by positivity))
      _ = _ := by
        field_simp [hα.ne', hβ.ne', hNreal.ne']
        ring
  exact ⟨k, hk, fun f C hC hf => (h f C hC hf).trans (mul_le_mul_of_nonneg_left hscale hC)⟩

/-- The cutoff can be chosen independently of the test. Along a sequence,
the mean coalescence drift vanishes even for tests whose oscillation grows
sublinearly in the total mass. -/
theorem exists_macroscopic_threshold_maskCoalescence_vanishing_drift
    {L N a b : ℕ → ℕ} [∀ n, NeZero (L n)] {w α β : ℝ} (hw : 0 ≤ w)
    (hα : 0 < α) (hβ : 0 < β) (hL : ∀ n, 3 ≤ L n) (hN : ∀ n, 0 < N n)
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w)
    (hab : ∀ n, a n ≤ b n) (halow : ∀ n, α * (N n : ℝ) ≤ (a n : ℝ))
    (hwidth : ∀ n, β * (N n : ℝ) ≤ ((b n + 1 - a n : ℕ) : ℝ)) :
    ∃ k : ℕ → ℕ, (∀ n, k n ∈ Finset.Icc (a n) (b n)) ∧
      ∀ (f : (n : ℕ) → (Fin (L n) → Bool) → ℝ) (C : ℕ → ℝ),
        (∀ n, 0 ≤ C n) → (∀ n s t, |f n s - f n t| ≤ C n) →
        Tendsto (fun n => C n / (N n : ℝ)) atTop (𝓝 0) →
        Tendsto (fun n => ∑ x, (μ n).weight x *
          maskCoalescenceGenerator (f n) (largePileMask (k n) x)) atTop (𝓝 0) := by
  choose k hk hbound using fun n =>
    exists_macroscopic_threshold_maskCoalescence_small_drift (hL n) hw (hN n) hα hβ
      (μ n) (a n) (b n) (hab n) (halow n) (hwidth n)
  refine ⟨k, hk, fun f C hC hf hscale => ?_⟩
  let e (n : ℕ) := C n * (4 * w / (α * β * (N n : ℝ)))
  have he : Tendsto e atTop (𝓝 0) := by
    have h : Tendsto (fun n => (4 * w / (α * β)) * (C n / (N n : ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds (x := 4 * w / (α * β))).mul hscale
    refine h.congr (fun n => ?_)
    dsimp [e]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
    ring
  have hneg : Tendsto (fun n => -e n) atTop (𝓝 0) := by simpa only [neg_zero] using he.neg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hneg he
    (fun n => (abs_le.mp (hbound n (f n) (C n) (hC n) (hf n))).1)
    (fun n => (abs_le.mp (hbound n (f n) (C n) (hC n) (hf n))).2)

def bitMass (b : Bool) : ℕ := if b then 1 else 0

def maskWindowMass {L : ℕ} [NeZero L] (r : ℕ) (s : Fin L → Bool) (j : Fin L) : ℝ :=
  ∑ t ∈ Finset.range r, (bitMass (s (j - (t : Fin L))) : ℝ)

def emptyMaskWindowAt {L : ℕ} [NeZero L] (r : ℕ) (s : Fin L → Bool) (j : Fin L) : ℝ :=
  if maskWindowMass r s j = 0 then 1 else 0

/-- The number of clockwise windows of length `r` that contain no marked sites. -/
def emptyMaskWindowCount {L : ℕ} [NeZero L] (r : ℕ) (s : Fin L → Bool) : ℝ :=
  ∑ j, emptyMaskWindowAt r s j

private theorem maskWindowMass_nonneg {L : ℕ} [NeZero L] (r : ℕ) (s : Fin L → Bool) (j : Fin L) :
    0 ≤ maskWindowMass r s j :=
  Finset.sum_nonneg (fun t _ => by positivity)

private theorem bitMass_coalesce_eq_zero_iff {L : ℕ} (hL : 3 ≤ L) (s : Fin L → Bool) (i j : Fin L) :
    bitMass (coalesceMask s i j) = 0 ↔
      transfer (fun t => bitMass (s t)) i (bitMass (s i)) j = 0 := by
  by_cases hj : j = i
  · subst j
    simp [coalesceMask, transfer, bitMass, Ne.symm (right_ne_self hL i)]
  · by_cases hr : j = right i
    · subst j
      cases hi : s i <;> cases ht : s (right i) <;>
        simp [coalesceMask, transfer, bitMass, hj, hi, ht]
    · simp [coalesceMask, transfer, hj, hr]

private theorem maskWindowMass_coalesce_zero_iff {L : ℕ} [NeZero L] (hL : 3 ≤ L)
    (r : ℕ) (s : Fin L → Bool) (i j : Fin L) :
    maskWindowMass r (coalesceMask s i) j = 0 ↔
      (∑ t ∈ Finset.range r, (transfer (fun u => bitMass (s u)) i (bitMass (s i))
        (j - (t : Fin L)) : ℝ)) = 0 := by
  unfold maskWindowMass
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun t _ => by positivity),
    Finset.sum_eq_zero_iff_of_nonneg (fun t _ => by positivity)]
  simp only [Nat.cast_eq_zero, bitMass_coalesce_eq_zero_iff hL]

private theorem maskWindowMass_succ_first {L : ℕ} [NeZero L] (r : ℕ)
    (s : Fin L → Bool) (j : Fin L) :
    maskWindowMass (r + 1) s j = maskWindowMass r s (j - 1) + (bitMass (s j) : ℝ) := by
  unfold maskWindowMass
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, sub_zero, Nat.cast_add, Nat.cast_one]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  congr 3
  abel

private theorem maskWindowMass_succ_last {L : ℕ} [NeZero L] (r : ℕ)
    (s : Fin L → Bool) (j : Fin L) :
    maskWindowMass (r + 1) s j = maskWindowMass r s j + (bitMass (s (j - (r : Fin L))) : ℝ) := by
  unfold maskWindowMass
  exact Finset.sum_range_succ _ _

private theorem empty_indicator_add_bit (m : ℝ) (hm : 0 ≤ m) (b : Bool) :
    (if m = 0 then (1 : ℝ) else 0) - (if m + (bitMass b : ℝ) = 0 then 1 else 0) =
      (if b = true ∧ m = 0 then 1 else 0) := by
  cases b
  · simp [bitMass]
  · have hpos : m + 1 ≠ 0 := by linarith
    simp [bitMass, hpos]

private theorem emptyMaskWindowAt_coalesce_change {L : ℕ} [NeZero L] (hL : 3 ≤ L)
    (r : ℕ) (hr : r + 1 < L) (s : Fin L → Bool) (i j : Fin L) :
    emptyMaskWindowAt (r + 1) (coalesceMask s i) j - emptyMaskWindowAt (r + 1) s j =
      (if j = i then (if s i = true ∧ maskWindowMass r s (i - 1) = 0 then 1 else 0) else 0) -
        (if j = i + ((r + 1 : ℕ) : Fin L) then
          (if s i = true ∧ maskWindowMass (r + 1) s j = 0 then 1 else 0) else 0) := by
  let q : ℝ := ∑ t ∈ Finset.range (r + 1), (transfer (fun u => bitMass (s u)) i (bitMass (s i))
    (j - (t : Fin L)) : ℝ)
  have hq :
      q - maskWindowMass (r + 1) s j = (bitMass (s i) : ℝ) *
        ((if j = i + ((r + 1 : ℕ) : Fin L) then 1 else 0) - (if j = i then 1 else 0)) :=
    transfer_window_sum_change (r + 1) _ i _ le_rfl j
  have hs : i + ((r + 1 : ℕ) : Fin L) ≠ i :=
    fun h => natCast_fin_ne_zero (by omega : 0 < r + 1) hr (add_left_cancel (h.trans (add_zero i).symm))
  unfold emptyMaskWindowAt
  simp only [maskWindowMass_coalesce_zero_iff hL]
  change (if q = 0 then (1 : ℝ) else 0) - _ = _
  by_cases hj : j = i
  · have he : j ≠ i + ((r + 1 : ℕ) : Fin L) := fun h => hs (h.symm.trans hj)
    simp only [if_pos hj, if_neg he, sub_zero] at ⊢
    simp only [if_pos hj, if_neg he] at hq
    rw [hj, maskWindowMass_succ_first] at hq
    have heq : q = maskWindowMass r s (i - 1) := by linarith
    rw [heq, hj, maskWindowMass_succ_first]
    exact empty_indicator_add_bit _ (maskWindowMass_nonneg _ _ _) _
  · by_cases he : j = i + ((r + 1 : ℕ) : Fin L)
    · simp only [if_neg hj, if_pos he, zero_sub] at hq ⊢
      have heq : q = maskWindowMass (r + 1) s j + (bitMass (s i) : ℝ) := by linarith
      rw [heq, ← neg_sub, empty_indicator_add_bit _ (maskWindowMass_nonneg _ _ _) _]
    · simp only [if_neg hj, if_neg he, sub_self, mul_zero] at hq ⊢
      rw [sub_eq_zero.mp hq, sub_self]

/-- Empty windows evolve by the discrete second difference in their length
under pure clockwise coalescence. -/
theorem maskCoalescenceGenerator_emptyMaskWindowCount {L : ℕ} [NeZero L] (hL : 3 ≤ L)
    (r : ℕ) (hr : r + 1 < L) (s : Fin L → Bool) :
    maskCoalescenceGenerator (emptyMaskWindowCount (r + 1)) s =
      emptyMaskWindowCount r s - 2 * emptyMaskWindowCount (r + 1) s +
        emptyMaskWindowCount (r + 2) s := by
  have hsite (i : Fin L) :
      emptyMaskWindowCount (r + 1) (coalesceMask s i) - emptyMaskWindowCount (r + 1) s =
        (emptyMaskWindowAt r s (i - 1) - emptyMaskWindowAt (r + 1) s i) -
          (emptyMaskWindowAt (r + 1) s (i + ((r + 1 : ℕ) : Fin L)) -
            emptyMaskWindowAt (r + 2) s (i + ((r + 1 : ℕ) : Fin L))) := by
    unfold emptyMaskWindowCount
    rw [← Finset.sum_sub_distrib]
    simp_rw [emptyMaskWindowAt_coalesce_change hL r hr s i]
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hleft : emptyMaskWindowAt r s (i - 1) - emptyMaskWindowAt (r + 1) s i =
        (if s i = true ∧ maskWindowMass r s (i - 1) = 0 then 1 else 0) := by
      unfold emptyMaskWindowAt
      rw [maskWindowMass_succ_first]
      exact empty_indicator_add_bit _ (maskWindowMass_nonneg _ _ _) _
    have hright : emptyMaskWindowAt (r + 1) s (i + ((r + 1 : ℕ) : Fin L)) -
        emptyMaskWindowAt (r + 2) s (i + ((r + 1 : ℕ) : Fin L)) =
          (if s i = true ∧ maskWindowMass (r + 1) s (i + ((r + 1 : ℕ) : Fin L)) = 0 then 1 else 0) := by
      unfold emptyMaskWindowAt
      have hadd := maskWindowMass_succ_last (r + 1) s (i + ((r + 1 : ℕ) : Fin L))
      rw [add_sub_cancel_right] at hadd
      rw [show r + 2 = (r + 1) + 1 by omega, hadd]
      exact empty_indicator_add_bit _ (maskWindowMass_nonneg _ _ _) _
    rw [hleft, hright]
  have hsum (d : Fin L) (q : ℕ) :
      (∑ i, emptyMaskWindowAt q s (i + d)) = emptyMaskWindowCount q s :=
    Equiv.sum_comp (Equiv.addRight d) (emptyMaskWindowAt q s)
  have hminus : (∑ i, emptyMaskWindowAt r s (i - 1)) = emptyMaskWindowCount r s := by
    simpa only [sub_eq_add_neg] using hsum (-1) r
  unfold maskCoalescenceGenerator
  simp_rw [hsite]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hminus, hsum, hsum]
  change emptyMaskWindowCount r s - emptyMaskWindowCount (r + 1) s -
    (emptyMaskWindowCount (r + 1) s - emptyMaskWindowCount (r + 2) s) = _
  ring

/-- Number of marked sites. -/
def maskCount {L : ℕ} (s : Fin L → Bool) : ℝ := ∑ i, (bitMass (s i) : ℝ)

private theorem maskWindowMass_full {L : ℕ} [NeZero L] (s : Fin L → Bool) (j : Fin L) :
    maskWindowMass L s j = maskCount s := by
  unfold maskWindowMass maskCount
  rw [← Fin.sum_univ_eq_sum_range (fun r => (bitMass (s (j - (r : Fin L))) : ℝ)) L]
  have hcast (i : Fin L) : (i.val : Fin L) = i := by
    apply Fin.ext
    rw [Fin.val_natCast, Nat.mod_eq_of_lt i.isLt]
  simp_rw [hcast, sub_eq_add_neg]
  calc
    _ = ∑ i : Fin L, (bitMass (s (j + i)) : ℝ) := Equiv.sum_comp (Equiv.neg (Fin L)) _
    _ = _ := Equiv.sum_comp (Equiv.addLeft j) (fun i => (bitMass (s i) : ℝ))

/-- Total number of empty windows of all proper positive lengths. -/
def emptyMaskWindowPotential {L : ℕ} [NeZero L] (s : Fin L → Bool) : ℝ :=
  ∑ r ∈ Finset.range (L - 1), emptyMaskWindowCount (r + 1) s

private theorem emptyMaskWindowCount_zero_sub_one {L : ℕ} [NeZero L] (s : Fin L → Bool) :
    emptyMaskWindowCount 0 s - emptyMaskWindowCount 1 s = maskCount s := by
  unfold emptyMaskWindowCount maskCount
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hzero (j : Fin L) : maskWindowMass 0 s j = 0 := by simp [maskWindowMass]
  have hone : maskWindowMass 1 s i = (bitMass (s i) : ℝ) := by
    simpa only [hzero, zero_add] using maskWindowMass_succ_first 0 s i
  cases h : s i <;> simp [emptyMaskWindowAt, hzero, hone, bitMass, h]

private theorem maskCoalescenceGenerator_emptyPotential_eq {L : ℕ} [NeZero L]
    (hL : 3 ≤ L) (s : Fin L → Bool) :
    maskCoalescenceGenerator emptyMaskWindowPotential s =
      maskCount s - (emptyMaskWindowCount (L - 1) s - emptyMaskWindowCount L s) := by
  have hsum : maskCoalescenceGenerator emptyMaskWindowPotential s =
      ∑ r ∈ Finset.range (L - 1), maskCoalescenceGenerator (emptyMaskWindowCount (r + 1)) s := by
    unfold maskCoalescenceGenerator emptyMaskWindowPotential
    simp_rw [← Finset.sum_sub_distrib]
    exact Finset.sum_comm
  rw [hsum]
  have hrewrite :
      (∑ r ∈ Finset.range (L - 1), maskCoalescenceGenerator (emptyMaskWindowCount (r + 1)) s) =
      ∑ r ∈ Finset.range (L - 1), ((emptyMaskWindowCount (r + 2) s - emptyMaskWindowCount (r + 1) s) -
        (emptyMaskWindowCount (r + 1) s - emptyMaskWindowCount r s)) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [maskCoalescenceGenerator_emptyMaskWindowCount hL r (by have := Finset.mem_range.mp hr; omega)]
    ring
  rw [hrewrite, sum_range_forward_diff (fun r => emptyMaskWindowCount (r + 1) s - emptyMaskWindowCount r s)]
  rw [Nat.sub_add_cancel (show 1 ≤ L by omega)]
  linarith only [emptyMaskWindowCount_zero_sub_one s]

/-- Under pure coalescence the total empty-window potential has drift at least
two whenever two or more sites are marked, and nonnegative drift otherwise. -/
theorem maskCoalescenceGenerator_emptyPotential_ge {L : ℕ} [NeZero L]
    (hL : 3 ≤ L) (s : Fin L → Bool) :
    (if 2 ≤ maskCount s then (2 : ℝ) else 0) ≤
      maskCoalescenceGenerator emptyMaskWindowPotential s := by
  have hLr : L - 1 + 1 = L := by omega
  have hlast (j : Fin L) : maskWindowMass L s j = maskWindowMass (L - 1) s j +
      (bitMass (s (j - ((L - 1 : ℕ) : Fin L))) : ℝ) := by
    simpa only [hLr] using maskWindowMass_succ_last (L - 1) s j
  rw [maskCoalescenceGenerator_emptyPotential_eq hL]
  by_cases htwo : 2 ≤ maskCount s
  · have hfull : emptyMaskWindowCount L s = 0 := by
      unfold emptyMaskWindowCount emptyMaskWindowAt
      simp [maskWindowMass_full, show maskCount s ≠ 0 by linarith]
    have hinter : emptyMaskWindowCount (L - 1) s = 0 := by
      unfold emptyMaskWindowCount emptyMaskWindowAt
      apply Finset.sum_eq_zero
      intro j _
      have hbit : (bitMass (s (j - ((L - 1 : ℕ) : Fin L))) : ℝ) ≤ 1 := by
        cases s (j - ((L - 1 : ℕ) : Fin L)) <;> simp [bitMass]
      have hmass := hlast j
      rw [maskWindowMass_full] at hmass
      exact if_neg (by linarith)
    simpa only [if_pos htwo, hfull, hinter, sub_self, sub_zero] using htwo
  · rw [if_neg htwo]
    apply sub_nonneg.mpr
    unfold emptyMaskWindowCount
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j, (bitMass (s (j - ((L - 1 : ℕ) : Fin L))) : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        unfold emptyMaskWindowAt
        rw [hlast, empty_indicator_add_bit _ (maskWindowMass_nonneg _ _ _) _]
        cases s (j - ((L - 1 : ℕ) : Fin L)) <;> simp [bitMass]
        split_ifs <;> norm_num
      _ = maskCount s := by
        simp only [sub_eq_add_neg]
        exact Equiv.sum_comp (Equiv.addRight (-((L - 1 : ℕ) : Fin L))) (fun i => (bitMass (s i) : ℝ))

/-- Adding marked sites can only remove empty windows. -/
theorem emptyMaskWindowPotential_antitone {L : ℕ} [NeZero L] {s t : Fin L → Bool}
    (h : ∀ i, s i = true → t i = true) : emptyMaskWindowPotential t ≤ emptyMaskWindowPotential s := by
  unfold emptyMaskWindowPotential emptyMaskWindowCount emptyMaskWindowAt
  apply Finset.sum_le_sum
  intro r _
  apply Finset.sum_le_sum
  intro j _
  by_cases hz : maskWindowMass (r + 1) t j = 0
  · have hmass : maskWindowMass (r + 1) s j ≤ maskWindowMass (r + 1) t j := by
      unfold maskWindowMass
      apply Finset.sum_le_sum
      intro u _
      by_cases hb : s (j - (u : Fin L)) = true
      · simp [bitMass, hb, h _ hb]
      · simp [bitMass, show s (j - (u : Fin L)) = false from Bool.eq_false_iff.mpr hb]
        positivity
    have hz' : maskWindowMass (r + 1) s j = 0 := by
      linarith only [hmass, hz, maskWindowMass_nonneg (r + 1) s j]
    simp [hz, hz']
  · simp only [if_neg hz]
    split_ifs <;> norm_num

/-- Insert a mark at a site. -/
def insertMask {L : ℕ} (s : Fin L → Bool) (i j : Fin L) : Bool := if j = i then true else s j

theorem coalesceMask_eq_self_of_false {L : ℕ} (s : Fin L → Bool) (i : Fin L)
    (h : s i = false) : coalesceMask s i = s := by
  funext j
  unfold coalesceMask
  by_cases hj : j = i
  · simp [hj, h]
  · by_cases hr : j = right i
    · simp only [if_neg hj, if_pos hr, h, Bool.false_or]
    · simp only [if_neg hj, if_neg hr]

private theorem largePileMask_wholePileOrStay_birth_eq {L N : ℕ} (hL : 3 ≤ L)
    (k : ℕ) (x : State L N) (i : Fin L)
    (h : 2 ≤ occ x i ∧ occ x i ≤ k ∧ occ x (right i) ≤ k ∧ k < occ x i + occ x (right i)) :
    largePileMask k (wholePileOrStay x i) = insertMask (largePileMask k x) (right i) := by
  unfold wholePileOrStay
  rw [if_pos h.1]
  funext j
  by_cases hj : j = i
  · subst j
    simp [insertMask, largePileMask, occ_move, transfer, Ne.symm (right_ne_self hL i),
      not_lt_of_ge h.2.1]
  · by_cases hr : j = right i
    · subst j
      have hsum : k < occ x (right i) + occ x i := by omega
      simp [insertMask, largePileMask, occ_move_right hL, hsum]
    · simp [insertMask, largePileMask, occ_move, transfer, hj, hr]

private theorem occ_move_le_of_ne_right {L N : ℕ} (x : State L N)
    (i j : Fin L) (k : ℕ) (hk : k ≤ occ x i) (h : j ≠ right i) :
    occ (move x i k hk) j ≤ occ x j := by
  simp [occ_move, transfer, h]

private theorem largePileMask_chipOrStay_le_insert {L N : ℕ}
    (k : ℕ) (x : State L N) (i j : Fin L) (hj : largePileMask k (chipOrStay x i) j = true) :
    insertMask (largePileMask k x) (right i) j = true := by
  by_cases hr : j = right i
  · simp [insertMask, hr]
  · rw [insertMask, if_neg hr]
    unfold chipOrStay at hj
    by_cases hi : 1 ≤ occ x i
    · rw [dif_pos hi] at hj
      have hj' : k < occ (move x i 1 hi) j := by simpa [largePileMask] using hj
      simpa [largePileMask] using hj'.trans_le (occ_move_le_of_ne_right x i j 1 hi hr)
    · rwa [dif_neg hi] at hj

private theorem largePileMask_chipOrStay_le_of_no_birth {L N : ℕ} (hL : 3 ≤ L)
    (k : ℕ) (x : State L N) (i j : Fin L)
    (h : ¬(1 ≤ occ x i ∧ occ x (right i) = k)) (hj : largePileMask k (chipOrStay x i) j = true) :
    largePileMask k x j = true := by
  unfold chipOrStay at hj
  by_cases hi : 1 ≤ occ x i
  · rw [dif_pos hi] at hj
    have hj' : k < occ (move x i 1 hi) j := by simpa [largePileMask] using hj
    by_cases hr : j = right i
    · subst j
      rw [occ_move_right hL] at hj'
      have hd : occ x (right i) ≠ k := fun he => h ⟨hi, he⟩
      simpa [largePileMask] using (show k < occ x (right i) by omega)
    · simpa [largePileMask] using hj'.trans_le (occ_move_le_of_ne_right x i j 1 hi hr)
  · rwa [dif_neg hi] at hj

/-- Loss of a test when a site is newly marked. For the empty-window test it
counts the previously empty windows that contain that site. -/
def maskBirthDamage {L : ℕ} (f : (Fin L → Bool) → ℝ) (s : Fin L → Bool) (i : Fin L) : ℝ :=
  f s - f (insertMask s i)

/-- Rate of upward cutoff crossings weighted by their effect on a test. -/
def maskBirthDamageRate {L N : ℕ} (f : (Fin L → Bool) → ℝ) (w : ℝ) (k : ℕ)
    (x : State L N) : ℝ :=
  ∑ i, ((if 1 ≤ occ x i ∧ occ x (right i) = k then w else 0) + wholeThresholdBirthAt k x i) *
    maskBirthDamage f (largePileMask k x) (right i)

private theorem mask_coalescence_atSite_le_birthDamage {L N : ℕ} (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (k : ℕ) (hk : 1 ≤ k) (f : (Fin L → Bool) → ℝ)
    (hf : ∀ s t, (∀ j, s j = true → t j = true) → f t ≤ f s)
    (x : State L N) (i : Fin L) :
    f (coalesceMask (largePileMask k x) i) - f (largePileMask k x) ≤
      atSite w (fun y => f (largePileMask k y)) x i +
        ((if 1 ≤ occ x i ∧ occ x (right i) = k then w else 0) + wholeThresholdBirthAt k x i) *
          maskBirthDamage f (largePileMask k x) (right i) := by
  let g := fun y : State L N => f (largePileMask k y)
  let d := maskBirthDamage f (largePileMask k x) (right i)
  let c := if 1 ≤ occ x i ∧ occ x (right i) = k then w else 0
  change f (coalesceMask (largePileMask k x) i) - g x ≤ atSite w g x i +
    (c + wholeThresholdBirthAt k x i) * d
  have hchip : -(c * d) ≤ w * (g (chipOrStay x i) - g x) := by
    by_cases hb : 1 ≤ occ x i ∧ occ x (right i) = k
    · have h := hf (largePileMask k (chipOrStay x i)) (insertMask (largePileMask k x) (right i))
        (largePileMask_chipOrStay_le_insert k x i)
      have hle := mul_le_mul_of_nonneg_left h hw
      simp only [c, if_pos hb, d, maskBirthDamage, g]
      linarith only [hle]
    · have h := hf (largePileMask k (chipOrStay x i)) (largePileMask k x)
        (fun j => largePileMask_chipOrStay_le_of_no_birth hL k x i j hb)
      simp only [c, if_neg hb, zero_mul, neg_zero]
      exact mul_nonneg hw (sub_nonneg.mpr h)
  have hwhole : f (coalesceMask (largePileMask k x) i) - g x =
      (g (wholePileOrStay x i) - g x) + wholeThresholdBirthAt k x i * d := by
    by_cases h : 2 ≤ occ x i ∧ occ x i ≤ k ∧ occ x (right i) ≤ k ∧ k < occ x i + occ x (right i)
    · have hsmall : largePileMask k x i = false := by simp [largePileMask, not_lt_of_ge h.2.1]
      rw [coalesceMask_eq_self_of_false _ _ hsmall]
      simp only [g, d, maskBirthDamage, wholeThresholdBirthAt, if_pos h, one_mul,
        largePileMask_wholePileOrStay_birth_eq hL k x i h]
      ring
    · simp [g, wholeThresholdBirthAt, h, largePileMask_wholePileOrStay_eq hL k hk x i h]
  have hat : atSite w g x i = w * (g (chipOrStay x i) - g x) +
      (g (wholePileOrStay x i) - g x) := by
    unfold atSite chipOrStay wholePileOrStay
    by_cases hi : 1 ≤ occ x i <;> by_cases hm : 2 ≤ occ x i <;> simp [hi, hm]
  rw [hwhole, hat]
  linarith only [hchip]

/-- For a test that decreases when marks are added, only births contribute
to the upper bound on its mean coalescence drift. Downward cutoff crossings
have the opposite sign and need no error budget. -/
theorem stationary_maskCoalescence_drift_le_birthDamage {L N : ℕ} (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (k : ℕ) (hk : 1 ≤ k)
    (f : (Fin L → Bool) → ℝ)
    (hf : ∀ s t, (∀ j, s j = true → t j = true) → f t ≤ f s) :
    (∑ x, μ.weight x * maskCoalescenceGenerator f (largePileMask k x)) ≤
      ∑ x, μ.weight x * maskBirthDamageRate f w k x := by
  let g := fun x : State L N => f (largePileMask k x)
  have hpoint (x : State L N) : maskCoalescenceGenerator f (largePileMask k x) ≤
      generator w g x + maskBirthDamageRate f w k x := by
    unfold maskCoalescenceGenerator generator maskBirthDamageRate
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => mask_coalescence_atSite_le_birthDamage hL hw k hk f hf x i)
  calc
    _ ≤ ∑ x, μ.weight x * (generator w g x + maskBirthDamageRate f w k x) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (μ.nonneg x))
    _ = _ := by simp_rw [mul_add, Finset.sum_add_distrib, μ.invariant g, zero_add]

/-- Stationary probability of at least two sites strictly above the cutoff. -/
def twoLargePilesProbability {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) (k : ℕ) : ℝ :=
  ∑ x, if 2 ≤ maskCount (largePileMask k x) then μ.weight x else 0

/-- Pairs of large piles at any separation are controlled by births weighted
by the number of empty intervals that they erase. -/
theorem stationary_twoLargePilesProbability_le_birthDamage {L N : ℕ} [NeZero L]
    (hL : 3 ≤ L) {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (k : ℕ) (hk : 1 ≤ k) :
    2 * twoLargePilesProbability μ k ≤
      ∑ x, μ.weight x * maskBirthDamageRate emptyMaskWindowPotential w k x := by
  calc
    _ = ∑ x, μ.weight x * (if 2 ≤ maskCount (largePileMask k x) then 2 else 0) := by
      unfold twoLargePilesProbability
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> ring
    _ ≤ ∑ x, μ.weight x * maskCoalescenceGenerator emptyMaskWindowPotential (largePileMask k x) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
        (maskCoalescenceGenerator_emptyPotential_ge hL _) (μ.nonneg x))
    _ ≤ _ := stationary_maskCoalescence_drift_le_birthDamage hL hw μ k hk emptyMaskWindowPotential
      (fun _ _ h => emptyMaskWindowPotential_antitone h)

end
end Chipping
