import ChippingSupercondensation.PeakFrame

/-!
# Piles of two

The number of piles changes in three ways. A chip onto a single creates a pile
of two, a chip from a pile of two destroys it, and a whole move onto another
pile merges two piles. `multiple_count_balance` states the resulting exact
drift, and `stationary_pile_count_balance` its stationary form:

`w E[#piles of two] + E[#pile-pile bonds] = w E[#occupied-single bonds]`.

Every single has at most one occupied site behind it, so the piles of two are
at most as many as the singles. In the majority region `PeakFrame` bounds the
singles by `w` times the occupied sites. `stationary_twoCount_majority_le`
combines the two: piles of exactly two number at most `w E[K]` there, up to the
cutoff errors. Piles of two therefore need no separate treatment of their
dissolution cycle at the level of counts.

The occupied sites split into singles, piles of two and piles of three or
more, and the background mass splits the same way. With the two bounds above,
`stationary_backgroundMass_le_big` shows for `w < 1/2` that the background mass
on the majority region is at most `(1 - w)/(1 - 2w)` times the background mass
in piles of three or more, plus `3w/(1 - 2w)` times the probability of the
region, up to the cutoff errors. The conjecture on the majority region thus
reduces to piles of at least three particles.

`generator_firstMoment_add_twoCount` prices each pile of two at `1/w` on top of
the fine first moment of `PeakFrame`. Singles drift towards the peak at rate
one, so the debris of a dissolved pile is paid for by the first moment, and
every term of the exact drift is a count, with no factor of `L` except the
inflow from behind. Its stationary form `stationary_pricedPiles_le` shows that
piles of two next to other mass, including a pile of two just ahead of the
peak, number at most `w` times the piles of three plus `w²` times the singles
and the piles of three or more, up to the cutoff errors.
-/

namespace Chipping

open Filter
open scoped BigOperators Topology

noncomputable section

/-- Sites holding exactly two particles. -/
def twoCount {L N : ℕ} (x : State L N) : ℝ :=
  ∑ i, if occ x i = 2 then 1 else 0

/-- Bonds from an occupied site to a single. -/
def occupiedSingleCount {L N : ℕ} (x : State L N) : ℝ :=
  ∑ i, if 0 < occ x i ∧ occ x (right i) = 1 then 1 else 0

/-- Bonds from a pile to a pile. -/
def pilePairCount {L N : ℕ} (x : State L N) : ℝ :=
  ∑ i, if 2 ≤ occ x i ∧ 2 ≤ occ x (right i) then 1 else 0

theorem multipleCount_move {L N : ℕ} (hL : 3 ≤ L) (x : State L N)
    (i : Fin L) (k : ℕ) (hk : k ≤ occ x i) :
    multipleCount (move x i k hk) - multipleCount x =
      ((if 2 ≤ occ x i - k then 1 else 0) - (if 2 ≤ occ x i then 1 else 0)) +
      ((if 2 ≤ occ x (right i) + k then 1 else 0) -
        (if 2 ≤ occ x (right i) then 1 else 0)) := by
  exact sum_siteObservable_move hL (fun m => if 2 ≤ m then 1 else 0) x i k hk

theorem multipleCount_atSite {L N : ℕ} (hL : 3 ≤ L) (w : ℝ) (x : State L N) (i : Fin L) :
    atSite w multipleCount x i =
      w * (if 0 < occ x i ∧ occ x (right i) = 1 then 1 else 0) -
      w * (if occ x i = 2 then 1 else 0) -
      (if 2 ≤ occ x i ∧ 2 ≤ occ x (right i) then 1 else 0) := by
  unfold atSite
  simp_rw [multipleCount_move hL]
  by_cases hzero : occ x i = 0
  · simp [hzero]
  · have hpos : 0 < occ x i := by omega
    have hone : 1 ≤ occ x i := by omega
    have hsrc : (if 2 ≤ occ x i - 1 then (1 : ℝ) else 0) - (if 2 ≤ occ x i then 1 else 0) =
        -(if occ x i = 2 then 1 else 0) := by
      by_cases h2 : occ x i = 2
      · simp [h2]
      · by_cases h3 : 3 ≤ occ x i
        · simp [show 2 ≤ occ x i - 1 by omega, show 2 ≤ occ x i by omega, h2]
        · simp [show ¬ 2 ≤ occ x i - 1 by omega, show ¬ 2 ≤ occ x i by omega, h2]
    have hdst : (if 2 ≤ occ x (right i) + 1 then (1 : ℝ) else 0) -
        (if 2 ≤ occ x (right i) then 1 else 0) = if occ x (right i) = 1 then 1 else 0 := by
      by_cases h1 : occ x (right i) = 1
      · simp [h1]
      · by_cases h2 : 2 ≤ occ x (right i)
        · simp [show 2 ≤ occ x (right i) + 1 by omega, h2, h1]
        · simp [show ¬ 2 ≤ occ x (right i) + 1 by omega, h2, h1]
    rw [dif_pos hone, hsrc, hdst]
    by_cases hmulti : 2 ≤ occ x i
    · rw [if_pos hmulti, Nat.sub_self]
      have hwhole : (if 2 ≤ 0 then (1 : ℝ) else 0) - (if 2 ≤ occ x i then 1 else 0) +
          ((if 2 ≤ occ x (right i) + occ x i then 1 else 0) -
            (if 2 ≤ occ x (right i) then 1 else 0)) =
          -(if 2 ≤ occ x (right i) then 1 else 0) := by
        rw [if_neg (by omega : ¬ 2 ≤ 0), if_pos hmulti,
          if_pos (show 2 ≤ occ x (right i) + occ x i by omega)]
        ring
      rw [hwhole]
      simp only [hpos, true_and, hmulti]
      ring
    · rw [if_neg hmulti]
      simp only [hpos, true_and, hmulti, false_and, if_false]
      ring

/-- The exact drift of the number of piles. -/
theorem multiple_count_balance {L N : ℕ} (hL : 3 ≤ L) (w : ℝ) (x : State L N) :
    generator w multipleCount x =
      w * occupiedSingleCount x - w * twoCount x - pilePairCount x := by
  unfold generator
  simp_rw [multipleCount_atSite hL]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rfl

/-- The stationary balance of the number of piles. -/
theorem stationary_pile_count_balance {L N : ℕ} {w : ℝ} (hL : 3 ≤ L)
    (μ : StationaryLaw L N w) :
    w * (∑ x, μ.weight x * twoCount x) + (∑ x, μ.weight x * pilePairCount x) =
      w * (∑ x, μ.weight x * occupiedSingleCount x) := by
  have h := μ.invariant multipleCount
  simp_rw [multiple_count_balance hL, mul_sub, Finset.sum_sub_distrib] at h
  simp_rw [mul_left_comm _ w, ← Finset.mul_sum] at h
  linarith

/-- Every single has at most one occupied site behind it. -/
theorem occupiedSingleCount_le_singleCount {L N : ℕ} [NeZero L] (x : State L N) :
    occupiedSingleCount x ≤ singleCount x := by
  unfold occupiedSingleCount singleCount
  calc
    _ ≤ ∑ i, (if occ x (right i) = 1 then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases h₁ : 0 < occ x i ∧ occ x (right i) = 1
      · rw [if_pos h₁, if_pos h₁.2]
      · rw [if_neg h₁]
        split_ifs <;> norm_num
    _ = ∑ j, (if occ x j = 1 then (1 : ℝ) else 0) := by
      simp_rw [right_eq_add_one]
      exact Equiv.sum_comp (Equiv.addRight 1) (fun j => if occ x j = 1 then (1 : ℝ) else 0)

/-- Piles other than a largest one each hold at least two background particles. -/
theorem multipleCount_le {L N : ℕ} [NeZero L] (x : State L N) :
    multipleCount x ≤ 1 + ((N : ℝ) - (largest x : ℝ)) / 2 := by
  have hmass : (∑ j, (occ x j : ℝ)) = (N : ℝ) := by exact_mod_cast x.property
  unfold multipleCount
  have hsplit (j : Fin L) : (if j = peakSite x then (1 : ℝ) else (occ x j : ℝ) / 2) =
      (occ x j : ℝ) / 2 + (if j = peakSite x then 1 - (occ x j : ℝ) / 2 else 0) := by
    split_ifs <;> ring
  calc
    _ ≤ ∑ j, (if j = peakSite x then (1 : ℝ) else (occ x j : ℝ) / 2) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hp : j = peakSite x
      · rw [if_pos hp]
        split_ifs <;> norm_num
      · rw [if_neg hp]
        by_cases h2 : 2 ≤ occ x j
        · rw [if_pos h2]
          have : (2 : ℝ) ≤ (occ x j : ℝ) := by exact_mod_cast h2
          linarith
        · rw [if_neg h2]
          positivity
    _ = _ := by
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, hmass, occ_peakSite]
      ring

/-- In stationary mean on the majority region, piles of exactly two are at
most `w` times the occupied sites, up to the cutoff errors. -/
theorem stationary_twoCount_majority_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 < w) (μ : StationaryLaw L N w) (t : ℕ) (ht : N < 2 * t) (htN : t ≤ N) :
    (∑ x, μ.weight x * (if t < largest x then twoCount x else 0)) ≤
      w * (∑ x, μ.weight x * (if t < largest x then occupiedCount x else 0)) +
        (w * (((L - 1 : ℕ) : ℝ) * ((N - t : ℕ) : ℝ)) + (1 + ((N - t : ℕ) : ℝ) / 2)) *
          (∑ x, if largest x = t + 1 then μ.weight x else 0) := by
  set P := ∑ x, if largest x = t + 1 then μ.weight x else 0 with hP
  have hb (y : State L N) (hy : t ≤ largest y) :
      0 ≤ multipleCount y ∧ multipleCount y ≤ 1 + ((N - t : ℕ) : ℝ) / 2 := by
    refine ⟨Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num), ?_⟩
    refine (multipleCount_le y).trans ?_
    rw [Nat.cast_sub htN]
    have : (t : ℝ) ≤ (largest y : ℝ) := by exact_mod_cast hy
    linarith
  have hd := (abs_le.mp (stationary_largestCutoff_abs_drift_le hL hw.le μ t multipleCount
    (b := 1 + ((N - t : ℕ) : ℝ) / 2) (by positivity) hb)).1
  have hlocal (x : State L N) :
      μ.weight x * (if t < largest x then generator w multipleCount x else 0) =
        w * (μ.weight x * (if t < largest x then occupiedSingleCount x else 0)) -
          w * (μ.weight x * (if t < largest x then twoCount x else 0)) -
          μ.weight x * (if t < largest x then pilePairCount x else 0) := by
    by_cases hx : t < largest x
    · rw [if_pos hx, if_pos hx, if_pos hx, if_pos hx, multiple_count_balance hL]
      ring
    · rw [if_neg hx, if_neg hx, if_neg hx, if_neg hx]
      ring
  simp_rw [hlocal] at hd
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hd
  have hpp : 0 ≤ ∑ x, μ.weight x * (if t < largest x then pilePairCount x else 0) :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (μ.nonneg x) (by
      split_ifs
      · exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
      · exact le_rfl))
  -- singles with an occupied site behind them
  have hos : (∑ x, μ.weight x * (if t < largest x then occupiedSingleCount x else 0)) ≤
      ∑ x, μ.weight x * (if t < largest x then singleCount x else 0) := by
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (μ.nonneg x)
    split_ifs
    · exact occupiedSingleCount_le_singleCount x
    · exact le_rfl
  have hsing := stationary_peak_singles_rear_flux_le hL hw.le μ t ht htN
  have hsing' : (∑ x, μ.weight x * (if t < largest x then singleCount x else 0)) ≤
      w * (∑ x, μ.weight x * (if t < largest x then occupiedCount x else 0)) +
        w * (((L - 1 : ℕ) : ℝ) * ((N - t : ℕ) : ℝ)) * P := by
    refine le_trans (Finset.sum_le_sum (fun x _ => ?_)) hsing
    apply mul_le_mul_of_nonneg_left _ (μ.nonneg x)
    split_ifs
    · have := departureMassRate_nonneg hw.le (occ x (peakSite x - 1))
      have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      nlinarith
    · exact le_rfl
  have hPnn : 0 ≤ P := Finset.sum_nonneg (fun x _ => by split_ifs <;> [exact μ.nonneg x; rfl])
  -- divide the pile balance by `w`
  have hmain : w * (∑ x, μ.weight x * (if t < largest x then twoCount x else 0)) ≤
      w * (∑ x, μ.weight x * (if t < largest x then occupiedSingleCount x else 0)) +
        w * (1 + ((N - t : ℕ) : ℝ) / 2) * P := by
    have : w * (1 + ((N - t : ℕ) : ℝ) / 2) * P =
        w * ((1 + ((N - t : ℕ) : ℝ) / 2)) * P := rfl
    nlinarith
  have hdiv : (∑ x, μ.weight x * (if t < largest x then twoCount x else 0)) ≤
      (∑ x, μ.weight x * (if t < largest x then occupiedSingleCount x else 0)) +
        (1 + ((N - t : ℕ) : ℝ) / 2) * P := by
    have h := hmain
    rw [mul_assoc w (1 + _) P, ← mul_add] at h
    exact le_of_mul_le_mul_left h hw
  nlinarith

/-! ### Reduction to piles of three or more -/

/-- Sites holding at least three particles. -/
def bigCount {L N : ℕ} (x : State L N) : ℝ :=
  ∑ i, if 3 ≤ occ x i then 1 else 0

/-- Mass on background sites holding at least three particles. -/
def bigBackgroundMass {L N : ℕ} [NeZero L] (x : State L N) : ℝ :=
  ∑ i, if i ≠ peakSite x ∧ 3 ≤ occ x i then (occ x i : ℝ) else 0

theorem occupiedCount_eq_split {L N : ℕ} (x : State L N) :
    occupiedCount x = singleCount x + twoCount x + bigCount x := by
  unfold occupiedCount singleCount twoCount bigCount
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h0 : occ x i = 0
  · simp [h0]
  · by_cases h1 : occ x i = 1
    · simp [h1]
    · by_cases h2 : occ x i = 2
      · simp [h2]
      · simp [show 0 < occ x i by omega, h1, h2, show 3 ≤ occ x i by omega]

/-- With a peak of at least three particles, the background consists of the
singles, the piles of two and the background mass in piles of three or more. -/
theorem backgroundMass_eq_split {L N : ℕ} [NeZero L] (x : State L N)
    (hpeak : 3 ≤ largest x) :
    backgroundMass x = singleCount x + 2 * twoCount x + bigBackgroundMass x := by
  have hmass : (∑ j, (occ x j : ℝ)) = (N : ℝ) := by exact_mod_cast x.property
  unfold backgroundMass largestMass singleCount twoCount bigBackgroundMass
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hpoint (j : Fin L) : (occ x j : ℝ) - (if j = peakSite x then (occ x j : ℝ) else 0) =
      ((if occ x j = 1 then 1 else 0) + 2 * (if occ x j = 2 then 1 else 0)) +
        (if j ≠ peakSite x ∧ 3 ≤ occ x j then (occ x j : ℝ) else 0) := by
    by_cases hj : j = peakSite x
    · have h3 : 3 ≤ occ x j := by rw [hj, occ_peakSite]; exact hpeak
      simp [hj, show occ x (peakSite x) ≠ 1 by rw [← hj]; omega,
        show occ x (peakSite x) ≠ 2 by rw [← hj]; omega]
    · by_cases h0 : occ x j = 0
      · simp [hj, h0]
      · by_cases h1 : occ x j = 1
        · simp [hj, h1]
        · by_cases h2 : occ x j = 2
          · simp [hj, h2]
          · simp [hj, h1, h2, show 3 ≤ occ x j by omega]
  rw [← Finset.sum_congr rfl (fun j _ => hpoint j), Finset.sum_sub_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _), hmass, occ_peakSite]

/-- The piles of three or more, counted with the peak. -/
theorem bigCount_le {L N : ℕ} [NeZero L] (x : State L N) :
    bigCount x ≤ 1 + bigBackgroundMass x / 3 := by
  unfold bigCount bigBackgroundMass
  have hsplit (j : Fin L) : (if 3 ≤ occ x j then (1 : ℝ) else 0) ≤
      (if j = peakSite x then 1 else 0) +
        (if j ≠ peakSite x ∧ 3 ≤ occ x j then (occ x j : ℝ) else 0) / 3 := by
    by_cases hj : j = peakSite x
    · rw [if_pos hj, if_neg (show ¬(j ≠ peakSite x ∧ 3 ≤ occ x j) from fun h => h.1 hj)]
      split_ifs <;> norm_num
    · rw [if_neg hj, zero_add]
      by_cases h3 : 3 ≤ occ x j
      · rw [if_pos h3, if_pos ⟨hj, h3⟩]
        have : (3 : ℝ) ≤ (occ x j : ℝ) := by exact_mod_cast h3
        linarith
      · rw [if_neg h3, if_neg (fun h => h3 h.2)]
        norm_num
  calc
    _ ≤ ∑ j, ((if j = peakSite x then (1 : ℝ) else 0) +
        (if j ≠ peakSite x ∧ 3 ≤ occ x j then (occ x j : ℝ) else 0) / 3) :=
      Finset.sum_le_sum (fun j _ => hsplit j)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul]

/-- In stationary mean on the majority region and for `w < 1/2`, the
background mass is at most `(1 - w)/(1 - 2w)` times the background mass in
piles of three or more, plus `3w/(1 - 2w)` times the probability of the
region, up to the cutoff errors. Singles and piles of two are both at most `w`
times the occupied sites, which in turn are controlled by the piles of three
or more. -/
theorem stationary_backgroundMass_le_big {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 < w) (hw2 : w < 1 / 2) (μ : StationaryLaw L N w)
    (t : ℕ) (ht : N < 2 * t) (htN : t ≤ N) :
    (∑ x, μ.weight x * (if t < largest x then backgroundMass x else 0)) ≤
      ((1 - w) / (1 - 2 * w)) *
          (∑ x, μ.weight x * (if t < largest x then bigBackgroundMass x else 0)) +
        (3 * w / (1 - 2 * w)) * (∑ x, if t < largest x then μ.weight x else 0) +
        ((3 * w / (1 - 2 * w) + 1) * (w * (((L - 1 : ℕ) : ℝ) * ((N - t : ℕ) : ℝ))) +
          (3 * w / (1 - 2 * w) + 2) *
            (w * (((L - 1 : ℕ) : ℝ) * ((N - t : ℕ) : ℝ)) + (1 + ((N - t : ℕ) : ℝ) / 2))) *
          (∑ x, if largest x = t + 1 then μ.weight x else 0) := by
  set P := ∑ x, if largest x = t + 1 then μ.weight x else 0 with hP
  set π := ∑ x, if t < largest x then μ.weight x else 0 with hπ
  set e₁ := w * (((L - 1 : ℕ) : ℝ) * ((N - t : ℕ) : ℝ)) * P with he₁
  set e₂ := (w * (((L - 1 : ℕ) : ℝ) * ((N - t : ℕ) : ℝ)) + (1 + ((N - t : ℕ) : ℝ) / 2)) * P
    with he₂
  let E (f : State L N → ℝ) : ℝ := ∑ x, μ.weight x * (if t < largest x then f x else 0)
  have hlin (f g : State L N → ℝ) (a b : ℝ) :
      E (fun x => a * f x + b * g x) = a * E f + b * E g := by
    simp only [E, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  have hmono (f g : State L N → ℝ) (hfg : ∀ x, t < largest x → f x ≤ g x) : E f ≤ E g := by
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (μ.nonneg x)
    split_ifs with hx
    · exact hfg x hx
    · exact le_rfl
  -- the two balances
  have hS : E singleCount ≤ w * E occupiedCount + e₁ := by
    have hsing := stationary_peak_singles_rear_flux_le hL hw.le μ t ht htN
    refine le_trans (Finset.sum_le_sum (fun x _ => ?_)) hsing
    apply mul_le_mul_of_nonneg_left _ (μ.nonneg x)
    split_ifs
    · have := departureMassRate_nonneg hw.le (occ x (peakSite x - 1))
      have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      nlinarith
    · exact le_rfl
  have hD : E twoCount ≤ w * E occupiedCount + e₂ :=
    stationary_twoCount_majority_le hL hw μ t ht htN
  have hpk (x : State L N) (hx : t < largest x) : 3 ≤ largest x := by
    have := largest_le_mass x
    omega
  have hK : E occupiedCount = E singleCount + E twoCount + E bigCount := by
    simp only [E]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [occupiedCount_eq_split]
    split_ifs <;> ring
  have hB : E backgroundMass = E singleCount + 2 * E twoCount + E bigBackgroundMass := by
    simp only [E]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : t < largest x
    · rw [if_pos hx, if_pos hx, if_pos hx, if_pos hx, backgroundMass_eq_split x (hpk x hx)]
      ring
    · rw [if_neg hx, if_neg hx, if_neg hx, if_neg hx]
      ring
  have hG : E bigCount ≤ π + E bigBackgroundMass / 3 := by
    simp only [E, hπ]
    rw [div_eq_mul_inv, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : t < largest x
    · rw [if_pos hx, if_pos hx, if_pos hx]
      have := mul_le_mul_of_nonneg_left (bigCount_le x) (μ.nonneg x)
      linarith
    · rw [if_neg hx, if_neg hx, if_neg hx]
      simp
  have hw' : 0 < 1 - 2 * w := by linarith
  have hKb : E occupiedCount ≤ (π + E bigBackgroundMass / 3 + e₁ + e₂) / (1 - 2 * w) := by
    rw [le_div_iff₀ hw']
    nlinarith
  have hfinal : E backgroundMass ≤ 3 * w * E occupiedCount + E bigBackgroundMass + e₁ + 2 * e₂ := by
    rw [hB]
    linarith
  have hKw : 3 * w * E occupiedCount ≤
      3 * w * ((π + E bigBackgroundMass / 3 + e₁ + e₂) / (1 - 2 * w)) :=
    mul_le_mul_of_nonneg_left hKb (by linarith)
  have hgoal : E backgroundMass ≤ ((1 - w) / (1 - 2 * w)) * E bigBackgroundMass +
      (3 * w / (1 - 2 * w)) * π + ((3 * w / (1 - 2 * w) + 1) * e₁ +
        (3 * w / (1 - 2 * w) + 2) * e₂) := by
    have hid : 3 * w * ((π + E bigBackgroundMass / 3 + e₁ + e₂) / (1 - 2 * w)) +
        E bigBackgroundMass + e₁ + 2 * e₂ =
        ((1 - w) / (1 - 2 * w)) * E bigBackgroundMass +
          (3 * w / (1 - 2 * w)) * π + ((3 * w / (1 - 2 * w) + 1) * e₁ +
            (3 * w / (1 - 2 * w) + 2) * e₂) := by
      field_simp
      ring
    linarith
  have herr : (3 * w / (1 - 2 * w) + 1) * e₁ + (3 * w / (1 - 2 * w) + 2) * e₂ =
      ((3 * w / (1 - 2 * w) + 1) * (w * (((L - 1 : ℕ) : ℝ) * ((N - t : ℕ) : ℝ))) +
        (3 * w / (1 - 2 * w) + 2) *
          (w * (((L - 1 : ℕ) : ℝ) * ((N - t : ℕ) : ℝ)) + (1 + ((N - t : ℕ) : ℝ) / 2))) * P := by
    rw [he₁, he₂]
    ring
  rw [← herr]
  exact hgoal

/-! ### Pricing piles of two -/

/-- Sites holding exactly three particles. -/
def threeCount {L N : ℕ} (x : State L N) : ℝ :=
  ∑ i, if occ x i = 3 then 1 else 0

/-- Bonds from an occupied site to a pile of two. -/
def occupiedTwoCount {L N : ℕ} (x : State L N) : ℝ :=
  ∑ i, if 0 < occ x i ∧ occ x (right i) = 2 then 1 else 0

/-- Bonds from a pile of two to an occupied site. -/
def twoOccupiedCount {L N : ℕ} (x : State L N) : ℝ :=
  ∑ i, if occ x i = 2 ∧ 0 < occ x (right i) then 1 else 0

/-- Bonds from a pile to a pile of two. -/
def pileTwoCount {L N : ℕ} (x : State L N) : ℝ :=
  ∑ i, if 2 ≤ occ x i ∧ occ x (right i) = 2 then 1 else 0

theorem twoCount_move {L N : ℕ} (hL : 3 ≤ L) (x : State L N)
    (i : Fin L) (k : ℕ) (hk : k ≤ occ x i) :
    twoCount (move x i k hk) - twoCount x =
      ((if occ x i - k = 2 then 1 else 0) - (if occ x i = 2 then 1 else 0)) +
      ((if occ x (right i) + k = 2 then 1 else 0) -
        (if occ x (right i) = 2 then 1 else 0)) := by
  exact sum_siteObservable_move hL (fun m => if m = 2 then 1 else 0) x i k hk

theorem twoCount_atSite {L N : ℕ} (hL : 3 ≤ L) (w : ℝ) (x : State L N) (i : Fin L) :
    atSite w twoCount x i =
      w * ((if occ x i = 3 then 1 else 0) - (if occ x i = 2 then 1 else 0) +
        (if 0 < occ x i ∧ occ x (right i) = 1 then 1 else 0) -
        (if 0 < occ x i ∧ occ x (right i) = 2 then 1 else 0)) -
      ((if occ x i = 2 ∧ 0 < occ x (right i) then 1 else 0) +
        (if 2 ≤ occ x i ∧ occ x (right i) = 2 then 1 else 0)) := by
  unfold atSite
  simp_rw [twoCount_move hL]
  by_cases hzero : occ x i = 0
  · simp [hzero]
  · have hpos : 0 < occ x i := by omega
    have hone : 1 ≤ occ x i := by omega
    rw [dif_pos hone]
    have hsrc : (if occ x i - 1 = 2 then (1 : ℝ) else 0) - (if occ x i = 2 then 1 else 0) =
        (if occ x i = 3 then 1 else 0) - (if occ x i = 2 then 1 else 0) := by
      congr 1
      by_cases h3 : occ x i = 3
      · simp [h3]
      · simp [h3, show occ x i - 1 ≠ 2 by omega]
    have hdst : (if occ x (right i) + 1 = 2 then (1 : ℝ) else 0) -
        (if occ x (right i) = 2 then 1 else 0) =
          (if occ x (right i) = 1 then 1 else 0) - (if occ x (right i) = 2 then 1 else 0) := by
      congr 1
      by_cases h1 : occ x (right i) = 1
      · simp [h1]
      · simp [h1, show occ x (right i) + 1 ≠ 2 by omega]
    rw [hsrc, hdst]
    by_cases hmulti : 2 ≤ occ x i
    · rw [if_pos hmulti, Nat.sub_self]
      have hwhole : (if (0 : ℕ) = 2 then (1 : ℝ) else 0) - (if occ x i = 2 then 1 else 0) +
          ((if occ x (right i) + occ x i = 2 then 1 else 0) -
            (if occ x (right i) = 2 then 1 else 0)) =
          -((if occ x i = 2 ∧ 0 < occ x (right i) then 1 else 0) +
            (if occ x (right i) = 2 then 1 else 0)) := by
        by_cases h2 : occ x i = 2
        · by_cases hr : occ x (right i) = 0
          · simp [h2, hr]
          · simp [h2, hr, show 0 < occ x (right i) by omega,
              show occ x (right i) + 2 ≠ 2 by omega]
            ring
        · simp [h2, show occ x (right i) + occ x i ≠ 2 by omega]
      rw [hwhole]
      simp only [hpos, true_and, hmulti]
      ring
    · rw [if_neg hmulti]
      have h1 : occ x i = 1 := by omega
      simp only [hpos, true_and, h1]
      norm_num

/-- The exact drift of the number of piles of two. -/
theorem twoCount_balance {L N : ℕ} (hL : 3 ≤ L) (w : ℝ) (x : State L N) :
    generator w twoCount x =
      w * (threeCount x - twoCount x + occupiedSingleCount x - occupiedTwoCount x) -
        (twoOccupiedCount x + pileTwoCount x) := by
  unfold generator
  simp_rw [twoCount_atSite hL]
  unfold threeCount twoCount occupiedSingleCount occupiedTwoCount twoOccupiedCount pileTwoCount
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem twoCount_le {L N : ℕ} (x : State L N) : twoCount x ≤ (N : ℝ) / 2 := by
  have hmass : (∑ j, (occ x j : ℝ)) = (N : ℝ) := by exact_mod_cast x.property
  unfold twoCount
  rw [← hmass, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  split_ifs with h
  · rw [h]
    norm_num
  · positivity

/-- The fine first moment of `PeakFrame` plus `1/w` per pile of two. Singles
drift towards the peak at rate one; a pile of two in isolation drifts at rate
`w - 1`, and a pile of two that has just dissolved into two adjacent singles
at rate `2w - 1`. Every term of the drift is a count, with no factor of `L`
except the inflow from behind. -/
theorem generator_firstMoment_add_twoCount {L N : ℕ} [NeZero L] (hL : 3 ≤ L) {w : ℝ}
    (hw : w ≠ 0) (x : State L N) (hmargin : N + 2 < 2 * largest x) :
    generator w (fun y => peakFrameMoment (fun s => (s : ℝ)) y + twoCount y / w) x =
      w * occupiedCount x - singleCount x -
          (L : ℝ) * departureMassRate w (occ x (peakSite x - 1)) +
        (threeCount x - twoCount x + occupiedSingleCount x - occupiedTwoCount x) -
        (twoOccupiedCount x + pileTwoCount x) / w := by
  have hadd : generator w (fun y => peakFrameMoment (fun s => (s : ℝ)) y + twoCount y / w) x =
      generator w (peakFrameMoment (fun s => (s : ℝ))) x + generator w twoCount x / w := by
    unfold generator
    rw [div_eq_mul_inv, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold atSite
    split_ifs <;> field_simp <;> ring
  rw [hadd, generator_peakFrameMoment_eq hL w _ Nat.cast_zero x hmargin,
    peakFrameDrift_firstMoment hL w x (by omega), twoCount_balance hL]
  field_simp
  ring

/-- With a peak of at least three particles, piles of two are background. -/
theorem twoCount_le_background {L N : ℕ} [NeZero L] (x : State L N) (hpeak : 3 ≤ largest x) :
    twoCount x ≤ ((N : ℝ) - (largest x : ℝ)) / 2 := by
  have hmass : (∑ j, (occ x j : ℝ)) = (N : ℝ) := by exact_mod_cast x.property
  unfold twoCount
  have hpoint (j : Fin L) : (if occ x j = 2 then (1 : ℝ) else 0) ≤
      ((occ x j : ℝ) - (if j = peakSite x then (occ x j : ℝ) else 0)) / 2 := by
    by_cases hj : j = peakSite x
    · have h3 : 3 ≤ occ x j := by rw [hj, occ_peakSite]; exact hpeak
      rw [if_neg (show occ x j ≠ 2 by omega), if_pos hj]
      norm_num
    · rw [if_neg hj, sub_zero]
      split_ifs with h
      · rw [h]
        norm_num
      · positivity
  calc
    _ ≤ ∑ j, ((occ x j : ℝ) - (if j = peakSite x then (occ x j : ℝ) else 0)) / 2 :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = _ := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
        if_pos (Finset.mem_univ _), hmass, occ_peakSite]

/-- Piles of two next to other mass are rare. In stationary mean on the
majority region, the bonds from a pile of two to an occupied site and from a
pile to a pile of two number at most `w` times the piles of three plus `w²`
times the singles and the piles of three or more, up to the cutoff errors.
This includes a pile of two just ahead of the peak. The same balance bounds
`(1 - w)` times the piles of two. -/
theorem stationary_pricedPiles_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 < w) (μ : StationaryLaw L N w) (t : ℕ) (ht : N < 2 * t) (htN : t ≤ N)
    (h3 : 3 ≤ t) :
    (1 - w) * (∑ x, μ.weight x * (if t < largest x then twoCount x else 0)) +
        (∑ x, μ.weight x * (if t < largest x then
          twoOccupiedCount x + pileTwoCount x else 0)) / w ≤
      w * (∑ x, μ.weight x * (if t < largest x then singleCount x else 0)) +
        w * (∑ x, μ.weight x * (if t < largest x then bigCount x else 0)) +
        (∑ x, μ.weight x * (if t < largest x then threeCount x else 0)) +
        (w * (((L - 1 : ℕ) : ℝ) * ((N - t : ℕ) : ℝ)) + ((N - t : ℕ) : ℝ) / 2) *
          (∑ x, if largest x = t + 1 then μ.weight x else 0) := by
  set P := ∑ x, if largest x = t + 1 then μ.weight x else 0 with hP
  set V : State L N → ℝ := fun y => peakFrameMoment (fun s => (s : ℝ)) y + twoCount y / w
    with hV
  set b : ℝ := ((L - 1 : ℕ) : ℝ) * ((N - t : ℕ) : ℝ) + ((N - t : ℕ) : ℝ) / (2 * w) with hb
  have hbound (y : State L N) (hy : t ≤ largest y) : 0 ≤ V y ∧ V y ≤ b := by
    obtain ⟨h1, h2⟩ := peakFrameMoment_bounds (fun s => (s : ℝ)) Nat.cast_zero
      (c := ((L - 1 : ℕ) : ℝ)) (fun s _ => Nat.cast_nonneg s)
      (fun s hs => by
        show (s : ℝ) ≤ ((L - 1 : ℕ) : ℝ)
        exact_mod_cast (show s ≤ L - 1 by omega)) y
    have htwo := twoCount_le_background y (by omega)
    have htwo0 : 0 ≤ twoCount y := Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
    have hgap : (N : ℝ) - (largest y : ℝ) ≤ ((N - t : ℕ) : ℝ) := by
      rw [Nat.cast_sub htN]
      have : (t : ℝ) ≤ (largest y : ℝ) := by exact_mod_cast hy
      linarith
    have hL1 : (0 : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    refine ⟨add_nonneg h1 (div_nonneg htwo0 hw.le), ?_⟩
    have hA : peakFrameMoment (fun s => (s : ℝ)) y ≤ ((L - 1 : ℕ) : ℝ) * ((N - t : ℕ) : ℝ) :=
      h2.trans (mul_le_mul_of_nonneg_left hgap hL1)
    have hB : twoCount y / w ≤ ((N - t : ℕ) : ℝ) / (2 * w) := by
      rw [div_le_div_iff₀ hw (by positivity)]
      nlinarith
    simp only [hV, hb]
    linarith
  have hd := (abs_le.mp (stationary_largestCutoff_abs_drift_le hL hw.le μ t V
    (by positivity) hbound)).1
  -- the drift is at most the stated combination
  have hpoint (x : State L N) (hx : t < largest x) :
      generator w V x ≤ w * singleCount x + w * bigCount x + threeCount x -
        (1 - w) * twoCount x - (twoOccupiedCount x + pileTwoCount x) / w := by
    have hmargin : N + 2 < 2 * largest x := by omega
    rw [hV, generator_firstMoment_add_twoCount hL hw.ne' x hmargin, occupiedCount_eq_split]
    have hq := departureMassRate_nonneg hw.le (occ x (peakSite x - 1))
    have hos := occupiedSingleCount_le_singleCount x
    have hot : 0 ≤ occupiedTwoCount x := Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    nlinarith
  have hsum : (∑ x, μ.weight x * (if t < largest x then generator w V x else 0)) ≤
      ∑ x, μ.weight x * (if t < largest x then
        w * singleCount x + w * bigCount x + threeCount x -
          (1 - w) * twoCount x - (twoOccupiedCount x + pileTwoCount x) / w else 0) := by
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (μ.nonneg x)
    split_ifs with hx
    · exact hpoint x hx
    · exact le_rfl
  have hexpand : (∑ x, μ.weight x * (if t < largest x then
        w * singleCount x + w * bigCount x + threeCount x -
          (1 - w) * twoCount x - (twoOccupiedCount x + pileTwoCount x) / w else 0)) =
      w * (∑ x, μ.weight x * (if t < largest x then singleCount x else 0)) +
        w * (∑ x, μ.weight x * (if t < largest x then bigCount x else 0)) +
        (∑ x, μ.weight x * (if t < largest x then threeCount x else 0)) -
        (1 - w) * (∑ x, μ.weight x * (if t < largest x then twoCount x else 0)) -
        (∑ x, μ.weight x * (if t < largest x then
          twoOccupiedCount x + pileTwoCount x else 0)) / w := by
    simp only [Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  have herr : w * b * P = (w * (((L - 1 : ℕ) : ℝ) * ((N - t : ℕ) : ℝ)) +
      ((N - t : ℕ) : ℝ) / 2) * P := by
    rw [hb]
    field_simp
    ring
  rw [← hP] at hd
  have hchain := le_trans hd (hsum.trans_eq hexpand)
  rw [herr] at hchain
  linarith

end
end Chipping
