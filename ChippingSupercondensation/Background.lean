import ChippingSupercondensation.LargestPile

/-!
# Occupied pairs and background mass

Stationarity bounds the occupied pairs at each offset by the number of multiple
sites. With window packing this gives
`occupiedDensity_tendsto_zero_of_multipleDensity_tendsto_zero`. At positive
density, `tails_vanish_iff_multipleBackgroundMass_tendsto_zero` reduces the tail
limit to the mass on background sites of size at least two. Capping masses at
`k` gives the capped mass balance, the cross-cap merger rate, bounds on
threshold pairs, and the bound on nearby macroscopic pairs.
-/

namespace Chipping

open Filter
open scoped BigOperators Topology

noncomputable section

/-- Indicator that both indicated sites are occupied. -/
def occupiedPair {L N : ℕ} (i j : Fin L) (x : State L N) : ℝ :=
  if 0 < occ x i ∧ 0 < occ x j then 1 else 0

private theorem occ_move_ge_of_ne {L N : ℕ} (x : State L N)
    (i j : Fin L) (k : ℕ) (hk : k ≤ occ x i) (hj : j ≠ i) :
    occ x j ≤ occ (move x i k hk) j := by
  simp [occ_move, transfer, hj]

/-- Both sites have mass at least `k`. -/
def thresholdPair {L N : ℕ} (k : ℕ) (i j : Fin L) (x : State L N) : ℝ :=
  if k ≤ occ x i ∧ k ≤ occ x j then 1 else 0

private theorem thresholdPair_nonneg {L N : ℕ} (k : ℕ) (i j : Fin L) (x : State L N) :
    0 ≤ thresholdPair k i j x := by
  unfold thresholdPair
  split_ifs <;> norm_num

private theorem thresholdPair_generator_ge_of_entry {L N : ℕ} {w : ℝ} (hw : 0 ≤ w)
    (x : State L N) (q : ℕ) (i j : Fin L) (hjr : j ≠ right i) (c : ℝ) (hc : 0 ≤ c)
    (hcreate : thresholdPair q (right i) j x = 0 → q ≤ occ x i ∧ q ≤ occ x j →
      c ≤ atSite w (thresholdPair q (right i) j) x i) :
    c * thresholdPair q i j x - (c + 2 * (w + 1)) * thresholdPair q (right i) j x ≤
      generator w (thresholdPair q (right i) j) x := by
  let a := right i
  let f : State L N → ℝ := thresholdPair q a j
  change c * thresholdPair q i j x - (c + 2 * (w + 1)) * f x ≤ generator w f x
  have hnonneg (y : State L N) : 0 ≤ f y := thresholdPair_nonneg q a j y
  by_cases ht : q ≤ occ x a ∧ q ≤ occ x j
  · have hfx : f x = 1 := if_pos ht
    have hlocal (k : Fin L) :
        -(if k = a then w + 1 else 0) - (if k = j then w + 1 else 0) ≤
          atSite w f x k := by
      unfold atSite
      rw [hfx]
      have hchip : -w ≤ (if h : 1 ≤ occ x k then w * (f (move x k 1 h) - 1) else 0) := by
        split_ifs with h
        · have hle : -(1 : ℝ) ≤ f (move x k 1 h) - 1 := by linarith [hnonneg (move x k 1 h)]
          simpa only [mul_neg, mul_one] using mul_le_mul_of_nonneg_left hle hw
        · linarith
      have hwhole : -(1 : ℝ) ≤ (if 2 ≤ occ x k then f (move x k (occ x k) le_rfl) - 1 else 0) := by
        split_ifs
        · linarith [hnonneg (move x k (occ x k) le_rfl)]
        · norm_num
      by_cases hka : k = a
      · have hkj : k ≠ j := fun h => hjr (h.symm.trans hka)
        simp only [if_pos hka, if_neg hkj, sub_zero]
        linarith
      · by_cases hkj : k = j
        · simp only [if_neg hka, if_pos hkj, neg_zero, zero_sub]
          linarith
        · have hkeep (n : ℕ) (hn : n ≤ occ x k) : f (move x k n hn) = 1 :=
            if_pos ⟨ht.1.trans (occ_move_ge_of_ne x k a n hn (Ne.symm hka)),
              ht.2.trans (occ_move_ge_of_ne x k j n hn (Ne.symm hkj))⟩
          simp [hka, hkj, hkeep]
    have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hlocal k)
    simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at hsum
    have hsource : thresholdPair q i j x ≤ 1 := by
      unfold thresholdPair
      split_ifs <;> norm_num
    unfold generator
    rw [hfx]
    linarith only [hsum, mul_le_mul_of_nonneg_left hsource hc]
  · have hfx : f x = 0 := if_neg ht
    have hsite_nonneg (k : Fin L) : 0 ≤ atSite w f x k := by
      unfold atSite
      rw [hfx]
      apply add_nonneg
      · split_ifs
        · exact mul_nonneg hw (by simpa only [sub_zero] using hnonneg _)
        · rfl
      · split_ifs
        · simpa only [sub_zero] using hnonneg _
        · rfl
    have hsource : c * thresholdPair q i j x ≤ atSite w f x i := by
      by_cases hs : q ≤ occ x i ∧ q ≤ occ x j
      · simpa only [thresholdPair, if_pos hs, mul_one] using hcreate hfx hs
      · simpa only [thresholdPair, if_neg hs, mul_zero] using hsite_nonneg i
    rw [hfx, mul_zero, sub_zero]
    exact hsource.trans (Finset.single_le_sum (fun k _ => hsite_nonneg k) (Finset.mem_univ i))

/-- A chip can advance the left end of an occupied pair. -/
theorem occupiedPair_generator_ge {L N : ℕ} (hL : 3 ≤ L) {w : ℝ} (hw : 0 ≤ w)
    (x : State L N) (i j : Fin L) (hji : j ≠ i) (hjr : j ≠ right i) :
    w * occupiedPair i j x - (3 * w + 2) * occupiedPair (right i) j x ≤
      generator w (occupiedPair (right i) j) x := by
  have hcreate (hfx : thresholdPair 1 (right i) j x = 0) (hs : 1 ≤ occ x i ∧ 1 ≤ occ x j) :
      w ≤ atSite w (thresholdPair 1 (right i) j) x i := by
    have ha : 1 ≤ occ (move x i 1 hs.1) (right i) := by
      rw [occ_move_right hL]
      omega
    have hj : 1 ≤ occ (move x i 1 hs.1) j :=
      hs.2.trans (occ_move_ge_of_ne x i j 1 hs.1 hji)
    have hnew : thresholdPair 1 (right i) j (move x i 1 hs.1) = 1 := if_pos ⟨ha, hj⟩
    unfold atSite
    simp only [dif_pos hs.1, hnew, hfx, sub_zero, mul_one]
    apply le_add_of_nonneg_right
    split_ifs
    · exact thresholdPair_nonneg _ _ _ _
    · rfl
  have h := thresholdPair_generator_ge_of_entry hw x 1 i j hjr w hw hcreate
  rw [show w + 2 * (w + 1) = 3 * w + 2 by ring] at h
  exact h

theorem stationary_occupiedPair_le_next {L N : ℕ} (hL : 3 ≤ L) {w : ℝ} (hw : 0 ≤ w)
    (μ : StationaryLaw L N w) (i j : Fin L) (hji : j ≠ i) (hjr : j ≠ right i) :
    w * (∑ x, μ.weight x * occupiedPair i j x) ≤
      (3 * w + 2) * (∑ x, μ.weight x * occupiedPair (right i) j x) := by
  have h : (∑ x, μ.weight x *
      (w * occupiedPair i j x - (3 * w + 2) * occupiedPair (right i) j x)) ≤
      ∑ x, μ.weight x * generator w (occupiedPair (right i) j) x :=
    Finset.sum_le_sum (fun x _ =>
      mul_le_mul_of_nonneg_left (occupiedPair_generator_ge hL hw x i j hji hjr) (μ.nonneg x))
  rw [μ.invariant] at h
  simp_rw [mul_sub, Finset.sum_sub_distrib, mul_left_comm _ w, mul_left_comm _ (3 * w + 2),
    ← Finset.mul_sum] at h
  exact sub_nonpos.mp h

/-- The number of occupied pairs at an oriented offset. -/
def occupiedPairCountAt {L N : ℕ} (d : Fin L) (x : State L N) : ℝ :=
  ∑ i, occupiedPair i (i + d) x

/-- The stationary mean number of occupied pairs at an oriented offset. -/
def meanOccupiedPairCountAt {L N : ℕ} {w : ℝ}
    (μ : StationaryLaw L N w) (d : Fin L) : ℝ :=
  ∑ x, μ.weight x * occupiedPairCountAt d x

/-- The stationary mean number of sites with mass at least two. -/
def meanMultipleCount {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) : ℝ :=
  ∑ x, μ.weight x * multipleCount x

private theorem meanMultipleCount_nonneg {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) :
    0 ≤ meanMultipleCount μ := by
  unfold meanMultipleCount multipleCount
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg (μ.nonneg x)
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

private theorem meanOccupiedPairCountAt_eq_sum_sites {L N : ℕ} {w : ℝ}
    (μ : StationaryLaw L N w) (d : Fin L) :
    meanOccupiedPairCountAt μ d = ∑ i, ∑ x, μ.weight x * occupiedPair i (i + d) x := by
  unfold meanOccupiedPairCountAt occupiedPairCountAt
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

private theorem stationary_occupiedPairCount_succ_le {L N : ℕ} [NeZero L]
    (hL : 3 ≤ L) {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w)
    (r : ℕ) (hr : 0 < r) (hrL : r + 1 < L) :
    w * meanOccupiedPairCountAt μ ((r + 1 : ℕ) : Fin L) ≤
      (3 * w + 2) * meanOccupiedPairCountAt μ (r : Fin L) := by
  conv_lhs => rw [meanOccupiedPairCountAt_eq_sum_sites, Finset.mul_sum]
  conv_rhs => rw [meanOccupiedPairCountAt_eq_sum_sites, Finset.mul_sum]
  have hshift (i : Fin L) : i + ((r + 1 : ℕ) : Fin L) = right i + (r : Fin L) := by
    simp only [right_eq_add_one, Nat.cast_add, Nat.cast_one]
    abel
  calc
    _ ≤ ∑ i : Fin L, (3 * w + 2) *
        ∑ x, μ.weight x * occupiedPair (right i) (right i + (r : Fin L)) x := by
      apply Finset.sum_le_sum
      intro i _
      have hji : i + ((r + 1 : ℕ) : Fin L) ≠ i :=
        fun h => natCast_fin_ne_zero (by omega : 0 < r + 1) hrL
          (add_left_cancel (h.trans (add_zero i).symm))
      have hjr : i + ((r + 1 : ℕ) : Fin L) ≠ right i := by
        rw [hshift]
        exact fun h => natCast_fin_ne_zero hr (by omega : r < L)
          (add_left_cancel (h.trans (add_zero (right i)).symm))
      simpa only [hshift] using stationary_occupiedPair_le_next hL hw μ i _ hji hjr
    _ = _ := by
      simp only [right_eq_add_one]
      exact Equiv.sum_comp (Equiv.addRight (1 : Fin L)) (fun i => (3 * w + 2) *
        ∑ x, μ.weight x * occupiedPair i (i + (r : Fin L)) x)

/-- At positive rate, the expected number of occupied pairs at any fixed
positive offset is bounded by a constant times the number of multiple sites. -/
theorem stationary_occupiedPairCount_le_multipleCount {L N : ℕ} [NeZero L]
    (hL : 3 ≤ L) {w : ℝ} (hw : 0 < w) (μ : StationaryLaw L N w)
    (r : ℕ) (hr : 0 < r) (hrL : r < L) :
    meanOccupiedPairCountAt μ (r : Fin L) ≤
      ((3 * w + 2) / w) ^ (r - 1) * meanMultipleCount μ := by
  have hbase : meanOccupiedPairCountAt μ (1 : Fin L) ≤ meanMultipleCount μ := by
    have hbalance := stationary_occupied_site_balance hL μ
    have hnonneg : 0 ≤ ∑ x, μ.weight x * multipleAdjacentCount x := by
      unfold multipleAdjacentCount
      apply Finset.sum_nonneg
      intro x _
      apply mul_nonneg (μ.nonneg x)
      exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
    apply le_of_mul_le_mul_left _ hw
    unfold meanOccupiedPairCountAt occupiedPairCountAt occupiedPair meanMultipleCount
    simp only [← right_eq_add_one]
    change w * (∑ x, μ.weight x * adjacentCount x) ≤ w * (∑ x, μ.weight x * multipleCount x)
    linarith
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hz : r = 0
    · subst r
      simpa using hbase
    · have hpos : 0 < r := Nat.pos_of_ne_zero hz
      have hstep := stationary_occupiedPairCount_succ_le hL hw.le μ r hpos hrL
      have hnext : meanOccupiedPairCountAt μ ((r + 1 : ℕ) : Fin L) ≤
          ((3 * w + 2) / w) * meanOccupiedPairCountAt μ (r : Fin L) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hw, mul_comm _ w]
        exact hstep
      refine hnext.trans ?_
      have hmul := mul_le_mul_of_nonneg_left (ih hpos (by omega)) (by positivity :
        0 ≤ (3 * w + 2) / w)
      have hrsub : r.succ - 1 = (r - 1) + 1 := by omega
      rw [hrsub, pow_succ']
      simpa only [mul_assoc] using hmul

private theorem sum_binary_le_one_add_pairs (f : ℕ → ℝ)
    (hf : ∀ i, f i = 0 ∨ f i = 1) (R : ℕ) :
    (∑ s ∈ Finset.range R, f s) ≤
      1 + ∑ s ∈ Finset.range R, ∑ t ∈ Finset.range s, f t * f s := by
  have hn (i : ℕ) : 0 ≤ f i := by rcases hf i with h | h <;> simp [h]
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rcases hf R with h | h
    · simpa [h] using ih
    · simp only [h, mul_one]
      have hpair : 0 ≤ ∑ s ∈ Finset.range R, ∑ t ∈ Finset.range s, f t * f s :=
        Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun t _ => mul_nonneg (hn t) (hn s)))
      linarith only [hpair]

/-- Number of pairs at the given offset, both at or above the cutoff. -/
def thresholdPairCountAt {L N : ℕ} (k : ℕ) (d : Fin L) (x : State L N) : ℝ :=
  ∑ i, thresholdPair k i (i + d) x

def meanThresholdPairCountAt {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) (k : ℕ) (d : Fin L) : ℝ :=
  ∑ x, μ.weight x * thresholdPairCountAt k d x

/-- Sites meeting a mass threshold in a window are bounded by one plus the number of occupied
pairs in that window. Summing over all its translations gives this packing bound. -/
theorem thresholdCount_window_packing {L N : ℕ} [NeZero L] (x : State L N) (k R : ℕ) :
    (R : ℝ) * (∑ i, if k ≤ occ x i then (1 : ℝ) else 0) ≤
      (L : ℝ) + ∑ s ∈ Finset.range R, ∑ t ∈ Finset.range s,
        thresholdPairCountAt k ((s - t : ℕ) : Fin L) x := by
  let f (i : Fin L) : ℝ := if k ≤ occ x i then 1 else 0
  have hbin (i : Fin L) : f i = 0 ∨ f i = 1 := by
    unfold f
    split_ifs <;> simp
  have hpair (i j : Fin L) : f i * f j = thresholdPair k i j x := by
    by_cases hi : k ≤ occ x i <;> by_cases hj : k ≤ occ x j <;> simp [f, thresholdPair, hi, hj]
  have hleft (s : ℕ) : (∑ i : Fin L, f (i + (s : Fin L))) = (∑ i, if k ≤ occ x i then (1 : ℝ) else 0) :=
    Equiv.sum_comp (Equiv.addRight (s : Fin L)) f
  have hright (s t : ℕ) (ht : t ≤ s) :
      (∑ i : Fin L, f (i + (t : Fin L)) * f (i + (s : Fin L))) =
        thresholdPairCountAt k ((s - t : ℕ) : Fin L) x := by
    have hshift (i : Fin L) :
        i + (t : Fin L) + ((s - t : ℕ) : Fin L) = i + (s : Fin L) := by
      rw [add_assoc, ← Nat.cast_add]
      congr 2
      omega
    simp_rw [hpair, ← hshift]
    exact Equiv.sum_comp (Equiv.addRight (t : Fin L))
      (fun i => thresholdPair k i (i + ((s - t : ℕ) : Fin L)) x)
  calc
    _ = ∑ i : Fin L, ∑ s ∈ Finset.range R, f (i + (s : Fin L)) := by
      rw [Finset.sum_comm]
      simp [hleft, nsmul_eq_mul]
    _ ≤ ∑ i : Fin L, (1 + ∑ s ∈ Finset.range R, ∑ t ∈ Finset.range s,
        f (i + (t : Fin L)) * f (i + (s : Fin L))) :=
      Finset.sum_le_sum (fun i _ => sum_binary_le_one_add_pairs _ (fun s => hbin _) R)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_comm (s := (Finset.univ : Finset (Fin L)))
        (t := Finset.range R)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      exact hright s t (Finset.mem_range.mp ht).le

/-- Occupied sites in a window are bounded by one plus the number of occupied
pairs in that window. Summing over all its translations gives this packing bound. -/
theorem occupiedCount_window_packing {L N : ℕ} [NeZero L] (x : State L N) (R : ℕ) :
    (R : ℝ) * occupiedCount x ≤
      (L : ℝ) + ∑ s ∈ Finset.range R, ∑ t ∈ Finset.range s,
        occupiedPairCountAt ((s - t : ℕ) : Fin L) x :=
  thresholdCount_window_packing x 1 R

private theorem stationary_threshold_window_packing {L N : ℕ} [NeZero L] {w : ℝ}
    (μ : StationaryLaw L N w) (k R : ℕ) (hR : 0 < R) (b : ℝ) (hb : 0 ≤ b)
    (hpair : ∀ r : ℕ, 0 < r → r < R → meanThresholdPairCountAt μ k (r : Fin L) ≤ b) :
    (∑ x, μ.weight x * (∑ i, if k ≤ occ x i then (1 : ℝ) else 0)) / (L : ℝ) ≤
      1 / (R : ℝ) + (R : ℝ) * b / (L : ℝ) := by
  let count (x : State L N) : ℝ := ∑ i, if k ≤ occ x i then 1 else 0
  have hsum :
      (∑ s ∈ Finset.range R, ∑ t ∈ Finset.range s, meanThresholdPairCountAt μ k ((s - t : ℕ) : Fin L)) ≤
        (R : ℝ) ^ 2 * b := by
    calc
      _ ≤ ∑ s ∈ Finset.range R, ∑ _t ∈ Finset.range s, b := by
        apply Finset.sum_le_sum
        intro s hs
        have hs' := Finset.mem_range.mp hs
        apply Finset.sum_le_sum
        intro t ht
        have ht' := Finset.mem_range.mp ht
        exact hpair (s - t) (by omega) (by omega)
      _ = ∑ s ∈ Finset.range R, (s : ℝ) * b := by simp [nsmul_eq_mul]
      _ ≤ ∑ _s ∈ Finset.range R, (R : ℝ) * b := by
        apply Finset.sum_le_sum
        intro s hs
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hs).le) hb
      _ = _ := by simp [nsmul_eq_mul, pow_two, mul_assoc]
  have hweighted :
      (R : ℝ) * (∑ x, μ.weight x * count x) ≤
        (L : ℝ) + ∑ s ∈ Finset.range R, ∑ t ∈ Finset.range s,
          meanThresholdPairCountAt μ k ((s - t : ℕ) : Fin L) := by
    calc
      _ = ∑ x, μ.weight x * ((R : ℝ) * count x) := by
        simp only [Finset.mul_sum, mul_left_comm]
      _ ≤ ∑ x, μ.weight x * ((L : ℝ) + ∑ s ∈ Finset.range R, ∑ t ∈ Finset.range s,
          thresholdPairCountAt k ((s - t : ℕ) : Fin L) x) :=
        Finset.sum_le_sum (fun x _ =>
          mul_le_mul_of_nonneg_left (thresholdCount_window_packing x k R) (μ.nonneg x))
      _ = _ := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, μ.normalized, one_mul]
        congr 1
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.sum_comm]
        rfl
  have hpack := hweighted.trans (add_le_add_left hsum (L : ℝ))
  have hRreal : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hLreal : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (NeZero.pos L)
  have hscaled := div_le_div_of_nonneg_right hpack (mul_pos hRreal hLreal).le
  change (∑ x, μ.weight x * count x) / _ ≤ _
  convert hscaled using 1 <;> field_simp [hRreal.ne', hLreal.ne'] <;> ring

/-- At fixed positive rate, any window size bounds the occupied-site density
by its reciprocal plus a constant times the multiple-site density. -/
theorem stationary_occupiedDensity_le {L N : ℕ} [NeZero L]
    (hL : 3 ≤ L) {w : ℝ} (hw : 0 < w) (μ : StationaryLaw L N w)
    (R : ℕ) (hR : 0 < R) (hRL : R ≤ L) :
    meanOccupiedCount μ / (L : ℝ) ≤
      1 / (R : ℝ) + ((R : ℝ) * ((3 * w + 2) / w) ^ R) * (meanMultipleCount μ / (L : ℝ)) := by
  let c : ℝ := (3 * w + 2) / w
  have hc : 1 ≤ c := (le_div_iff₀ hw).mpr (by linarith)
  have hb := mul_nonneg (pow_nonneg (zero_le_one.trans hc) R) (meanMultipleCount_nonneg μ)
  have estimate := stationary_threshold_window_packing μ 1 R hR _ hb
    (fun r hr hrR => (stationary_occupiedPairCount_le_multipleCount hL hw μ r hr
      (hrR.trans_le hRL)).trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hc (by omega)) (meanMultipleCount_nonneg μ)))
  convert estimate using 1
  dsimp [c]
  ring

private theorem density_tendsto_zero_of_window_bounds {L : ℕ → ℕ} {u v : ℕ → ℝ}
    (hLlim : Tendsto L atTop atTop) (hu : ∀ n, 0 ≤ u n) (hv : Tendsto v atTop (𝓝 0))
    (bound : ∀ R : ℕ, 0 < R → ∃ c : ℝ, ∀ n, R ≤ L n → u n ≤ 1 / (R : ℝ) + c * v n) :
    Tendsto u atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (hu n)
  · intro b hb
    obtain ⟨R, hRbig⟩ := exists_nat_gt ((2 : ℝ) / b)
    have hRreal : (0 : ℝ) < (R : ℝ) := (by positivity : (0 : ℝ) < 2 / b).trans hRbig
    have hR : 0 < R := by exact_mod_cast hRreal
    have hrecip : 1 / (R : ℝ) < b / 2 := by
      apply (div_lt_iff₀ hRreal).mpr
      have hmul := (div_lt_iff₀ hb).mp hRbig
      nlinarith only [hmul]
    obtain ⟨c, hc⟩ := bound R hR
    have hconv : Tendsto (fun n => c * v n) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds (x := c)).mul hv
    filter_upwards [(tendsto_atTop.1 hLlim R), (tendsto_order.1 hconv).2 (b / 2) (half_pos hb)]
      with n hn hsmall
    linarith only [hc n hn, hrecip, hsmall]

/-- If multiple sites have vanishing density, so do all occupied sites.
This holds at any fixed positive chip rate and uses no majority assumption. -/
theorem occupiedDensity_tendsto_zero_of_multipleDensity_tendsto_zero
    {L N : ℕ → ℕ} [∀ n, NeZero (L n)] {w : ℝ}
    (hL : ∀ n, 3 ≤ L n) (hLlim : Tendsto L atTop atTop) (hw : 0 < w)
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w)
    (hmultiple : Tendsto (fun n => meanMultipleCount (μ n) / (L n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => meanOccupiedCount (μ n) / (L n : ℝ)) atTop (𝓝 0) := by
  refine density_tendsto_zero_of_window_bounds hLlim (fun n => ?_) hmultiple ?_
  · apply div_nonneg _ (by positivity)
    unfold meanOccupiedCount occupiedCount
    exact Finset.sum_nonneg (fun x _ => mul_nonneg ((μ n).nonneg x)
      (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)))
  · intro R hR
    exact ⟨_, fun n hn => stationary_occupiedDensity_le (hL n) hw (μ n) R hR hn⟩

/-- Background mass on sites with at least two particles. A chosen largest
pile is removed even if several sites tie for largest. -/
def multipleBackgroundMass {L N : ℕ} [NeZero L] (x : State L N) : ℝ :=
  ∑ i ∈ Finset.univ.erase (peakSite x), if 2 ≤ occ x i then (occ x i : ℝ) else 0

private theorem backgroundMass_eq_sum_except_peak {L N : ℕ} [NeZero L] (x : State L N) :
    backgroundMass x = ∑ i ∈ Finset.univ.erase (peakSite x), (occ x i : ℝ) := by
  have hsum : (∑ i, (occ x i : ℝ)) = (N : ℝ) := by exact_mod_cast x.property
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), hsum, occ_peakSite]
  rfl

private theorem multipleBackgroundMass_bounds {L N : ℕ} [NeZero L] (x : State L N) :
    0 ≤ multipleBackgroundMass x ∧
      multipleBackgroundMass x ≤ backgroundMass x ∧
      backgroundMass x ≤ multipleBackgroundMass x + occupiedCount x ∧
      multipleCount x ≤ 1 + multipleBackgroundMass x / 2 := by
  have hcut (i : Fin L) : 0 ≤ (if 2 ≤ occ x i then (occ x i : ℝ) else 0) := by
    split_ifs <;> positivity
  refine ⟨Finset.sum_nonneg (fun i _ => hcut i), ?_, ?_, ?_⟩
  · rw [backgroundMass_eq_sum_except_peak]
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · rfl
    · positivity
  · rw [backgroundMass_eq_sum_except_peak]
    calc
      _ ≤ ∑ i ∈ Finset.univ.erase (peakSite x),
          ((if 2 ≤ occ x i then (occ x i : ℝ) else 0) + (if 0 < occ x i then 1 else 0)) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hm : 2 ≤ occ x i
        · simp only [if_pos hm]
          split_ifs <;> linarith
        · have hs : occ x i = 0 ∨ occ x i = 1 := by omega
          rcases hs with hs | hs <;> simp [hs]
      _ ≤ _ := by
        rw [Finset.sum_add_distrib]
        apply add_le_add_left
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ => by split_ifs <;> norm_num)
  · have hrest : (∑ i ∈ Finset.univ.erase (peakSite x), (if 2 ≤ occ x i then (1 : ℝ) else 0)) ≤
        multipleBackgroundMass x / 2 := by
      unfold multipleBackgroundMass
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · have h : (2 : ℝ) ≤ (occ x i : ℝ) := by exact_mod_cast hi
        norm_num
        linarith
      · norm_num
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)] at hrest
    change multipleCount x - _ ≤ _ at hrest
    have hpeak : (if 2 ≤ occ x (peakSite x) then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    linarith only [hrest, hpeak]

/-- The stationary mean mass in multiple background sites. -/
def meanMultipleBackgroundMass {L N : ℕ} [NeZero L] {w : ℝ} (μ : StationaryLaw L N w) : ℝ :=
  ∑ x, μ.weight x * multipleBackgroundMass x

private theorem stationary_multipleBackgroundMass_bounds {L N : ℕ} [NeZero L] {w : ℝ}
    (μ : StationaryLaw L N w) (hN : 0 < N) :
    0 ≤ meanMultipleBackgroundMass μ ∧
      meanMultipleBackgroundMass μ ≤ (N : ℝ) * meanBackground μ ∧
      (N : ℝ) * meanBackground μ ≤ meanMultipleBackgroundMass μ + meanOccupiedCount μ ∧
      meanMultipleCount μ ≤ 1 + meanMultipleBackgroundMass μ / 2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hback (x : State L N) : (N : ℝ) * backgroundFraction x = backgroundMass x := by
    have hl : largest x ≤ N := by
      have hnonneg : 0 ≤ backgroundMass x := by
        rw [backgroundMass_eq_sum_except_peak]
        exact Finset.sum_nonneg (fun _ _ => by positivity)
      unfold backgroundMass largestMass at hnonneg
      exact_mod_cast sub_nonneg.mp hnonneg
    unfold backgroundFraction backgroundMass largestMass
    rw [Nat.cast_sub hl]
    field_simp [hn]
  have hsum : (N : ℝ) * meanBackground μ = ∑ x, μ.weight x * backgroundMass x := by
    simp_rw [meanBackground, Finset.mul_sum, mul_left_comm (N : ℝ), hback]
  rw [hsum]
  refine ⟨Finset.sum_nonneg (fun x _ => mul_nonneg (μ.nonneg x) (multipleBackgroundMass_bounds x).1),
    ?_, ?_, ?_⟩
  · exact Finset.sum_le_sum (fun x _ =>
      mul_le_mul_of_nonneg_left (multipleBackgroundMass_bounds x).2.1 (μ.nonneg x))
  · calc
      _ ≤ ∑ x, μ.weight x * (multipleBackgroundMass x + occupiedCount x) :=
        Finset.sum_le_sum (fun x _ =>
          mul_le_mul_of_nonneg_left (multipleBackgroundMass_bounds x).2.2.1 (μ.nonneg x))
      _ = _ := by simp_rw [mul_add, Finset.sum_add_distrib, meanMultipleBackgroundMass, meanOccupiedCount]
  · calc
      _ ≤ ∑ x, μ.weight x * (1 + multipleBackgroundMass x / 2) :=
        Finset.sum_le_sum (fun x _ =>
          mul_le_mul_of_nonneg_left (multipleBackgroundMass_bounds x).2.2.2 (μ.nonneg x))
      _ = _ := by
        simp_rw [mul_add, mul_one, Finset.sum_add_distrib, μ.normalized, meanMultipleBackgroundMass,
          div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]

/-- At fixed positive density and chip rate, the background fraction vanishes
if and only if the fraction in background piles of size at least two vanishes.
The stationarity argument controls singletons without a majority assumption. -/
theorem meanBackground_tendsto_zero_iff_multipleBackgroundMass_tendsto_zero
    {L N : ℕ → ℕ} [∀ n, NeZero (L n)] {w ρ : ℝ}
    (hL : ∀ n, 3 ≤ L n) (hLlim : Tendsto L atTop atTop) (hw : 0 < w) (hρ : 0 < ρ)
    (hdensity : Tendsto (fun n => (N n : ℝ) / (L n : ℝ)) atTop (𝓝 ρ))
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w) :
    Tendsto (fun n => meanBackground (μ n)) atTop (𝓝 0) ↔
      Tendsto (fun n => meanMultipleBackgroundMass (μ n) / (N n : ℝ)) atTop (𝓝 0) := by
  have hpos := eventually_pos_mass_of_tendsto_density hρ hdensity
  have hm (n : ℕ) : 0 ≤ meanBackground (μ n) :=
    Finset.sum_nonneg (fun x _ => mul_nonneg ((μ n).nonneg x) (backgroundFraction_nonneg x))
  have hNreal (n : ℕ) (hn : 0 < N n) : (0 : ℝ) < (N n : ℝ) := by exact_mod_cast hn
  have hLreal (n : ℕ) : (0 : ℝ) < (L n : ℝ) := by
    exact_mod_cast (show 0 < L n by have := hL n; omega)
  constructor
  · intro h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    · exact hpos.mono (fun n hn => div_nonneg (stationary_multipleBackgroundMass_bounds (μ n) hn).1
        (hNreal n hn).le)
    · exact hpos.mono (fun n hn => (div_le_iff₀ (hNreal n hn)).mpr
        (by simpa only [mul_comm (meanBackground (μ n))] using
          (stationary_multipleBackgroundMass_bounds (μ n) hn).2.1))
  · intro h
    have hinvL : Tendsto (fun n => 1 / (L n : ℝ)) atTop (𝓝 0) := by
      simp only [one_div]
      exact (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp hLlim
    have hu : Tendsto (fun n => 1 / (L n : ℝ) +
        (meanMultipleBackgroundMass (μ n) / (N n : ℝ) * ((N n : ℝ) / (L n : ℝ))) / 2)
        atTop (𝓝 0) := by
      simpa only [zero_mul, zero_div, add_zero] using
        hinvL.add ((h.mul hdensity).div_const (2 : ℝ))
    have hmultiple : Tendsto (fun n => meanMultipleCount (μ n) / (L n : ℝ)) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
      · exact Eventually.of_forall (fun n => div_nonneg (meanMultipleCount_nonneg (μ n)) (hLreal n).le)
      · filter_upwards [hpos] with n hn
        calc
          _ ≤ (1 + meanMultipleBackgroundMass (μ n) / 2) / (L n : ℝ) :=
            div_le_div_of_nonneg_right (stationary_multipleBackgroundMass_bounds (μ n) hn).2.2.2
              (hLreal n).le
          _ = _ := by
            rw [add_div]
            have hscale : meanMultipleBackgroundMass (μ n) / (N n : ℝ) *
                ((N n : ℝ) / (L n : ℝ)) = meanMultipleBackgroundMass (μ n) / (L n : ℝ) := by
              field_simp [(hLreal n).ne', (hNreal n hn).ne']
            rw [hscale, div_right_comm]
    have hoccupied := occupiedDensity_tendsto_zero_of_multipleDensity_tendsto_zero
      hL hLlim hw μ hmultiple
    have hoccupied' : Tendsto (fun n => meanOccupiedCount (μ n) / (N n : ℝ)) atTop (𝓝 0) := by
      have hratio := hoccupied.div hdensity hρ.ne'
      rw [zero_div] at hratio
      refine hratio.congr' ?_
      filter_upwards [hpos] with n hn
      change (meanOccupiedCount (μ n) / (L n : ℝ)) / ((N n : ℝ) / (L n : ℝ)) =
        meanOccupiedCount (μ n) / (N n : ℝ)
      field_simp [(hLreal n).ne', (hNreal n hn).ne']
    have hu' : Tendsto (fun n => meanMultipleBackgroundMass (μ n) / (N n : ℝ) +
        meanOccupiedCount (μ n) / (N n : ℝ)) atTop (𝓝 0) := by
      simpa only [add_zero] using h.add hoccupied'
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu'
    · exact Eventually.of_forall hm
    · filter_upwards [hpos] with n hn
      have hb := (stationary_multipleBackgroundMass_bounds (μ n) hn).2.2.1
      have hcmp := div_le_div_of_nonneg_right hb (hNreal n hn).le
      rwa [mul_comm (N n : ℝ), mul_div_cancel_right₀ _ (hNreal n hn).ne', add_div] at hcmp

/-- The conjectured background tails can be controlled by estimating only
the mass of multiple background piles. -/
theorem tails_vanish_iff_multipleBackgroundMass_tendsto_zero
    {L N : ℕ → ℕ} [∀ n, NeZero (L n)] {w ρ : ℝ}
    (hL : ∀ n, 3 ≤ L n) (hLlim : Tendsto L atTop atTop) (hw : 0 < w) (hρ : 0 < ρ)
    (hdensity : Tendsto (fun n => (N n : ℝ) / (L n : ℝ)) atTop (𝓝 ρ))
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => backgroundTail (μ n) ε) atTop (𝓝 0)) ↔
      Tendsto (fun n => meanMultipleBackgroundMass (μ n) / (N n : ℝ)) atTop (𝓝 0) :=
  (tails_vanish_iff_mean_vanishes μ).trans
    (meanBackground_tendsto_zero_iff_multipleBackgroundMass_tendsto_zero hL hLlim hw hρ hdensity μ)

private def cappedSiteMass (k a : ℕ) : ℝ := (min k a : ℕ)

/-- Total mass with the contribution of each pile capped at `k`. -/
def cappedMass {L N : ℕ} (k : ℕ) (x : State L N) : ℝ :=
  ∑ i, cappedSiteMass k (occ x i)

/-- The loss of capped mass in an active whole pile merge. -/
def cappedMergeLossAt {L N : ℕ} (k : ℕ) (x : State L N) (i : Fin L) : ℝ :=
  if 2 ≤ occ x i then
    cappedSiteMass k (occ x i) + cappedSiteMass k (occ x (right i)) -
      cappedSiteMass k (occ x i + occ x (right i))
  else 0

private theorem cappedMergeLossAt_nonneg {L N : ℕ} (k : ℕ) (x : State L N) (i : Fin L) :
    0 ≤ cappedMergeLossAt k x i := by
  unfold cappedMergeLossAt cappedSiteMass
  split_ifs
  · apply sub_nonneg.mpr
    rw [← Nat.cast_add]
    exact_mod_cast (show min k (occ x i + occ x (right i)) ≤
      min k (occ x i) + min k (occ x (right i)) by omega)
  · rfl

private theorem cappedSiteMass_chip_change (k a b : ℕ) (ha : 1 ≤ a) :
    (cappedSiteMass k (a - 1) - cappedSiteMass k a) +
      (cappedSiteMass k (b + 1) - cappedSiteMass k b) =
      (if k < a then 1 else 0 : ℝ) - (if k ≤ b then 1 else 0) := by
  have hsource : cappedSiteMass k (a - 1) - cappedSiteMass k a =
      (if k < a then 1 else 0 : ℝ) - 1 := by
    unfold cappedSiteMass
    by_cases h : k < a
    · rw [if_pos h, min_eq_left (by omega : k ≤ a - 1), min_eq_left h.le]
      simp
    · rw [if_neg h, min_eq_right (by omega : a - 1 ≤ k), min_eq_right (by omega : a ≤ k),
        Nat.cast_sub ha]
      simp
  have hdest : cappedSiteMass k (b + 1) - cappedSiteMass k b =
      1 - (if k ≤ b then 1 else 0 : ℝ) := by
    unfold cappedSiteMass
    by_cases h : k ≤ b
    · rw [if_pos h, min_eq_left (by omega : k ≤ b + 1), min_eq_left h]
      simp
    · rw [if_neg h, min_eq_right (by omega : b + 1 ≤ k), min_eq_right (by omega : b ≤ k)]
      push_cast
      ring
  rw [hsource, hdest]
  ring

/-- Count sites whose mass strictly exceeds the cap. -/
def aboveCapCount {L N : ℕ} (k : ℕ) (x : State L N) : ℝ :=
  ∑ i, if k < occ x i then 1 else 0

/-- Count clockwise bonds from an occupied site to a site at or above the cap. -/
def occupiedToCapCount {L N : ℕ} (k : ℕ) (x : State L N) : ℝ :=
  ∑ i, if 1 ≤ occ x i ∧ k ≤ occ x (right i) then 1 else 0

private theorem cappedMass_atSite_eq {L N : ℕ} (hL : 3 ≤ L)
    (w : ℝ) (k : ℕ) (x : State L N) (i : Fin L) :
    atSite w (cappedMass k) x i =
      w * (if k < occ x i then 1 else 0) -
        w * (if 1 ≤ occ x i ∧ k ≤ occ x (right i) then 1 else 0) -
        cappedMergeLossAt k x i := by
  unfold atSite cappedMass cappedMergeLossAt
  simp_rw [sum_siteObservable_move hL (cappedSiteMass k)]
  by_cases hchip : 1 ≤ occ x i
  · simp only [dif_pos hchip, cappedSiteMass_chip_change k _ _ hchip, hchip, true_and]
    by_cases ha : k < occ x i <;> by_cases hb : k ≤ occ x (right i) <;>
      by_cases hwhole : 2 ≤ occ x i <;>
      simp [ha, hb, hwhole, cappedSiteMass, Nat.add_comm] <;> ring
  · have hwhole : ¬2 ≤ occ x i := by omega
    have hlt : ¬k < occ x i := by omega
    simp [hchip, hwhole, hlt]

/-- The cap isolates a budget for whole pile mergers that consume capped mass. -/
theorem stationary_cappedMass_balance {L N : ℕ} (hL : 3 ≤ L) {w : ℝ}
    (μ : StationaryLaw L N w) (k : ℕ) :
    (∑ x, μ.weight x * ∑ i, cappedMergeLossAt k x i) +
      w * (∑ x, μ.weight x * occupiedToCapCount k x) =
      w * (∑ x, μ.weight x * aboveCapCount k x) := by
  have hstate (x : State L N) :
      generator w (cappedMass k) x = w * aboveCapCount k x -
        w * occupiedToCapCount k x - ∑ i, cappedMergeLossAt k x i := by
    unfold generator aboveCapCount occupiedToCapCount
    simp_rw [cappedMass_atSite_eq hL w k]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h := μ.invariant (cappedMass k)
  simp_rw [hstate, mul_sub, Finset.sum_sub_distrib, mul_left_comm _ w, ← Finset.mul_sum] at h
  linarith only [h]


def meanAboveCapCount {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) (k : ℕ) : ℝ :=
  ∑ x, μ.weight x * aboveCapCount k x

private theorem meanAboveCapCount_nonneg {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) (k : ℕ) :
    0 ≤ meanAboveCapCount μ k := by
  unfold meanAboveCapCount aboveCapCount
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (μ.nonneg x)
    (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)))

/-- Two piles at least as large as the cap lose exactly the cap in a merge.
The chip balance therefore controls the number of such adjacent pairs. -/
theorem stationary_adjacentThresholdPair_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (k : ℕ) (hk : 2 ≤ k) :
    ((k : ℝ) + w) * meanThresholdPairCountAt μ k 1 ≤ w * meanAboveCapCount μ k := by
  have hb := stationary_cappedMass_balance hL μ k
  have hpoint (x : State L N) :
      ((k : ℝ) + w) * thresholdPairCountAt k 1 x ≤
        (∑ i, cappedMergeLossAt k x i) + w * occupiedToCapCount k x := by
    unfold thresholdPairCountAt occupiedToCapCount
    simp only [← right_eq_add_one, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    by_cases he : k ≤ occ x i ∧ k ≤ occ x (right i)
    · have hm : 2 ≤ occ x i := hk.trans he.1
      have hc : 1 ≤ occ x i := by omega
      have hs : k ≤ occ x i + occ x (right i) := by omega
      simp [thresholdPair, he, cappedMergeLossAt, hm, hc, he.1, he.2, cappedSiteMass,
        min_eq_left he.1, min_eq_left he.2, min_eq_left hs]
    · simp only [thresholdPair, if_neg he, mul_zero]
      apply add_nonneg (cappedMergeLossAt_nonneg k x i)
      apply mul_nonneg hw
      split_ifs <;> norm_num
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (State L N)))
    (fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (μ.nonneg x))
  unfold meanThresholdPairCountAt meanAboveCapCount
  simp_rw [mul_add, Finset.sum_add_distrib, mul_left_comm _ ((k : ℝ) + w),
    mul_left_comm _ w, ← Finset.mul_sum] at h
  exact h.trans_eq hb

/-- The stationary rate of whole pile moves that create a pile above `k`
from two piles at or below `k` is bounded by the chip rate times the expected
number of existing piles above `k`. -/
theorem stationary_crossCapMergeRate_le {L N : ℕ} (hL : 3 ≤ L) {w : ℝ}
    (hw : 0 ≤ w) (μ : StationaryLaw L N w) (k : ℕ) :
    (∑ x, μ.weight x * ∑ i, if 2 ≤ occ x i ∧ occ x i ≤ k ∧ occ x (right i) ≤ k ∧
        k < occ x i + occ x (right i) then 1 else 0) ≤ w * meanAboveCapCount μ k := by
  have hlocal (x : State L N) (i : Fin L) :
      (if 2 ≤ occ x i ∧ occ x i ≤ k ∧ occ x (right i) ≤ k ∧
        k < occ x i + occ x (right i) then (1 : ℝ) else 0) ≤ cappedMergeLossAt k x i := by
    split_ifs with h
    · obtain ⟨ha, hk₁, hk₂, hs⟩ := h
      simp only [cappedMergeLossAt, if_pos ha, cappedSiteMass, min_eq_right hk₁,
        min_eq_right hk₂, min_eq_left hs.le]
      have hplus : (k : ℝ) + 1 ≤ (occ x i : ℝ) + (occ x (right i) : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hs
      linarith only [hplus]
    · exact cappedMergeLossAt_nonneg k x i
  have hcap : (∑ x, μ.weight x * ∑ i, cappedMergeLossAt k x i) ≤
      w * meanAboveCapCount μ k := by
    have heq := stationary_cappedMass_balance hL μ k
    have hnonneg : 0 ≤ ∑ x, μ.weight x * occupiedToCapCount k x := by
      unfold occupiedToCapCount
      exact Finset.sum_nonneg (fun x _ => mul_nonneg (μ.nonneg x)
        (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)))
    unfold meanAboveCapCount
    linarith only [heq, mul_nonneg hw hnonneg]
  exact (Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i _ => hlocal x i)) (μ.nonneg x))).trans hcap

/-- At a cutoff of at least two, a whole pile move advances a threshold pair
at rate one. The comparison is uniform in the pile masses. -/
theorem stationary_thresholdPair_le_next {L N : ℕ} (hL : 3 ≤ L) {w : ℝ} (hw : 0 ≤ w)
    (μ : StationaryLaw L N w) (k : ℕ) (hk : 2 ≤ k)
    (i j : Fin L) (hji : j ≠ i) (hjr : j ≠ right i) :
    (∑ x, μ.weight x * thresholdPair k i j x) ≤
      (2 * w + 3) * (∑ x, μ.weight x * thresholdPair k (right i) j x) := by
  have hgen (x : State L N) :
      thresholdPair k i j x - (2 * w + 3) * thresholdPair k (right i) j x ≤
        generator w (thresholdPair k (right i) j) x := by
    have hcreate (hfx : thresholdPair k (right i) j x = 0) (hs : k ≤ occ x i ∧ k ≤ occ x j) :
        1 ≤ atSite w (thresholdPair k (right i) j) x i := by
      have hm : 2 ≤ occ x i := hk.trans hs.1
      have ha : k ≤ occ (move x i (occ x i) le_rfl) (right i) := by
        rw [occ_move_right hL]
        omega
      have hj : k ≤ occ (move x i (occ x i) le_rfl) j :=
        hs.2.trans (occ_move_ge_of_ne x i j _ le_rfl hji)
      have hnew : thresholdPair k (right i) j (move x i (occ x i) le_rfl) = 1 := if_pos ⟨ha, hj⟩
      unfold atSite
      rw [hfx, if_pos hm, hnew, sub_zero]
      apply le_add_of_nonneg_left
      split_ifs
      · exact mul_nonneg hw (by simpa only [sub_zero] using thresholdPair_nonneg k (right i) j _)
      · rfl
    have h := thresholdPair_generator_ge_of_entry hw x k i j hjr 1 zero_le_one hcreate
    rw [one_mul, show 1 + 2 * (w + 1) = 2 * w + 3 by ring] at h
    exact h
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (State L N)))
    (fun x _ => mul_le_mul_of_nonneg_left (hgen x) (μ.nonneg x))
  rw [μ.invariant] at h
  simp_rw [mul_sub, Finset.sum_sub_distrib, mul_left_comm _ (2 * w + 3), ← Finset.mul_sum] at h
  exact sub_nonpos.mp h

private theorem meanThresholdPairCountAt_eq_sum_sites {L N : ℕ} {w : ℝ}
    (μ : StationaryLaw L N w) (k : ℕ) (d : Fin L) :
    meanThresholdPairCountAt μ k d = ∑ i, ∑ x, μ.weight x * thresholdPair k i (i + d) x := by
  unfold meanThresholdPairCountAt thresholdPairCountAt
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

private theorem stationary_thresholdPairCount_succ_le {L N : ℕ} [NeZero L]
    (hL : 3 ≤ L) {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w)
    (k : ℕ) (hk : 2 ≤ k) (r : ℕ) (hr : 0 < r) (hrL : r + 1 < L) :
    meanThresholdPairCountAt μ k ((r + 1 : ℕ) : Fin L) ≤
      (2 * w + 3) * meanThresholdPairCountAt μ k (r : Fin L) := by
  conv_lhs => rw [meanThresholdPairCountAt_eq_sum_sites]
  conv_rhs => rw [meanThresholdPairCountAt_eq_sum_sites, Finset.mul_sum]
  have hshift (i : Fin L) : i + ((r + 1 : ℕ) : Fin L) = right i + (r : Fin L) := by
    simp only [right_eq_add_one, Nat.cast_add, Nat.cast_one]
    abel
  calc
    _ ≤ ∑ i : Fin L, (2 * w + 3) *
        ∑ x, μ.weight x * thresholdPair k (right i) (right i + (r : Fin L)) x := by
      apply Finset.sum_le_sum
      intro i _
      have hji : i + ((r + 1 : ℕ) : Fin L) ≠ i :=
        fun h => natCast_fin_ne_zero (by omega : 0 < r + 1) hrL
          (add_left_cancel (h.trans (add_zero i).symm))
      have hjr : i + ((r + 1 : ℕ) : Fin L) ≠ right i := by
        rw [hshift]
        exact fun h => natCast_fin_ne_zero hr (by omega : r < L)
          (add_left_cancel (h.trans (add_zero (right i)).symm))
      simpa only [hshift] using stationary_thresholdPair_le_next hL hw μ k hk i _ hji hjr
    _ = _ := by
      simp only [right_eq_add_one]
      exact Equiv.sum_comp (Equiv.addRight (1 : Fin L)) (fun i => (2 * w + 3) *
        ∑ x, μ.weight x * thresholdPair k i (i + (r : Fin L)) x)

/-- The adjacent threshold bound propagates to every prescribed nonzero
offset, with a factor `(2 * w + 3) ^ (r - 1)`. -/
theorem stationary_thresholdPairCount_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (k : ℕ) (hk : 2 ≤ k)
    (r : ℕ) (hr : 0 < r) (hrL : r < L) :
    meanThresholdPairCountAt μ k (r : Fin L) ≤
      (2 * w + 3) ^ (r - 1) * (w * meanAboveCapCount μ k / ((k : ℝ) + w)) := by
  have hpos : 0 < (k : ℝ) + w := by
    have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hz : r = 0
    · subst r
      change meanThresholdPairCountAt μ k (1 : Fin L) ≤
        (2 * w + 3) ^ 0 * (w * meanAboveCapCount μ k / ((k : ℝ) + w))
      rw [pow_zero, one_mul]
      apply (le_div_iff₀ hpos).mpr
      rw [mul_comm]
      exact stationary_adjacentThresholdPair_le hL hw μ k hk
    · have hr' : 0 < r := Nat.pos_of_ne_zero hz
      refine (stationary_thresholdPairCount_succ_le hL hw μ k hk r hr' hrL).trans ?_
      have hmul := mul_le_mul_of_nonneg_left (ih hr' (by omega)) (by linarith : 0 ≤ 2 * w + 3)
      have hexp : r.succ - 1 = (r - 1) + 1 := by omega
      rw [hexp, pow_succ']
      simpa only [mul_assoc] using hmul

/-- A reciprocal-window bound on the density of multiple sites in terms of
the density of sites holding three or more particles. -/
theorem stationary_multipleDensity_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 < w) (μ : StationaryLaw L N w) (R : ℕ) (hR : 0 < R) (hRL : R ≤ L) :
    meanMultipleCount μ / (L : ℝ) ≤
      1 / (R : ℝ) + ((R : ℝ) * (2 * w + 3) ^ R) * (meanAboveCapCount μ 2 / (L : ℝ)) := by
  have hc : 1 ≤ 2 * w + 3 := by linarith
  have hcap := meanAboveCapCount_nonneg μ 2
  have hfactor : w * meanAboveCapCount μ 2 / (2 + w) ≤ meanAboveCapCount μ 2 := by
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith
  have h := stationary_threshold_window_packing μ 2 R hR
    ((2 * w + 3) ^ R * meanAboveCapCount μ 2) (by positivity) (by
      intro r hr hrR
      have hpair := stationary_thresholdPairCount_le hL hw.le μ 2 (by decide) r hr (hrR.trans_le hRL)
      exact hpair.trans (mul_le_mul (pow_le_pow_right₀ hc (by omega))
        (by simpa using hfactor) (by positivity) (by positivity)))
  convert h using 1
  ring

theorem multipleDensity_tendsto_zero_of_bigDensity_tendsto_zero
    {L N : ℕ → ℕ} [∀ n, NeZero (L n)] {w : ℝ} (hL : ∀ n, 3 ≤ L n)
    (hLlim : Tendsto L atTop atTop) (hw : 0 < w) (μ : (n : ℕ) → StationaryLaw (L n) (N n) w)
    (hbig : Tendsto (fun n => meanAboveCapCount (μ n) 2 / (L n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => meanMultipleCount (μ n) / (L n : ℝ)) atTop (𝓝 0) := by
  apply density_tendsto_zero_of_window_bounds hLlim
    (fun n => div_nonneg (meanMultipleCount_nonneg (μ n)) (by positivity)) hbig
  intro R hR
  exact ⟨_, fun n hn => stationary_multipleDensity_le (hL n) hw (μ n) R hR hn⟩

private theorem meanAboveCapCount_le {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) (k : ℕ) :
    meanAboveCapCount μ k ≤ (N : ℝ) / ((k : ℝ) + 1) := by
  have hpoint (x : State L N) : ((k : ℝ) + 1) * aboveCapCount k x ≤ (N : ℝ) := by
    unfold aboveCapCount
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ i, (occ x i : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs with h
        · rw [mul_one, ← Nat.cast_one, ← Nat.cast_add]
          exact_mod_cast Nat.succ_le_of_lt h
        · rw [mul_zero]
          positivity
      _ = _ := by exact_mod_cast x.property
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (State L N)))
    (fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (μ.nonneg x))
  simp_rw [mul_left_comm _ ((k : ℝ) + 1), ← Finset.mul_sum, ← Finset.sum_mul,
    μ.normalized, one_mul] at h
  apply (le_div_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
  rw [mul_comm]
  exact h

/-- Stationary probability of two sites of mass at least `k` at a clockwise
distance from one through `R`. Use `R < L` to exclude the same site. -/
def nearbyThresholdPairProbability {L N : ℕ} [NeZero L] {w : ℝ}
    (μ : StationaryLaw L N w) (k R : ℕ) : ℝ := by
  classical
  exact ∑ x, if ∃ r ∈ Finset.range R, ∃ i : Fin L,
    k ≤ occ x i ∧ k ≤ occ x (i + ((r + 1 : ℕ) : Fin L)) then μ.weight x else 0

theorem nearbyThresholdPairProbability_nonneg {L N : ℕ} [NeZero L] {w : ℝ}
    (μ : StationaryLaw L N w) (k R : ℕ) : 0 ≤ nearbyThresholdPairProbability μ k R := by
  unfold nearbyThresholdPairProbability
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact μ.nonneg x
  · rfl

private theorem geom_sum_le_pow_of_two_le {c : ℝ} (hc : 2 ≤ c) (R : ℕ) :
    (∑ r ∈ Finset.range R, c ^ r) ≤ c ^ R := by
  have hstrong (n : ℕ) : (∑ r ∈ Finset.range n, c ^ r) ≤ c ^ n - 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hp : 0 ≤ c ^ n := pow_nonneg (by linarith) n
      nlinarith only [ih, mul_le_mul_of_nonneg_left hc hp]
  linarith only [hstrong R]

/-- The probability of any nearby pair of large piles is bounded by the
stationary cap budget and the number of steps needed to move them together. -/
theorem nearbyThresholdPairProbability_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (k R : ℕ) (hk : 2 ≤ k) (hR : R < L) :
    nearbyThresholdPairProbability μ k R ≤
      (2 * w + 3) ^ R * (w * ((N : ℝ) / ((k : ℝ) + 1)) / ((k : ℝ) + w)) := by
  classical
  have hcount_nonneg (x : State L N) (d : Fin L) : 0 ≤ thresholdPairCountAt k d x :=
    Finset.sum_nonneg (fun i _ => thresholdPair_nonneg k i _ x)
  have hprob : nearbyThresholdPairProbability μ k R ≤
      ∑ r ∈ Finset.range R, meanThresholdPairCountAt μ k ((r + 1 : ℕ) : Fin L) := by
    unfold nearbyThresholdPairProbability meanThresholdPairCountAt
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro x _
    rw [← Finset.mul_sum]
    split_ifs with h
    · obtain ⟨r, hr, i, hi, hj⟩ := h
      have h1 : 1 ≤ thresholdPairCountAt k ((r + 1 : ℕ) : Fin L) x := by
        have hsingle := Finset.single_le_sum (s := (Finset.univ : Finset (Fin L)))
          (f := fun j => thresholdPair k j (j + ((r + 1 : ℕ) : Fin L)) x)
          (fun j _ => thresholdPair_nonneg k j _ x) (Finset.mem_univ i)
        have hval : thresholdPair k i (i + ((r + 1 : ℕ) : Fin L)) x = 1 := if_pos ⟨hi, hj⟩
        dsimp only at hsingle
        rw [hval] at hsingle
        exact hsingle
      have hsum := Finset.single_le_sum
        (f := fun s => thresholdPairCountAt k ((s + 1 : ℕ) : Fin L) x)
        (fun s _ => hcount_nonneg x ((s + 1 : ℕ) : Fin L)) hr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (h1.trans hsum) (μ.nonneg x)
    · exact mul_nonneg (μ.nonneg x) (Finset.sum_nonneg (fun r _ => hcount_nonneg x _))
  let c := 2 * w + 3
  let b := w * meanAboveCapCount μ k / ((k : ℝ) + w)
  have hc : 2 ≤ c := by dsimp [c]; linarith
  have hb : 0 ≤ b := div_nonneg (mul_nonneg hw (meanAboveCapCount_nonneg μ k))
    (add_nonneg (by positivity) hw)
  calc
    _ ≤ ∑ r ∈ Finset.range R, c ^ r * b := hprob.trans (by
      apply Finset.sum_le_sum
      intro r hr
      have hrL : r + 1 < L := (Nat.succ_le_of_lt (Finset.mem_range.mp hr)).trans_lt hR
      simpa only [Nat.add_sub_cancel] using
        stationary_thresholdPairCount_le hL hw μ k hk (r + 1) (by omega) hrL)
    _ = (∑ r ∈ Finset.range R, c ^ r) * b := (Finset.sum_mul ..).symm
    _ ≤ c ^ R * b := mul_le_mul_of_nonneg_right (geom_sum_le_pow_of_two_le hc R) hb
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith) _)
      apply div_le_div_of_nonneg_right _ (add_nonneg (by positivity) hw)
      exact mul_le_mul_of_nonneg_left (meanAboveCapCount_le μ k) hw

/-- For piles of at least a fixed fraction `α` of all particles, the bound
decays as the inverse total mass times the window factor. -/
theorem nearbyThresholdPairProbability_le_proportional {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w α : ℝ} (hw : 0 ≤ w) (hα : 0 < α) (hN : 0 < N) (μ : StationaryLaw L N w)
    (k R : ℕ) (hk : 2 ≤ k) (hR : R < L) (hfrac : α * (N : ℝ) ≤ (k : ℝ)) :
    nearbyThresholdPairProbability μ k R ≤
      (w / α ^ 2) * ((2 * w + 3) ^ R / (N : ℝ)) := by
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hαN := mul_pos hα hn
  have hdenom : (α * (N : ℝ)) ^ 2 ≤ ((k : ℝ) + 1) * ((k : ℝ) + w) := by
    rw [pow_two]
    exact mul_le_mul (by linarith) (by linarith) hαN.le (by positivity)
  calc
    _ ≤ (2 * w + 3) ^ R * (w * ((N : ℝ) / ((k : ℝ) + 1)) / ((k : ℝ) + w)) :=
      nearbyThresholdPairProbability_le hL hw μ k R hk hR
    _ = (2 * w + 3) ^ R * ((w * (N : ℝ)) / (((k : ℝ) + 1) * ((k : ℝ) + w))) := by
      congr 1
      rw [← mul_div_assoc, div_div]
    _ ≤ (2 * w + 3) ^ R * ((w * (N : ℝ)) / (α * (N : ℝ)) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith) _)
      exact div_le_div_of_nonneg_left (mul_nonneg hw hn.le) (sq_pos_of_pos hαN) hdenom
    _ = _ := by
      field_simp [hα.ne', hn.ne']
      ring

/-- Competing macroscopic piles are unlikely anywhere inside a window whose
growth factor is sublinear in total mass. -/
theorem nearbyThresholdPairProbability_tendsto_zero {L N k R : ℕ → ℕ}
    [∀ n, NeZero (L n)] {w α : ℝ} (hw : 0 ≤ w) (hα : 0 < α) (hL : ∀ n, 3 ≤ L n)
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w)
    (hwindow : ∀ᶠ n in atTop, 0 < N n ∧ 2 ≤ k n ∧ R n < L n ∧ α * (N n : ℝ) ≤ (k n : ℝ))
    (hscale : Tendsto (fun n => (2 * w + 3) ^ (R n) / (N n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => nearbyThresholdPairProbability (μ n) (k n) (R n)) atTop (𝓝 0) := by
  have hlimit : Tendsto (fun n => (w / α ^ 2) * ((2 * w + 3) ^ (R n) / (N n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := w / α ^ 2)).mul hscale
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimit
    (Eventually.of_forall (fun n => nearbyThresholdPairProbability_nonneg (μ n) (k n) (R n)))
    (hwindow.mono (fun n ⟨hn, hk, hr, hfrac⟩ =>
      nearbyThresholdPairProbability_le_proportional (hL n) hw hα hn (μ n) (k n) (R n) hk hr hfrac))

/-- A threshold pair contributes at least its squared mass fraction to the
probability that two sampled particles are within the window. This gives an
alternative bound at windows too large for geometric propagation. -/
theorem nearbyThresholdPairProbability_mul_fraction_sq_le {L N : ℕ} [NeZero L]
    {w : ℝ} (hw : 0 ≤ w) (hw' : w ≤ 1) (μ : StationaryLaw L N w)
    (k R : ℕ) (hR : R < L) :
    ((k : ℝ) / (N : ℝ)) ^ 2 * nearbyThresholdPairProbability μ k R ≤
      (R : ℝ) * ((R : ℝ) + 1) / (N : ℝ) := by
  classical
  have hprod (x : State L N) (d : Fin L) : 0 ≤ massProductAt x d :=
    Finset.sum_nonneg (fun i _ => by positivity)
  refine le_trans ?_ (stationary_shortOffsetProbability_le hw hw' R hR μ)
  unfold nearbyThresholdPairProbability
  have hsum (r : ℕ) : (∑ x, μ.weight x * massProductAt x ((r + 1 : ℕ) : Fin L)) / (N : ℝ) ^ 2 =
      ∑ x, μ.weight x * massProductAt x ((r + 1 : ℕ) : Fin L) / (N : ℝ) ^ 2 := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
  simp_rw [hsum]
  rw [Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  split_ifs with hp
  · obtain ⟨r, hr, i, hi, hj⟩ := hp
    have hsite : (k : ℝ) ^ 2 ≤ (occ x i : ℝ) * (occ x (i + ((r + 1 : ℕ) : Fin L)) : ℝ) := by
      rw [pow_two]
      exact mul_le_mul (by exact_mod_cast hi) (by exact_mod_cast hj) (by positivity) (by positivity)
    have hsingle := Finset.single_le_sum (s := (Finset.univ : Finset (Fin L)))
      (f := fun j => (occ x j : ℝ) * (occ x (j + ((r + 1 : ℕ) : Fin L)) : ℝ))
      (fun _ _ => by positivity) (Finset.mem_univ i)
    have hbound : (k : ℝ) ^ 2 ≤ massProductAt x ((r + 1 : ℕ) : Fin L) := hsite.trans hsingle
    have hpiece : ((k : ℝ) / (N : ℝ)) ^ 2 * μ.weight x ≤
        μ.weight x * massProductAt x ((r + 1 : ℕ) : Fin L) / (N : ℝ) ^ 2 := by
      rw [div_pow, mul_comm _ (μ.weight x), ← mul_div_assoc]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbound (μ.nonneg x)) (sq_nonneg _)
    exact hpiece.trans (Finset.single_le_sum
      (f := fun s => μ.weight x * massProductAt x ((s + 1 : ℕ) : Fin L) / (N : ℝ) ^ 2)
      (fun s _ => div_nonneg (mul_nonneg (μ.nonneg x) (hprod x _)) (sq_nonneg _)) hr)
  · rw [mul_zero]
    exact Finset.sum_nonneg (fun s _ => div_nonneg (mul_nonneg (μ.nonneg x) (hprod x _)) (sq_nonneg _))

/-- At rates at most one, a window of size `o(sqrt(N))` contains no competing
macroscopic pair with probability tending to one. -/
theorem nearbyThresholdPairProbability_tendsto_zero_of_subsqrt {L N k R : ℕ → ℕ}
    [∀ n, NeZero (L n)] {w α : ℝ} (hw : 0 ≤ w) (hw' : w ≤ 1) (hα : 0 < α)
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w)
    (hwindow : ∀ᶠ n in atTop, 0 < N n ∧ R n < L n ∧ α * (N n : ℝ) ≤ (k n : ℝ))
    (hscale : Tendsto (fun n => (R n : ℝ) * ((R n : ℝ) + 1) / (N n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => nearbyThresholdPairProbability (μ n) (k n) (R n)) atTop (𝓝 0) := by
  have hlimit := hscale.div_const (α ^ 2)
  rw [zero_div] at hlimit
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimit
  · exact Eventually.of_forall (fun n => nearbyThresholdPairProbability_nonneg (μ n) (k n) (R n))
  · filter_upwards [hwindow] with n hn
    obtain ⟨hN, hR, hk⟩ := hn
    have hNreal : (0 : ℝ) < (N n : ℝ) := by exact_mod_cast hN
    have hαk : α ≤ (k n : ℝ) / (N n : ℝ) := (le_div_iff₀ hNreal).mpr hk
    have hsq : α ^ 2 ≤ ((k n : ℝ) / (N n : ℝ)) ^ 2 := pow_le_pow_left₀ hα.le hαk 2
    apply (le_div_iff₀ (sq_pos_of_pos hα)).mpr
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_right hsq (nearbyThresholdPairProbability_nonneg _ _ _)).trans
      (nearbyThresholdPairProbability_mul_fraction_sq_le hw hw' (μ n) (k n) (R n) hR)

end
end Chipping
