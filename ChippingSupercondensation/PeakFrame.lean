import ChippingSupercondensation.LargestPile

/-!
# Moments in the frame of the peak

While one pile holds a majority with a margin of two particles, no single jump
can change which site carries the largest mass. Background mass can then be
measured by its clockwise offset from that pile. For any weight profile `h`
with `h 0 = 0`, `generator_peakFrameMoment_eq` gives the exact drift of
`∑ j, h (offset j) * η j`. Background sites send mass forward at their
departure rate, the peak chips one particle to offset one, and a whole move of
the peak shifts every background offset down by one.

The profile `h s = s` measures how far the background lies ahead of the peak.
Its drift is `w K - S - L q`, where `K` counts occupied sites, `S` counts
single particles, and `q` is the rate at which mass enters the peak from the
site behind it (`generator_peakFirstMoment_eq`). In stationary mean on the
majority region this gives two bounds up to a cutoff error. The number of
singles is at most `w` times the number of occupied sites. Mass reaches the
peak from behind at a rate of order `w E[K] / L`. A cutoff can be chosen so
that the error is proportional to the mean background plus one, rather than
to the total mass.
-/

namespace Chipping

open Filter
open scoped BigOperators Topology

noncomputable section

/-- Clockwise offset of site `j` from the selected peak, in `0, …, L - 1`. -/
def peakOffset {L N : ℕ} [NeZero L] (x : State L N) (j : Fin L) : ℕ :=
  (j - peakSite x).val

/-- Mass weighted by a profile of its clockwise offset from the peak. -/
def peakFrameMoment {L N : ℕ} [NeZero L] (h : ℕ → ℝ) (x : State L N) : ℝ :=
  ∑ j, h (peakOffset x j) * (occ x j : ℝ)

/-- The number of sites holding exactly one particle. -/
def singleCount {L N : ℕ} (x : State L N) : ℝ :=
  ∑ i, if occ x i = 1 then 1 else 0

/-- The drift of `peakFrameMoment h` in the majority region. Background sites
send mass forward at their departure rate, the peak chips into offset one, and
a whole move of the peak lowers every background offset by one. -/
def peakFrameDrift {L N : ℕ} [NeZero L] (w : ℝ) (h : ℕ → ℝ) (x : State L N) : ℝ :=
  w * h 1 +
    (∑ i, if i = peakSite x then 0 else
      departureMassRate w (occ x i) * (h (peakOffset x (right i)) - h (peakOffset x i))) -
    ∑ j, (occ x j : ℝ) * (h (peakOffset x j) - h (peakOffset x j - 1))

theorem peakOffset_eq_zero_iff {L N : ℕ} [NeZero L] (x : State L N) (j : Fin L) :
    peakOffset x j = 0 ↔ j = peakSite x := by
  unfold peakOffset
  rw [← Fin.val_zero L, Fin.val_inj, sub_eq_zero]

theorem peakOffset_lt {L N : ℕ} [NeZero L] (x : State L N) (j : Fin L) :
    peakOffset x j < L :=
  (j - peakSite x).isLt

theorem peakOffset_peakSite {L N : ℕ} [NeZero L] (x : State L N) :
    peakOffset x (peakSite x) = 0 :=
  (peakOffset_eq_zero_iff x _).mpr rfl

theorem peakOffset_right_peakSite {L N : ℕ} [NeZero L] (hL : 3 ≤ L) (x : State L N) :
    peakOffset x (right (peakSite x)) = 1 := by
  unfold peakOffset
  rw [right_eq_add_one, add_sub_cancel_left, Fin.val_one', Nat.mod_eq_of_lt (by omega)]

private theorem fin_val_add_one_of_ne_zero {L : ℕ} [NeZero L] (d : Fin L) (hd : d + 1 ≠ 0) :
    (d + 1).val = d.val + 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by have := NeZero.pos L; omega⟩
  apply Fin.val_add_one_of_lt
  apply Fin.lt_last_iff_ne_last.mpr
  rintro rfl
  exact hd (Fin.last_add_one n)

/-- One step clockwise raises the offset by one, except from the site behind
the peak, which wraps around to offset zero. -/
theorem peakOffset_right {L N : ℕ} [NeZero L] (x : State L N) (i : Fin L)
    (hi : i ≠ peakSite x - 1) : peakOffset x (right i) = peakOffset x i + 1 := by
  unfold peakOffset
  have hd : i - peakSite x + 1 ≠ 0 := by
    intro h
    apply hi
    linear_combination h
  rw [right_eq_add_one, add_sub_right_comm]
  exact fin_val_add_one_of_ne_zero _ hd

theorem peakOffset_peakSite_sub_one {L N : ℕ} [NeZero L] (hL : 3 ≤ L) (x : State L N) :
    peakOffset x (peakSite x - 1) = L - 1 := by
  unfold peakOffset
  rw [sub_sub_cancel_left, Fin.coe_neg, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < L),
    Nat.mod_eq_of_lt (by omega : L - 1 < L)]

theorem peakSite_sub_one_ne {L N : ℕ} [NeZero L] (hL : 3 ≤ L) (x : State L N) :
    peakSite x - 1 ≠ peakSite x := by
  intro h
  have h0 := congrArg (peakOffset x) h
  rw [peakOffset_peakSite_sub_one hL, peakOffset_peakSite] at h0
  omega

/-- A move that keeps the peak in place changes the moment by the moved mass
times the change of weight across the bond. -/
private theorem peakFrameMoment_move_of_peak_eq {L N : ℕ} [NeZero L] (h : ℕ → ℝ)
    (x : State L N) (i : Fin L) (k : ℕ) (hk : k ≤ occ x i)
    (hpeak : peakSite (move x i k hk) = peakSite x) :
    peakFrameMoment h (move x i k hk) - peakFrameMoment h x =
      (k : ℝ) * (h (peakOffset x (right i)) - h (peakOffset x i)) := by
  have hoff (j : Fin L) : peakOffset (move x i k hk) j = peakOffset x j := by
    unfold peakOffset
    rw [hpeak]
  unfold peakFrameMoment
  simp_rw [hoff]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub, occ_move_delta, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- A whole move of the peak lowers every background offset by one. The mass
at offset one joins the peak, where the weight vanishes. -/
private theorem peakFrameMoment_whole_peak {L N : ℕ} [NeZero L] (hL : 3 ≤ L) (h : ℕ → ℝ)
    (h0 : h 0 = 0) (x : State L N) (hmajority : N < 2 * largest x) :
    peakFrameMoment h (move x (peakSite x) (occ x (peakSite x)) le_rfl) -
        peakFrameMoment h x =
      -∑ j, (occ x j : ℝ) * (h (peakOffset x j) - h (peakOffset x j - 1)) := by
  set p := peakSite x with hp
  set y := move x p (occ x p) le_rfl with hy
  have hpy : peakSite y = right p := by
    have h' := peakSite_whole_move hL x hmajority p
    rw [if_pos hp] at h'
    exact h'
  have hterm (j : Fin L) :
      h (peakOffset y j) * (occ y j : ℝ) = h (peakOffset x j - 1) * (occ x j : ℝ) := by
    by_cases hjp : j = p
    · have hzero : occ y j = 0 := by
        rw [hjp, hy, occ_move]
        simp [transfer, Ne.symm (right_ne_self hL p)]
      rw [hzero, (peakOffset_eq_zero_iff x j).mpr hjp, Nat.zero_sub, h0]
      simp
    · by_cases hjr : j = right p
      · have h1 : peakOffset y j = 0 := (peakOffset_eq_zero_iff y j).mpr (hjr.trans hpy.symm)
        have h2 : peakOffset x j = 1 := by rw [hjr, hp]; exact peakOffset_right_peakSite hL x
        rw [h1, h2, h0]
        simp
      · have hocc : occ y j = occ x j := by
          rw [hy, occ_move]
          simp [transfer, hjp, hjr]
        have hoff : peakOffset y j = peakOffset x j - 1 := by
          unfold peakOffset
          rw [hpy, ← hp, right_eq_add_one, ← sub_sub]
          exact Fin.val_sub_one_of_ne_zero (sub_ne_zero.mpr hjp)
        rw [hocc, hoff]
  unfold peakFrameMoment
  simp_rw [hterm]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The exact drift of any peak-frame moment while the peak holds a majority
that survives a single chip. -/
theorem generator_peakFrameMoment_eq {L N : ℕ} [NeZero L] (hL : 3 ≤ L) (w : ℝ)
    (h : ℕ → ℝ) (h0 : h 0 = 0) (x : State L N) (hmargin : N + 2 < 2 * largest x) :
    generator w (peakFrameMoment h) x = peakFrameDrift w h x := by
  set p := peakSite x with hp
  have hp₂ : 2 ≤ occ x p := by rw [hp, occ_peakSite]; omega
  have hp₁ : 1 ≤ occ x p := by omega
  set W := ∑ j, (occ x j : ℝ) * (h (peakOffset x j) - h (peakOffset x j - 1)) with hW
  have hsite (i : Fin L) : atSite w (peakFrameMoment h) x i =
      (if i = p then w * h 1 - W else 0) +
      (if i = p then 0 else departureMassRate w (occ x i) *
        (h (peakOffset x (right i)) - h (peakOffset x i))) := by
    unfold atSite
    by_cases hip : i = p
    · rw [hip, if_pos rfl, if_pos rfl, add_zero, dif_pos hp₁, if_pos hp₂,
        peakFrameMoment_move_of_peak_eq h x p 1 hp₁ (peakSite_chip_move x hmargin p hp₁),
        hp, peakFrameMoment_whole_peak hL h h0 x (by omega), ← hp,
        peakOffset_right_peakSite hL x, peakOffset_peakSite, h0]
      ring
    · rw [if_neg hip, if_neg hip, zero_add]
      have hwhole : peakSite (move x i (occ x i) le_rfl) = peakSite x := by
        rw [peakSite_whole_move hL x (by omega) i, if_neg hip]
      unfold departureMassRate
      by_cases h₁ : 1 ≤ occ x i
      · rw [dif_pos h₁, peakFrameMoment_move_of_peak_eq h x i 1 h₁
          (peakSite_chip_move x hmargin i h₁), if_pos h₁]
        by_cases h₂ : 2 ≤ occ x i
        · rw [if_pos h₂, if_pos h₂, peakFrameMoment_move_of_peak_eq h x i _ le_rfl hwhole]
          push_cast
          ring
        · rw [if_neg h₂, if_neg h₂]
          push_cast
          ring
      · have h₂ : ¬ 2 ≤ occ x i := by omega
        rw [dif_neg h₁, if_neg h₂, if_neg h₁, if_neg h₂]
        ring
  unfold generator peakFrameDrift
  simp_rw [hsite]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ p, if_pos (Finset.mem_univ _)]
  ring

theorem largest_le_mass {L N : ℕ} [NeZero L] (x : State L N) : largest x ≤ N := by
  rw [← occ_peakSite x]
  exact (Finset.single_le_sum (fun j _ => Nat.zero_le (occ x j))
    (Finset.mem_univ (peakSite x))).trans_eq x.property

/-- A profile bounded by `c` weights at most `c` times the background mass. -/
theorem peakFrameMoment_bounds {L N : ℕ} [NeZero L] (h : ℕ → ℝ) (h0 : h 0 = 0) {c : ℝ}
    (hnonneg : ∀ s < L, 0 ≤ h s) (hc : ∀ s < L, h s ≤ c) (x : State L N) :
    0 ≤ peakFrameMoment h x ∧ peakFrameMoment h x ≤ c * ((N : ℝ) - (largest x : ℝ)) := by
  have hmass : (∑ j, (occ x j : ℝ)) = (N : ℝ) := by exact_mod_cast x.property
  constructor
  · exact Finset.sum_nonneg (fun j _ =>
      mul_nonneg (hnonneg _ (peakOffset_lt x j)) (by positivity))
  · unfold peakFrameMoment
    have hsplit (j : Fin L) : (if j = peakSite x then 0 else c * (occ x j : ℝ)) =
        c * (occ x j : ℝ) - (if j = peakSite x then c * (occ x j : ℝ) else 0) := by
      split_ifs <;> ring
    calc
      _ ≤ ∑ j, (if j = peakSite x then 0 else c * (occ x j : ℝ)) := by
        apply Finset.sum_le_sum
        intro j _
        split_ifs with hj
        · rw [(peakOffset_eq_zero_iff x j).mpr hj, h0, zero_mul]
        · exact mul_le_mul_of_nonneg_right (hc _ (peakOffset_lt x j)) (Nat.cast_nonneg _)
      _ = _ := by
        simp_rw [hsplit]
        rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _),
          ← Finset.mul_sum, hmass, occ_peakSite]
        ring

/-- The stationary peak-frame balance on the majority region. The error is
the rate of leaving the region times the largest value of the moment there. -/
theorem stationary_peakFrameDrift_majority_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (h : ℕ → ℝ) (h0 : h 0 = 0) {c : ℝ}
    (hnonneg : ∀ s < L, 0 ≤ h s) (hc : ∀ s < L, h s ≤ c)
    (t : ℕ) (ht : N < 2 * t) (htN : t ≤ N) :
    |∑ x, μ.weight x * (if t < largest x then peakFrameDrift w h x else 0)| ≤
      w * (c * ((N - t : ℕ) : ℝ)) * (∑ x, if largest x = t + 1 then μ.weight x else 0) := by
  have hc0 : 0 ≤ c := (hnonneg 0 (NeZero.pos L)).trans (hc 0 (NeZero.pos L))
  have hbound (y : State L N) (hy : t ≤ largest y) :
      0 ≤ peakFrameMoment h y ∧ peakFrameMoment h y ≤ c * ((N - t : ℕ) : ℝ) := by
    obtain ⟨h1, h2⟩ := peakFrameMoment_bounds h h0 hnonneg hc y
    refine ⟨h1, h2.trans (mul_le_mul_of_nonneg_left ?_ hc0)⟩
    rw [Nat.cast_sub htN]
    exact sub_le_sub_left (by exact_mod_cast hy) _
  have hs := stationary_largestCutoff_abs_drift_le hL hw μ t (peakFrameMoment h)
    (b := c * ((N - t : ℕ) : ℝ)) (mul_nonneg hc0 (Nat.cast_nonneg _)) hbound
  have hlocal (x : State L N) :
      (if t < largest x then generator w (peakFrameMoment h) x else 0) =
        (if t < largest x then peakFrameDrift w h x else 0) := by
    split_ifs with hx
    · exact generator_peakFrameMoment_eq hL w h h0 x (by omega)
    · rfl
  simpa only [hlocal] using hs

private theorem natCast_sub_one_eq (s : ℕ) :
    (s : ℝ) - ((s - 1 : ℕ) : ℝ) = if s = 0 then 0 else 1 := by
  split_ifs with hs
  · simp [hs]
  · rw [Nat.cast_sub (by omega : 1 ≤ s)]
    ring

private theorem sum_departureMassRate {L N : ℕ} (w : ℝ) (x : State L N) :
    (∑ i, departureMassRate w (occ x i)) = w * occupiedCount x + ((N : ℝ) - singleCount x) := by
  have hmass : (∑ i, (occ x i : ℝ)) = (N : ℝ) := by exact_mod_cast x.property
  have hpoint (i : Fin L) : departureMassRate w (occ x i) =
      w * (if 0 < occ x i then 1 else 0) + ((occ x i : ℝ) - (if occ x i = 1 then 1 else 0)) := by
    unfold departureMassRate
    by_cases h₂ : 2 ≤ occ x i
    · have h₁ : 1 ≤ occ x i := by omega
      have hpos : 0 < occ x i := by omega
      have hne : occ x i ≠ 1 := by omega
      simp [h₁, h₂, hpos, hne]
    · by_cases h₁ : 1 ≤ occ x i
      · have hone : occ x i = 1 := by omega
        simp [hone]
      · have hzero : occ x i = 0 := by omega
        simp [hzero]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hmass]
  rfl

/-- The first moment of the background ahead of the peak. Chips push every
occupied site's mass forward at rate `w`, singles fall back as the peak
approaches, and mass entering the peak from behind loses its whole offset. -/
theorem peakFrameDrift_firstMoment {L N : ℕ} [NeZero L] (hL : 3 ≤ L) (w : ℝ)
    (x : State L N) (hpeak : 2 ≤ largest x) :
    peakFrameDrift w (fun s => (s : ℝ)) x =
      w * occupiedCount x - singleCount x -
        (L : ℝ) * departureMassRate w (occ x (peakSite x - 1)) := by
  set p := peakSite x with hp
  have hmass : (∑ j, (occ x j : ℝ)) = (N : ℝ) := by exact_mod_cast x.property
  have hp₂ : 2 ≤ occ x p := by rw [hp, occ_peakSite]; exact hpeak
  have hrear : p - 1 ≠ p := peakSite_sub_one_ne hL x
  have hshift : (∑ j, (occ x j : ℝ) *
      ((peakOffset x j : ℝ) - ((peakOffset x j - 1 : ℕ) : ℝ))) = (N : ℝ) - (occ x p : ℝ) := by
    have hpoint (j : Fin L) : (occ x j : ℝ) *
        ((peakOffset x j : ℝ) - ((peakOffset x j - 1 : ℕ) : ℝ)) =
          (occ x j : ℝ) - (if j = p then (occ x j : ℝ) else 0) := by
      rw [natCast_sub_one_eq]
      by_cases hj : j = p
      · rw [if_pos ((peakOffset_eq_zero_iff x j).mpr hj), if_pos hj]
        ring
      · rw [if_neg (fun h0 => hj ((peakOffset_eq_zero_iff x j).mp h0)), if_neg hj]
        ring
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _), hmass]
  have hfront : (∑ i, if i = p then (0 : ℝ) else departureMassRate w (occ x i) *
      ((peakOffset x (right i) : ℝ) - (peakOffset x i : ℝ))) =
        (∑ i, departureMassRate w (occ x i)) - departureMassRate w (occ x p) -
          (L : ℝ) * departureMassRate w (occ x (p - 1)) := by
    have hpoint (i : Fin L) : (if i = p then (0 : ℝ) else departureMassRate w (occ x i) *
        ((peakOffset x (right i) : ℝ) - (peakOffset x i : ℝ))) =
          departureMassRate w (occ x i) -
            (if i = p then departureMassRate w (occ x i) else 0) -
            (if i = p - 1 then (L : ℝ) * departureMassRate w (occ x i) else 0) := by
      by_cases hip : i = p
      · rw [if_pos hip, if_pos hip, if_neg (fun h => hrear (h.symm.trans hip))]
        ring
      · rw [if_neg hip, if_neg hip]
        by_cases hir : i = p - 1
        · have hright : right i = p := by rw [hir, right_eq_add_one, sub_add_cancel]
          rw [if_pos hir, hright, peakOffset_peakSite, hir, peakOffset_peakSite_sub_one hL x,
            Nat.cast_sub (by omega : 1 ≤ L)]
          push_cast
          ring
        · rw [if_neg hir, peakOffset_right x i hir]
          push_cast
          ring
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  have hqp : departureMassRate w (occ x p) = w + (occ x p : ℝ) := by
    unfold departureMassRate
    rw [if_pos (by omega), if_pos hp₂]
  unfold peakFrameDrift
  simp only [Nat.cast_one]
  rw [← hp, hfront, hshift, hqp, sum_departureMassRate]
  ring

/-- In stationary mean on the majority region, singles balance the chip rate
of the occupied sites, up to the mass flowing into the peak from behind. -/
theorem stationary_peak_singles_balance {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (t : ℕ) (ht : N < 2 * t) (htN : t ≤ N) :
    |∑ x, μ.weight x * (if t < largest x then
        w * occupiedCount x - singleCount x -
          (L : ℝ) * departureMassRate w (occ x (peakSite x - 1)) else 0)| ≤
      w * (((L - 1 : ℕ) : ℝ) * ((N - t : ℕ) : ℝ)) *
        (∑ x, if largest x = t + 1 then μ.weight x else 0) := by
  have h := stationary_peakFrameDrift_majority_le hL hw μ (fun s => (s : ℝ)) Nat.cast_zero
    (c := ((L - 1 : ℕ) : ℝ)) (fun s _ => Nat.cast_nonneg s)
    (fun s hs => by
      show (s : ℝ) ≤ ((L - 1 : ℕ) : ℝ)
      exact_mod_cast (show s ≤ L - 1 by omega)) t ht htN
  have hlocal (x : State L N) :
      (if t < largest x then peakFrameDrift w (fun s => (s : ℝ)) x else 0) =
        (if t < largest x then
          w * occupiedCount x - singleCount x -
            (L : ℝ) * departureMassRate w (occ x (peakSite x - 1)) else 0) := by
    split_ifs with hx
    · exact peakFrameDrift_firstMoment hL w x (by omega)
    · rfl
  simpa only [hlocal] using h

/-- Singles and the inflow into the peak from behind are together controlled
by the chip rate of the occupied sites, in stationary mean on the majority
region. -/
theorem stationary_peak_singles_rear_flux_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (t : ℕ) (ht : N < 2 * t) (htN : t ≤ N) :
    (∑ x, μ.weight x * (if t < largest x then
        singleCount x + (L : ℝ) * departureMassRate w (occ x (peakSite x - 1)) else 0)) ≤
      w * (∑ x, μ.weight x * (if t < largest x then occupiedCount x else 0)) +
        w * (((L - 1 : ℕ) : ℝ) * ((N - t : ℕ) : ℝ)) *
          (∑ x, if largest x = t + 1 then μ.weight x else 0) := by
  have h := (abs_le.mp (stationary_peak_singles_balance hL hw μ t ht htN)).1
  have hpoint (x : State L N) :
      μ.weight x * (if t < largest x then
        w * occupiedCount x - singleCount x -
          (L : ℝ) * departureMassRate w (occ x (peakSite x - 1)) else 0) =
        w * (μ.weight x * (if t < largest x then occupiedCount x else 0)) -
          μ.weight x * (if t < largest x then
            singleCount x + (L : ℝ) * departureMassRate w (occ x (peakSite x - 1)) else 0) := by
    split_ifs <;> ring
  simp_rw [hpoint] at h
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  linarith

theorem departureMassRate_nonneg {w : ℝ} (hw : 0 ≤ w) (a : ℕ) :
    0 ≤ departureMassRate w a := by
  unfold departureMassRate
  split_ifs <;> positivity

/-- The site just behind the peak is rarely occupied. Mass there would have
travelled around the ring, and its inflow rate is of order `w E[K] / L`. -/
theorem stationary_peak_rear_occupied_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (t : ℕ) (ht : N < 2 * t) (htN : t ≤ N) :
    w * (L : ℝ) * (∑ x, if t < largest x ∧ 1 ≤ occ x (peakSite x - 1) then μ.weight x else 0) ≤
      w * (∑ x, μ.weight x * (if t < largest x then occupiedCount x else 0)) +
        w * (((L - 1 : ℕ) : ℝ) * ((N - t : ℕ) : ℝ)) *
          (∑ x, if largest x = t + 1 then μ.weight x else 0) := by
  refine le_trans ?_ (stationary_peak_singles_rear_flux_le hL hw μ t ht htN)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have hS : 0 ≤ singleCount x :=
    Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
  by_cases hx : t < largest x
  · rw [if_pos hx]
    by_cases hr : 1 ≤ occ x (peakSite x - 1)
    · rw [if_pos ⟨hx, hr⟩]
      have hq : w ≤ departureMassRate w (occ x (peakSite x - 1)) := by
        unfold departureMassRate
        rw [if_pos hr]
        split_ifs <;> simp
      have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      nlinarith [μ.nonneg x, mul_le_mul_of_nonneg_left hq hL0]
    · rw [if_neg (fun h => hr h.2), mul_zero]
      exact mul_nonneg (μ.nonneg x) (add_nonneg hS
        (mul_nonneg (Nat.cast_nonneg L) (departureMassRate_nonneg hw _)))
  · rw [if_neg (fun h => hx h.1), if_neg hx, mul_zero, mul_zero]

/-- Choosing the cutoff to minimize the exit rate weighted by the background
mass on exit. The error then scales with the mean background, not the total
mass. -/
theorem exists_cutoff_with_small_weighted_boundary {L N : ℕ} [NeZero L] {w : ℝ}
    (μ : StationaryLaw L N w) (a b : ℕ) (hab : a ≤ b) :
    ∃ t ∈ Finset.Icc a b,
      ((N - t : ℕ) : ℝ) * (∑ x, if largest x = t + 1 then μ.weight x else 0) ≤
        (∑ x, μ.weight x * ((N : ℝ) - (largest x : ℝ) + 1)) / ((b + 1 - a : ℕ) : ℝ) := by
  set A := ∑ x, μ.weight x * ((N : ℝ) - (largest x : ℝ) + 1) with hA
  set c : ℝ := ((b + 1 - a : ℕ) : ℝ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact_mod_cast (show b + 1 - a ≠ 0 by omega)
  have hs : (Finset.Icc a b).Nonempty := ⟨a, Finset.mem_Icc.mpr ⟨le_rfl, hab⟩⟩
  have hpoint (x : State L N) :
      (∑ t ∈ Finset.Icc a b, if largest x = t + 1 then ((N - t : ℕ) : ℝ) else 0) ≤
        (N : ℝ) - (largest x : ℝ) + 1 := by
    have hM := largest_le_mass x
    by_cases h0 : largest x = 0
    · have hzero : (∑ t ∈ Finset.Icc a b,
          if largest x = t + 1 then ((N - t : ℕ) : ℝ) else 0) = 0 :=
        Finset.sum_eq_zero (fun t _ => if_neg (by omega))
      rw [hzero, h0]
      push_cast
      linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    · have hcongr : (∑ t ∈ Finset.Icc a b,
          if largest x = t + 1 then ((N - t : ℕ) : ℝ) else 0) =
            ∑ t ∈ Finset.Icc a b, if largest x - 1 = t then ((N - t : ℕ) : ℝ) else 0 :=
        Finset.sum_congr rfl (fun t _ => if_congr (by omega) rfl rfl)
      rw [hcongr, Finset.sum_ite_eq]
      split_ifs
      · rw [Nat.cast_sub (by omega : largest x - 1 ≤ N), Nat.cast_sub (by omega : 1 ≤ largest x)]
        push_cast
        linarith
      · have : (largest x : ℝ) ≤ N := by exact_mod_cast hM
        linarith
  have hsum :
      (∑ t ∈ Finset.Icc a b,
        ((N - t : ℕ) : ℝ) * (∑ x, if largest x = t + 1 then μ.weight x else 0)) ≤
        ∑ _t ∈ Finset.Icc a b, A / c := by
    have hswap : (∑ t ∈ Finset.Icc a b,
        ((N - t : ℕ) : ℝ) * (∑ x, if largest x = t + 1 then μ.weight x else 0)) =
          ∑ x, μ.weight x *
            (∑ t ∈ Finset.Icc a b, if largest x = t + 1 then ((N - t : ℕ) : ℝ) else 0) := by
      simp_rw [Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro t _
      split_ifs <;> ring
    rw [hswap, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    change _ ≤ c * (A / c)
    rw [mul_div_cancel₀ _ hc0, hA]
    exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (μ.nonneg x))
  exact Finset.exists_le_of_sum_le hs hsum

/-- Some cutoff in any band above half the mass controls the singles and the
inflow from behind, with an error proportional to the mean background plus
one divided by the width of the band. -/
theorem exists_majority_cutoff_singles_rear_flux_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (a b : ℕ) (hab : a ≤ b)
    (ha : N < 2 * a) (hbN : b ≤ N) :
    ∃ t ∈ Finset.Icc a b,
      (∑ x, μ.weight x * (if t < largest x then
          singleCount x + (L : ℝ) * departureMassRate w (occ x (peakSite x - 1)) else 0)) ≤
        w * (∑ x, μ.weight x * (if t < largest x then occupiedCount x else 0)) +
          w * ((L - 1 : ℕ) : ℝ) *
            ((∑ x, μ.weight x * ((N : ℝ) - (largest x : ℝ) + 1)) / ((b + 1 - a : ℕ) : ℝ)) := by
  obtain ⟨t, ht, hsmall⟩ := exists_cutoff_with_small_weighted_boundary μ a b hab
  have hta := (Finset.mem_Icc.mp ht).1
  have htb := (Finset.mem_Icc.mp ht).2
  refine ⟨t, ht, (stationary_peak_singles_rear_flux_le hL hw μ t (by omega) (by omega)).trans ?_⟩
  have hL1 : (0 : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsmall (mul_nonneg hw hL1)
  linarith [hmul]

end
end Chipping
