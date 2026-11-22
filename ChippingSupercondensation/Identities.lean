import ChippingSupercondensation.Stationary

/-!
# Exact stationary identities

The occupied-site balance `QK = wD - wA - C` from section 3 of the starter, the
change in the sum of squared masses and the resulting bound on neighbouring mass
products, and squared window masses with the offset identity
`stationary_massProductAt_eq` and its short-offset bounds. Summing over offsets
gives the directional balance `w - J = w E[K]/N + N/(L - 1) E[H]`
(`stationary_particleSeparation_directional_balance`). At positive density,
`E[H] → 0` is equivalent to `J → w`.
-/

namespace Chipping

open Filter
open scoped BigOperators Topology

noncomputable section

/-- The number of occupied sites, as a real-valued observable. -/
def occupiedCount {L N : ℕ} (x : State L N) : ℝ :=
  ∑ i, if 0 < occ x i then 1 else 0

/-- The number of sites with at least two particles. -/
def multipleCount {L N : ℕ} (x : State L N) : ℝ :=
  ∑ i, if 2 ≤ occ x i then 1 else 0

/-- Directed bonds with both ends occupied, including the wraparound bond. -/
def adjacentCount {L N : ℕ} (x : State L N) : ℝ :=
  ∑ i, if 0 < occ x i ∧ 0 < occ x (right i) then 1 else 0

/-- Directed bonds from a multiple pile to an occupied site. -/
def multipleAdjacentCount {L N : ℕ} (x : State L N) : ℝ :=
  ∑ i, if 2 ≤ occ x i ∧ 0 < occ x (right i) then 1 else 0

theorem occupiedCount_move {L N : ℕ} (hL : 3 ≤ L) (x : State L N)
    (i : Fin L) (k : ℕ) (hk : k ≤ occ x i) :
    occupiedCount (move x i k hk) - occupiedCount x =
      ((if 0 < occ x i - k then 1 else 0) - (if 0 < occ x i then 1 else 0)) +
      ((if 0 < occ x (right i) + k then 1 else 0) -
        (if 0 < occ x (right i) then 1 else 0)) := by
  exact sum_siteObservable_move hL (fun m => if 0 < m then 1 else 0) x i k hk

theorem occupiedCount_atSite {L N : ℕ} (hL : 3 ≤ L) (w : ℝ)
    (x : State L N) (i : Fin L) :
    atSite w occupiedCount x i =
      w * (if 2 ≤ occ x i then 1 else 0) -
      w * (if 0 < occ x i ∧ 0 < occ x (right i) then 1 else 0) -
      (if 2 ≤ occ x i ∧ 0 < occ x (right i) then 1 else 0) := by
  unfold atSite
  simp_rw [occupiedCount_move hL]
  by_cases hzero : occ x i = 0
  · simp [hzero]
  · have hpos : 0 < occ x i := by omega
    have hone : 1 ≤ occ x i := by omega
    by_cases hmulti : 2 ≤ occ x i
    · have hsub : 0 < occ x i - 1 := by omega
      have hchip : 0 < occ x (right i) + 1 := by omega
      have hwhole : 0 < occ x (right i) + occ x i := by omega
      by_cases hdest : 0 < occ x (right i)
      · simp [hone, hmulti, hpos, hsub, hchip, hwhole, hdest]
      · simp [hone, hmulti, hpos, hsub, hchip, hwhole, hdest]
    · have heq : occ x i = 1 := by omega
      by_cases hdest : 0 < occ x (right i)
      · simp [heq, hdest]
      · simp [heq, hdest]

/-- The statewise occupied-site balance on a periodic ring. -/
theorem occupied_site_balance {L N : ℕ} (hL : 3 ≤ L) (w : ℝ)
    (x : State L N) :
    generator w occupiedCount x =
      w * multipleCount x - w * adjacentCount x - multipleAdjacentCount x := by
  unfold generator
  simp_rw [occupiedCount_atSite hL]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rfl

/-- Stationarity turns the statewise balance into an expectation identity. -/
theorem stationary_occupied_site_balance {L N : ℕ} {w : ℝ}
    (hL : 3 ≤ L) (μ : StationaryLaw L N w) :
    w * (∑ x, μ.weight x * multipleCount x) =
      w * (∑ x, μ.weight x * adjacentCount x) +
        ∑ x, μ.weight x * multipleAdjacentCount x := by
  have h := μ.invariant occupiedCount
  simp_rw [occupied_site_balance hL, mul_sub] at h
  simp only [Finset.sum_sub_distrib] at h
  have hD : (∑ x, μ.weight x * (w * multipleCount x)) =
      w * (∑ x, μ.weight x * multipleCount x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hA : (∑ x, μ.weight x * (w * adjacentCount x)) =
      w * (∑ x, μ.weight x * adjacentCount x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hD, hA] at h
  linarith

/-- The sum of squared site masses. -/
def squaredMass {L N : ℕ} (x : State L N) : ℝ :=
  ∑ i, (occ x i : ℝ) ^ 2

theorem particleSeparation_eq_one_sub_squaredMass_div {L N : ℕ} (x : State L N) :
    particleSeparation x = 1 - squaredMass x / (N : ℝ) ^ 2 := by
  unfold particleSeparation siteMassFraction squaredMass
  simp_rw [div_pow]
  simp only [div_eq_mul_inv, Finset.sum_mul]

/-- Exact change in squared mass when transferring `k` particles. -/
theorem squaredMass_move {L N : ℕ} (hL : 3 ≤ L) (x : State L N) (i : Fin L)
    (k : ℕ) (hk : k ≤ occ x i) :
    squaredMass (move x i k hk) - squaredMass x =
      2 * (k : ℝ) * ((occ x (right i) : ℝ) - (occ x i : ℝ) + k) := by
  unfold squaredMass
  rw [sum_siteObservable_move hL (fun m : ℕ => (m : ℝ) ^ 2) x i k hk]
  push_cast [Nat.cast_sub hk]
  ring

/-- Chip drift divided by `-2w`, expressed as a signed sum for any rate. -/
def chipSquaredMassLoss {L N : ℕ} (x : State L N) : ℝ :=
  ∑ i, if 1 ≤ occ x i then (occ x i : ℝ) - (occ x (right i) : ℝ) - 1 else 0

/-- Whole pile drift divided by two, including only active departures. -/
def wholePileSquaredMassGain {L N : ℕ} (x : State L N) : ℝ :=
  ∑ i, if 2 ≤ occ x i then (occ x i : ℝ) * (occ x (right i) : ℝ) else 0

theorem squaredMass_atSite {L N : ℕ} (hL : 3 ≤ L) (w : ℝ)
    (x : State L N) (i : Fin L) :
    atSite w squaredMass x i =
      2 * ((if 2 ≤ occ x i then (occ x i : ℝ) * (occ x (right i) : ℝ) else 0) -
        w * (if 1 ≤ occ x i then (occ x i : ℝ) - (occ x (right i) : ℝ) - 1 else 0)) := by
  unfold atSite
  simp_rw [squaredMass_move hL]
  by_cases hchip : 1 ≤ occ x i <;> by_cases hwhole : 2 ≤ occ x i <;>
    simp [hchip, hwhole] <;> ring

/-- The generator separates into the chip and whole pile contributions. -/
theorem squared_mass_balance {L N : ℕ} (hL : 3 ≤ L) (w : ℝ) (x : State L N) :
    generator w squaredMass x =
      2 * (wholePileSquaredMassGain x - w * chipSquaredMassLoss x) := by
  unfold generator wholePileSquaredMassGain chipSquaredMassLoss
  simp_rw [squaredMass_atSite hL]
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib]

/-- At stationarity the two signed contributions to squared mass balance. -/
theorem stationary_squared_mass_balance {L N : ℕ} {w : ℝ}
    (hL : 3 ≤ L) (μ : StationaryLaw L N w) :
    (∑ x, μ.weight x * wholePileSquaredMassGain x) =
      w * (∑ x, μ.weight x * chipSquaredMassLoss x) := by
  have hinvariant := μ.invariant squaredMass
  simp_rw [squared_mass_balance hL] at hinvariant
  have hsum : (∑ x, μ.weight x * (2 * (wholePileSquaredMassGain x -
      w * chipSquaredMassLoss x))) =
      2 * ((∑ x, μ.weight x * wholePileSquaredMassGain x) -
        w * (∑ x, μ.weight x * chipSquaredMassLoss x)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum] at hinvariant
  linarith

/-- The signed chip term is bounded above by the total mass. -/
theorem chipSquaredMassLoss_le_total {L N : ℕ} (x : State L N) :
    chipSquaredMassLoss x ≤ (N : ℝ) := by
  have htotal : ∑ i, occ x i = N := x.property
  unfold chipSquaredMassLoss
  calc
    _ ≤ ∑ i, (occ x i : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · have hright : (0 : ℝ) ≤ (occ x (right i) : ℝ) := by positivity
        linarith
      · positivity
    _ = (N : ℝ) := by exact_mod_cast htotal

/-- Expected whole pile contact grows at most linearly in total mass. -/
theorem stationary_wholePileSquaredMassGain_le {L N : ℕ} {w : ℝ}
    (hL : 3 ≤ L) (hw : 0 ≤ w) (μ : StationaryLaw L N w) :
    (∑ x, μ.weight x * wholePileSquaredMassGain x) ≤ w * (N : ℝ) := by
  rw [stationary_squared_mass_balance hL μ]
  apply mul_le_mul_of_nonneg_left _ hw
  calc
    _ ≤ ∑ x, μ.weight x * (N : ℝ) :=
      Finset.sum_le_sum (fun x _ =>
        mul_le_mul_of_nonneg_left (chipSquaredMassLoss_le_total x) (μ.nonneg x))
    _ = (N : ℝ) := by rw [← Finset.sum_mul, μ.normalized, one_mul]

/-- The expected mass product over all directed neighbouring bonds. -/
def meanAdjacentMassProduct {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) : ℝ :=
  ∑ x, μ.weight x * ∑ i, (occ x i : ℝ) * (occ x (right i) : ℝ)

private theorem right_injective {L : ℕ} : Function.Injective (@right L) := by
  intro i j heq
  apply Fin.ext
  have hv : i.val + 1 ≡ j.val + 1 [MOD L] := congrArg Fin.val heq
  simpa [Nat.ModEq, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using
    hv.add_right_cancel' 1

/-- Allowing singleton departures adds at most one total mass to the contact bound. -/
theorem meanAdjacentMassProduct_le {L N : ℕ} {w : ℝ}
    (hL : 3 ≤ L) (hw : 0 ≤ w) (μ : StationaryLaw L N w) :
    meanAdjacentMassProduct μ ≤ (w + 1) * (N : ℝ) := by
  have hstate (x : State L N) :
      (∑ i, (occ x i : ℝ) * (occ x (right i) : ℝ)) ≤
        wholePileSquaredMassGain x + (N : ℝ) := by
    have htotal : ∑ i, occ x i = N := x.property
    have hright : ∑ i, (occ x (right i) : ℝ) = (N : ℝ) := by
      have hsum : ∑ i, occ x (right i) = ∑ i, occ x i :=
        (Equiv.ofBijective right (Finite.injective_iff_bijective.mp right_injective)).sum_comp
          (occ x)
      exact_mod_cast hsum.trans htotal
    rw [← hright]
    unfold wholePileSquaredMassGain
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hi
    · exact le_add_of_nonneg_right (by positivity)
    · have hi' : (occ x i : ℝ) ≤ 1 := by exact_mod_cast (show occ x i ≤ 1 by omega)
      simpa using mul_le_mul_of_nonneg_right hi' (show (0 : ℝ) ≤ (occ x (right i) : ℝ) by positivity)
  unfold meanAdjacentMassProduct
  calc
    _ ≤ ∑ x, μ.weight x * (wholePileSquaredMassGain x + (N : ℝ)) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hstate x) (μ.nonneg x))
    _ = (∑ x, μ.weight x * wholePileSquaredMassGain x) + (N : ℝ) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, μ.normalized, one_mul]
    _ ≤ (w + 1) * (N : ℝ) := by
      rw [add_mul, one_mul]
      exact add_le_add_right (stationary_wholePileSquaredMassGain_le hL hw μ) _

/-- The probability that two independently sampled particles lie on a directed
neighbouring bond tends to zero when the total mass grows at fixed rate. -/
theorem normalized_meanAdjacentMassProduct_tendsto_zero {L N : ℕ → ℕ} {w : ℝ}
    (hL : ∀ n, 3 ≤ L n) (hw : 0 ≤ w) (hN : Tendsto N atTop atTop)
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w) :
    Tendsto (fun n => meanAdjacentMassProduct (μ n) / (N n : ℝ) ^ 2) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n => (N n : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp hN
  have hlimit : Tendsto (fun n => (w + 1) / (N n : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := w + 1)).mul hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlimit
  · intro n
    unfold meanAdjacentMassProduct
    exact div_nonneg (Finset.sum_nonneg (fun x _ => mul_nonneg ((μ n).nonneg x)
      (Finset.sum_nonneg (fun i _ => by positivity)))) (sq_nonneg _)
  · intro n
    calc
      _ ≤ (w + 1) * (N n : ℝ) / (N n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (meanAdjacentMassProduct_le (hL n) hw (μ n)) (sq_nonneg _)
      _ = (w + 1) / (N n : ℝ) := by
        by_cases hn : (N n : ℝ) = 0
        · simp [hn]
        · field_simp [hn]
          ring

/-- The mass of a window of length `r` ending at site `j`. -/
def windowMass {L N : ℕ} [NeZero L] (r : ℕ) (x : State L N) (j : Fin L) : ℝ :=
  ∑ s ∈ Finset.range r, (occ x (j - (s : Fin L)) : ℝ)

theorem transfer_window_sum_change {L : ℕ} [NeZero L] (r : ℕ)
    (x : Fin L → ℕ) (i : Fin L) (k : ℕ) (hk : k ≤ x i) (j : Fin L) :
    (∑ s ∈ Finset.range r, (transfer x i k (j - (s : Fin L)) : ℝ)) -
      (∑ s ∈ Finset.range r, (x (j - (s : Fin L)) : ℝ)) =
      (k : ℝ) * ((if j = i + (r : Fin L) then 1 else 0) - (if j = i then 1 else 0)) := by
  let f (s : ℕ) : ℝ := if j - (s : Fin L) = i then 1 else 0
  rw [← Finset.sum_sub_distrib]
  have hdiff (s : ℕ) :
      (transfer x i k (j - (s : Fin L)) : ℝ) - (x (j - (s : Fin L)) : ℝ) =
        (k : ℝ) * (f (s + 1) - f s) := by
    have hsource (t : Fin L) : (if t = i then k else 0) ≤ x t := by
      split_ifs with ht
      · simpa [ht] using hk
      · exact Nat.zero_le _
    have hiff : j - (s : Fin L) = right i ↔ j - ((s + 1 : ℕ) : Fin L) = i := by
      simp only [right_eq_add_one, Nat.cast_add, Nat.cast_one,
        sub_add_eq_sub_sub, sub_eq_iff_eq_add]
    unfold transfer
    push_cast [Nat.cast_sub (hsource _)]
    unfold f
    simp only [← hiff]
    split_ifs <;> ring
  simp_rw [hdiff]
  rw [← Finset.mul_sum, sum_range_forward_diff]
  simp [f, sub_eq_iff_eq_add]

theorem windowMass_move {L N : ℕ} [NeZero L] (r : ℕ)
    (x : State L N) (i : Fin L) (k : ℕ) (hk : k ≤ occ x i) (j : Fin L) :
    windowMass r (move x i k hk) j - windowMass r x j =
      (k : ℝ) * ((if j = i + (r : Fin L) then 1 else 0) - (if j = i then 1 else 0)) := by
  simpa only [windowMass, occ_move] using transfer_window_sum_change r (occ x) i k hk j

/-- The sum of squares of the masses of all translated windows. -/
def squaredWindowMass {L N : ℕ} [NeZero L] (r : ℕ) (x : State L N) : ℝ :=
  ∑ j, windowMass r x j ^ 2

theorem squaredWindowMass_move {L N : ℕ} [NeZero L]
    (r : ℕ) (hr : (r : Fin L) ≠ 0) (x : State L N) (i : Fin L)
    (k : ℕ) (hk : k ≤ occ x i) :
    squaredWindowMass r (move x i k hk) - squaredWindowMass r x =
      2 * (k : ℝ) * (windowMass r x (i + (r : Fin L)) - windowMass r x i) +
        2 * (k : ℝ) ^ 2 := by
  have hends : i + (r : Fin L) ≠ i :=
    fun h => hr (add_left_cancel (h.trans (add_zero i).symm))
  unfold squaredWindowMass
  rw [← Finset.sum_sub_distrib]
  have hlocal (j : Fin L) :
      windowMass r (move x i k hk) j ^ 2 - windowMass r x j ^ 2 =
        (if j = i + (r : Fin L) then 2 * k * windowMass r x j + (k : ℝ) ^ 2 else 0) +
        (if j = i then -(2 * k * windowMass r x j) + (k : ℝ) ^ 2 else 0) := by
    have h := windowMass_move r x i k hk j
    have hmove : windowMass r (move x i k hk) j = windowMass r x j +
        (k : ℝ) * ((if j = i + (r : Fin L) then 1 else 0) - (if j = i then 1 else 0)) := by
      linarith
    rw [hmove]
    split_ifs with h₁ h₂
    · exact (hends (h₁.symm.trans h₂)).elim
    all_goals ring
  simp_rw [hlocal]
  simp [Finset.sum_add_distrib]
  ring

/-- The sum of mass products at a fixed oriented offset on the ring. -/
def massProductAt {L N : ℕ} (x : State L N) (d : Fin L) : ℝ :=
  ∑ i, (occ x i : ℝ) * (occ x (i + d) : ℝ)

theorem massProductAt_neg {L N : ℕ} [NeZero L] (x : State L N) (d : Fin L) :
    massProductAt x (-d) = massProductAt x d := by
  unfold massProductAt
  calc
    _ = ∑ i : Fin L, (occ x (i + d) : ℝ) * (occ x ((i + d) + -d) : ℝ) := by
      symm
      exact Equiv.sum_comp (Equiv.addRight d)
        (fun i => (occ x i : ℝ) * (occ x (i + -d) : ℝ))
    _ = _ := by simp [mul_comm]

theorem windowMass_at_forward_end {L N : ℕ} [NeZero L]
    (x : State L N) (i : Fin L) (r : ℕ) :
    windowMass r x (i + (r : Fin L)) =
      ∑ s ∈ Finset.range r, (occ x (i + ((s + 1 : ℕ) : Fin L)) : ℝ) := by
  induction r with
  | zero => simp [windowMass]
  | succ r h =>
    have hshift (s : ℕ) : i + ((r + 1 : ℕ) : Fin L) - ((s + 1 : ℕ) : Fin L) =
        i + (r : Fin L) - (s : Fin L) := by
      push_cast
      abel
    rw [windowMass, Finset.sum_range_succ', Finset.sum_range_succ]
    simp_rw [hshift]
    rw [← windowMass, h]
    simp [add_comm]

private theorem sum_mass_window_diff {L N : ℕ} [NeZero L] (x : State L N) (r : ℕ) :
    (∑ i, (occ x i : ℝ) *
      (windowMass r x (i + (r : Fin L)) - windowMass r x i)) =
      massProductAt x (r : Fin L) - squaredMass x := by
  simp_rw [windowMass_at_forward_end, windowMass, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin L))) (t := Finset.range r),
    Finset.sum_comm (s := (Finset.univ : Finset (Fin L))) (t := Finset.range r)]
  have hsum (s : ℕ) :
      (∑ i, (occ x i : ℝ) * (occ x (i - (s : Fin L)) : ℝ)) =
        massProductAt x (s : Fin L) := by
    rw [← massProductAt_neg]
    simp only [massProductAt, sub_eq_add_neg]
  simp_rw [hsum]
  change (∑ s ∈ Finset.range r, massProductAt x ((s + 1 : ℕ) : Fin L)) -
      (∑ s ∈ Finset.range r, massProductAt x (s : Fin L)) = _
  rw [← Finset.sum_sub_distrib,
    sum_range_forward_diff (fun s : ℕ => massProductAt x (s : Fin L)) r]
  simp [massProductAt, squaredMass, pow_two]

/-- The change from a rate-one whole move at every occupied site.
Singletons move only at rate `w`. Larger piles also chip at rate `w`. -/
def rateCorrection (w : ℝ) (a : ℕ) : ℝ :=
  if 2 ≤ a then w else if 1 ≤ a then w - 1 else 0

/-- The correction to the squared window drift from the actual departure rates. -/
def windowRateCorrection {L N : ℕ} [NeZero L] (w : ℝ) (r : ℕ) (x : State L N) : ℝ :=
  ∑ i, rateCorrection w (occ x i) *
    (windowMass r x (i + (r : Fin L)) - windowMass r x i + 1)

private theorem squaredWindowMass_atSite {L N : ℕ} [NeZero L]
    (w : ℝ) (r : ℕ) (hr : (r : Fin L) ≠ 0) (x : State L N) (i : Fin L) :
    atSite w (squaredWindowMass r) x i =
      2 * ((occ x i : ℝ) *
        (windowMass r x (i + (r : Fin L)) - windowMass r x i + (occ x i : ℝ)) +
        rateCorrection w (occ x i) *
          (windowMass r x (i + (r : Fin L)) - windowMass r x i + 1)) := by
  unfold atSite
  simp_rw [squaredWindowMass_move r hr]
  by_cases hmany : 2 ≤ occ x i
  · have hone : 1 ≤ occ x i := by omega
    simp [rateCorrection, hmany, hone]
    ring
  · by_cases hone : 1 ≤ occ x i
    · have hmass : occ x i = 1 := by omega
      simp [rateCorrection, hmass]
      ring
    · have hmass : occ x i = 0 := by omega
      simp [rateCorrection, hmass]

/-- The squared window drift isolates the mass product at the window's length. -/
theorem squared_window_mass_balance {L N : ℕ} [NeZero L]
    (w : ℝ) (r : ℕ) (hr : (r : Fin L) ≠ 0) (x : State L N) :
    generator w (squaredWindowMass r) x =
      2 * (massProductAt x (r : Fin L) + windowRateCorrection w r x) := by
  unfold generator windowRateCorrection
  simp_rw [squaredWindowMass_atSite w r hr]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hwhole : (∑ i, (occ x i : ℝ) *
      (windowMass r x (i + (r : Fin L)) - windowMass r x i + (occ x i : ℝ))) =
      massProductAt x (r : Fin L) := by
    simp only [mul_add, Finset.sum_add_distrib, sum_mass_window_diff, ← pow_two]
    rw [← squaredMass, sub_add_cancel]
  rw [hwhole]

/-- Under stationarity, the expected correlation at a nonzero offset equals
the negative of the expected rate correction for that window. -/
theorem stationary_massProductAt_eq {L N : ℕ} [NeZero L] {w : ℝ}
    (r : ℕ) (hr : (r : Fin L) ≠ 0) (μ : StationaryLaw L N w) :
    (∑ x, μ.weight x * massProductAt x (r : Fin L)) =
      -(∑ x, μ.weight x * windowRateCorrection w r x) := by
  have h := μ.invariant (squaredWindowMass r)
  simp_rw [squared_window_mass_balance w r hr, mul_left_comm _ (2 : ℝ), mul_add] at h
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at h
  linarith

private theorem sum_windowMass {L N : ℕ} [NeZero L] (r : ℕ) (x : State L N) :
    (∑ i, windowMass r x i) = (r : ℝ) * (N : ℝ) := by
  have hmass : (∑ i, (occ x i : ℝ)) = (N : ℝ) := by exact_mod_cast x.property
  unfold windowMass
  rw [Finset.sum_comm]
  have hshift (s : ℕ) : (∑ i, (occ x (i - (s : Fin L)) : ℝ)) = (N : ℝ) := by
    rw [← hmass]
    simp only [sub_eq_add_neg]
    exact Equiv.sum_comp (Equiv.addRight (-(s : Fin L))) (fun i => (occ x i : ℝ))
  simp [hshift]

private theorem neg_windowRateCorrection_le {L N : ℕ} [NeZero L]
    {w : ℝ} (hw : 0 ≤ w) (hw' : w ≤ 1) (r : ℕ) (x : State L N) :
    -windowRateCorrection w r x ≤ ((r : ℝ) + 1) * (N : ℝ) := by
  have hmass : (∑ i, (occ x i : ℝ)) = (N : ℝ) := by exact_mod_cast x.property
  have hforward : (∑ i, windowMass r x (i + (r : Fin L))) = (r : ℝ) * (N : ℝ) :=
    (Equiv.sum_comp (Equiv.addRight (r : Fin L)) (windowMass r x)).trans (sum_windowMass r x)
  unfold windowRateCorrection
  rw [← Finset.sum_neg_distrib]
  calc
    _ ≤ ∑ i, (w * windowMass r x i + (1 - w) * windowMass r x (i + (r : Fin L)) +
        (occ x i : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      have hright : 0 ≤ windowMass r x (i + (r : Fin L)) :=
        Finset.sum_nonneg (fun _ _ => by positivity)
      have hleft : 0 ≤ windowMass r x i :=
        Finset.sum_nonneg (fun _ _ => by positivity)
      have hrw := mul_nonneg hw hright
      have hrw' := mul_nonneg (sub_nonneg.mpr hw') hright
      have hlw := mul_nonneg hw hleft
      have hlw' := mul_nonneg (sub_nonneg.mpr hw') hleft
      by_cases hmany : 2 ≤ occ x i
      · simp only [rateCorrection, if_pos hmany]
        have hm : (0 : ℝ) ≤ (occ x i : ℝ) := by positivity
        nlinarith
      · by_cases hone : 1 ≤ occ x i
        · have hm : occ x i = 1 := by omega
          simp [rateCorrection, hm]
          nlinarith
        · simp only [rateCorrection, if_neg hmany, if_neg hone, zero_mul, neg_zero]
          positivity
    _ = ((r : ℝ) + 1) * (N : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, sum_windowMass, hforward, hmass]
      ring

/-- The expected mass product at a nonzero offset is at most `(r + 1) * N`
when the chip rate is at most one. -/
theorem stationary_massProductAt_le {L N : ℕ} [NeZero L] {w : ℝ}
    (hw : 0 ≤ w) (hw' : w ≤ 1) (r : ℕ) (hr : (r : Fin L) ≠ 0)
    (μ : StationaryLaw L N w) :
    (∑ x, μ.weight x * massProductAt x (r : Fin L)) ≤ ((r : ℝ) + 1) * (N : ℝ) := by
  rw [stationary_massProductAt_eq r hr μ, ← Finset.sum_neg_distrib]
  simp_rw [← mul_neg]
  calc
    _ ≤ ∑ x, μ.weight x * (((r : ℝ) + 1) * (N : ℝ)) :=
      Finset.sum_le_sum (fun x _ =>
        mul_le_mul_of_nonneg_left (neg_windowRateCorrection_le hw hw' r x) (μ.nonneg x))
    _ = _ := by rw [← Finset.sum_mul, μ.normalized, one_mul]

/-- The stationary probability of a prescribed nonzero offset is bounded by
its window length plus one, divided by the total mass. -/
theorem normalized_stationary_massProductAt_bounds {L N : ℕ} [NeZero L] {w : ℝ}
    (hw : 0 ≤ w) (hw' : w ≤ 1) (r : ℕ) (hr : (r : Fin L) ≠ 0)
    (μ : StationaryLaw L N w) :
    let p := (∑ x, μ.weight x * massProductAt x (r : Fin L)) / (N : ℝ) ^ 2
    0 ≤ p ∧ p ≤ ((r : ℝ) + 1) / (N : ℝ) := by
  dsimp
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun x _ => mul_nonneg (μ.nonneg x)
      (Finset.sum_nonneg (fun _ _ => by positivity)))) (sq_nonneg _)
  · calc
      _ ≤ (((r : ℝ) + 1) * (N : ℝ)) / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (stationary_massProductAt_le hw hw' r hr μ) (sq_nonneg _)
      _ = ((r : ℝ) + 1) / (N : ℝ) := by
        by_cases hN : (N : ℝ) = 0
        · simp [hN]
        · field_simp [hN]
          ring

/-- Any prescribed offset whose window length is sublinear in total mass has
vanishing stationary probability. -/
theorem normalized_stationary_massProductAt_tendsto_zero
    {L N r : ℕ → ℕ} [∀ n, NeZero (L n)] {w : ℝ} (hw : 0 ≤ w) (hw' : w ≤ 1)
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w)
    (hr : ∀ᶠ n in atTop, (r n : Fin (L n)) ≠ 0)
    (hscale : Tendsto (fun n => ((r n : ℝ) + 1) / (N n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (∑ x, (μ n).weight x * massProductAt x (r n : Fin (L n))) / (N n : ℝ) ^ 2)
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hscale
  · exact hr.mono (fun n hn => (normalized_stationary_massProductAt_bounds hw hw' (r n) hn (μ n)).1)
  · exact hr.mono (fun n hn => (normalized_stationary_massProductAt_bounds hw hw' (r n) hn (μ n)).2)

/-- The combined probability of clockwise offsets from one through `R`. -/
theorem stationary_shortOffsetProbability_le {L N : ℕ} [NeZero L] {w : ℝ}
    (hw : 0 ≤ w) (hw' : w ≤ 1) (R : ℕ) (hR : R < L) (μ : StationaryLaw L N w) :
    (∑ d ∈ Finset.range R,
      (∑ x, μ.weight x * massProductAt x ((d + 1 : ℕ) : Fin L)) / (N : ℝ) ^ 2) ≤
      (R : ℝ) * ((R : ℝ) + 1) / (N : ℝ) := by
  calc
    _ ≤ ∑ _d ∈ Finset.range R, ((R : ℝ) + 1) / (N : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdR : d + 1 ≤ R := Nat.succ_le_of_lt (Finset.mem_range.mp hd)
      have hdL : d + 1 < L := lt_of_le_of_lt hdR hR
      have hdne : ((d + 1 : ℕ) : Fin L) ≠ 0 := by
        intro he
        have hv := congrArg Fin.val he
        change (d + 1) % L = 0 at hv
        rw [Nat.mod_eq_of_lt hdL] at hv
        omega
      refine ((normalized_stationary_massProductAt_bounds hw hw' (d + 1) hdne μ).2).trans ?_
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact add_le_add_right (by exact_mod_cast hdR) 1
    _ = _ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_assoc]

private theorem sum_massProductAt {L N : ℕ} [NeZero L] (x : State L N) :
    (∑ d, massProductAt x d) = (N : ℝ) ^ 2 := by
  have hmass : (∑ i, (occ x i : ℝ)) = (N : ℝ) := by exact_mod_cast x.property
  have hshift (i : Fin L) : (∑ d, (occ x (i + d) : ℝ)) = (N : ℝ) :=
    (Equiv.sum_comp (Equiv.addLeft i) (fun j => (occ x j : ℝ))).trans hmass
  unfold massProductAt
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hshift]
  rw [← Finset.sum_mul, hmass, pow_two]

/-- The full separation probability sums the mass products at every nonzero offset. -/
theorem particleSeparation_eq_nonzeroOffsetProbability {L N : ℕ} [NeZero L]
    (x : State L N) (hN : 0 < N) :
    particleSeparation x = (∑ d ∈ Finset.univ.erase (0 : Fin L), massProductAt x d) / (N : ℝ) ^ 2 := by
  classical
  have hzero : massProductAt x (0 : Fin L) = squaredMass x := by
    simp [massProductAt, squaredMass, pow_two]
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rw [particleSeparation_eq_one_sub_squaredMass_div,
    Finset.sum_erase_eq_sub (Finset.mem_univ (0 : Fin L)), sum_massProductAt, hzero, sub_div,
    div_self (pow_ne_zero _ hNreal)]

/-- The stationary mass product summed around the ring is `L` times the
same correlation measured from any one site. -/
theorem stationary_massProductAt_eq_single_site {L N : ℕ} [NeZero L]
    (hL : 3 ≤ L) {w : ℝ} (hw : 0 < w) (μ : StationaryLaw L N w) (i d : Fin L) :
    (∑ x, μ.weight x * massProductAt x d) =
      (L : ℝ) * ∑ x, μ.weight x * ((occ x i : ℝ) * (occ x (i + d) : ℝ)) := by
  let f (j : Fin L) (x : State L N) : ℝ :=
    μ.weight x * ((occ x j : ℝ) * (occ x (j + d) : ℝ))
  have heq (j : Fin L) : (∑ x, f j x) = ∑ x, f i x := by
    let e := i - j
    have hi : i + -e = j := by dsimp [e]; abel
    have hid : i + d + -e = j + d := by dsimp [e]; abel
    calc
      _ = ∑ x, f i (rotateState e x) := by
        simp only [f, stationaryWeight_rotateState hL hw μ, occ_rotateState, hi, hid]
      _ = _ := Equiv.sum_comp (rotateStateEquiv e) (f i)
  conv_lhs =>
    simp only [massProductAt, Finset.mul_sum]
    rw [Finset.sum_comm]
  change (∑ j, ∑ x, f j x) = (L : ℝ) * ∑ x, f i x
  simp [heq, nsmul_eq_mul]

/-- The rate correction weighted by the difference between the mass in the
next `r` sites and the previous `r - 1` sites, excluding the departure site. -/
def offsetRateImbalance {L N : ℕ} [NeZero L] (w : ℝ) (r : ℕ) (x : State L N) : ℝ :=
  ∑ i, rateCorrection w (occ x i) *
    ((∑ s ∈ Finset.range r, (occ x (i + ((s + 1 : ℕ) : Fin L)) : ℝ)) -
      (∑ s ∈ Finset.range (r - 1), (occ x (i - ((s + 1 : ℕ) : Fin L)) : ℝ)))

private theorem rateCorrection_mul_mass_sub_one (w : ℝ) (a : ℕ) :
    rateCorrection w a * ((a : ℝ) - 1) = w * ((a : ℝ) - (if 0 < a then 1 else 0)) := by
  by_cases hmany : 2 ≤ a
  · have hpos : 0 < a := by omega
    simp [rateCorrection, hmany, hpos]
  · by_cases hpos : 0 < a
    · have ha : a = 1 := by omega
      simp [rateCorrection, ha]
    · have ha : a = 0 := by omega
      simp [rateCorrection, ha]

private theorem windowRateCorrection_eq_offsetRateImbalance_sub {L N : ℕ} [NeZero L]
    (w : ℝ) (r : ℕ) (x : State L N) :
    windowRateCorrection w (r + 1) x =
      offsetRateImbalance w (r + 1) x - w * ((N : ℝ) - occupiedCount x) := by
  have hback (i : Fin L) : windowMass (r + 1) x i = (occ x i : ℝ) +
      ∑ s ∈ Finset.range r, (occ x (i - ((s + 1 : ℕ) : Fin L)) : ℝ) := by
    unfold windowMass
    rw [Finset.sum_range_succ']
    simp [add_comm]
  have hmass : (∑ i, (occ x i : ℝ)) = (N : ℝ) := by exact_mod_cast x.property
  unfold windowRateCorrection offsetRateImbalance occupiedCount
  simp_rw [windowMass_at_forward_end, hback, Nat.add_sub_cancel]
  rw [← hmass, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := rateCorrection_mul_mass_sub_one w (occ x i)
  nlinarith only [h]

private theorem sum_erase_zero_eq_sum_range {L : ℕ} [NeZero L] (f : Fin L → ℝ) :
    (∑ d ∈ Finset.univ.erase 0, f d) = ∑ r ∈ Finset.range (L - 1), f ((r + 1 : ℕ) : Fin L) := by
  classical
  cases L with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ L =>
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : Fin (L + 1))), Fin.sum_univ_succ]
    simp only [add_sub_cancel_left, Nat.add_sub_cancel]
    rw [← Fin.sum_univ_eq_sum_range (fun r => f ((r + 1 : ℕ) : Fin (L + 1))) L]
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    apply Fin.ext
    rw [Fin.val_natCast, Nat.mod_eq_of_lt (Nat.succ_lt_succ r.isLt)]
    rfl

/-- The chipping rate correction summed across all nonzero window lengths. -/
def directionalRateImbalance {L N : ℕ} [NeZero L] (w : ℝ) (x : State L N) : ℝ :=
  ∑ r ∈ Finset.range (L - 1), offsetRateImbalance w (r + 1) x

/-- The stationary expected number of occupied sites. -/
def meanOccupiedCount {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) : ℝ :=
  ∑ x, μ.weight x * occupiedCount x

/-- Summing the window balances gives an exact identity for the full separation
probability. The on-site term is the chip rate times the mass in excess of one
particle per occupied site. -/
theorem stationary_particleSeparation_directional_balance {L N : ℕ} [NeZero L] {w : ℝ}
    (hN : 0 < N) (μ : StationaryLaw L N w) :
    (N : ℝ) ^ 2 * meanParticleSeparation μ +
        (∑ x, μ.weight x * directionalRateImbalance w x) =
      ((L - 1 : ℕ) : ℝ) * w * ((N : ℝ) - meanOccupiedCount μ) := by
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hsep (x : State L N) :
      (N : ℝ) ^ 2 * particleSeparation x =
        ∑ r ∈ Finset.range (L - 1), massProductAt x ((r + 1 : ℕ) : Fin L) := by
    rw [particleSeparation_eq_nonzeroOffsetProbability x hN, sum_erase_zero_eq_sum_range]
    field_simp [hNreal]
  have hterm :
      (∑ x, μ.weight x * (w * ((N : ℝ) - occupiedCount x))) =
        w * ((N : ℝ) - meanOccupiedCount μ) := by
    simp only [meanOccupiedCount, mul_left_comm _ w, ← Finset.mul_sum, mul_sub,
      Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, μ.normalized, one_mul]
  have hstationary (r : ℕ) (hr : r ∈ Finset.range (L - 1)) :
      (∑ x, μ.weight x * massProductAt x ((r + 1 : ℕ) : Fin L)) +
        (∑ x, μ.weight x * offsetRateImbalance w (r + 1) x) =
        w * ((N : ℝ) - meanOccupiedCount μ) := by
    have hlt : r + 1 < L := by have := Finset.mem_range.mp hr; omega
    have hne : ((r + 1 : ℕ) : Fin L) ≠ 0 := by
      intro he
      have hv := congrArg Fin.val he
      change (r + 1) % L = 0 at hv
      rw [Nat.mod_eq_of_lt hlt] at hv
      omega
    have h := stationary_massProductAt_eq (r + 1) hne μ
    have hmul (x : State L N) :
        μ.weight x * (offsetRateImbalance w (r + 1) x - w * ((N : ℝ) - occupiedCount x)) =
          μ.weight x * offsetRateImbalance w (r + 1) x -
          μ.weight x * (w * ((N : ℝ) - occupiedCount x)) := mul_sub _ _ _
    simp_rw [windowRateCorrection_eq_offsetRateImbalance_sub, hmul,
      Finset.sum_sub_distrib, hterm] at h
    linarith
  unfold meanParticleSeparation directionalRateImbalance
  simp_rw [Finset.mul_sum, mul_left_comm ((N : ℝ) ^ 2), hsep, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (State L N)))
    (t := Finset.range (L - 1)), ← Finset.sum_add_distrib]
  calc
    _ = ∑ _r ∈ Finset.range (L - 1), w * ((N : ℝ) - meanOccupiedCount μ) := by
      apply Finset.sum_congr rfl
      exact hstationary
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc]

/-- Every occupied site other than a largest pile accounts for at least one
particle in the background. -/
theorem occupiedCount_le_one_add_mass_mul_backgroundFraction {L N : ℕ} [NeZero L]
    (x : State L N) (hN : 0 < N) :
    occupiedCount x ≤ 1 + (N : ℝ) * backgroundFraction x := by
  classical
  obtain ⟨i, hi, hlarge⟩ :=
    Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (occ x)
  change largest x = occ x i at hlarge
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hle : largest x ≤ N := by
    rw [hlarge]
    exact (Finset.single_le_sum (fun j _ => Nat.zero_le (occ x j)) hi).trans_eq x.property
  have hback : (N : ℝ) * backgroundFraction x = (N : ℝ) - (occ x i : ℝ) := by
    unfold backgroundFraction
    rw [Nat.cast_sub hle, hlarge]
    field_simp [hn]
  have hsum : (∑ j, (occ x j : ℝ)) = (N : ℝ) := by exact_mod_cast x.property
  have hother :
      (∑ j ∈ Finset.univ.erase i, (if 0 < occ x j then (1 : ℝ) else 0)) ≤
        ∑ j ∈ Finset.univ.erase i, (occ x j : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    split_ifs with hj
    · exact_mod_cast hj
    · positivity
  rw [Finset.sum_erase_eq_sub hi, Finset.sum_erase_eq_sub hi, hsum] at hother
  have hone : (if 0 < occ x i then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  change occupiedCount x - _ ≤ _ at hother
  rw [hback]
  linarith

theorem meanOccupiedCount_le_one_add_mass_mul_meanParticleSeparation
    {L N : ℕ} [NeZero L] {w : ℝ} (μ : StationaryLaw L N w) (hN : 0 < N) :
    meanOccupiedCount μ ≤ 1 + (N : ℝ) * meanParticleSeparation μ := by
  unfold meanOccupiedCount meanParticleSeparation
  calc
    _ ≤ ∑ x, μ.weight x * (1 + (N : ℝ) * particleSeparation x) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (μ.nonneg x)
      refine (occupiedCount_le_one_add_mass_mul_backgroundFraction x hN).trans ?_
      exact add_le_add_left (mul_le_mul_of_nonneg_left
        (backgroundFraction_le_particleSeparation_le_twice x hN).1 (by positivity)) _
    _ = _ := by
      simp_rw [mul_add, mul_one, mul_left_comm _ (N : ℝ), Finset.sum_add_distrib,
        μ.normalized, ← Finset.mul_sum]

/-- Expected directional imbalance per particle per nonzero offset. -/
def normalizedDirectionalRateImbalance {L N : ℕ} [NeZero L] {w : ℝ}
    (μ : StationaryLaw L N w) : ℝ :=
  (∑ x, μ.weight x * directionalRateImbalance w x) / (((L - 1 : ℕ) : ℝ) * (N : ℝ))

private theorem normalizedDirectionalRateImbalance_balance {L N : ℕ} [NeZero L] {w : ℝ}
    (hL : 1 < L) (hN : 0 < N) (μ : StationaryLaw L N w) :
    w - normalizedDirectionalRateImbalance μ =
      w * (meanOccupiedCount μ / (N : ℝ)) +
        ((N : ℝ) / ((L - 1 : ℕ) : ℝ)) * meanParticleSeparation μ := by
  have hA : ((L - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show L - 1 ≠ 0 by omega)
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have h := stationary_particleSeparation_directional_balance hN μ
  have hdir : (∑ x, μ.weight x * directionalRateImbalance w x) =
      ((L - 1 : ℕ) : ℝ) * w * ((N : ℝ) - meanOccupiedCount μ) -
        (N : ℝ) ^ 2 * meanParticleSeparation μ := by linarith
  unfold normalizedDirectionalRateImbalance
  rw [hdir]
  generalize ((L - 1 : ℕ) : ℝ) = a at hA ⊢
  field_simp [hA, hn]
  ring

/-- The deficit of the directional imbalance controls the separation probability
from both sides. The remaining error from counting occupied sites is at most
`w / N` plus a multiple of the separation probability. -/
theorem directional_deficit_bounds {L N : ℕ} [NeZero L] {w : ℝ}
    (hL : 1 < L) (hN : 0 < N) (hw : 0 ≤ w) (μ : StationaryLaw L N w) :
    ((N : ℝ) / ((L - 1 : ℕ) : ℝ)) * meanParticleSeparation μ ≤
        w - normalizedDirectionalRateImbalance μ ∧
      w - normalizedDirectionalRateImbalance μ ≤
        w / (N : ℝ) + (w + (N : ℝ) / ((L - 1 : ℕ) : ℝ)) * meanParticleSeparation μ := by
  rw [normalizedDirectionalRateImbalance_balance hL hN μ]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hcount : 0 ≤ meanOccupiedCount μ := by
    unfold meanOccupiedCount occupiedCount
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg (μ.nonneg x)
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
  have hscaled : meanOccupiedCount μ / (N : ℝ) ≤ 1 / (N : ℝ) + meanParticleSeparation μ := by
    calc
      _ ≤ (1 + (N : ℝ) * meanParticleSeparation μ) / (N : ℝ) :=
        div_le_div_of_nonneg_right
          (meanOccupiedCount_le_one_add_mass_mul_meanParticleSeparation μ hN) (by positivity)
      _ = _ := by
        field_simp [hn]
        ring
  constructor
  · exact le_add_of_nonneg_left (mul_nonneg hw (div_nonneg hcount (by positivity)))
  · calc
      _ ≤ w * (1 / (N : ℝ) + meanParticleSeparation μ) +
          ((N : ℝ) / ((L - 1 : ℕ) : ℝ)) * meanParticleSeparation μ :=
        add_le_add_right (mul_le_mul_of_nonneg_left hscaled hw) _
      _ = _ := by ring

/-- At fixed positive density, the separation probability vanishes exactly
when the normalized directional imbalance approaches the chip rate. -/
theorem meanParticleSeparation_tendsto_zero_iff_directionalRateImbalance_tendsto
    {L N : ℕ → ℕ} [∀ n, NeZero (L n)] {w ρ : ℝ}
    (hL : ∀ n, 3 ≤ L n) (hLlim : Tendsto L atTop atTop) (hw : 0 ≤ w) (hρ : 0 < ρ)
    (hdensity : Tendsto (fun n => (N n : ℝ) / (L n : ℝ)) atTop (𝓝 ρ))
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w) :
    Tendsto (fun n => meanParticleSeparation (μ n)) atTop (𝓝 0) ↔
      Tendsto (fun n => normalizedDirectionalRateImbalance (μ n)) atTop (𝓝 w) := by
  have hinvL : Tendsto (fun n => (L n : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp hLlim
  have hposN := eventually_pos_mass_of_tendsto_density hρ hdensity
  have hinvN : Tendsto (fun n => (N n : ℝ)⁻¹) atTop (𝓝 0) := by
    have h := hinvL.div hdensity hρ.ne'
    rw [zero_div] at h
    refine h.congr' ?_
    filter_upwards [hposN] with n hn
    have hn' : (N n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hl' : (L n : ℝ) ≠ 0 := by exact_mod_cast (show L n ≠ 0 by have := hL n; omega)
    change (L n : ℝ)⁻¹ / ((N n : ℝ) / (L n : ℝ)) = (N n : ℝ)⁻¹
    field_simp [hn', hl']
  have hdenom : Tendsto (fun n => ((L n - 1 : ℕ) : ℝ) / (L n : ℝ)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hinvL
    rw [sub_zero] at h
    refine h.congr (fun n => ?_)
    have hl : 1 ≤ L n := by have := hL n; omega
    have hl' : (L n : ℝ) ≠ 0 := by exact_mod_cast (show L n ≠ 0 by omega)
    change 1 - (L n : ℝ)⁻¹ = ((L n - 1 : ℕ) : ℝ) / (L n : ℝ)
    rw [Nat.cast_sub hl, Nat.cast_one, sub_div, div_self hl', one_div]
  have hratio : Tendsto (fun n => (N n : ℝ) / ((L n - 1 : ℕ) : ℝ)) atTop (𝓝 ρ) := by
    have h := hdensity.div hdenom one_ne_zero
    rw [div_one] at h
    refine h.congr (fun n => ?_)
    have hl' : (L n : ℝ) ≠ 0 := by exact_mod_cast (show L n ≠ 0 by have := hL n; omega)
    have ha : ((L n - 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (show L n - 1 ≠ 0 by have := hL n; omega)
    change ((N n : ℝ) / (L n : ℝ)) / (((L n - 1 : ℕ) : ℝ) / (L n : ℝ)) = _
    generalize ((L n - 1 : ℕ) : ℝ) = a at ha ⊢
    field_simp [hl', ha]
  have hbounds := hposN.mono (fun n hn =>
    directional_deficit_bounds (show 1 < L n by have := hL n; omega) hn hw (μ n))
  constructor
  · intro hsep
    have hlo := hratio.mul hsep
    rw [mul_zero] at hlo
    have hhi := ((tendsto_const_nhds (x := w)).mul hinvN).add
      (((tendsto_const_nhds (x := w)).add hratio).mul hsep)
    simp only [mul_zero, add_zero] at hhi
    have hhi' : Tendsto (fun n => w / (N n : ℝ) +
        (w + (N n : ℝ) / ((L n - 1 : ℕ) : ℝ)) * meanParticleSeparation (μ n)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, Pi.add_apply, Pi.mul_apply] using hhi
    have hdiff : Tendsto (fun n => w - normalizedDirectionalRateImbalance (μ n)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi'
        (hbounds.mono (fun _ hn => hn.1)) (hbounds.mono (fun _ hn => hn.2))
    simpa only [sub_zero, Pi.sub_apply, sub_sub_cancel] using (tendsto_const_nhds (x := w)).sub hdiff
  · intro hdir
    have hdiff : Tendsto (fun n => w - normalizedDirectionalRateImbalance (μ n)) atTop (𝓝 0) := by
      simpa only [sub_self, Pi.sub_apply] using (tendsto_const_nhds (x := w)).sub hdir
    have hnonneg (n : ℕ) (hn : 0 < N n) : 0 ≤ meanParticleSeparation (μ n) := by
      exact Finset.sum_nonneg (fun x _ => mul_nonneg ((μ n).nonneg x)
        ((backgroundFraction_nonneg x).trans
          (backgroundFraction_le_particleSeparation_le_twice x hn).1))
    have hprod : Tendsto (fun n => ((N n : ℝ) / ((L n - 1 : ℕ) : ℝ)) *
        meanParticleSeparation (μ n)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiff
        (hposN.mono (fun n hn => mul_nonneg (by positivity) (hnonneg n hn)))
        (hbounds.mono (fun _ hn => hn.1))
    have h := hprod.div hratio hρ.ne'
    rw [zero_div] at h
    refine h.congr' ?_
    filter_upwards [hposN] with n hn
    have hn' : (N n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have ha : ((L n - 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (show L n - 1 ≠ 0 by have := hL n; omega)
    change ((N n : ℝ) / ((L n - 1 : ℕ) : ℝ) * meanParticleSeparation (μ n)) /
      ((N n : ℝ) / ((L n - 1 : ℕ) : ℝ)) = meanParticleSeparation (μ n)
    rw [mul_comm, mul_div_cancel_right₀ _ (div_ne_zero hn' ha)]

end
end Chipping
