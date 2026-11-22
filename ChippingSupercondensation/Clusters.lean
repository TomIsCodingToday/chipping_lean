import ChippingSupercondensation.PeakFrame

/-!
# Clusters in the frame of the peak

Index the sites clockwise from the peak by offsets `0, …, L - 1`, and give
every offset its *anchor*, the nearest offset at or behind it that holds at
least two particles. The anchor of a single is the pile that will sweep it, so
a pile together with the singles ahead of it, up to the next pile, forms a
cluster. Singles between the peak and the first background pile belong to the
peak.

The first part works with plain sequences `a : ℕ → ℕ` of masses. A whole move
of a pile carries its whole cluster one step (`seqMoment_pile_move`). A chip
into an empty site from a site not holding exactly two particles changes no
anchor (`seqMoment_trivial_chip`). A whole move of the peak lowers every anchor
by one (`seqMoment_shift`).

The second part transfers this to the ring while the peak holds a majority
that survives a single chip. For a profile `h` with `h 0 = 0`,
`clusterMoment h` weights each particle by `h` of its anchor's offset.
`generator_clusterMoment_eq` shows that its drift is the cluster mass times
the second difference of `h` at each background pile, plus `w` times the
change from chips. Only chips that land on an occupied site, leave a pile of
two, or enter the peak from behind contribute
(`sum_clusterChipChange_eq_exceptional`). Chip-and-reabsorb cycles therefore
cost nothing, unlike in the uncoarsened moments of `PeakFrame`.
`stationary_clusterDrift_majority_le` gives the stationary version with the
usual cutoff error. For the linear profile, piles enter the peak from behind
only as fast as exceptional chips push anchored mass forward
(`stationary_cluster_linear_balance`).

`seqMoment_chip` and `seqMoment_entry_chip` compute every chip exactly, and
`clusterChipChange_eq` identifies the ring version. Each chip change splits
into a forward gain (`seqChipGain`) and, for a nondecreasing profile, a
nonnegative loss (`seqChipLoss`). The gain comes from chips onto occupied
sites. The loss comes from piles of two that dissolve, returning their cluster
to the previous anchor, and from mass entering the peak.
`stationary_cluster_balance_le` states the resulting stationary inequality:
curvature at background piles plus loss is at most the gain, up to the cutoff
error. Two consequences share the same right side, the linear forward gain
of chips onto occupied sites. `stationary_dissolution_le` bounds the piles
entering the peak from behind, together with every dissolving pile of two
weighted by its cluster mass and its distance to the previous anchor.
`stationary_nearClusterMass_le` bounds the mass of the clusters anchored
within `R` of the peak by `w R` times that gain.

`stationary_clusterChipGain_le` splits that gain. The peak's own chips onto an
occupied site contribute at most `w (P(M > t) + E[K])`, by the background mass
identity and the singles balance of `PeakFrame`. Only the gain of chips from
background sites (`backgroundChipGain`) remains.
-/

namespace Chipping

open Filter
open scoped BigOperators Topology

noncomputable section

/-- The greatest index at most `u` holding at least two particles, or zero. -/
def seqAnchor (a : ℕ → ℕ) (u : ℕ) : ℕ :=
  Nat.findGreatest (fun v => 2 ≤ a v) u

theorem seqAnchor_le (a : ℕ → ℕ) (u : ℕ) : seqAnchor a u ≤ u :=
  Nat.findGreatest_le u

theorem seqAnchor_of_pile (a : ℕ → ℕ) {u : ℕ} (hu : 2 ≤ a u) : seqAnchor a u = u :=
  Nat.findGreatest_eq hu

theorem le_seqAnchor (a : ℕ → ℕ) {u v : ℕ} (hv : v ≤ u) (hp : 2 ≤ a v) : v ≤ seqAnchor a u :=
  Nat.le_findGreatest hv hp

theorem seqAnchor_no_pile (a : ℕ → ℕ) {u v : ℕ} (h₁ : seqAnchor a u < v) (h₂ : v ≤ u) :
    a v < 2 := by
  have := Nat.findGreatest_is_greatest h₁ h₂
  omega

theorem seqAnchor_pile (a : ℕ → ℕ) (h0 : 2 ≤ a 0) (u : ℕ) : 2 ≤ a (seqAnchor a u) :=
  Nat.findGreatest_spec (P := fun v => 2 ≤ a v) (Nat.zero_le u) h0

theorem seqAnchor_eq_iff (a : ℕ → ℕ) (u m : ℕ) :
    seqAnchor a u = m ↔ m ≤ u ∧ (m ≠ 0 → 2 ≤ a m) ∧ ∀ v, m < v → v ≤ u → a v < 2 := by
  unfold seqAnchor
  rw [Nat.findGreatest_eq_iff]
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨h₁, h₂, fun v hv hvu => by have := h₃ hv hvu; omega⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨h₁, h₂, fun v hv hvu => by have := h₃ v hv hvu; omega⟩

theorem seqAnchor_congr {a b : ℕ → ℕ} {u : ℕ} (h : ∀ v ≤ u, (2 ≤ a v ↔ 2 ≤ b v)) :
    seqAnchor a u = seqAnchor b u := by
  induction u with
  | zero => simp [seqAnchor]
  | succ n ih =>
    unfold seqAnchor
    rw [Nat.findGreatest_succ, Nat.findGreatest_succ]
    rw [if_congr (h (n + 1) le_rfl) rfl rfl]
    split_ifs
    · rfl
    · exact ih (fun v hv => h v (by omega))

theorem seqAnchor_succ_of_lt (a : ℕ → ℕ) {u : ℕ} (hu : a (u + 1) < 2) :
    seqAnchor a (u + 1) = seqAnchor a u := by
  unfold seqAnchor
  exact Nat.findGreatest_of_not (by omega)

/-- Move `k` units from index `s` to index `s + 1`. -/
def seqMove (a : ℕ → ℕ) (s k : ℕ) (u : ℕ) : ℕ :=
  if u = s then a u - k else if u = s + 1 then a u + k else a u

/-- Mass weighted by a profile of its anchor, over the first `L` indices. -/
def seqMoment (h : ℕ → ℝ) (L : ℕ) (a : ℕ → ℕ) : ℝ :=
  ∑ u ∈ Finset.range L, h (seqAnchor a u) * (a u : ℝ)

/-- The total mass anchored at index `s`: the pile at `s` and its singles. -/
def seqClusterMass (L : ℕ) (a : ℕ → ℕ) (s : ℕ) : ℝ :=
  ∑ u ∈ Finset.range L, if seqAnchor a u = s then (a u : ℝ) else 0

/-- After a whole move of the pile at `s`, offsets beyond `s` that were swept
by `s` are now swept from `s + 1`. -/
theorem seqAnchor_pile_move_ge (a : ℕ → ℕ) {s u : ℕ} (hpile : 2 ≤ a s)
    (hu : s + 1 ≤ u) :
    seqAnchor (seqMove a s (a s)) u =
      if s + 1 ≤ seqAnchor a u then seqAnchor a u else s + 1 := by
  set b := seqMove a s (a s) with hb
  have hb_ge (v : ℕ) (hv : s + 1 < v) : b v = a v := by
    simp [hb, seqMove, show v ≠ s by omega, show v ≠ s + 1 by omega]
  have hb_succ : 2 ≤ b (s + 1) := by simp [hb, seqMove]; omega
  have hs_le : s ≤ seqAnchor a u := le_seqAnchor a (by omega) hpile
  split_ifs with hm
  · rw [seqAnchor_eq_iff]
    refine ⟨seqAnchor_le a u, fun _ => ?_, fun v hv hvu => ?_⟩
    · by_cases he : seqAnchor a u = s + 1
      · rw [he]; exact hb_succ
      · rw [hb_ge _ (by omega)]
        exact Nat.findGreatest_spec (P := fun v => 2 ≤ a v) (by omega : s ≤ u) hpile
    · rw [hb_ge _ (by omega)]
      exact seqAnchor_no_pile a hv hvu
  · have he : seqAnchor a u = s := by omega
    rw [seqAnchor_eq_iff]
    refine ⟨hu, fun _ => hb_succ, fun v hv hvu => ?_⟩
    rw [hb_ge _ hv]
    exact seqAnchor_no_pile a (by omega) hvu

theorem seqAnchor_pile_move_lt (a : ℕ → ℕ) {s u : ℕ} (k : ℕ) (hu : u < s) :
    seqAnchor (seqMove a s k) u = seqAnchor a u := by
  apply seqAnchor_congr
  intro v hv
  simp [seqMove, show v ≠ s by omega, show v ≠ s + 1 by omega]

/-- A whole move of a pile carries its whole cluster one step forward. -/
theorem seqMoment_pile_move (h : ℕ → ℝ) {L : ℕ} (a : ℕ → ℕ) {s : ℕ} (hs : s + 1 < L)
    (hpile : 2 ≤ a s) :
    seqMoment h L (seqMove a s (a s)) - seqMoment h L a =
      seqClusterMass L a s * (h (s + 1) - h s) := by
  set b := seqMove a s (a s) with hb
  have hpoint (u : ℕ) : h (seqAnchor b u) * (b u : ℝ) - h (seqAnchor a u) * (a u : ℝ) =
      (h (s + 1) - h s) * (if seqAnchor a u = s then (a u : ℝ) else 0) +
        h (s + 1) * (a s : ℝ) * ((if u = s + 1 then 1 else 0) - (if u = s then 1 else 0)) := by
    rcases lt_trichotomy u s with hlt | heq | hgt
    · rw [hb, seqAnchor_pile_move_lt a _ hlt]
      have hne : seqAnchor a u ≠ s := by have := seqAnchor_le a u; omega
      simp [seqMove, show u ≠ s by omega, show u ≠ s + 1 by omega, hne]
    · subst heq
      have hself : seqAnchor a u = u := seqAnchor_of_pile a hpile
      simp [hb, seqMove, hself]
      ring
    · by_cases hsucc : u = s + 1
      · subst hsucc
        have hnew : seqAnchor b (s + 1) = s + 1 := by
          apply seqAnchor_of_pile
          simp [hb, seqMove]
          omega
        have hold : seqAnchor a (s + 1) = s ∨ seqAnchor a (s + 1) = s + 1 := by
          have h₁ := le_seqAnchor a (by omega : s ≤ s + 1) hpile
          have h₂ := seqAnchor_le a (s + 1)
          omega
        rw [hnew]
        simp only [hb, seqMove, if_neg (show s + 1 ≠ s by omega), if_pos rfl, if_true]
        rcases hold with h₀ | h₀
        · rw [h₀, if_pos rfl]
          push_cast
          ring
        · rw [h₀, if_neg (show s + 1 ≠ s by omega)]
          push_cast
          ring
      · have hbu : b u = a u := by
          simp [hb, seqMove, show u ≠ s by omega, hsucc]
        rw [hbu, hb, seqAnchor_pile_move_ge a hpile (by omega : s + 1 ≤ u)]
        have hs_le : s ≤ seqAnchor a u := le_seqAnchor a (by omega) hpile
        simp only [if_neg (show u ≠ s + 1 from hsucc), if_neg (show u ≠ s by omega), sub_zero,
          mul_zero, add_zero]
        by_cases hm : s + 1 ≤ seqAnchor a u
        · rw [if_pos hm, if_neg (show seqAnchor a u ≠ s by omega)]
          ring
        · have he : seqAnchor a u = s := by omega
          rw [if_neg hm, if_pos he, he]
          ring
  unfold seqMoment seqClusterMass
  rw [← Finset.sum_sub_distrib]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
    if_pos (Finset.mem_range.mpr hs), if_pos (Finset.mem_range.mpr (by omega))]
  ring

/-- A chip into an empty site from a site that does not hold exactly two
particles moves the particle within its cluster. -/
theorem seqMoment_trivial_chip (h : ℕ → ℝ) {L : ℕ} (a : ℕ → ℕ) {s : ℕ} (hs : s + 1 < L)
    (hone : 1 ≤ a s) (htwo : a s ≠ 2) (hempty : a (s + 1) = 0) :
    seqMoment h L (seqMove a s 1) = seqMoment h L a := by
  set b := seqMove a s 1 with hb
  have hpred (v : ℕ) : 2 ≤ a v ↔ 2 ≤ b v := by
    by_cases hv : v = s
    · subst hv
      simp [hb, seqMove]
      omega
    · by_cases hv' : v = s + 1
      · subst hv'
        simp [hb, seqMove, hempty]
      · simp [hb, seqMove, hv, hv']
  have hanchor (u : ℕ) : seqAnchor b u = seqAnchor a u :=
    (seqAnchor_congr (fun v _ => hpred v)).symm
  have hpoint (u : ℕ) : h (seqAnchor b u) * (b u : ℝ) - h (seqAnchor a u) * (a u : ℝ) =
      h (seqAnchor a u) * ((if u = s + 1 then 1 else 0) - (if u = s then 1 else 0)) := by
    rw [hanchor]
    by_cases hu : u = s
    · subst hu
      simp [hb, seqMove, Nat.cast_sub hone]
      ring
    · by_cases hu' : u = s + 1
      · subst hu'
        simp [hb, seqMove, hempty]
      · simp [hb, seqMove, hu, hu']
  apply sub_eq_zero.mp
  unfold seqMoment
  rw [← Finset.sum_sub_distrib]
  simp_rw [hpoint, mul_sub, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
    if_pos (Finset.mem_range.mpr hs), if_pos (Finset.mem_range.mpr (by omega)),
    seqAnchor_succ_of_lt a (by omega), sub_self]

/-- Masses seen from the peak after its whole move. Index one joins the peak,
every later index moves down by one, and the old peak site is empty. -/
def seqShift (L : ℕ) (a : ℕ → ℕ) (u : ℕ) : ℕ :=
  if u = 0 then a 0 + a 1 else if u + 1 < L then a (u + 1) else 0

theorem seqAnchor_shift (L : ℕ) (a : ℕ → ℕ) {u : ℕ} (hu : u + 1 < L) :
    seqAnchor (seqShift L a) u = seqAnchor a (u + 1) - 1 := by
  rw [seqAnchor_eq_iff]
  have hmle : seqAnchor a (u + 1) ≤ u + 1 := seqAnchor_le a (u + 1)
  refine ⟨by omega, fun hc => ?_, fun v hv hvu => ?_⟩
  · have hspec := ((seqAnchor_eq_iff a (u + 1) (seqAnchor a (u + 1))).mp rfl).2.1 (by omega)
    simp only [seqShift, if_neg hc, if_pos (show seqAnchor a (u + 1) - 1 + 1 < L by omega)]
    rwa [Nat.sub_add_cancel (by omega)]
  · simp only [seqShift, if_neg (show v ≠ 0 by omega), if_pos (show v + 1 < L by omega)]
    exact seqAnchor_no_pile a (u := u + 1) (by omega) (by omega)

/-- A whole move of the peak lowers every anchor by one. Mass anchored at
offset one joins the peak, where the weight vanishes. -/
theorem seqMoment_shift (h : ℕ → ℝ) (h0 : h 0 = 0) {L : ℕ} (hL : 2 ≤ L) (a : ℕ → ℕ) :
    seqMoment h L (seqShift L a) - seqMoment h L a =
      ∑ u ∈ Finset.range L, (a u : ℝ) * (h (seqAnchor a u - 1) - h (seqAnchor a u)) := by
  let G (v : ℕ) : ℝ := if 2 ≤ v then h (seqAnchor a v - 1) * (a v : ℝ) else 0
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  have hold : (∑ u ∈ Finset.range (n + 1), h (seqAnchor a u - 1) * (a u : ℝ)) =
      ∑ u ∈ Finset.range (n + 1), G u := by
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : 2 ≤ u
    · simp [G, hu]
    · have hz : seqAnchor a u - 1 = 0 := by have := seqAnchor_le a u; omega
      simp [G, hu, hz, h0]
  have hnew : seqMoment h (n + 1) (seqShift (n + 1) a) = ∑ u ∈ Finset.range n, G (u + 1) := by
    unfold seqMoment
    rw [Finset.sum_range_succ]
    have hlast : seqShift (n + 1) a n = 0 := by
      simp [seqShift, show n ≠ 0 by omega]
    rw [hlast, Nat.cast_zero, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro u hu
    have hu' := Finset.mem_range.mp hu
    by_cases hu0 : u = 0
    · subst hu0
      have h00 : seqAnchor (seqShift (n + 1) a) 0 = 0 := by
        have := seqAnchor_le (seqShift (n + 1) a) 0; omega
      simp [G, h00, h0]
    · rw [seqAnchor_shift (n + 1) a (by omega)]
      simp [G, seqShift, hu0, show u + 1 < n + 1 by omega, show 2 ≤ u + 1 by omega]
  rw [hnew]
  have hsplit : (∑ u ∈ Finset.range (n + 1), G u) = ∑ u ∈ Finset.range n, G (u + 1) := by
    rw [Finset.sum_range_succ']
    simp [G]
  unfold seqMoment
  rw [← hsplit, ← hold, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- Grouping a sum over offsets by anchors. -/
theorem seqMoment_sum_by_anchor (f : ℕ → ℝ) (L : ℕ) (a : ℕ → ℕ) :
    ∑ u ∈ Finset.range L, (a u : ℝ) * f (seqAnchor a u) =
      ∑ s ∈ Finset.range L, seqClusterMass L a s * f s := by
  unfold seqClusterMass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq (Finset.range L) (seqAnchor a u),
    if_pos (Finset.mem_range.mpr ((seqAnchor_le a u).trans_lt (Finset.mem_range.mp hu)))]

/-- Only piles and the peak anchor any mass. -/
theorem seqClusterMass_eq_zero (L : ℕ) (a : ℕ → ℕ) {s : ℕ} (hs : s ≠ 0) (hp : a s < 2) :
    seqClusterMass L a s = 0 := by
  apply Finset.sum_eq_zero
  intro u _
  rw [if_neg]
  intro he
  have := ((seqAnchor_eq_iff a u s).mp he).2.1 hs
  omega

/-- The mass anchored at the last offset is the pile there, if any. -/
theorem seqClusterMass_last (L : ℕ) (a : ℕ → ℕ) (hL : 1 ≤ L) (hp : 2 ≤ a (L - 1)) :
    seqClusterMass L a (L - 1) = (a (L - 1) : ℝ) := by
  unfold seqClusterMass
  rw [Finset.sum_eq_single (L - 1)]
  · rw [if_pos (seqAnchor_of_pile a hp)]
  · intro u hu hne
    rw [if_neg]
    intro he
    have := seqAnchor_le a u
    have := Finset.mem_range.mp hu
    omega
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

/-- Masses seen from the peak after `k` units enter it from the last offset. -/
def seqEntry (L : ℕ) (a : ℕ → ℕ) (k : ℕ) (u : ℕ) : ℕ :=
  if u = 0 then a 0 + k else if u = L - 1 then a u - k else a u

/-- A whole move of the pile just behind the peak removes its weight. -/
theorem seqMoment_entry_whole (h : ℕ → ℝ) (h0 : h 0 = 0) {L : ℕ} (hL : 2 ≤ L)
    (a : ℕ → ℕ) (hpeak : 2 ≤ a 0) (hp : 2 ≤ a (L - 1)) :
    seqMoment h L (seqEntry L a (a (L - 1))) - seqMoment h L a =
      seqClusterMass L a (L - 1) * (0 - h (L - 1)) := by
  set b := seqEntry L a (a (L - 1)) with hb
  have hanchor (u : ℕ) (hu : u < L - 1) : seqAnchor b u = seqAnchor a u := by
    apply seqAnchor_congr
    intro v hv
    by_cases hv0 : v = 0
    · subst hv0
      simp [hb, seqEntry]
      omega
    · simp [hb, seqEntry, hv0, show v ≠ L - 1 by omega]
  obtain ⟨n, hn⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  have hn' : L - 1 = n := by omega
  rw [seqClusterMass_last L a (by omega) hp]
  unfold seqMoment
  rw [hn, Finset.sum_range_succ, Finset.sum_range_succ]
  rw [hn'] at hanchor hp hb
  have hbn : b n = 0 := by simp [hb, seqEntry, show n ≠ 0 by omega, hn']
  rw [hbn, seqAnchor_of_pile a hp]
  have hrest : (∑ u ∈ Finset.range n, h (seqAnchor b u) * (b u : ℝ)) =
      ∑ u ∈ Finset.range n, h (seqAnchor a u) * (a u : ℝ) := by
    apply Finset.sum_congr rfl
    intro u hu
    have hu' := Finset.mem_range.mp hu
    rw [hanchor u hu']
    by_cases hu0 : u = 0
    · subst hu0
      have hz : seqAnchor a 0 = 0 := by have := seqAnchor_le a 0; omega
      simp [hz, h0]
    · simp [hb, seqEntry, hu0, show u ≠ n by omega, hn']
  rw [hrest]
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

/-- The moment only depends on the first `L` masses. -/
theorem seqMoment_congr (h : ℕ → ℝ) {L : ℕ} {a b : ℕ → ℕ} (hab : ∀ u < L, a u = b u) :
    seqMoment h L a = seqMoment h L b := by
  unfold seqMoment
  apply Finset.sum_congr rfl
  intro u hu
  have hu' := Finset.mem_range.mp hu
  rw [seqAnchor_congr (fun v hv => by rw [hab v (by omega)]), hab u hu']

theorem seqClusterMass_congr {L : ℕ} {a b : ℕ → ℕ} (hab : ∀ u < L, a u = b u) (s : ℕ) :
    seqClusterMass L a s = seqClusterMass L b s := by
  unfold seqClusterMass
  apply Finset.sum_congr rfl
  intro u hu
  have hu' := Finset.mem_range.mp hu
  rw [seqAnchor_congr (fun v hv => by rw [hab v (by omega)]), hab u hu']

/-! ### General chips -/

/-- Mass beyond index `s` swept by the same pile as index `s`. -/
def seqForwardMass (L : ℕ) (a : ℕ → ℕ) (s : ℕ) : ℝ :=
  ∑ u ∈ Finset.range L, if s + 1 ≤ u ∧ seqAnchor a u = seqAnchor a s then (a u : ℝ) else 0

/-- With no pile strictly between `s` and `u`, the two share an anchor. -/
theorem seqAnchor_eq_of_no_pile (a : ℕ → ℕ) {s u : ℕ} (hsu : s ≤ u)
    (hno : ∀ v, s < v → v ≤ u → a v < 2) : seqAnchor a u = seqAnchor a s := by
  induction u, hsu using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [seqAnchor_succ_of_lt a (hno (n + 1) (by omega) le_rfl)]
    exact ih (fun v hv hvn => hno v hv (by omega))

theorem seqAnchor_chip_source (a : ℕ → ℕ) (s : ℕ) :
    seqAnchor (seqMove a s 1) s = if 3 ≤ a s then s else seqAnchor a (s - 1) := by
  split_ifs with h3
  · apply seqAnchor_of_pile
    simp [seqMove]
    omega
  · rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      have h₁ := seqAnchor_le (seqMove a 0 1) 0
      have h₂ := seqAnchor_le a (0 - 1)
      omega
    · obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
      rw [seqAnchor_succ_of_lt _ (by simp [seqMove]; omega), Nat.add_sub_cancel,
        seqAnchor_pile_move_lt a 1 (by omega : n < n + 1)]

/-- Beyond the target of a chip, offsets anchored before the source either
stay with their anchor or, when the target becomes a pile, move to it. -/
theorem seqAnchor_chip_forward (a : ℕ → ℕ) {s u : ℕ}
    (hu : s + 1 ≤ u) (hm : seqAnchor a u ≤ s) :
    seqAnchor a u = seqAnchor a s ∧
      seqAnchor (seqMove a s 1) u =
        if 1 ≤ a (s + 1) then s + 1 else seqAnchor (seqMove a s 1) s := by
  have hno : ∀ v, s < v → v ≤ u → a v < 2 :=
    fun v hv hvu => seqAnchor_no_pile a (by omega) hvu
  refine ⟨seqAnchor_eq_of_no_pile a (by omega) hno, ?_⟩
  have hb_ge (v : ℕ) (hv : s + 1 < v) : seqMove a s 1 v = a v := by
    simp [seqMove, show v ≠ s by omega, show v ≠ s + 1 by omega]
  split_ifs with ht
  · have hpile : 2 ≤ seqMove a s 1 (s + 1) := by simp [seqMove]; omega
    rw [seqAnchor_eq_of_no_pile _ hu (fun v hv hvu => by rw [hb_ge v hv]; exact hno v (by omega) hvu),
      seqAnchor_of_pile _ hpile]
  · apply seqAnchor_eq_of_no_pile _ (by omega)
    intro v hv hvu
    by_cases hv' : v = s + 1
    · subst hv'
      simp [seqMove]
      omega
    · rw [hb_ge v (by omega)]
      exact hno v hv hvu

theorem seqAnchor_chip_forward_pile (a : ℕ → ℕ) {s : ℕ} (u : ℕ)
    (hm : s + 1 ≤ seqAnchor a u) : seqAnchor (seqMove a s 1) u = seqAnchor a u := by
  have hb_ge (v : ℕ) (hv : s + 1 < v) : seqMove a s 1 v = a v := by
    simp [seqMove, show v ≠ s by omega, show v ≠ s + 1 by omega]
  rw [seqAnchor_eq_iff]
  refine ⟨seqAnchor_le a u, fun _ => ?_, fun v hv hvu => ?_⟩
  · have hspec := ((seqAnchor_eq_iff a u (seqAnchor a u)).mp rfl).2.1 (by omega)
    by_cases he : seqAnchor a u = s + 1
    · rw [he] at hspec ⊢
      simp [seqMove]
      omega
    · rw [hb_ge _ (by omega)]
      exact hspec
  · rw [hb_ge v (by omega)]
    exact seqAnchor_no_pile a hv hvu

/-- The exact change of a cluster moment under a chip from index `s` to
`s + 1`. A chip onto an occupied site moves the chipped particle, and when the
target becomes a pile also the rest of the source's cluster beyond `s`, from
the source's anchor `A` to `s + 1`. A chip from a pile of two returns the
single left behind, and when the target is empty the whole cluster, to the
previous anchor `A'`. -/
theorem seqMoment_chip (h : ℕ → ℝ) {L : ℕ} (a : ℕ → ℕ) {s : ℕ} (hs : s + 1 < L)
    (hone : 1 ≤ a s) :
    seqMoment h L (seqMove a s 1) - seqMoment h L a =
      (if 1 ≤ a (s + 1) then
        (h (s + 1) - h (seqAnchor a s)) * (1 + seqForwardMass L a s) else 0) +
      (if a s = 2 then (h (seqAnchor a (s - 1)) - h s) *
        (if a (s + 1) = 0 then 2 + seqForwardMass L a s else 1) else 0) := by
  set b := seqMove a s 1 with hb
  set A := seqAnchor a s with hA
  set A' := seqAnchor a (s - 1) with hA'
  set F := seqForwardMass L a s with hF
  have hsrc := seqAnchor_chip_source a s
  rw [← hb, ← hA'] at hsrc
  have hA_eq : a s = 1 → A = A' := by
    intro h1
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [hA, hA', h0]
    · obtain ⟨n, hn⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
      rw [hA, hA', hn, seqAnchor_succ_of_lt a (by rw [← hn]; omega), Nat.add_sub_cancel]
  have hA_self : 2 ≤ a s → A = s := fun h2 => seqAnchor_of_pile a h2
  -- the new anchor of the forward part of the source's cluster
  let new : ℕ := if 1 ≤ a (s + 1) then s + 1 else seqAnchor b s
  -- split the change into re-anchoring and the moved particle
  have hdecomp : seqMoment h L b - seqMoment h L a =
      (∑ u ∈ Finset.range L, (h (seqAnchor b u) - h (seqAnchor a u)) * (a u : ℝ)) +
        (h (seqAnchor b (s + 1)) - h (seqAnchor b s)) := by
    have hmoved : (∑ u ∈ Finset.range L, h (seqAnchor b u) * ((b u : ℝ) - (a u : ℝ))) =
        h (seqAnchor b (s + 1)) - h (seqAnchor b s) := by
      have hpt (u : ℕ) : h (seqAnchor b u) * ((b u : ℝ) - (a u : ℝ)) =
          (if u = s + 1 then h (seqAnchor b u) else 0) - (if u = s then h (seqAnchor b u) else 0) := by
        by_cases hu : u = s
        · subst hu
          simp [hb, seqMove, Nat.cast_sub hone]
        · by_cases hu' : u = s + 1
          · subst hu'
            simp [hb, seqMove]
          · simp [hb, seqMove, hu, hu']
      simp_rw [hpt]
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
        if_pos (Finset.mem_range.mpr hs), if_pos (Finset.mem_range.mpr (by omega))]
    unfold seqMoment
    rw [← hmoved, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _
    ring
  -- pointwise re-anchoring
  have hre (u : ℕ) (hu : u ∈ Finset.range L) :
      (h (seqAnchor b u) - h (seqAnchor a u)) * (a u : ℝ) =
        (if u = s ∧ a s = 2 then (h A' - h s) * 2 else 0) +
        (if s + 1 ≤ u ∧ seqAnchor a u = A then (h new - h A) * (a u : ℝ) else 0) := by
    rcases lt_trichotomy u s with hlt | heq | hgt
    · rw [hb, seqAnchor_pile_move_lt a 1 hlt, if_neg (by omega), if_neg (by omega)]
      ring
    · subst heq
      rw [if_neg (show ¬(u + 1 ≤ u ∧ seqAnchor a u = A) from fun h => by omega), add_zero,
        hsrc]
      by_cases h3 : 3 ≤ a u
      · rw [if_pos h3, if_neg (show ¬(u = u ∧ a u = 2) from fun h => by have := h.2; omega),
          ← hA, hA_self (by omega)]
        ring
      · rw [if_neg h3]
        by_cases h2 : a u = 2
        · rw [if_pos ⟨rfl, h2⟩, ← hA, hA_self (by omega), h2]
          push_cast
          ring
        · rw [if_neg (fun h => h2 h.2), ← hA, hA_eq (by omega)]
          ring
    · by_cases hm : seqAnchor a u ≤ s
      · obtain ⟨heqA, hnew⟩ := seqAnchor_chip_forward a (by omega : s + 1 ≤ u) hm
        rw [← hb] at hnew
        rw [if_neg (by omega), zero_add, if_pos ⟨by omega, heqA⟩, hnew, heqA]
      · rw [hb, seqAnchor_chip_forward_pile a u (by omega),
          if_neg (by omega), if_neg (fun h => by
            have := seqAnchor_le a s
            rw [← hA] at this
            omega)]
        ring
  rw [hdecomp, Finset.sum_congr rfl hre, Finset.sum_add_distrib]
  have hfirst : (∑ u ∈ Finset.range L, if u = s ∧ a s = 2 then (h A' - h s) * 2 else 0) =
      if a s = 2 then (h A' - h s) * 2 else 0 := by
    by_cases h2 : a s = 2
    · rw [if_pos h2]
      rw [Finset.sum_eq_single s]
      · rw [if_pos ⟨rfl, h2⟩]
      · intro u _ hne
        rw [if_neg (fun h => hne h.1)]
      · intro h
        exact (h (Finset.mem_range.mpr (by omega))).elim
    · rw [if_neg h2]
      exact Finset.sum_eq_zero (fun u _ => if_neg (fun h => h2 h.2))
  have hsecond : (∑ u ∈ Finset.range L,
      if s + 1 ≤ u ∧ seqAnchor a u = A then (h new - h A) * (a u : ℝ) else 0) =
        (h new - h A) * F := by
    rw [hF, seqForwardMass, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> ring
  rw [hfirst, hsecond]
  -- the moved particle: target anchor and source anchor after the chip
  have hbt : seqAnchor b (s + 1) = new := by
    by_cases ht : 1 ≤ a (s + 1)
    · have : new = s + 1 := if_pos ht
      rw [this]
      apply seqAnchor_of_pile
      simp [hb, seqMove]
      omega
    · have : new = seqAnchor b s := if_neg ht
      rw [this]
      exact seqAnchor_succ_of_lt b (by simp [hb, seqMove]; omega)
  rw [hbt, hsrc]
  have hF0 : 2 ≤ a (s + 1) → F = 0 := by
    intro h2
    rw [hF, seqForwardMass]
    apply Finset.sum_eq_zero
    intro u hu
    rw [if_neg]
    rintro ⟨hu1, hu2⟩
    have h₁ := le_seqAnchor a hu1 h2
    have h₂ := seqAnchor_le a s
    rw [← hA] at h₂
    omega
  by_cases ht : 1 ≤ a (s + 1)
  · have hnew : new = s + 1 := if_pos ht
    have hz : a (s + 1) ≠ 0 := by omega
    rw [hnew]
    simp only [ht, hz, ↓reduceIte]
    by_cases h3 : 3 ≤ a s
    · have h2 : a s ≠ 2 := by omega
      rw [if_pos h3]
      simp only [h2, ↓reduceIte]
      rw [hA_self (by omega)]
      ring
    · rw [if_neg h3]
      by_cases h2 : a s = 2
      · simp only [h2, ↓reduceIte]
        rw [hA_self (by omega)]
        ring
      · simp only [h2, ↓reduceIte]
        rw [hA_eq (by omega)]
        ring
  · have hnew : new = seqAnchor b s := if_neg ht
    have hz : a (s + 1) = 0 := by omega
    rw [hnew, hsrc]
    simp only [ht, ↓reduceIte]
    simp only [hz, ↓reduceIte]
    by_cases h3 : 3 ≤ a s
    · have h2 : a s ≠ 2 := by omega
      rw [if_pos h3]
      simp only [h2, ↓reduceIte]
      rw [hA_self (by omega)]
      ring
    · rw [if_neg h3]
      by_cases h2 : a s = 2
      · simp only [h2, ↓reduceIte]
        rw [hA_self (by omega)]
        ring
      · simp only [h2, ↓reduceIte]
        rw [hA_eq (by omega)]
        ring

/-! ### Clusters on the ring -/

/-- The mass at each offset clockwise from the selected peak. -/
def frameMass {L N : ℕ} [NeZero L] (x : State L N) (u : ℕ) : ℕ :=
  occ x (peakSite x + (u : Fin L))

/-- Background mass weighted by a profile of the offset of its anchor. Mass
anchored at the peak has weight `h 0`. -/
def clusterMoment {L N : ℕ} [NeZero L] (h : ℕ → ℝ) (x : State L N) : ℝ :=
  seqMoment h L (frameMass x)

/-- The mass of the cluster anchored at offset `s`. -/
def frameClusterMass {L N : ℕ} [NeZero L] (x : State L N) (s : ℕ) : ℝ :=
  seqClusterMass L (frameMass x) s

/-- The change of the cluster moment when one particle chips from site `i`. -/
def clusterChipChange {L N : ℕ} [NeZero L] (h : ℕ → ℝ) (x : State L N) (i : Fin L) : ℝ :=
  if hi : 1 ≤ occ x i then clusterMoment h (move x i 1 hi) - clusterMoment h x else 0

theorem peak_add_eq_iff {L N : ℕ} [NeZero L] (x : State L N) {u : ℕ} (hu : u < L)
    (j : Fin L) : peakSite x + (u : Fin L) = j ↔ u = peakOffset x j := by
  unfold peakOffset
  constructor
  · rintro rfl
    rw [add_sub_cancel_left, Fin.val_natCast, Nat.mod_eq_of_lt hu]
  · rintro rfl
    rw [Fin.cast_val_eq_self]
    abel

theorem frameMass_zero {L N : ℕ} [NeZero L] (x : State L N) : frameMass x 0 = largest x := by
  simp [frameMass, occ_peakSite]

theorem sum_sites_eq_sum_offsets {L : ℕ} [NeZero L] (p : Fin L) (F : Fin L → ℝ) :
    ∑ i, F i = ∑ s ∈ Finset.range L, F (p + (s : Fin L)) := by
  rw [← Equiv.sum_comp (Equiv.addLeft p) F,
    ← Fin.sum_univ_eq_sum_range (fun s => F (p + (s : Fin L))) L]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fin.cast_val_eq_self]
  rfl

theorem sum_frameMass {L N : ℕ} [NeZero L] (x : State L N) :
    (∑ u ∈ Finset.range L, (frameMass x u : ℝ)) = (N : ℝ) := by
  have hmass : (∑ i, (occ x i : ℝ)) = (N : ℝ) := by exact_mod_cast x.property
  rw [← hmass, sum_sites_eq_sum_offsets (peakSite x)]
  rfl

theorem frameMass_move_of_peak_eq {L N : ℕ} [NeZero L] (x : State L N) (i : Fin L)
    (k : ℕ) (hk : k ≤ occ x i) (hpeak : peakSite (move x i k hk) = peakSite x)
    (hi : i ≠ peakSite x - 1) (u : ℕ) (hu : u < L) :
    frameMass (move x i k hk) u = seqMove (frameMass x) (peakOffset x i) k u := by
  have h₁ := peak_add_eq_iff x hu i
  have h₂ : peakSite x + (u : Fin L) = right i ↔ u = peakOffset x i + 1 := by
    rw [peak_add_eq_iff x hu, peakOffset_right x i hi]
  unfold frameMass seqMove
  rw [hpeak, occ_move]
  unfold transfer
  by_cases hs : u = peakOffset x i
  · rw [if_pos (h₁.mpr hs), if_neg (fun h => by have := h₂.mp h; omega), if_pos hs]
    rfl
  · rw [if_neg (fun h => hs (h₁.mp h)), if_neg hs, Nat.sub_zero]
    by_cases hs' : u = peakOffset x i + 1
    · rw [if_pos (h₂.mpr hs'), if_pos hs']
    · rw [if_neg (fun h => hs' (h₂.mp h)), if_neg hs', Nat.add_zero]

theorem frameMass_whole_peak {L N : ℕ} [NeZero L] (hL : 3 ≤ L) (x : State L N)
    (hmajority : N < 2 * largest x) (u : ℕ) (hu : u < L) :
    frameMass (move x (peakSite x) (occ x (peakSite x)) le_rfl) u =
      seqShift L (frameMass x) u := by
  set p := peakSite x with hp
  have hpy : peakSite (move x p (occ x p) le_rfl) = right p := by
    have h' := peakSite_whole_move hL x hmajority p
    rw [if_pos hp] at h'
    exact h'
  have hrp : right p ≠ p := right_ne_self hL p
  unfold frameMass seqShift
  rw [hpy, occ_move]
  unfold transfer
  by_cases hu0 : u = 0
  · subst hu0
    simp only [Nat.cast_zero, add_zero, if_neg hrp, Nat.sub_zero, if_pos rfl, if_true]
    rw [← hp, right_eq_add_one, Nat.cast_one]
    ring
  · rw [if_neg hu0]
    have hshift : right p + (u : Fin L) = p + ((u + 1 : ℕ) : Fin L) := by
      rw [right_eq_add_one]
      push_cast
      abel
    rw [hshift]
    by_cases hlast : u + 1 < L
    · rw [if_pos hlast]
      have hne : p + ((u + 1 : ℕ) : Fin L) ≠ p := by
        intro h
        have := (peak_add_eq_iff x hlast p).mp (by rw [← hp]; exact h)
        rw [peakOffset_peakSite] at this
        omega
      have hne' : p + ((u + 1 : ℕ) : Fin L) ≠ right p := by
        intro h
        have := (peak_add_eq_iff x hlast (right p)).mp (by rw [← hp]; exact h)
        rw [hp, peakOffset_right_peakSite hL x] at this
        omega
      rw [if_neg hne, if_neg hne', Nat.sub_zero, Nat.add_zero]
    · have hL' : u + 1 = L := by omega
      have hwrap : p + ((u + 1 : ℕ) : Fin L) = p := by
        rw [hL', Fin.natCast_self, add_zero]
      rw [if_neg hlast, hwrap, if_pos rfl, if_neg (Ne.symm hrp), Nat.sub_self]

theorem frameMass_move_rear {L N : ℕ} [NeZero L] (hL : 3 ≤ L) (x : State L N)
    (k : ℕ) (hk : k ≤ occ x (peakSite x - 1))
    (hpeak : peakSite (move x (peakSite x - 1) k hk) = peakSite x) (u : ℕ) (hu : u < L) :
    frameMass (move x (peakSite x - 1) k hk) u = seqEntry L (frameMass x) k u := by
  have hright : right (peakSite x - 1) = peakSite x := by rw [right_eq_add_one, sub_add_cancel]
  have h₁ : peakSite x + (u : Fin L) = peakSite x - 1 ↔ u = L - 1 := by
    rw [peak_add_eq_iff x hu, peakOffset_peakSite_sub_one hL]
  have h₂ : peakSite x + (u : Fin L) = right (peakSite x - 1) ↔ u = 0 := by
    rw [hright, peak_add_eq_iff x hu, peakOffset_peakSite]
  unfold frameMass seqEntry
  rw [hpeak, occ_move]
  unfold transfer
  by_cases hu0 : u = 0
  · rw [if_neg (fun h => by have := h₁.mp h; omega), if_pos (h₂.mpr hu0), if_pos hu0,
      Nat.sub_zero]
    subst hu0
    rfl
  · rw [if_neg (fun h => hu0 (h₂.mp h)), if_neg hu0, Nat.add_zero]
    by_cases hl : u = L - 1
    · rw [if_pos (h₁.mpr hl), if_pos hl]
    · rw [if_neg (fun h => hl (h₁.mp h)), if_neg hl, Nat.sub_zero]

/-- A chip into an empty site, from a site other than the one behind the peak
and not holding exactly two particles, leaves every cluster unchanged. -/
theorem clusterChipChange_eq_zero {L N : ℕ} [NeZero L] (h : ℕ → ℝ) (x : State L N)
    (hmargin : N + 2 < 2 * largest x) (i : Fin L) (hi : i ≠ peakSite x - 1)
    (htwo : occ x i ≠ 2) (hempty : occ x (right i) = 0) :
    clusterChipChange h x i = 0 := by
  unfold clusterChipChange
  split_ifs with hone
  · have hs : peakOffset x i + 1 < L := by
      have := peakOffset_lt x (right i)
      rw [peakOffset_right x i hi] at this
      exact this
    have hcongr := seqMoment_congr h
      (frameMass_move_of_peak_eq x i 1 hone (peakSite_chip_move x hmargin i hone) hi)
    have hself : peakSite x + ((peakOffset x i : ℕ) : Fin L) = i :=
      (peak_add_eq_iff x (peakOffset_lt x i) i).mpr rfl
    have hr : peakSite x + ((peakOffset x i + 1 : ℕ) : Fin L) = right i :=
      (peak_add_eq_iff x hs (right i)).mpr (peakOffset_right x i hi).symm
    unfold clusterMoment
    rw [hcongr]
    apply sub_eq_zero.mpr
    apply seqMoment_trivial_chip h (frameMass x) hs
    · simpa [frameMass, hself] using hone
    · simpa [frameMass, hself] using htwo
    · unfold frameMass
      rw [hr]
      exact hempty
  · rfl

private theorem atSite_clusterMoment {L N : ℕ} [NeZero L] (w : ℝ) (h : ℕ → ℝ)
    (x : State L N) (i : Fin L) :
    atSite w (clusterMoment h) x i = w * clusterChipChange h x i +
      (if 2 ≤ occ x i then
        clusterMoment h (move x i (occ x i) le_rfl) - clusterMoment h x else 0) := by
  unfold atSite clusterChipChange
  split_ifs <;> ring

/-- The whole move from a background offset carries its cluster one step; from
the offset behind the peak the cluster joins the peak. -/
private theorem whole_change_background {L N : ℕ} [NeZero L] (hL : 3 ≤ L) (h : ℕ → ℝ)
    (h0 : h 0 = 0) (x : State L N) (hmargin : N + 2 < 2 * largest x) {s : ℕ}
    (hs1 : 1 ≤ s) (hsL : s < L) (hpile : 2 ≤ frameMass x s) :
    clusterMoment h (move x (peakSite x + (s : Fin L)) (occ x (peakSite x + (s : Fin L))) le_rfl) -
        clusterMoment h x =
      frameClusterMass x s * ((if s + 1 < L then h (s + 1) else 0) - h s) := by
  have hoff : peakOffset x (peakSite x + (s : Fin L)) = s :=
    ((peak_add_eq_iff x hsL _).mp rfl).symm
  have hne : peakSite x + (s : Fin L) ≠ peakSite x := by
    intro he
    have := congrArg (peakOffset x) he
    rw [hoff, peakOffset_peakSite] at this
    omega
  have hpeak : peakSite (move x (peakSite x + (s : Fin L))
      (occ x (peakSite x + (s : Fin L))) le_rfl) = peakSite x := by
    rw [peakSite_whole_move hL x (by omega), if_neg hne]
  have ha0 : 2 ≤ frameMass x 0 := by rw [frameMass_zero]; omega
  by_cases hlast : s + 1 < L
  · have hrear : peakSite x + (s : Fin L) ≠ peakSite x - 1 := by
      intro he
      have := congrArg (peakOffset x) he
      rw [hoff, peakOffset_peakSite_sub_one hL] at this
      omega
    have hcongr := seqMoment_congr h
      (frameMass_move_of_peak_eq x _ _ le_rfl hpeak hrear)
    rw [if_pos hlast]
    unfold clusterMoment frameClusterMass
    rw [hcongr, hoff]
    exact seqMoment_pile_move h (frameMass x) hlast hpile
  · have hsL' : s = L - 1 := by omega
    have hrear : peakSite x + (s : Fin L) = peakSite x - 1 :=
      (peak_add_eq_iff x hsL _).mpr (by rw [peakOffset_peakSite_sub_one hL]; exact hsL')
    rw [if_neg hlast]
    revert hpeak
    rw [hrear]
    intro hpeak
    have hcongr := seqMoment_congr h (frameMass_move_rear hL x _ le_rfl hpeak)
    have hocc : occ x (peakSite x - 1) = frameMass x (L - 1) := by
      unfold frameMass
      rw [← hsL', hrear]
    unfold clusterMoment frameClusterMass
    rw [hcongr, hocc, hsL']
    rw [hsL'] at hpile
    exact seqMoment_entry_whole h h0 (by omega) (frameMass x) ha0 hpile

/-- The whole move of the peak lowers every anchor by one. -/
private theorem whole_change_peak {L N : ℕ} [NeZero L] (hL : 3 ≤ L) (h : ℕ → ℝ)
    (h0 : h 0 = 0) (x : State L N) (hmargin : N + 2 < 2 * largest x) :
    clusterMoment h (move x (peakSite x) (occ x (peakSite x)) le_rfl) - clusterMoment h x =
      ∑ t ∈ Finset.range L, frameClusterMass x t * (h (t - 1) - h t) := by
  have hcongr := seqMoment_congr h (frameMass_whole_peak hL x (by omega))
  unfold clusterMoment frameClusterMass
  rw [hcongr, seqMoment_shift h h0 (by omega)]
  exact seqMoment_sum_by_anchor (fun v => h (v - 1) - h v) L (frameMass x)

/-- The exact drift of a cluster moment while the peak holds a majority that
survives a single chip. Each background cluster moves with its pile and with
the peak, which gives the second difference of the profile. Chips contribute
only through `clusterChipChange`, which vanishes for most chips
(`clusterChipChange_eq_zero`). The peak at offset `L` carries weight zero. -/
theorem generator_clusterMoment_eq {L N : ℕ} [NeZero L] (hL : 3 ≤ L) (w : ℝ)
    (h : ℕ → ℝ) (h0 : h 0 = 0) (x : State L N) (hmargin : N + 2 < 2 * largest x) :
    generator w (clusterMoment h) x =
      (∑ s ∈ Finset.range L, if 1 ≤ s ∧ 2 ≤ frameMass x s then
          frameClusterMass x s * ((if s + 1 < L then h (s + 1) else 0) - 2 * h s + h (s - 1))
        else 0) +
      w * ∑ i, clusterChipChange h x i := by
  let W (s : ℕ) : ℝ := if 2 ≤ frameMass x s then
      clusterMoment h (move x (peakSite x + (s : Fin L))
        (occ x (peakSite x + (s : Fin L))) le_rfl) - clusterMoment h x
    else 0
  have hgen : generator w (clusterMoment h) x =
      w * (∑ i, clusterChipChange h x i) + ∑ s ∈ Finset.range L, W s := by
    unfold generator
    simp_rw [atSite_clusterMoment]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_sites_eq_sum_offsets (peakSite x)
        (fun i => if 2 ≤ occ x i then
          clusterMoment h (move x i (occ x i) le_rfl) - clusterMoment h x else 0)]
    rfl
  have ha0 : 2 ≤ frameMass x 0 := by rw [frameMass_zero]; omega
  have hW0 : W 0 = ∑ t ∈ Finset.range L, (if 1 ≤ t ∧ 2 ≤ frameMass x t then
      frameClusterMass x t * (h (t - 1) - h t) else 0) := by
    have hp0 : peakSite x + ((0 : ℕ) : Fin L) = peakSite x := by simp
    simp only [W, if_pos ha0]
    rw [show (move x (peakSite x + ((0 : ℕ) : Fin L)) (occ x (peakSite x + ((0 : ℕ) : Fin L)))
        le_rfl) = move x (peakSite x) (occ x (peakSite x)) le_rfl by rw [hp0],
      whole_change_peak hL h h0 x hmargin]
    apply Finset.sum_congr rfl
    intro t _
    by_cases ht : 1 ≤ t ∧ 2 ≤ frameMass x t
    · rw [if_pos ht]
    · rw [if_neg ht]
      by_cases ht0 : t = 0
      · rw [ht0, Nat.zero_sub, sub_self, mul_zero]
      · rw [show frameClusterMass x t = 0 from
          seqClusterMass_eq_zero L (frameMass x) ht0 (by omega), zero_mul]
  have hWs (s : ℕ) (hs : s ∈ Finset.range L) (hs1 : s ≠ 0) :
      W s = if 1 ≤ s ∧ 2 ≤ frameMass x s then
        frameClusterMass x s * ((if s + 1 < L then h (s + 1) else 0) - h s) else 0 := by
    simp only [W]
    by_cases hp : 2 ≤ frameMass x s
    · rw [if_pos hp, if_pos ⟨by omega, hp⟩]
      exact whole_change_background hL h h0 x hmargin (by omega) (Finset.mem_range.mp hs) hp
    · rw [if_neg hp, if_neg (fun h => hp h.2)]
  rw [hgen]
  have hsum : (∑ s ∈ Finset.range L, W s) = W 0 + ∑ s ∈ Finset.range L,
      (if s = 0 then 0 else W s) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (NeZero.pos L))]
    congr 1
    rw [← Finset.add_sum_erase (Finset.range L) (fun s => if s = 0 then 0 else W s)
      (Finset.mem_range.mpr (NeZero.pos L)), if_pos rfl, zero_add]
    apply Finset.sum_congr rfl
    intro s hs
    rw [if_neg (Finset.ne_of_mem_erase hs)]
  rw [hsum, hW0, ← Finset.sum_add_distrib]
  rw [add_comm (w * _)]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hs0 : s = 0
  · subst hs0
    simp
  · rw [if_neg hs0, hWs s hs hs0]
    by_cases hc : 1 ≤ s ∧ 2 ≤ frameMass x s
    · rw [if_pos hc, if_pos hc, if_pos hc]
      ring
    · rw [if_neg hc, if_neg hc, if_neg hc, add_zero]

/-- The drift of `clusterMoment h` in the majority region. -/
def clusterDrift {L N : ℕ} [NeZero L] (w : ℝ) (h : ℕ → ℝ) (x : State L N) : ℝ :=
  (∑ s ∈ Finset.range L, if 1 ≤ s ∧ 2 ≤ frameMass x s then
      frameClusterMass x s * ((if s + 1 < L then h (s + 1) else 0) - 2 * h s + h (s - 1))
    else 0) +
  w * ∑ i, clusterChipChange h x i

/-- Only chips that land on an occupied site, leave a pile of two, or enter
the peak from behind can change a cluster moment. -/
theorem sum_clusterChipChange_eq_exceptional {L N : ℕ} [NeZero L] (h : ℕ → ℝ)
    (x : State L N) (hmargin : N + 2 < 2 * largest x) :
    (∑ i, clusterChipChange h x i) =
      ∑ i, if i = peakSite x - 1 ∨ occ x i = 2 ∨ 0 < occ x (right i) then
        clusterChipChange h x i else 0 := by
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hc
  · rfl
  · push_neg at hc
    exact clusterChipChange_eq_zero h x hmargin i hc.1 hc.2.1 (by omega)

/-- A profile bounded by `c` weights at most `c` times the background mass. -/
theorem clusterMoment_bounds {L N : ℕ} [NeZero L] (h : ℕ → ℝ) (h0 : h 0 = 0) {c : ℝ}
    (hnonneg : ∀ s < L, 0 ≤ h s) (hc : ∀ s < L, h s ≤ c) (x : State L N) :
    0 ≤ clusterMoment h x ∧ clusterMoment h x ≤ c * ((N : ℝ) - (largest x : ℝ)) := by
  have hlt (u : ℕ) (hu : u ∈ Finset.range L) : seqAnchor (frameMass x) u < L :=
    (seqAnchor_le _ u).trans_lt (Finset.mem_range.mp hu)
  unfold clusterMoment seqMoment
  constructor
  · exact Finset.sum_nonneg (fun u hu =>
      mul_nonneg (hnonneg _ (hlt u hu)) (Nat.cast_nonneg _))
  · have hsplit (u : ℕ) : (if u = 0 then 0 else c * (frameMass x u : ℝ)) =
        c * (frameMass x u : ℝ) - (if u = 0 then c * (frameMass x u : ℝ) else 0) := by
      split_ifs <;> ring
    calc
      _ ≤ ∑ u ∈ Finset.range L, (if u = 0 then 0 else c * (frameMass x u : ℝ)) := by
        apply Finset.sum_le_sum
        intro u hu
        split_ifs with hu0
        · rw [hu0]
          have hz : seqAnchor (frameMass x) 0 = 0 := by
            have := seqAnchor_le (frameMass x) 0; omega
          rw [hz, h0, zero_mul]
        · exact mul_le_mul_of_nonneg_right (hc _ (hlt u hu)) (Nat.cast_nonneg _)
      _ = _ := by
        simp_rw [hsplit]
        rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr
          (NeZero.pos L)), ← Finset.mul_sum, sum_frameMass, frameMass_zero]
        ring

/-- The stationary cluster balance on the majority region `M > t > N/2`. -/
theorem stationary_clusterDrift_majority_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (h : ℕ → ℝ) (h0 : h 0 = 0) {c : ℝ}
    (hnonneg : ∀ s < L, 0 ≤ h s) (hc : ∀ s < L, h s ≤ c)
    (t : ℕ) (ht : N < 2 * t) (htN : t ≤ N) :
    |∑ x, μ.weight x * (if t < largest x then clusterDrift w h x else 0)| ≤
      w * (c * ((N - t : ℕ) : ℝ)) * (∑ x, if largest x = t + 1 then μ.weight x else 0) := by
  have hc0 : 0 ≤ c := (hnonneg 0 (NeZero.pos L)).trans (hc 0 (NeZero.pos L))
  have hbound (y : State L N) (hy : t ≤ largest y) :
      0 ≤ clusterMoment h y ∧ clusterMoment h y ≤ c * ((N - t : ℕ) : ℝ) := by
    obtain ⟨h1, h2⟩ := clusterMoment_bounds h h0 hnonneg hc y
    refine ⟨h1, h2.trans (mul_le_mul_of_nonneg_left ?_ hc0)⟩
    rw [Nat.cast_sub htN]
    exact sub_le_sub_left (by exact_mod_cast hy) _
  have hs := stationary_largestCutoff_abs_drift_le hL hw μ t (clusterMoment h)
    (b := c * ((N - t : ℕ) : ℝ)) (mul_nonneg hc0 (Nat.cast_nonneg _)) hbound
  have hlocal (x : State L N) :
      (if t < largest x then generator w (clusterMoment h) x else 0) =
        (if t < largest x then clusterDrift w h x else 0) := by
    split_ifs with hx
    · exact generator_clusterMoment_eq hL w h h0 x (by omega)
    · rfl
  simpa only [hlocal] using hs

/-- For the profile `h s = s`, every background cluster has zero second
difference except the one just behind the peak, which loses its whole offset
when it enters the peak. -/
theorem clusterDrift_linear {L N : ℕ} [NeZero L] (hL : 3 ≤ L) (w : ℝ) (x : State L N) :
    clusterDrift w (fun s => (s : ℝ)) x =
      w * (∑ i, clusterChipChange (fun s => (s : ℝ)) x i) -
        (L : ℝ) * (if 2 ≤ frameMass x (L - 1) then (frameMass x (L - 1) : ℝ) else 0) := by
  unfold clusterDrift
  have hpoint (s : ℕ) (hs : s ∈ Finset.range L) :
      (if 1 ≤ s ∧ 2 ≤ frameMass x s then
        frameClusterMass x s * ((if s + 1 < L then ((s + 1 : ℕ) : ℝ) else 0) - 2 * (s : ℝ) +
          ((s - 1 : ℕ) : ℝ)) else 0) =
        if s = L - 1 then -(L : ℝ) * (if 2 ≤ frameMass x (L - 1) then
          (frameMass x (L - 1) : ℝ) else 0) else 0 := by
    have hsL := Finset.mem_range.mp hs
    by_cases hc : 1 ≤ s ∧ 2 ≤ frameMass x s
    · rw [if_pos hc]
      by_cases hl : s + 1 < L
      · rw [if_pos hl, if_neg (show s ≠ L - 1 by omega), Nat.cast_sub hc.1]
        push_cast
        ring
      · have hs' : s = L - 1 := by omega
        rw [if_neg hl, if_pos hs', ← hs', if_pos hc.2]
        have hcm : frameClusterMass x s = (frameMass x s : ℝ) := by
          unfold frameClusterMass
          rw [hs']
          exact seqClusterMass_last L (frameMass x) (by omega) (hs' ▸ hc.2)
        rw [hcm, Nat.cast_sub hc.1, hs', Nat.cast_sub (by omega : 1 ≤ L)]
        push_cast
        ring
    · rw [if_neg hc]
      by_cases hs' : s = L - 1
      · rw [if_pos hs', ← hs', if_neg (fun h => hc ⟨by omega, h⟩), mul_zero]
      · rw [if_neg hs']
  rw [Finset.sum_congr rfl hpoint, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
  ring

/-- In stationary mean on the majority region, piles enter the peak from
behind only as fast as exceptional chips push anchored mass forward. -/
theorem stationary_cluster_linear_balance {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (t : ℕ) (ht : N < 2 * t) (htN : t ≤ N) :
    |∑ x, μ.weight x * (if t < largest x then
        w * (∑ i, clusterChipChange (fun s => (s : ℝ)) x i) -
          (L : ℝ) * (if 2 ≤ frameMass x (L - 1) then (frameMass x (L - 1) : ℝ) else 0)
      else 0)| ≤
      w * (((L - 1 : ℕ) : ℝ) * ((N - t : ℕ) : ℝ)) *
        (∑ x, if largest x = t + 1 then μ.weight x else 0) := by
  have h := stationary_clusterDrift_majority_le hL hw μ (fun s => (s : ℝ)) Nat.cast_zero
    (c := ((L - 1 : ℕ) : ℝ)) (fun s _ => Nat.cast_nonneg s)
    (fun s hs => by
      show (s : ℝ) ≤ ((L - 1 : ℕ) : ℝ)
      exact_mod_cast (show s ≤ L - 1 by omega)) t ht htN
  have hlocal (x : State L N) :
      (if t < largest x then clusterDrift w (fun s => (s : ℝ)) x else 0) =
        (if t < largest x then
          w * (∑ i, clusterChipChange (fun s => (s : ℝ)) x i) -
            (L : ℝ) * (if 2 ≤ frameMass x (L - 1) then (frameMass x (L - 1) : ℝ) else 0)
        else 0) := by
    by_cases hx : t < largest x
    · rw [if_pos hx, if_pos hx]
      exact clusterDrift_linear hL w x
    · rw [if_neg hx, if_neg hx]
  simpa only [hlocal] using h

/-- A chip from the index behind the peak into the peak removes the chipped
particle's weight. A pile of two there returns its remaining single to the
previous anchor. -/
theorem seqMoment_entry_chip (h : ℕ → ℝ) (h0 : h 0 = 0) {L : ℕ} (hL : 2 ≤ L)
    (a : ℕ → ℕ) (hpeak : 2 ≤ a 0) (hone : 1 ≤ a (L - 1)) :
    seqMoment h L (seqEntry L a 1) - seqMoment h L a =
      -h (seqAnchor a (L - 1)) +
        (if a (L - 1) = 2 then h (seqAnchor a (L - 1 - 1)) - h (L - 1) else 0) := by
  set b := seqEntry L a 1 with hb
  obtain ⟨n, hn⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  have hn' : L - 1 = n := by omega
  rw [hn'] at hone ⊢
  have hagree (v : ℕ) (hv : v < n) : (2 ≤ a v ↔ 2 ≤ b v) := by
    by_cases hv0 : v = 0
    · subst hv0
      simp [hb, seqEntry]
      omega
    · simp [hb, seqEntry, hv0, show v ≠ L - 1 by omega]
  have hanchor (u : ℕ) (hu : u < n) : seqAnchor b u = seqAnchor a u :=
    (seqAnchor_congr (fun v hv => hagree v (by omega))).symm
  have hbn : b n = a n - 1 := by simp [hb, seqEntry, show n ≠ 0 by omega, hn']
  have hlast : seqAnchor b n = if 3 ≤ a n then n else seqAnchor a (n - 1) := by
    split_ifs with h3
    · exact seqAnchor_of_pile b (by rw [hbn]; omega)
    · obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [hm, seqAnchor_succ_of_lt b (by rw [← hm, hbn]; omega), Nat.add_sub_cancel,
        hanchor m (by omega)]
  unfold seqMoment
  rw [hn, Finset.sum_range_succ, Finset.sum_range_succ]
  have hrest : (∑ u ∈ Finset.range n, h (seqAnchor b u) * (b u : ℝ)) =
      ∑ u ∈ Finset.range n, h (seqAnchor a u) * (a u : ℝ) := by
    apply Finset.sum_congr rfl
    intro u hu
    have hu' := Finset.mem_range.mp hu
    rw [hanchor u hu']
    by_cases hu0 : u = 0
    · subst hu0
      have hz : seqAnchor a 0 = 0 := by have := seqAnchor_le a 0; omega
      simp [hz, h0]
    · simp [hb, seqEntry, hu0, show u ≠ n by omega, hn']
  rw [hrest, hbn, hlast, Nat.cast_sub hone]
  by_cases h3 : 3 ≤ a n
  · rw [if_pos h3, if_neg (show a n ≠ 2 by omega), seqAnchor_of_pile a (by omega)]
    push_cast
    ring
  · rw [if_neg h3]
    by_cases h2 : a n = 2
    · rw [if_pos h2, show seqAnchor a n = n from seqAnchor_of_pile a (by omega), h2]
      push_cast
      ring
    · have h1 : a n = 1 := by omega
      have hA : seqAnchor a n = seqAnchor a (n - 1) := by
        obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [hm, seqAnchor_succ_of_lt a (by rw [← hm]; omega), Nat.add_sub_cancel]
      rw [if_neg h2, h1, hA]
      push_cast
      ring

/-- The change of a cluster moment when one particle chips from offset `s`:
a chip inside the background, or a chip into the peak from the last offset. -/
def seqChipChange (h : ℕ → ℝ) (L : ℕ) (a : ℕ → ℕ) (s : ℕ) : ℝ :=
  if s + 1 < L then
    (if 1 ≤ a (s + 1) then (h (s + 1) - h (seqAnchor a s)) * (1 + seqForwardMass L a s)
      else 0) +
    (if a s = 2 then (h (seqAnchor a (s - 1)) - h s) *
      (if a (s + 1) = 0 then 2 + seqForwardMass L a s else 1) else 0)
  else
    -h (seqAnchor a s) + (if a s = 2 then h (seqAnchor a (s - 1)) - h s else 0)

/-- The part of a chip change that carries mass forward: the chipped particle
and, when a single becomes a pile, the rest of the source's cluster. -/
def seqChipGain (h : ℕ → ℝ) (L : ℕ) (a : ℕ → ℕ) (s : ℕ) : ℝ :=
  if s + 1 < L ∧ 1 ≤ a (s + 1) then
    (h (s + 1) - h (seqAnchor a s)) * (1 + seqForwardMass L a s) else 0

theorem seqForwardMass_nonneg (L : ℕ) (a : ℕ → ℕ) (s : ℕ) : 0 ≤ seqForwardMass L a s :=
  Finset.sum_nonneg (fun u _ => by split_ifs <;> positivity)

/-- For a nondecreasing nonnegative profile, the rest of a chip change is a
loss: piles of two that dissolve return mass to an earlier anchor, and mass
entering the peak loses its weight. -/
theorem seqChipChange_le_gain (h : ℕ → ℝ) (hmono : Monotone h) (hnonneg : ∀ s, 0 ≤ h s)
    (L : ℕ) (a : ℕ → ℕ) (s : ℕ) :
    seqChipChange h L a s ≤ seqChipGain h L a s := by
  have hF := seqForwardMass_nonneg L a s
  have hback : h (seqAnchor a (s - 1)) - h s ≤ 0 :=
    sub_nonpos.mpr (hmono ((seqAnchor_le a (s - 1)).trans (Nat.sub_le s 1)))
  have hloss : (if a s = 2 then (h (seqAnchor a (s - 1)) - h s) *
      (if a (s + 1) = 0 then 2 + seqForwardMass L a s else 1) else 0) ≤ 0 := by
    split_ifs
    · exact mul_nonpos_of_nonpos_of_nonneg hback (by linarith)
    · exact mul_nonpos_of_nonpos_of_nonneg hback (by norm_num)
    · exact le_rfl
  have hentry :
      -h (seqAnchor a s) + (if a s = 2 then h (seqAnchor a (s - 1)) - h s else 0) ≤ 0 := by
    have := hnonneg (seqAnchor a s)
    split_ifs <;> linarith
  unfold seqChipChange seqChipGain
  by_cases hs : s + 1 < L
  · rw [if_pos hs]
    by_cases ht : 1 ≤ a (s + 1)
    · rw [if_pos ht, if_pos (show s + 1 < L ∧ 1 ≤ a (s + 1) from ⟨hs, ht⟩)]
      linarith
    · rw [if_neg ht, if_neg (show ¬(s + 1 < L ∧ 1 ≤ a (s + 1)) from fun h => ht h.2), zero_add]
      exact hloss
  · rw [if_neg hs, if_neg (show ¬(s + 1 < L ∧ 1 ≤ a (s + 1)) from fun h => hs h.1)]
    exact hentry

/-- The explicit form of `clusterChipChange` at every offset. -/
theorem clusterChipChange_eq {L N : ℕ} [NeZero L] (hL : 3 ≤ L) (h : ℕ → ℝ) (h0 : h 0 = 0)
    (x : State L N) (hmargin : N + 2 < 2 * largest x) {s : ℕ} (hs : s < L) :
    clusterChipChange h x (peakSite x + (s : Fin L)) =
      if 1 ≤ frameMass x s then seqChipChange h L (frameMass x) s else 0 := by
  have hoff : peakOffset x (peakSite x + (s : Fin L)) = s :=
    ((peak_add_eq_iff x hs _).mp rfl).symm
  have hocc : occ x (peakSite x + (s : Fin L)) = frameMass x s := rfl
  have ha0 : 2 ≤ frameMass x 0 := by rw [frameMass_zero]; omega
  unfold clusterChipChange
  by_cases hone : 1 ≤ frameMass x s
  · rw [dif_pos (by rw [hocc]; exact hone), if_pos hone]
    have hpeak := peakSite_chip_move x hmargin (peakSite x + (s : Fin L)) (by rw [hocc]; exact hone)
    unfold seqChipChange
    by_cases hlast : s + 1 < L
    · rw [if_pos hlast]
      have hrear : peakSite x + (s : Fin L) ≠ peakSite x - 1 := by
        intro he
        have := congrArg (peakOffset x) he
        rw [hoff, peakOffset_peakSite_sub_one hL] at this
        omega
      have hcongr := seqMoment_congr h (frameMass_move_of_peak_eq x _ 1 _ hpeak hrear)
      unfold clusterMoment
      rw [hcongr, hoff]
      exact seqMoment_chip h (frameMass x) hlast hone
    · rw [if_neg hlast]
      have hsL : s = L - 1 := by omega
      have hrear : peakSite x + (s : Fin L) = peakSite x - 1 :=
        (peak_add_eq_iff x hs _).mpr (by rw [peakOffset_peakSite_sub_one hL]; exact hsL)
      revert hpeak
      have hmove : ∀ (hk : 1 ≤ occ x (peakSite x + (s : Fin L))),
          move x (peakSite x + (s : Fin L)) 1 hk =
            move x (peakSite x - 1) 1 (by rw [← hrear]; exact hk) := by
        intro hk
        congr 1
      intro hpeak
      rw [hmove] at hpeak ⊢
      have hcongr := seqMoment_congr h (frameMass_move_rear hL x 1 _ hpeak)
      unfold clusterMoment
      rw [hcongr, hsL]
      rw [hsL] at hone
      exact seqMoment_entry_chip h h0 (by omega) (frameMass x) ha0 hone
  · rw [dif_neg (by rw [hocc]; exact hone), if_neg hone]

/-- The part of a chip change lost to dissolution and to entering the peak. -/
def seqChipLoss (h : ℕ → ℝ) (L : ℕ) (a : ℕ → ℕ) (s : ℕ) : ℝ :=
  seqChipGain h L a s - seqChipChange h L a s

theorem seqChipLoss_nonneg (h : ℕ → ℝ) (hmono : Monotone h) (hnonneg : ∀ s, 0 ≤ h s)
    (L : ℕ) (a : ℕ → ℕ) (s : ℕ) : 0 ≤ seqChipLoss h L a s :=
  sub_nonneg.mpr (seqChipChange_le_gain h hmono hnonneg L a s)

/-- Cluster mass weighted by the negative second difference of the profile,
summed over background piles. -/
def clusterCurvature {L N : ℕ} [NeZero L] (h : ℕ → ℝ) (x : State L N) : ℝ :=
  ∑ s ∈ Finset.range L, if 1 ≤ s ∧ 2 ≤ frameMass x s then
    frameClusterMass x s * (2 * h s - h (s - 1) - (if s + 1 < L then h (s + 1) else 0))
  else 0

/-- Total forward gain of all chips. -/
def clusterChipGain {L N : ℕ} [NeZero L] (h : ℕ → ℝ) (x : State L N) : ℝ :=
  ∑ s ∈ Finset.range L, if 1 ≤ frameMass x s then seqChipGain h L (frameMass x) s else 0

/-- Total loss of all chips to dissolution and to entering the peak. -/
def clusterChipLoss {L N : ℕ} [NeZero L] (h : ℕ → ℝ) (x : State L N) : ℝ :=
  ∑ s ∈ Finset.range L, if 1 ≤ frameMass x s then seqChipLoss h L (frameMass x) s else 0

/-- The cluster drift splits into curvature, forward gain and loss. -/
theorem clusterDrift_eq_gain_sub {L N : ℕ} [NeZero L] (hL : 3 ≤ L) (w : ℝ) (h : ℕ → ℝ)
    (h0 : h 0 = 0) (x : State L N) (hmargin : N + 2 < 2 * largest x) :
    clusterDrift w h x = w * (clusterChipGain h x - clusterChipLoss h x) - clusterCurvature h x := by
  have hchips : (∑ i, clusterChipChange h x i) = clusterChipGain h x - clusterChipLoss h x := by
    rw [sum_sites_eq_sum_offsets (peakSite x) (clusterChipChange h x)]
    unfold clusterChipGain clusterChipLoss
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    rw [clusterChipChange_eq hL h h0 x hmargin (Finset.mem_range.mp hs)]
    unfold seqChipLoss
    split_ifs <;> ring
  have hcurv : (∑ s ∈ Finset.range L, if 1 ≤ s ∧ 2 ≤ frameMass x s then
      frameClusterMass x s * ((if s + 1 < L then h (s + 1) else 0) - 2 * h s + h (s - 1))
    else 0) = -clusterCurvature h x := by
    unfold clusterCurvature
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> ring
  unfold clusterDrift
  rw [hchips, hcurv]
  ring

/-- The stationary cluster balance for a nonnegative profile.
Curvature of the profile at background piles and losses from dissolution and
entry into the peak are paid for by the forward gain of chips onto occupied
sites, up to the cutoff error. -/
theorem stationary_cluster_balance_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (h : ℕ → ℝ) (h0 : h 0 = 0)
    (hnonneg : ∀ s, 0 ≤ h s) {c : ℝ} (hc : ∀ s < L, h s ≤ c)
    (t : ℕ) (ht : N < 2 * t) (htN : t ≤ N) :
    (∑ x, μ.weight x * (if t < largest x then clusterCurvature h x else 0)) +
        w * (∑ x, μ.weight x * (if t < largest x then clusterChipLoss h x else 0)) ≤
      w * (∑ x, μ.weight x * (if t < largest x then clusterChipGain h x else 0)) +
        w * (c * ((N - t : ℕ) : ℝ)) * (∑ x, if largest x = t + 1 then μ.weight x else 0) := by
  have hb := (abs_le.mp (stationary_clusterDrift_majority_le hL hw μ h h0
    (fun s _ => hnonneg s) hc t ht htN)).1
  have hpoint (x : State L N) :
      μ.weight x * (if t < largest x then clusterDrift w h x else 0) =
        w * (μ.weight x * (if t < largest x then clusterChipGain h x else 0)) -
          w * (μ.weight x * (if t < largest x then clusterChipLoss h x else 0)) -
          μ.weight x * (if t < largest x then clusterCurvature h x else 0) := by
    by_cases hx : t < largest x
    · rw [if_pos hx, if_pos hx, if_pos hx, if_pos hx,
        clusterDrift_eq_gain_sub hL w h h0 x (by omega)]
      ring
    · rw [if_neg hx, if_neg hx, if_neg hx, if_neg hx]
      ring
  simp_rw [hpoint] at hb
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hb
  linarith

/-- For the linear profile, the loss at a pile of two with an empty site ahead
is its cluster mass times its distance to the previous anchor. -/
theorem seqChipLoss_linear_dissolve (L : ℕ) (a : ℕ → ℕ) {s : ℕ} (hs : s + 1 < L)
    (htwo : a s = 2) (hempty : a (s + 1) = 0) :
    seqChipLoss (fun v => (v : ℝ)) L a s =
      ((s : ℝ) - (seqAnchor a (s - 1) : ℝ)) * (2 + seqForwardMass L a s) := by
  unfold seqChipLoss seqChipGain seqChipChange
  rw [if_neg (show ¬(s + 1 < L ∧ 1 ≤ a (s + 1)) from fun h => by omega), if_pos hs,
    if_neg (show ¬(1 ≤ a (s + 1)) by omega), if_pos htwo, if_pos hempty]
  ring

/-- Piles of two dissolve before travelling far from the pile behind them.
In stationary mean on the majority region, the piles entering the peak from
behind, at rate `L` per unit of mass, together with every pile of two that has
an empty site ahead, weighted by `w`, its cluster mass and its distance to the
previous anchor, cost no more than `w` times the forward gain of chips onto
occupied sites, measured by distance to the source's anchor and forward
cluster mass. -/
theorem stationary_dissolution_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (t : ℕ) (ht : N < 2 * t) (htN : t ≤ N) :
    (L : ℝ) * (∑ x, μ.weight x * (if t < largest x ∧ 2 ≤ frameMass x (L - 1) then
        (frameMass x (L - 1) : ℝ) else 0)) +
      w * (∑ x, μ.weight x * (if t < largest x then
        ∑ s ∈ Finset.range L, (if s + 1 < L ∧ frameMass x s = 2 ∧ frameMass x (s + 1) = 0 then
          ((s : ℝ) - (seqAnchor (frameMass x) (s - 1) : ℝ)) *
            (2 + seqForwardMass L (frameMass x) s) else 0)
      else 0)) ≤
    w * (∑ x, μ.weight x * (if t < largest x then
        clusterChipGain (fun v => (v : ℝ)) x else 0)) +
      w * (((L - 1 : ℕ) : ℝ) * ((N - t : ℕ) : ℝ)) *
        (∑ x, if largest x = t + 1 then μ.weight x else 0) := by
  have hmono : Monotone (fun v : ℕ => (v : ℝ)) := fun _ _ h => Nat.cast_le.mpr h
  have hbal := stationary_cluster_balance_le hL hw μ (fun v => (v : ℝ)) Nat.cast_zero
    (fun s => Nat.cast_nonneg s) (c := ((L - 1 : ℕ) : ℝ))
    (fun s hs => by
      show (s : ℝ) ≤ ((L - 1 : ℕ) : ℝ)
      exact_mod_cast (show s ≤ L - 1 by omega)) t ht htN
  -- curvature of the linear profile sits only at the last offset
  have hcurv (x : State L N) : clusterCurvature (fun v => (v : ℝ)) x =
      (L : ℝ) * (if 2 ≤ frameMass x (L - 1) then (frameMass x (L - 1) : ℝ) else 0) := by
    unfold clusterCurvature
    have hpoint (s : ℕ) (hs : s ∈ Finset.range L) :
        (if 1 ≤ s ∧ 2 ≤ frameMass x s then frameClusterMass x s *
          (2 * (s : ℝ) - ((s - 1 : ℕ) : ℝ) - (if s + 1 < L then ((s + 1 : ℕ) : ℝ) else 0))
        else 0) = if s = L - 1 then (L : ℝ) * (if 2 ≤ frameMass x (L - 1) then
          (frameMass x (L - 1) : ℝ) else 0) else 0 := by
      have hsL := Finset.mem_range.mp hs
      by_cases hc : 1 ≤ s ∧ 2 ≤ frameMass x s
      · rw [if_pos hc]
        by_cases hl : s + 1 < L
        · rw [if_pos hl, if_neg (show s ≠ L - 1 by omega), Nat.cast_sub hc.1]
          push_cast
          ring
        · have hs' : s = L - 1 := by omega
          rw [if_neg hl, if_pos hs', ← hs', if_pos hc.2]
          have hcm : frameClusterMass x s = (frameMass x s : ℝ) := by
            unfold frameClusterMass
            rw [hs']
            exact seqClusterMass_last L (frameMass x) (by omega) (hs' ▸ hc.2)
          rw [hcm, Nat.cast_sub hc.1, hs', Nat.cast_sub (by omega : 1 ≤ L)]
          push_cast
          ring
      · rw [if_neg hc]
        by_cases hs' : s = L - 1
        · rw [if_pos hs', ← hs', if_neg (fun h => hc ⟨by omega, h⟩), mul_zero]
        · rw [if_neg hs']
    rw [Finset.sum_congr rfl hpoint, Finset.sum_ite_eq',
      if_pos (Finset.mem_range.mpr (by omega))]
  -- the loss dominates its dissolution part
  have hloss (x : State L N) :
      (∑ s ∈ Finset.range L, (if s + 1 < L ∧ frameMass x s = 2 ∧ frameMass x (s + 1) = 0 then
          ((s : ℝ) - (seqAnchor (frameMass x) (s - 1) : ℝ)) *
            (2 + seqForwardMass L (frameMass x) s) else 0)) ≤
        clusterChipLoss (fun v => (v : ℝ)) x := by
    unfold clusterChipLoss
    apply Finset.sum_le_sum
    intro s _
    by_cases hc : s + 1 < L ∧ frameMass x s = 2 ∧ frameMass x (s + 1) = 0
    · rw [if_pos hc, if_pos (by omega),
        seqChipLoss_linear_dissolve L (frameMass x) hc.1 hc.2.1 hc.2.2]
    · rw [if_neg hc]
      split_ifs
      · exact seqChipLoss_nonneg _ hmono (fun s => Nat.cast_nonneg s) L _ s
      · exact le_rfl
  have hcurv_sum : (∑ x, μ.weight x * (if t < largest x then
      clusterCurvature (fun v => (v : ℝ)) x else 0)) =
        (L : ℝ) * (∑ x, μ.weight x * (if t < largest x ∧ 2 ≤ frameMass x (L - 1) then
          (frameMass x (L - 1) : ℝ) else 0)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : t < largest x
    · rw [if_pos hx, hcurv]
      by_cases hp : 2 ≤ frameMass x (L - 1)
      · rw [if_pos hp, if_pos ⟨hx, hp⟩]
        ring
      · rw [if_neg hp, if_neg (fun h => hp h.2)]
        ring
    · rw [if_neg hx, if_neg (fun h => hx h.1)]
      ring
  have hloss_sum : (∑ x, μ.weight x * (if t < largest x then
        ∑ s ∈ Finset.range L, (if s + 1 < L ∧ frameMass x s = 2 ∧ frameMass x (s + 1) = 0 then
          ((s : ℝ) - (seqAnchor (frameMass x) (s - 1) : ℝ)) *
            (2 + seqForwardMass L (frameMass x) s) else 0)
      else 0)) ≤ ∑ x, μ.weight x * (if t < largest x then
        clusterChipLoss (fun v => (v : ℝ)) x else 0) := by
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (μ.nonneg x)
    split_ifs
    · exact hloss x
    · exact le_rfl
  rw [hcurv_sum] at hbal
  have := mul_le_mul_of_nonneg_left hloss_sum hw
  linarith

/-! ### Clusters near the peak -/

/-- A concave profile with slope `R - j` on the bond from `j` to `j + 1`,
constant beyond offset `R`. -/
def cappedProfile (R : ℕ) (s : ℕ) : ℝ :=
  ∑ j ∈ Finset.range s, ((R - j : ℕ) : ℝ)

theorem cappedProfile_zero (R : ℕ) : cappedProfile R 0 = 0 := by simp [cappedProfile]

theorem cappedProfile_succ (R s : ℕ) :
    cappedProfile R (s + 1) = cappedProfile R s + ((R - s : ℕ) : ℝ) := by
  simp [cappedProfile, Finset.sum_range_succ]

theorem cappedProfile_nonneg (R s : ℕ) : 0 ≤ cappedProfile R s :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

theorem cappedProfile_mono (R : ℕ) : Monotone (cappedProfile R) := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih =>
    rw [cappedProfile_succ]
    linarith [(Nat.cast_nonneg (R - n) : (0 : ℝ) ≤ ((R - n : ℕ) : ℝ))]

theorem cappedProfile_le_sq (R s : ℕ) : cappedProfile R s ≤ (R : ℝ) * R := by
  induction s with
  | zero => simp [cappedProfile]; positivity
  | succ n ih =>
    rw [cappedProfile_succ]
    by_cases hn : n < R
    · -- below the cap the profile is at most `R * n` plus the increment
      have hlin : cappedProfile R n ≤ (R : ℝ) * n := by
        unfold cappedProfile
        calc
          _ ≤ ∑ _j ∈ Finset.range n, (R : ℝ) :=
            Finset.sum_le_sum (fun j _ => by exact_mod_cast Nat.sub_le R j)
          _ = (R : ℝ) * n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
      have hinc : ((R - n : ℕ) : ℝ) = (R : ℝ) - n := by rw [Nat.cast_sub hn.le]
      have hnR : (n : ℝ) + 1 ≤ R := by exact_mod_cast hn
      rw [hinc]
      nlinarith
    · rw [show R - n = 0 by omega, Nat.cast_zero, add_zero]
      exact ih

/-- Across a stretch of `k` bonds the capped profile rises by at most `k R`. -/
theorem cappedProfile_sub_le (R : ℕ) {A s : ℕ} (hA : A ≤ s) :
    cappedProfile R s - cappedProfile R A ≤ (R : ℝ) * ((s : ℝ) - A) := by
  induction s, hA using Nat.le_induction with
  | base => simp
  | succ n _ ih =>
    rw [cappedProfile_succ]
    have : ((R - n : ℕ) : ℝ) ≤ R := by exact_mod_cast Nat.sub_le R n
    push_cast
    nlinarith

theorem seqClusterMass_nonneg (L : ℕ) (a : ℕ → ℕ) (s : ℕ) : 0 ≤ seqClusterMass L a s :=
  Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

/-- The mass of the clusters anchored at offsets `1, …, R`. -/
def nearClusterMass {L N : ℕ} [NeZero L] (R : ℕ) (x : State L N) : ℝ :=
  ∑ s ∈ Finset.range L, if 1 ≤ s ∧ s ≤ R ∧ 2 ≤ frameMass x s then frameClusterMass x s else 0

/-- The capped profile has curvature at least one at every pile within `R`. -/
theorem nearClusterMass_le_curvature {L N : ℕ} [NeZero L] (R : ℕ) (x : State L N) :
    nearClusterMass R x ≤ clusterCurvature (cappedProfile R) x := by
  unfold nearClusterMass clusterCurvature
  apply Finset.sum_le_sum
  intro s _
  have hm := seqClusterMass_nonneg L (frameMass x) s
  by_cases hc : 1 ≤ s ∧ 2 ≤ frameMass x s
  · rw [if_pos hc]
    obtain ⟨n, hn⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
    have hcoef : 2 * cappedProfile R s - cappedProfile R (s - 1) -
        (if s + 1 < L then cappedProfile R (s + 1) else 0) ≥
          if s ≤ R then 1 else 0 := by
      rw [hn, Nat.add_sub_cancel, cappedProfile_succ R n]
      have hnn := cappedProfile_nonneg R n
      by_cases hl : n + 1 + 1 < L
      · rw [if_pos hl, cappedProfile_succ R (n + 1), cappedProfile_succ R n]
        by_cases hR : n + 1 ≤ R
        · rw [if_pos hR, Nat.cast_sub (by omega : n ≤ R), Nat.cast_sub hR]
          push_cast
          linarith
        · rw [if_neg hR, show R - n = 0 by omega, show R - (n + 1) = 0 by omega]
          push_cast
          linarith
      · rw [if_neg hl]
        by_cases hR : n + 1 ≤ R
        · rw [if_pos hR, Nat.cast_sub (by omega : n ≤ R)]
          have : (n : ℝ) + 1 ≤ R := by exact_mod_cast hR
          linarith
        · rw [if_neg hR]
          have := (Nat.cast_nonneg (R - n) : (0 : ℝ) ≤ ((R - n : ℕ) : ℝ))
          linarith
    by_cases hR : s ≤ R
    · rw [if_pos ⟨hc.1, hR, hc.2⟩]
      rw [if_pos hR] at hcoef
      unfold frameClusterMass at hm ⊢
      nlinarith
    · rw [if_neg (fun h => hR h.2.1)]
      rw [if_neg hR] at hcoef
      unfold frameClusterMass at hm ⊢
      nlinarith
  · rw [if_neg hc, if_neg (fun h => hc ⟨h.1, h.2.2⟩)]

/-- The forward gain of a chip under the capped profile is at most `R` times
its gain under the linear profile. -/
theorem clusterChipGain_capped_le {L N : ℕ} [NeZero L] (R : ℕ) (x : State L N) :
    clusterChipGain (cappedProfile R) x ≤ (R : ℝ) * clusterChipGain (fun v => (v : ℝ)) x := by
  unfold clusterChipGain
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  split_ifs with hone
  · unfold seqChipGain
    split_ifs with hc
    · have hF := seqForwardMass_nonneg L (frameMass x) s
      have hA : seqAnchor (frameMass x) s ≤ s + 1 := (seqAnchor_le _ s).trans (Nat.le_succ s)
      have hsub := cappedProfile_sub_le R hA
      push_cast at hsub ⊢
      nlinarith
    · simp
  · simp

/-- Clusters anchored within `R` of the peak have mass at most `w R` times the
linear forward gain of chips onto occupied sites, in stationary mean on the
majority region, up to the cutoff error. The same gain bounds dissolution in
`stationary_dissolution_le`. -/
theorem stationary_nearClusterMass_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (R : ℕ)
    (t : ℕ) (ht : N < 2 * t) (htN : t ≤ N) :
    (∑ x, μ.weight x * (if t < largest x then nearClusterMass R x else 0)) ≤
      w * (R : ℝ) * (∑ x, μ.weight x * (if t < largest x then
        clusterChipGain (fun v => (v : ℝ)) x else 0)) +
      w * ((R : ℝ) * R * ((N - t : ℕ) : ℝ)) *
        (∑ x, if largest x = t + 1 then μ.weight x else 0) := by
  have hbal := stationary_cluster_balance_le hL hw μ (cappedProfile R) (cappedProfile_zero R)
    (cappedProfile_nonneg R) (c := (R : ℝ) * R) (fun s _ => cappedProfile_le_sq R s) t ht htN
  have hloss : 0 ≤ ∑ x, μ.weight x * (if t < largest x then
      clusterChipLoss (cappedProfile R) x else 0) := by
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg (μ.nonneg x)
    split_ifs
    · exact Finset.sum_nonneg (fun s _ => by
        split_ifs
        · exact seqChipLoss_nonneg _ (cappedProfile_mono R) (cappedProfile_nonneg R) L _ s
        · exact le_rfl)
    · exact le_rfl
  have hnear : (∑ x, μ.weight x * (if t < largest x then nearClusterMass R x else 0)) ≤
      ∑ x, μ.weight x * (if t < largest x then clusterCurvature (cappedProfile R) x else 0) := by
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (μ.nonneg x)
    split_ifs
    · exact nearClusterMass_le_curvature R x
    · exact le_rfl
  have hgain : (∑ x, μ.weight x * (if t < largest x then
      clusterChipGain (cappedProfile R) x else 0)) ≤
        (R : ℝ) * (∑ x, μ.weight x * (if t < largest x then
          clusterChipGain (fun v => (v : ℝ)) x else 0)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    split_ifs
    · have := mul_le_mul_of_nonneg_left (clusterChipGain_capped_le R x) (μ.nonneg x)
      linarith
    · simp
  have hwg := mul_le_mul_of_nonneg_left hgain hw
  nlinarith

/-! ### The peak's share of the forward gain -/

/-- The forward gain of chips from background sites under the linear profile. -/
def backgroundChipGain {L N : ℕ} [NeZero L] (x : State L N) : ℝ :=
  ∑ s ∈ Finset.range L, if 1 ≤ s ∧ 1 ≤ frameMass x s then
    seqChipGain (fun v => (v : ℝ)) L (frameMass x) s else 0

theorem singleCount_eq_frame {L N : ℕ} [NeZero L] (x : State L N) :
    singleCount x = ∑ u ∈ Finset.range L, if frameMass x u = 1 then (1 : ℝ) else 0 := by
  unfold singleCount
  exact sum_sites_eq_sum_offsets (peakSite x) (fun i => if occ x i = 1 then (1 : ℝ) else 0)

/-- Mass anchored at the peak beyond offset zero consists of singles. -/
theorem seqForwardMass_peak_le_singles {L N : ℕ} [NeZero L] (x : State L N) :
    seqForwardMass L (frameMass x) 0 ≤ singleCount x := by
  rw [singleCount_eq_frame]
  unfold seqForwardMass
  apply Finset.sum_le_sum
  intro u _
  have hz : seqAnchor (frameMass x) 0 = 0 := by
    have := seqAnchor_le (frameMass x) 0; omega
  rw [hz]
  by_cases hc : 0 + 1 ≤ u ∧ seqAnchor (frameMass x) u = 0
  · rw [if_pos hc]
    have hlt : frameMass x u < 2 := seqAnchor_no_pile (frameMass x) (by omega) le_rfl
    by_cases h1 : frameMass x u = 1
    · rw [if_pos h1, h1]
      norm_num
    · have h0 : frameMass x u = 0 := by omega
      rw [if_neg h1, h0]
      norm_num
  · rw [if_neg hc]
    split_ifs <;> norm_num

/-- The linear forward gain splits into the peak's chips and the background's. -/
theorem clusterChipGain_linear_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L) (x : State L N)
    (hpeak : 1 ≤ frameMass x 0) :
    clusterChipGain (fun v => (v : ℝ)) x ≤
      (frameMass x 1 : ℝ) + singleCount x + backgroundChipGain x := by
  unfold clusterChipGain backgroundChipGain
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega : 0 < L)),
    ← Finset.add_sum_erase (Finset.range L) (fun s => if 1 ≤ s ∧ 1 ≤ frameMass x s then
      seqChipGain (fun v => (v : ℝ)) L (frameMass x) s else 0)
      (Finset.mem_range.mpr (by omega : 0 < L))]
  have hrest : (∑ s ∈ (Finset.range L).erase 0, if 1 ≤ frameMass x s then
      seqChipGain (fun v => (v : ℝ)) L (frameMass x) s else 0) =
        ∑ s ∈ (Finset.range L).erase 0, if 1 ≤ s ∧ 1 ≤ frameMass x s then
          seqChipGain (fun v => (v : ℝ)) L (frameMass x) s else 0 := by
    apply Finset.sum_congr rfl
    intro s hs
    have hs0 := Finset.ne_of_mem_erase hs
    by_cases h1 : 1 ≤ frameMass x s
    · rw [if_pos h1, if_pos ⟨by omega, h1⟩]
    · rw [if_neg h1, if_neg (fun h => h1 h.2)]
  rw [hrest, if_pos hpeak, if_neg (show ¬(1 ≤ 0 ∧ 1 ≤ frameMass x 0) by omega), zero_add]
  have hpeakgain : seqChipGain (fun v => (v : ℝ)) L (frameMass x) 0 ≤
      (frameMass x 1 : ℝ) + singleCount x := by
    have hF := seqForwardMass_peak_le_singles x
    have hz : seqAnchor (frameMass x) 0 = 0 := by
      have := seqAnchor_le (frameMass x) 0; omega
    unfold seqChipGain
    split_ifs with hc
    · rw [hz]
      have h1 : (1 : ℝ) ≤ (frameMass x 1 : ℝ) := by exact_mod_cast hc.2
      push_cast
      linarith
    · have := seqForwardMass_nonneg L (frameMass x) 0
      have hS : 0 ≤ singleCount x := Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
      positivity
  linarith

/-- In stationary mean on the majority region, the peak contributes at most
`w (P(M > t) + E[K])` to the linear forward gain, up to the cutoff error.
Only the background's gain remains to be bounded. -/
theorem stationary_clusterChipGain_le {L N : ℕ} [NeZero L] (hL : 3 ≤ L)
    {w : ℝ} (hw : 0 ≤ w) (μ : StationaryLaw L N w) (t : ℕ) (ht : N < 2 * t) (htN : t ≤ N) :
    (∑ x, μ.weight x * (if t < largest x then clusterChipGain (fun v => (v : ℝ)) x else 0)) ≤
      w * ((∑ x, if t < largest x then μ.weight x else 0) +
        ∑ x, μ.weight x * (if t < largest x then occupiedCount x else 0)) +
      (∑ x, μ.weight x * (if t < largest x then backgroundChipGain x else 0)) +
      w * ((L : ℝ) * ((N - t : ℕ) : ℝ)) * (∑ x, if largest x = t + 1 then μ.weight x else 0) := by
  set P := ∑ x, if largest x = t + 1 then μ.weight x else 0 with hP
  -- the mass just ahead of the peak
  have hfront := (abs_le.mp (stationary_backgroundMass_majority_drift_le hL hw μ t ht htN)).1
  have hfront' : (∑ x, μ.weight x * (if t < largest x then (frameMass x 1 : ℝ) else 0)) ≤
      w * (∑ x, if t < largest x then μ.weight x else 0) +
        w * ((N - t : ℕ) : ℝ) * P := by
    have hpoint (x : State L N) :
        μ.weight x * (if t < largest x then (frameMass x 1 : ℝ) else 0) ≤
          w * (if t < largest x then μ.weight x else 0) -
            μ.weight x * (if t < largest x then
              w - (occ x (right (peakSite x)) : ℝ) -
                departureMassRate w (occ x (peakSite x - 1)) else 0) := by
      have hq := departureMassRate_nonneg hw (occ x (peakSite x - 1))
      have hfm : (frameMass x 1 : ℝ) = (occ x (right (peakSite x)) : ℝ) := by
        unfold frameMass
        rw [right_eq_add_one, Nat.cast_one]
      by_cases hx : t < largest x
      · rw [if_pos hx, if_pos hx, if_pos hx, hfm]
        nlinarith [μ.nonneg x]
      · rw [if_neg hx, if_neg hx, if_neg hx]
        simp
    calc
      _ ≤ ∑ x, (w * (if t < largest x then μ.weight x else 0) -
            μ.weight x * (if t < largest x then
              w - (occ x (right (peakSite x)) : ℝ) -
                departureMassRate w (occ x (peakSite x - 1)) else 0)) :=
        Finset.sum_le_sum (fun x _ => hpoint x)
      _ ≤ _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        linarith
  -- the singles
  have hsing := stationary_peak_singles_rear_flux_le hL hw μ t ht htN
  have hsing' : (∑ x, μ.weight x * (if t < largest x then singleCount x else 0)) ≤
      w * (∑ x, μ.weight x * (if t < largest x then occupiedCount x else 0)) +
        w * (((L - 1 : ℕ) : ℝ) * ((N - t : ℕ) : ℝ)) * P := by
    refine le_trans (Finset.sum_le_sum (fun x _ => ?_)) hsing
    apply mul_le_mul_of_nonneg_left _ (μ.nonneg x)
    split_ifs
    · have := departureMassRate_nonneg hw (occ x (peakSite x - 1))
      have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      nlinarith
    · exact le_rfl
  -- the pointwise split
  have hsplit : (∑ x, μ.weight x * (if t < largest x then clusterChipGain (fun v => (v : ℝ)) x
      else 0)) ≤
      (∑ x, μ.weight x * (if t < largest x then (frameMass x 1 : ℝ) else 0)) +
        (∑ x, μ.weight x * (if t < largest x then singleCount x else 0)) +
        (∑ x, μ.weight x * (if t < largest x then backgroundChipGain x else 0)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : t < largest x
    · rw [if_pos hx, if_pos hx, if_pos hx, if_pos hx]
      have hpk : 1 ≤ frameMass x 0 := by rw [frameMass_zero]; omega
      have := mul_le_mul_of_nonneg_left (clusterChipGain_linear_le hL x hpk) (μ.nonneg x)
      linarith
    · rw [if_neg hx, if_neg hx, if_neg hx, if_neg hx]
      simp
  have hLcast : ((L - 1 : ℕ) : ℝ) + 1 = (L : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ L)]
    ring
  have hPnn : 0 ≤ P := Finset.sum_nonneg (fun x _ => by split_ifs <;> [exact μ.nonneg x; rfl])
  have herr : w * ((N - t : ℕ) : ℝ) * P + w * (((L - 1 : ℕ) : ℝ) * ((N - t : ℕ) : ℝ)) * P =
      w * ((L : ℝ) * ((N - t : ℕ) : ℝ)) * P := by
    rw [← hLcast]
    ring
  linarith

end
end Chipping
