import ChippingSupercondensation.Clusters
import ChippingSupercondensation.PileCount

/-!
# Clusters of mass three

Piles of two are priced in `PileCount`. The next level prices clusters of
mass three, a bare pile of three or a pile of two with one single in its
cluster, by weights that depend on this internal state. A count of piles of
three cannot do this: it does not distinguish a single ahead of its pile, which
will be reabsorbed, from a single shed behind it.

This file records how cluster masses and the class weights change under every
whole move and under every chip into an empty site from a site not holding
exactly two particles. A whole move of a background pile carries its cluster
one step, or merges it with the cluster ahead (`seqClusterMass_pile_move`). A
whole move of the peak lowers every cluster by one offset
(`seqClusterMass_shift`). A trivial chip changes no cluster mass
(`seqClusterMass_trivial_chip`). All of these follow from the cluster-moment
lemmas of `Clusters`, since a cluster mass is the cluster moment of the
indicator of its anchor (`seqClusterMass_eq_seqMoment`).

The class weight is `B₁` for a bare pile of three, `B₂` for a pile of two with
one single in its cluster, and zero otherwise (`massThreeWeight`).
`generator_massThreePotential_eq` gives the exact drift of the total class
weight on the majority region. Whole moves enter explicitly: a pile absorbing
its single gains `B₁ - B₂`, merges and absorption by the peak only lose weight.
Chips enter through `massThreeChipChange`, which for a trivial chip is
`B₂ - B₁` at a bare pile of three and zero otherwise
(`massThreeChipChange_trivial`). `generator_massThreeLyapunov_eq` adds the
first moment and the price of piles of two.

`seqClusterMass_chip` gives the cluster masses after any chip, and the lemmas
`seqMassThreePotential_dissolve`, `seqMassThreePotential_shed`,
`seqMassThreePotential_pile_onto_pile`, `seqMassThreePotential_pile_onto_single`,
`seqMassThreePotential_single_onto_pile` and
`seqMassThreePotential_single_onto_single` evaluate the class-weight change of
every chip that is not trivial. `massThreeChipChange_eq_seq` transfers them to
the ring. A dissolving pile of two never adds class weight
(`seqMassThreePotential_dissolve_le`).

These formulas also show that weights of this form are too weak. Three adjacent
singles in one cluster have two bonds along which a chip rebuilds a pile, and
the first creates a cluster of mass three, so their drift is
`-1 + 3w + w B₂`. A drift of at most `-c` there needs `B₂ ≤ (1 - 3w - c)/w`.
The pile of two with its single just ahead needs `B₂ ≥ 2 + c/w + c/w²`. So `c`
is at most of order `w`, while every occupied site costs `w` in the first
moment. Classes that also contain the debris of a dissolved cluster, with
weights of order `1/w²`, are needed instead.
-/

namespace Chipping

open Filter
open scoped BigOperators Topology

noncomputable section

/-! ### Cluster masses under whole moves and trivial chips -/

/-- A cluster mass is the cluster moment of the indicator of its anchor. -/
theorem seqClusterMass_eq_seqMoment (L : ℕ) (a : ℕ → ℕ) (t : ℕ) :
    seqClusterMass L a t = seqMoment (fun v => if v = t then 1 else 0) L a := by
  unfold seqClusterMass seqMoment
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : seqAnchor a u = t <;> simp [h]

/-- After a whole move of the pile at `s`, its cluster sits at `s + 1`, joined
by the cluster that was there if `s + 1` held a pile. -/
theorem seqClusterMass_pile_move {L : ℕ} (a : ℕ → ℕ) {s : ℕ} (hs : s + 1 < L)
    (hpile : 2 ≤ a s) (t : ℕ) :
    seqClusterMass L (seqMove a s (a s)) t =
      seqClusterMass L a t +
        seqClusterMass L a s * ((if t = s + 1 then 1 else 0) - (if t = s then 1 else 0)) := by
  have h := seqMoment_pile_move (fun v => if v = t then (1 : ℝ) else 0) a hs hpile
  rw [← seqClusterMass_eq_seqMoment, ← seqClusterMass_eq_seqMoment] at h
  have e₁ : (if s + 1 = t then (1 : ℝ) else 0) = if t = s + 1 then 1 else 0 :=
    if_congr eq_comm rfl rfl
  have e₂ : (if s = t then (1 : ℝ) else 0) = if t = s then 1 else 0 := if_congr eq_comm rfl rfl
  simp only at h
  rw [e₁, e₂] at h
  linarith

/-- After a whole move of the peak, the cluster at offset `t + 1` sits at `t`. -/
theorem seqClusterMass_shift {L : ℕ} (hL : 2 ≤ L) (a : ℕ → ℕ) {t : ℕ} (ht : 1 ≤ t) :
    seqClusterMass L (seqShift L a) t = seqClusterMass L a (t + 1) := by
  have h := seqMoment_shift (fun v => if v = t then (1 : ℝ) else 0) (by simp; omega) hL a
  beta_reduce at h
  rw [← seqClusterMass_eq_seqMoment, ← seqClusterMass_eq_seqMoment] at h
  have hsplit : (∑ u ∈ Finset.range L, (a u : ℝ) *
      ((if seqAnchor a u - 1 = t then 1 else 0) - (if seqAnchor a u = t then 1 else 0))) =
        seqClusterMass L a (t + 1) - seqClusterMass L a t := by
    unfold seqClusterMass
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _
    have hiff : seqAnchor a u - 1 = t ↔ seqAnchor a u = t + 1 := by omega
    rw [if_congr hiff rfl rfl]
    split_ifs <;> ring
  rw [hsplit] at h
  linarith

/-- A chip into an empty site from a site not holding exactly two particles
changes no cluster mass. -/
theorem seqClusterMass_trivial_chip {L : ℕ} (a : ℕ → ℕ) {s : ℕ} (hs : s + 1 < L)
    (hone : 1 ≤ a s) (htwo : a s ≠ 2) (hempty : a (s + 1) = 0) (t : ℕ) :
    seqClusterMass L (seqMove a s 1) t = seqClusterMass L a t := by
  rw [seqClusterMass_eq_seqMoment, seqClusterMass_eq_seqMoment]
  exact seqMoment_trivial_chip _ a hs hone htwo hempty

/-- A whole move of the pile at the last offset into the peak removes its
cluster and changes no other. -/
theorem seqClusterMass_entry_whole {L : ℕ} (hL : 2 ≤ L) (a : ℕ → ℕ)
    (hpeak : 2 ≤ a 0) (hp : 2 ≤ a (L - 1)) {t : ℕ} (ht : 1 ≤ t) :
    seqClusterMass L (seqEntry L a (a (L - 1))) t =
      seqClusterMass L a t - (if t = L - 1 then seqClusterMass L a (L - 1) else 0) := by
  have h := seqMoment_entry_whole (fun v => if v = t then (1 : ℝ) else 0) (by simp; omega) hL
    a hpeak hp
  rw [← seqClusterMass_eq_seqMoment, ← seqClusterMass_eq_seqMoment] at h
  have e : (if L - 1 = t then (1 : ℝ) else 0) = if t = L - 1 then 1 else 0 :=
    if_congr eq_comm rfl rfl
  simp only at h
  rw [e] at h
  split_ifs at h ⊢ <;> linarith

/-! ### The class weights -/

/-- The weight of a cluster with pile mass `p` and cluster mass `m`: `B₁` for
a bare pile of three, `B₂` for a pile of two with one single, and zero for
every other cluster. -/
def massThreeWeight (B₁ B₂ : ℝ) (p : ℕ) (m : ℝ) : ℝ :=
  if m = 3 then (if p = 3 then B₁ else if p = 2 then B₂ else 0) else 0

theorem massThreeWeight_zero_mass (B₁ B₂ : ℝ) (p : ℕ) : massThreeWeight B₁ B₂ p 0 = 0 := by
  simp [massThreeWeight]

/-- The total class weight of the background clusters. -/
def seqMassThreePotential (B₁ B₂ : ℝ) (L : ℕ) (a : ℕ → ℕ) : ℝ :=
  ∑ t ∈ Finset.range L, if 1 ≤ t then massThreeWeight B₁ B₂ (a t) (seqClusterMass L a t) else 0

theorem seqClusterMass_eq_zero_of_lt {L : ℕ} (a : ℕ → ℕ) {t : ℕ} (ht : L ≤ t) :
    seqClusterMass L a t = 0 := by
  unfold seqClusterMass
  apply Finset.sum_eq_zero
  intro u hu
  rw [if_neg]
  have := seqAnchor_le a u
  have := Finset.mem_range.mp hu
  omega

/-- A whole move of a background pile changes only its own cluster and the
cluster it joins. -/
theorem seqMassThreePotential_pile_move (B₁ B₂ : ℝ) {L : ℕ} (a : ℕ → ℕ) {s : ℕ}
    (hs1 : 1 ≤ s) (hs : s + 1 < L) (hpile : 2 ≤ a s) :
    seqMassThreePotential B₁ B₂ L (seqMove a s (a s)) - seqMassThreePotential B₁ B₂ L a =
      massThreeWeight B₁ B₂ (a (s + 1) + a s) (seqClusterMass L a s + seqClusterMass L a (s + 1)) -
        massThreeWeight B₁ B₂ (a (s + 1)) (seqClusterMass L a (s + 1)) -
        massThreeWeight B₁ B₂ (a s) (seqClusterMass L a s) := by
  set b := seqMove a s (a s) with hb
  have hpoint (t : ℕ) :
      (if 1 ≤ t then massThreeWeight B₁ B₂ (b t) (seqClusterMass L b t) else 0) -
        (if 1 ≤ t then massThreeWeight B₁ B₂ (a t) (seqClusterMass L a t) else 0) =
      (if t = s + 1 then
        massThreeWeight B₁ B₂ (a (s + 1) + a s) (seqClusterMass L a s + seqClusterMass L a (s + 1)) -
          massThreeWeight B₁ B₂ (a (s + 1)) (seqClusterMass L a (s + 1)) else 0) -
      (if t = s then massThreeWeight B₁ B₂ (a s) (seqClusterMass L a s) else 0) := by
    rw [hb, seqClusterMass_pile_move a hs hpile t]
    by_cases hts : t = s
    · subst hts
      rw [if_pos hs1, if_pos hs1, if_neg (by omega), if_pos rfl, if_neg (by omega)]
      simp [seqMove, massThreeWeight_zero_mass]
    · by_cases hts1 : t = s + 1
      · subst hts1
        have hne : s + 1 ≠ s := by omega
        simp only [show 1 ≤ s + 1 by omega, if_true, if_neg hne, seqMove, sub_zero, mul_one]
        rw [add_comm (seqClusterMass L a (s + 1)) (seqClusterMass L a s)]
      · rw [if_neg hts1, if_neg hts, if_neg hts1, if_neg hts]
        simp only [seqMove, if_neg hts, if_neg hts1, sub_zero, mul_zero, add_zero, sub_self]
  unfold seqMassThreePotential
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun t _ => hpoint t),
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
    if_pos (Finset.mem_range.mpr hs), if_pos (Finset.mem_range.mpr (by omega))]

/-- A whole move of the peak absorbs the cluster at offset one and lowers every
other cluster by one offset. -/
theorem seqMassThreePotential_shift (B₁ B₂ : ℝ) {L : ℕ} (hL : 2 ≤ L) (a : ℕ → ℕ) :
    seqMassThreePotential B₁ B₂ L (seqShift L a) - seqMassThreePotential B₁ B₂ L a =
      -massThreeWeight B₁ B₂ (a 1) (seqClusterMass L a 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  let T (v : ℕ) : ℝ := if 2 ≤ v then massThreeWeight B₁ B₂ (a v) (seqClusterMass (n + 1) a v)
    else 0
  have hnew : seqMassThreePotential B₁ B₂ (n + 1) (seqShift (n + 1) a) =
      ∑ u ∈ Finset.range n, T (u + 1) := by
    unfold seqMassThreePotential
    rw [Finset.sum_range_succ]
    have hlast : (if 1 ≤ n then massThreeWeight B₁ B₂ (seqShift (n + 1) a n)
        (seqClusterMass (n + 1) (seqShift (n + 1) a) n) else 0) = 0 := by
      rw [if_pos (by omega), seqClusterMass_shift hL a (by omega),
        seqClusterMass_eq_zero_of_lt a (by omega), massThreeWeight_zero_mass]
    rw [hlast, add_zero]
    apply Finset.sum_congr rfl
    intro u hu
    have hu' := Finset.mem_range.mp hu
    by_cases hu0 : u = 0
    · subst hu0
      simp [T]
    · rw [if_pos (by omega), seqClusterMass_shift hL a (by omega)]
      simp [T, seqShift, hu0, show u + 1 < n + 1 by omega, show 2 ≤ u + 1 by omega]
  have hold : seqMassThreePotential B₁ B₂ (n + 1) a =
      massThreeWeight B₁ B₂ (a 1) (seqClusterMass (n + 1) a 1) + ∑ u ∈ Finset.range n, T (u + 1) := by
    unfold seqMassThreePotential
    rw [Finset.sum_range_succ']
    simp only [show ¬ 1 ≤ 0 by omega, if_false, add_zero]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [show 1 ≤ 0 + 1 by omega, if_true, T, show ¬ 2 ≤ 0 + 1 by omega, if_false,
      add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    rw [if_pos (by omega), if_pos (by omega)]
  rw [hnew, hold]
  ring

/-- A trivial chip only changes the pile mass of its source. -/
theorem seqMassThreePotential_trivial_chip (B₁ B₂ : ℝ) {L : ℕ} (a : ℕ → ℕ) {s : ℕ}
    (hs : s + 1 < L) (hone : 1 ≤ a s) (htwo : a s ≠ 2) (hempty : a (s + 1) = 0) :
    seqMassThreePotential B₁ B₂ L (seqMove a s 1) - seqMassThreePotential B₁ B₂ L a =
      if 1 ≤ s then massThreeWeight B₁ B₂ (a s - 1) (seqClusterMass L a s) -
        massThreeWeight B₁ B₂ (a s) (seqClusterMass L a s) else 0 := by
  have hm (t : ℕ) := seqClusterMass_trivial_chip a hs hone htwo hempty t
  have hnext : seqClusterMass L a (s + 1) = 0 :=
    seqClusterMass_eq_zero L a (by omega) (by omega)
  have hpoint (t : ℕ) :
      (if 1 ≤ t then massThreeWeight B₁ B₂ (seqMove a s 1 t) (seqClusterMass L (seqMove a s 1) t)
        else 0) - (if 1 ≤ t then massThreeWeight B₁ B₂ (a t) (seqClusterMass L a t) else 0) =
      if t = s then (if 1 ≤ s then massThreeWeight B₁ B₂ (a s - 1) (seqClusterMass L a s) -
        massThreeWeight B₁ B₂ (a s) (seqClusterMass L a s) else 0) else 0 := by
    rw [hm t]
    by_cases hts : t = s
    · subst hts
      simp only [seqMove, if_pos rfl, if_true]
      split_ifs <;> ring
    · rw [if_neg hts]
      by_cases hts1 : t = s + 1
      · subst hts1
        simp [seqMove, hnext, massThreeWeight_zero_mass]
      · simp [seqMove, hts, hts1]
  unfold seqMassThreePotential
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun t _ => hpoint t), Finset.sum_ite_eq',
    if_pos (Finset.mem_range.mpr (by omega))]

/-- A whole move of the pile behind the peak removes its cluster's weight. -/
theorem seqMassThreePotential_entry_whole (B₁ B₂ : ℝ) {L : ℕ} (hL : 2 ≤ L) (a : ℕ → ℕ)
    (hpeak : 2 ≤ a 0) (hp : 2 ≤ a (L - 1)) :
    seqMassThreePotential B₁ B₂ L (seqEntry L a (a (L - 1))) - seqMassThreePotential B₁ B₂ L a =
      -massThreeWeight B₁ B₂ (a (L - 1)) (seqClusterMass L a (L - 1)) := by
  have hpoint (t : ℕ) (ht : t ∈ Finset.range L) :
      (if 1 ≤ t then massThreeWeight B₁ B₂ (seqEntry L a (a (L - 1)) t)
          (seqClusterMass L (seqEntry L a (a (L - 1))) t) else 0) -
        (if 1 ≤ t then massThreeWeight B₁ B₂ (a t) (seqClusterMass L a t) else 0) =
      if t = L - 1 then -massThreeWeight B₁ B₂ (a (L - 1)) (seqClusterMass L a (L - 1)) else 0 := by
    by_cases ht1 : 1 ≤ t
    · rw [if_pos ht1, if_pos ht1, seqClusterMass_entry_whole hL a hpeak hp ht1]
      by_cases hl : t = L - 1
      · subst hl
        simp [seqEntry, show L - 1 ≠ 0 by omega, massThreeWeight_zero_mass]
      · rw [if_neg hl, if_neg hl, sub_zero]
        simp [seqEntry, show t ≠ 0 by omega, hl]
    · rw [if_neg ht1, if_neg ht1, if_neg (by omega), sub_zero]
  unfold seqMassThreePotential
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl hpoint, Finset.sum_ite_eq',
    if_pos (Finset.mem_range.mpr (by omega))]

/-! ### Cluster masses under general chips -/

/-- The cluster masses after any chip from index `s` to `s + 1`. The new pile
at `s + 1`, if the target was occupied, takes the chipped particle and the
forward part of the source's cluster from the source's anchor. A source pile
of two returns its remaining mass to the previous anchor. -/
theorem seqClusterMass_chip {L : ℕ} (a : ℕ → ℕ) {s : ℕ} (hs : s + 1 < L) (hone : 1 ≤ a s)
    (t : ℕ) :
    seqClusterMass L (seqMove a s 1) t = seqClusterMass L a t +
      (if 1 ≤ a (s + 1) then ((if t = s + 1 then 1 else 0) - (if t = seqAnchor a s then 1 else 0)) *
        (1 + seqForwardMass L a s) else 0) +
      (if a s = 2 then ((if t = seqAnchor a (s - 1) then 1 else 0) - (if t = s then 1 else 0)) *
        (if a (s + 1) = 0 then 2 + seqForwardMass L a s else 1) else 0) := by
  have h := seqMoment_chip (fun v => if v = t then (1 : ℝ) else 0) a hs hone
  beta_reduce at h
  rw [← seqClusterMass_eq_seqMoment, ← seqClusterMass_eq_seqMoment] at h
  have e₁ : (if s + 1 = t then (1 : ℝ) else 0) = if t = s + 1 then 1 else 0 :=
    if_congr eq_comm rfl rfl
  have e₂ : (if seqAnchor a s = t then (1 : ℝ) else 0) = if t = seqAnchor a s then 1 else 0 :=
    if_congr eq_comm rfl rfl
  have e₃ : (if seqAnchor a (s - 1) = t then (1 : ℝ) else 0) =
      if t = seqAnchor a (s - 1) then 1 else 0 := if_congr eq_comm rfl rfl
  have e₄ : (if s = t then (1 : ℝ) else 0) = if t = s then 1 else 0 := if_congr eq_comm rfl rfl
  rw [e₁, e₂, e₃, e₄] at h
  linarith

/-- The cluster of a pile is the pile and the forward mass it sweeps. -/
theorem seqClusterMass_pile {L : ℕ} (a : ℕ → ℕ) {s : ℕ} (hsL : s < L) (hpile : 2 ≤ a s) :
    seqClusterMass L a s = (a s : ℝ) + seqForwardMass L a s := by
  have hself : seqAnchor a s = s := seqAnchor_of_pile a hpile
  unfold seqClusterMass seqForwardMass
  rw [hself]
  have hpt (u : ℕ) (_ : u ∈ Finset.range L) : (if seqAnchor a u = s then (a u : ℝ) else 0) =
      (if u = s then (a s : ℝ) else 0) +
        (if s + 1 ≤ u ∧ seqAnchor a u = s then (a u : ℝ) else 0) := by
    by_cases hus : u = s
    · subst hus
      simp [hself]
    · by_cases hlt : u < s
      · have := seqAnchor_le a u
        simp [show seqAnchor a u ≠ s by omega, hus, show ¬ s + 1 ≤ u by omega]
      · simp [hus, show s + 1 ≤ u by omega]
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_range.mpr hsL)]

theorem seqClusterMass_nonpile {L : ℕ} (a : ℕ → ℕ) {s : ℕ} (hs : 1 ≤ s) (hp : a s < 2) :
    seqClusterMass L a s = 0 :=
  seqClusterMass_eq_zero L a (by omega) hp

theorem massThreeWeight_nonneg {B₁ B₂ : ℝ} (h₁ : 0 ≤ B₁) (h₂ : 0 ≤ B₂) (p : ℕ) (m : ℝ) :
    0 ≤ massThreeWeight B₁ B₂ p m := by
  unfold massThreeWeight
  split_ifs <;> linarith

/-- If two sequences have the same masses and cluster masses outside a finite
set of indices, their class weights differ by the changes on that set. -/
theorem seqMassThreePotential_sub_of_agree (B₁ B₂ : ℝ) {L : ℕ} (a b : ℕ → ℕ)
    (T : Finset ℕ) (hT : T ⊆ Finset.range L)
    (hagree : ∀ t ∈ Finset.range L, t ∉ T →
      b t = a t ∧ seqClusterMass L b t = seqClusterMass L a t) :
    seqMassThreePotential B₁ B₂ L b - seqMassThreePotential B₁ B₂ L a =
      ∑ t ∈ T, (if 1 ≤ t then massThreeWeight B₁ B₂ (b t) (seqClusterMass L b t) -
        massThreeWeight B₁ B₂ (a t) (seqClusterMass L a t) else 0) := by
  unfold seqMassThreePotential
  rw [← Finset.sum_sub_distrib]
  have hpt : ∀ t ∈ Finset.range L,
      ((if 1 ≤ t then massThreeWeight B₁ B₂ (b t) (seqClusterMass L b t) else 0) -
        (if 1 ≤ t then massThreeWeight B₁ B₂ (a t) (seqClusterMass L a t) else 0)) =
      (if 1 ≤ t then massThreeWeight B₁ B₂ (b t) (seqClusterMass L b t) -
        massThreeWeight B₁ B₂ (a t) (seqClusterMass L a t) else 0) := by
    intro t _
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hpt]
  symm
  apply Finset.sum_subset hT
  intro t ht htT
  obtain ⟨h₁, h₂⟩ := hagree t ht htT
  rw [h₁, h₂]
  split_ifs <;> ring

/-- A pile of two with an empty site ahead dissolves: its whole cluster
returns to the previous anchor. -/
theorem seqMassThreePotential_dissolve (B₁ B₂ : ℝ) {L : ℕ} (a : ℕ → ℕ) {s : ℕ}
    (hs1 : 1 ≤ s) (hs : s + 1 < L) (htwo : a s = 2) (hempty : a (s + 1) = 0) :
    seqMassThreePotential B₁ B₂ L (seqMove a s 1) - seqMassThreePotential B₁ B₂ L a =
      -massThreeWeight B₁ B₂ 2 (seqClusterMass L a s) +
        (if 1 ≤ seqAnchor a (s - 1) then
          massThreeWeight B₁ B₂ (a (seqAnchor a (s - 1)))
              (seqClusterMass L a (seqAnchor a (s - 1)) + seqClusterMass L a s) -
            massThreeWeight B₁ B₂ (a (seqAnchor a (s - 1)))
              (seqClusterMass L a (seqAnchor a (s - 1))) else 0) := by
  set A' := seqAnchor a (s - 1) with hA'
  set b := seqMove a s 1 with hb
  have hA'lt : A' < s := by have := seqAnchor_le a (s - 1); omega
  have hms : seqClusterMass L a s = 2 + seqForwardMass L a s := by
    rw [seqClusterMass_pile a (by omega) (by omega), htwo]
    norm_num
  have hm (t : ℕ) : seqClusterMass L b t = seqClusterMass L a t +
      ((if t = A' then 1 else 0) - (if t = s then 1 else 0)) * seqClusterMass L a s := by
    rw [hb, seqClusterMass_chip a hs (by omega) t, if_neg (show ¬ 1 ≤ a (s + 1) by omega),
      if_pos htwo, if_pos hempty, hms]
    ring
  have hzero1 : seqClusterMass L a (s + 1) = 0 := seqClusterMass_nonpile a (by omega) (by omega)
  rw [seqMassThreePotential_sub_of_agree B₁ B₂ a b {A', s, s + 1}
    (by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> exact Finset.mem_range.mpr (by omega))
    (by
      intro t _ ht
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
      refine ⟨by simp [hb, seqMove, ht.2.1, ht.2.2], ?_⟩
      rw [hm t, if_neg ht.1, if_neg ht.2.1]
      ring)]
  rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), Finset.sum_singleton]
  have hbs : b s = 1 := by simp [hb, seqMove, htwo]
  have hbs1 : b (s + 1) = 1 := by simp [hb, seqMove, hempty]
  have hbA : b A' = a A' := by simp [hb, seqMove, show A' ≠ s by omega, show A' ≠ s + 1 by omega]
  have hmbs : seqClusterMass L b s = 0 := by
    rw [hm s, if_neg (by omega), if_pos rfl]
    ring
  have hmbs1 : seqClusterMass L b (s + 1) = 0 := by
    rw [hm (s + 1), if_neg (by omega), if_neg (by omega), hzero1]
    ring
  have hmbA : seqClusterMass L b A' = seqClusterMass L a A' + seqClusterMass L a s := by
    rw [hm A', if_pos rfl, if_neg (by omega)]
    ring
  rw [if_pos hs1, if_pos (by omega : 1 ≤ s + 1), hbs, hbs1, hmbs, hmbs1, hzero1, htwo]
  simp only [massThreeWeight_zero_mass]
  by_cases h1 : 1 ≤ A'
  · rw [if_pos h1, if_pos h1, hbA, hmbA]
    ring
  · rw [if_neg h1, if_neg h1]
    ring

/-- Dissolving a cluster never adds class weight. -/
theorem seqMassThreePotential_dissolve_le {B₁ B₂ : ℝ} (h₁ : 0 ≤ B₁) (h₂ : 0 ≤ B₂)
    {L : ℕ} (a : ℕ → ℕ) {s : ℕ} (hs1 : 1 ≤ s) (hs : s + 1 < L) (htwo : a s = 2)
    (hempty : a (s + 1) = 0) :
    seqMassThreePotential B₁ B₂ L (seqMove a s 1) - seqMassThreePotential B₁ B₂ L a ≤
      -massThreeWeight B₁ B₂ 2 (seqClusterMass L a s) := by
  rw [seqMassThreePotential_dissolve B₁ B₂ a hs1 hs htwo hempty]
  split_ifs with h1
  · have hpile : 2 ≤ a (seqAnchor a (s - 1)) :=
      ((seqAnchor_eq_iff a (s - 1) _).mp rfl).2.1 (by omega)
    have hA'L : seqAnchor a (s - 1) < L := by have := seqAnchor_le a (s - 1); omega
    have hmA : (2 : ℝ) ≤ seqClusterMass L a (seqAnchor a (s - 1)) := by
      rw [seqClusterMass_pile a hA'L hpile]
      have := seqForwardMass_nonneg L a (seqAnchor a (s - 1))
      have : (2 : ℝ) ≤ (a (seqAnchor a (s - 1)) : ℝ) := by exact_mod_cast hpile
      linarith
    have hms : (2 : ℝ) ≤ seqClusterMass L a s := by
      rw [seqClusterMass_pile a (by omega) (by omega), htwo]
      have := seqForwardMass_nonneg L a s
      push_cast
      linarith
    have hbig : massThreeWeight B₁ B₂ (a (seqAnchor a (s - 1)))
        (seqClusterMass L a (seqAnchor a (s - 1)) + seqClusterMass L a s) = 0 := by
      unfold massThreeWeight
      rw [if_neg (by linarith)]
    rw [hbig]
    have := massThreeWeight_nonneg h₁ h₂ (a (seqAnchor a (s - 1)))
      (seqClusterMass L a (seqAnchor a (s - 1)))
    linarith
  · linarith

/-- A pile of two chips onto the single just ahead: the pile moves forward
with the rest of its cluster and sheds one single to the previous anchor. -/
theorem seqMassThreePotential_shed (B₁ B₂ : ℝ) {L : ℕ} (a : ℕ → ℕ) {s : ℕ}
    (hs1 : 1 ≤ s) (hs : s + 1 < L) (htwo : a s = 2) (hsingle : a (s + 1) = 1) :
    seqMassThreePotential B₁ B₂ L (seqMove a s 1) - seqMassThreePotential B₁ B₂ L a =
      massThreeWeight B₁ B₂ 2 (seqClusterMass L a s - 1) -
        massThreeWeight B₁ B₂ 2 (seqClusterMass L a s) +
        (if 1 ≤ seqAnchor a (s - 1) then
          massThreeWeight B₁ B₂ (a (seqAnchor a (s - 1)))
              (seqClusterMass L a (seqAnchor a (s - 1)) + 1) -
            massThreeWeight B₁ B₂ (a (seqAnchor a (s - 1)))
              (seqClusterMass L a (seqAnchor a (s - 1))) else 0) := by
  set A' := seqAnchor a (s - 1) with hA'
  set b := seqMove a s 1 with hb
  have hA'lt : A' < s := by have := seqAnchor_le a (s - 1); omega
  have hself : seqAnchor a s = s := seqAnchor_of_pile a (by omega)
  have hms : seqClusterMass L a s = 2 + seqForwardMass L a s := by
    rw [seqClusterMass_pile a (by omega) (by omega), htwo]
    norm_num
  have hm (t : ℕ) : seqClusterMass L b t = seqClusterMass L a t +
      ((if t = s + 1 then 1 else 0) - (if t = s then 1 else 0)) * (seqClusterMass L a s - 1) +
      ((if t = A' then 1 else 0) - (if t = s then 1 else 0)) := by
    rw [hb, seqClusterMass_chip a hs (by omega) t, if_pos (show 1 ≤ a (s + 1) by omega),
      if_pos htwo, if_neg (show a (s + 1) ≠ 0 by omega), hself, hms]
    ring
  have hzero1 : seqClusterMass L a (s + 1) = 0 := seqClusterMass_nonpile a (by omega) (by omega)
  rw [seqMassThreePotential_sub_of_agree B₁ B₂ a b {A', s, s + 1}
    (by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> exact Finset.mem_range.mpr (by omega))
    (by
      intro t _ ht
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
      refine ⟨by simp [hb, seqMove, ht.2.1, ht.2.2], ?_⟩
      rw [hm t, if_neg ht.2.2, if_neg ht.2.1, if_neg ht.1]
      ring)]
  rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), Finset.sum_singleton]
  have hbs : b s = 1 := by simp [hb, seqMove, htwo]
  have hbs1 : b (s + 1) = 2 := by simp [hb, seqMove, hsingle]
  have hbA : b A' = a A' := by simp [hb, seqMove, show A' ≠ s by omega, show A' ≠ s + 1 by omega]
  have hmbs : seqClusterMass L b s = 0 := by
    rw [hm s, if_neg (by omega), if_pos rfl, if_neg (by omega), hms]
    ring
  have hmbs1 : seqClusterMass L b (s + 1) = seqClusterMass L a s - 1 := by
    rw [hm (s + 1), if_pos rfl, if_neg (by omega), if_neg (by omega), hzero1]
    ring
  have hmbA : seqClusterMass L b A' = seqClusterMass L a A' + 1 := by
    rw [hm A', if_neg (by omega), if_neg (by omega), if_pos rfl]
    ring
  rw [if_pos hs1, if_pos (by omega : 1 ≤ s + 1), hbs, hbs1, hmbs, hmbs1, hzero1, htwo]
  simp only [massThreeWeight_zero_mass]
  by_cases h1 : 1 ≤ A'
  · rw [if_pos h1, if_pos h1, hbA, hmbA]
    ring
  · rw [if_neg h1, if_neg h1]
    ring

/-- A pile of at least three chips onto the pile just ahead: one particle
passes from its cluster to the next. -/
theorem seqMassThreePotential_pile_onto_pile (B₁ B₂ : ℝ) {L : ℕ} (a : ℕ → ℕ) {s : ℕ}
    (hs1 : 1 ≤ s) (hs : s + 1 < L) (hbig : 3 ≤ a s) (hnext : 2 ≤ a (s + 1)) :
    seqMassThreePotential B₁ B₂ L (seqMove a s 1) - seqMassThreePotential B₁ B₂ L a =
      (massThreeWeight B₁ B₂ (a s - 1) (seqClusterMass L a s - 1) -
        massThreeWeight B₁ B₂ (a s) (seqClusterMass L a s)) +
      (massThreeWeight B₁ B₂ (a (s + 1) + 1) (seqClusterMass L a (s + 1) + 1) -
        massThreeWeight B₁ B₂ (a (s + 1)) (seqClusterMass L a (s + 1))) := by
  set b := seqMove a s 1 with hb
  have hself : seqAnchor a s = s := seqAnchor_of_pile a (by omega)
  have hF : seqForwardMass L a s = 0 := by
    unfold seqForwardMass
    apply Finset.sum_eq_zero
    intro u _
    rw [if_neg]
    rintro ⟨hu, hA⟩
    have := le_seqAnchor a hu hnext
    rw [hself] at hA
    omega
  have hm (t : ℕ) : seqClusterMass L b t = seqClusterMass L a t +
      ((if t = s + 1 then 1 else 0) - (if t = s then 1 else 0)) := by
    rw [hb, seqClusterMass_chip a hs (by omega) t, if_pos (show 1 ≤ a (s + 1) by omega),
      if_neg (show a s ≠ 2 by omega), hself, hF]
    ring
  rw [seqMassThreePotential_sub_of_agree B₁ B₂ a b {s, s + 1}
    (by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> exact Finset.mem_range.mpr (by omega))
    (by
      intro t _ ht
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
      refine ⟨by simp [hb, seqMove, ht.1, ht.2], ?_⟩
      rw [hm t, if_neg ht.2, if_neg ht.1]
      ring)]
  rw [Finset.sum_insert (by simp), Finset.sum_singleton]
  have hbs : b s = a s - 1 := by simp [hb, seqMove]
  have hbs1 : b (s + 1) = a (s + 1) + 1 := by simp [hb, seqMove]
  have hmbs : seqClusterMass L b s = seqClusterMass L a s - 1 := by
    rw [hm s, if_neg (by omega), if_pos rfl]
    ring
  have hmbs1 : seqClusterMass L b (s + 1) = seqClusterMass L a (s + 1) + 1 := by
    rw [hm (s + 1), if_pos rfl, if_neg (by omega)]
    ring
  rw [if_pos hs1, if_pos (by omega : 1 ≤ s + 1), hbs, hbs1, hmbs, hmbs1]

/-- A pile of at least three chips onto the single just ahead: the single
becomes a pile of two that takes the forward part of the cluster. -/
theorem seqMassThreePotential_pile_onto_single (B₁ B₂ : ℝ) {L : ℕ} (a : ℕ → ℕ) {s : ℕ}
    (hs1 : 1 ≤ s) (hs : s + 1 < L) (hbig : 3 ≤ a s) (hsingle : a (s + 1) = 1) :
    seqMassThreePotential B₁ B₂ L (seqMove a s 1) - seqMassThreePotential B₁ B₂ L a =
      (massThreeWeight B₁ B₂ (a s - 1) ((a s : ℝ) - 1) -
        massThreeWeight B₁ B₂ (a s) (seqClusterMass L a s)) +
      massThreeWeight B₁ B₂ 2 (1 + seqForwardMass L a s) := by
  set b := seqMove a s 1 with hb
  have hself : seqAnchor a s = s := seqAnchor_of_pile a (by omega)
  have hms : seqClusterMass L a s = (a s : ℝ) + seqForwardMass L a s :=
    seqClusterMass_pile a (by omega) (by omega)
  have hm (t : ℕ) : seqClusterMass L b t = seqClusterMass L a t +
      ((if t = s + 1 then 1 else 0) - (if t = s then 1 else 0)) * (1 + seqForwardMass L a s) := by
    rw [hb, seqClusterMass_chip a hs (by omega) t, if_pos (show 1 ≤ a (s + 1) by omega),
      if_neg (show a s ≠ 2 by omega), hself]
    ring
  have hzero1 : seqClusterMass L a (s + 1) = 0 := seqClusterMass_nonpile a (by omega) (by omega)
  rw [seqMassThreePotential_sub_of_agree B₁ B₂ a b {s, s + 1}
    (by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> exact Finset.mem_range.mpr (by omega))
    (by
      intro t _ ht
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
      refine ⟨by simp [hb, seqMove, ht.1, ht.2], ?_⟩
      rw [hm t, if_neg ht.2, if_neg ht.1]
      ring)]
  rw [Finset.sum_insert (by simp), Finset.sum_singleton]
  have hbs : b s = a s - 1 := by simp [hb, seqMove]
  have hbs1 : b (s + 1) = 2 := by simp [hb, seqMove, hsingle]
  have hmbs : seqClusterMass L b s = (a s : ℝ) - 1 := by
    rw [hm s, if_neg (by omega), if_pos rfl, hms]
    ring
  have hmbs1 : seqClusterMass L b (s + 1) = 1 + seqForwardMass L a s := by
    rw [hm (s + 1), if_pos rfl, if_neg (by omega), hzero1]
    ring
  rw [if_pos hs1, if_pos (by omega : 1 ≤ s + 1), hbs, hbs1, hmbs, hmbs1, hzero1, hsingle,
    massThreeWeight_zero_mass]
  ring

/-- A single chips onto the pile just ahead: one particle passes from the
single's cluster to the next. -/
theorem seqMassThreePotential_single_onto_pile (B₁ B₂ : ℝ) {L : ℕ} (a : ℕ → ℕ) {s : ℕ}
    (hs1 : 1 ≤ s) (hs : s + 1 < L) (hone : a s = 1) (hnext : 2 ≤ a (s + 1)) :
    seqMassThreePotential B₁ B₂ L (seqMove a s 1) - seqMassThreePotential B₁ B₂ L a =
      (if 1 ≤ seqAnchor a s then
        massThreeWeight B₁ B₂ (a (seqAnchor a s)) (seqClusterMass L a (seqAnchor a s) - 1) -
          massThreeWeight B₁ B₂ (a (seqAnchor a s)) (seqClusterMass L a (seqAnchor a s)) else 0) +
      (massThreeWeight B₁ B₂ (a (s + 1) + 1) (seqClusterMass L a (s + 1) + 1) -
        massThreeWeight B₁ B₂ (a (s + 1)) (seqClusterMass L a (s + 1))) := by
  set A := seqAnchor a s with hA
  set b := seqMove a s 1 with hb
  have hAlt : A < s := by
    have h₁ := seqAnchor_le a s
    have h₂ : A ≠ s := by
      intro h
      have := ((seqAnchor_eq_iff a s A).mp rfl).2.1 (by omega)
      rw [h] at this
      omega
    omega
  have hF : seqForwardMass L a s = 0 := by
    unfold seqForwardMass
    apply Finset.sum_eq_zero
    intro u _
    rw [if_neg]
    rintro ⟨hu, hAu⟩
    have := le_seqAnchor a hu hnext
    rw [← hA] at hAu
    omega
  have hm (t : ℕ) : seqClusterMass L b t = seqClusterMass L a t +
      ((if t = s + 1 then 1 else 0) - (if t = A then 1 else 0)) := by
    rw [hb, seqClusterMass_chip a hs (by omega) t, if_pos (show 1 ≤ a (s + 1) by omega),
      if_neg (show a s ≠ 2 by omega), ← hA, hF]
    ring
  have hzero : seqClusterMass L a s = 0 := seqClusterMass_nonpile a hs1 (by omega)
  rw [seqMassThreePotential_sub_of_agree B₁ B₂ a b {A, s, s + 1}
    (by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> exact Finset.mem_range.mpr (by omega))
    (by
      intro t _ ht
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
      refine ⟨by simp [hb, seqMove, ht.2.1, ht.2.2], ?_⟩
      rw [hm t, if_neg ht.2.2, if_neg ht.1]
      ring)]
  rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), Finset.sum_singleton]
  have hbs : b s = 0 := by simp [hb, seqMove, hone]
  have hbs1 : b (s + 1) = a (s + 1) + 1 := by simp [hb, seqMove]
  have hbA : b A = a A := by simp [hb, seqMove, show A ≠ s by omega, show A ≠ s + 1 by omega]
  have hmbs : seqClusterMass L b s = 0 := by
    rw [hm s, if_neg (by omega), if_neg (by omega), hzero]
    ring
  have hmbs1 : seqClusterMass L b (s + 1) = seqClusterMass L a (s + 1) + 1 := by
    rw [hm (s + 1), if_pos rfl, if_neg (by omega)]
    ring
  have hmbA : seqClusterMass L b A = seqClusterMass L a A - 1 := by
    rw [hm A, if_neg (by omega), if_pos rfl]
    ring
  rw [if_pos hs1, if_pos (by omega : 1 ≤ s + 1), hbs, hbs1, hmbs, hmbs1, hzero, hone]
  simp only [massThreeWeight_zero_mass]
  by_cases h1 : 1 ≤ A
  · rw [if_pos h1, if_pos h1, hbA, hmbA]
    ring
  · rw [if_neg h1, if_neg h1]
    ring

/-- A single chips onto the single just ahead: a new pile of two forms, taking
the forward part of the single's cluster. -/
theorem seqMassThreePotential_single_onto_single (B₁ B₂ : ℝ) {L : ℕ} (a : ℕ → ℕ) {s : ℕ}
    (hs1 : 1 ≤ s) (hs : s + 1 < L) (hone : a s = 1) (hsingle : a (s + 1) = 1) :
    seqMassThreePotential B₁ B₂ L (seqMove a s 1) - seqMassThreePotential B₁ B₂ L a =
      (if 1 ≤ seqAnchor a s then
        massThreeWeight B₁ B₂ (a (seqAnchor a s))
            (seqClusterMass L a (seqAnchor a s) - (1 + seqForwardMass L a s)) -
          massThreeWeight B₁ B₂ (a (seqAnchor a s)) (seqClusterMass L a (seqAnchor a s)) else 0) +
      massThreeWeight B₁ B₂ 2 (1 + seqForwardMass L a s) := by
  set A := seqAnchor a s with hA
  set b := seqMove a s 1 with hb
  have hAlt : A < s := by
    have h₁ := seqAnchor_le a s
    have h₂ : A ≠ s := by
      intro h
      have := ((seqAnchor_eq_iff a s A).mp rfl).2.1 (by omega)
      rw [h] at this
      omega
    omega
  have hm (t : ℕ) : seqClusterMass L b t = seqClusterMass L a t +
      ((if t = s + 1 then 1 else 0) - (if t = A then 1 else 0)) * (1 + seqForwardMass L a s) := by
    rw [hb, seqClusterMass_chip a hs (by omega) t, if_pos (show 1 ≤ a (s + 1) by omega),
      if_neg (show a s ≠ 2 by omega), ← hA]
    ring
  have hzero : seqClusterMass L a s = 0 := seqClusterMass_nonpile a hs1 (by omega)
  have hzero1 : seqClusterMass L a (s + 1) = 0 := seqClusterMass_nonpile a (by omega) (by omega)
  rw [seqMassThreePotential_sub_of_agree B₁ B₂ a b {A, s, s + 1}
    (by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> exact Finset.mem_range.mpr (by omega))
    (by
      intro t _ ht
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
      refine ⟨by simp [hb, seqMove, ht.2.1, ht.2.2], ?_⟩
      rw [hm t, if_neg ht.2.2, if_neg ht.1]
      ring)]
  rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), Finset.sum_singleton]
  have hbs : b s = 0 := by simp [hb, seqMove, hone]
  have hbs1 : b (s + 1) = 2 := by simp [hb, seqMove, hsingle]
  have hbA : b A = a A := by simp [hb, seqMove, show A ≠ s by omega, show A ≠ s + 1 by omega]
  have hmbs : seqClusterMass L b s = 0 := by
    rw [hm s, if_neg (by omega), if_neg (by omega), hzero]
    ring
  have hmbs1 : seqClusterMass L b (s + 1) = 1 + seqForwardMass L a s := by
    rw [hm (s + 1), if_pos rfl, if_neg (by omega), hzero1]
    ring
  have hmbA : seqClusterMass L b A = seqClusterMass L a A - (1 + seqForwardMass L a s) := by
    rw [hm A, if_neg (by omega), if_pos rfl]
    ring
  rw [if_pos hs1, if_pos (by omega : 1 ≤ s + 1), hbs, hbs1, hmbs, hmbs1, hzero, hzero1, hone,
    hsingle]
  simp only [massThreeWeight_zero_mass]
  by_cases h1 : 1 ≤ A
  · rw [if_pos h1, if_pos h1, hbA, hmbA]
    ring
  · rw [if_neg h1, if_neg h1]
    ring

/-! ### On the ring -/

theorem seqMassThreePotential_congr (B₁ B₂ : ℝ) {L : ℕ} {a b : ℕ → ℕ}
    (hab : ∀ u < L, a u = b u) :
    seqMassThreePotential B₁ B₂ L a = seqMassThreePotential B₁ B₂ L b := by
  unfold seqMassThreePotential
  apply Finset.sum_congr rfl
  intro t ht
  rw [hab t (Finset.mem_range.mp ht), seqClusterMass_congr hab t]

/-- The total class weight of the background clusters in the frame of the peak. -/
def massThreePotential {L N : ℕ} [NeZero L] (B₁ B₂ : ℝ) (x : State L N) : ℝ :=
  seqMassThreePotential B₁ B₂ L (frameMass x)

/-- The change of the class weights when one particle chips from site `i`. -/
def massThreeChipChange {L N : ℕ} [NeZero L] (B₁ B₂ : ℝ) (x : State L N) (i : Fin L) : ℝ :=
  if hi : 1 ≤ occ x i then massThreePotential B₁ B₂ (move x i 1 hi) - massThreePotential B₁ B₂ x
  else 0

/-- The class-weight change of the whole move of a background pile. -/
def massThreeWholeChange {L N : ℕ} [NeZero L] (B₁ B₂ : ℝ) (x : State L N) (s : ℕ) : ℝ :=
  if s + 1 < L then
    massThreeWeight B₁ B₂ (frameMass x (s + 1) + frameMass x s)
        (frameClusterMass x s + frameClusterMass x (s + 1)) -
      massThreeWeight B₁ B₂ (frameMass x (s + 1)) (frameClusterMass x (s + 1)) -
      massThreeWeight B₁ B₂ (frameMass x s) (frameClusterMass x s)
  else -massThreeWeight B₁ B₂ (frameMass x s) (frameClusterMass x s)

private theorem atSite_massThreePotential {L N : ℕ} [NeZero L] (w B₁ B₂ : ℝ)
    (x : State L N) (i : Fin L) :
    atSite w (massThreePotential B₁ B₂) x i = w * massThreeChipChange B₁ B₂ x i +
      (if 2 ≤ occ x i then massThreePotential B₁ B₂ (move x i (occ x i) le_rfl) -
        massThreePotential B₁ B₂ x else 0) := by
  unfold atSite massThreeChipChange
  split_ifs <;> ring

private theorem massThree_whole_background {L N : ℕ} [NeZero L] (hL : 3 ≤ L) (B₁ B₂ : ℝ)
    (x : State L N) (hmargin : N + 2 < 2 * largest x) {s : ℕ}
    (hs1 : 1 ≤ s) (hsL : s < L) (hpile : 2 ≤ frameMass x s) :
    massThreePotential B₁ B₂
        (move x (peakSite x + (s : Fin L)) (occ x (peakSite x + (s : Fin L))) le_rfl) -
      massThreePotential B₁ B₂ x = massThreeWholeChange B₁ B₂ x s := by
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
  unfold massThreeWholeChange
  by_cases hlast : s + 1 < L
  · have hrear : peakSite x + (s : Fin L) ≠ peakSite x - 1 := by
      intro he
      have := congrArg (peakOffset x) he
      rw [hoff, peakOffset_peakSite_sub_one hL] at this
      omega
    have hcongr := seqMassThreePotential_congr B₁ B₂
      (frameMass_move_of_peak_eq x _ _ le_rfl hpeak hrear)
    rw [if_pos hlast]
    unfold massThreePotential frameClusterMass
    rw [hcongr, hoff]
    exact seqMassThreePotential_pile_move B₁ B₂ (frameMass x) hs1 hlast hpile
  · have hsL' : s = L - 1 := by omega
    have hrear : peakSite x + (s : Fin L) = peakSite x - 1 :=
      (peak_add_eq_iff x hsL _).mpr (by rw [peakOffset_peakSite_sub_one hL]; exact hsL')
    rw [if_neg hlast]
    revert hpeak
    rw [hrear]
    intro hpeak
    have hcongr := seqMassThreePotential_congr B₁ B₂ (frameMass_move_rear hL x _ le_rfl hpeak)
    have hocc : occ x (peakSite x - 1) = frameMass x (L - 1) := by
      unfold frameMass
      rw [← hsL', hrear]
    unfold massThreePotential frameClusterMass
    rw [hcongr, hocc, hsL']
    rw [hsL'] at hpile
    exact seqMassThreePotential_entry_whole B₁ B₂ (by omega) (frameMass x) ha0 hpile

/-- The exact drift of the class weights while the peak holds a majority that
survives a single chip. Whole moves are explicit; chips enter through
`massThreeChipChange`. -/
theorem generator_massThreePotential_eq {L N : ℕ} [NeZero L] (hL : 3 ≤ L) (w B₁ B₂ : ℝ)
    (x : State L N) (hmargin : N + 2 < 2 * largest x) :
    generator w (massThreePotential B₁ B₂) x =
      (∑ s ∈ Finset.range L, if 1 ≤ s ∧ 2 ≤ frameMass x s then
          massThreeWholeChange B₁ B₂ x s else 0) -
        massThreeWeight B₁ B₂ (frameMass x 1) (frameClusterMass x 1) +
        w * ∑ i, massThreeChipChange B₁ B₂ x i := by
  let W (s : ℕ) : ℝ := if 2 ≤ frameMass x s then
      massThreePotential B₁ B₂ (move x (peakSite x + (s : Fin L))
        (occ x (peakSite x + (s : Fin L))) le_rfl) - massThreePotential B₁ B₂ x
    else 0
  have hgen : generator w (massThreePotential B₁ B₂) x =
      w * (∑ i, massThreeChipChange B₁ B₂ x i) + ∑ s ∈ Finset.range L, W s := by
    unfold generator
    simp_rw [atSite_massThreePotential]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_sites_eq_sum_offsets (peakSite x)
        (fun i => if 2 ≤ occ x i then
          massThreePotential B₁ B₂ (move x i (occ x i) le_rfl) - massThreePotential B₁ B₂ x
          else 0)]
    rfl
  have ha0 : 2 ≤ frameMass x 0 := by rw [frameMass_zero]; omega
  have hW0 : W 0 = -massThreeWeight B₁ B₂ (frameMass x 1) (frameClusterMass x 1) := by
    have hp0 : peakSite x + ((0 : ℕ) : Fin L) = peakSite x := by simp
    simp only [W, if_pos ha0]
    rw [show (move x (peakSite x + ((0 : ℕ) : Fin L)) (occ x (peakSite x + ((0 : ℕ) : Fin L)))
        le_rfl) = move x (peakSite x) (occ x (peakSite x)) le_rfl by rw [hp0]]
    have hcongr := seqMassThreePotential_congr B₁ B₂ (frameMass_whole_peak hL x (by omega))
    unfold massThreePotential frameClusterMass
    rw [hcongr]
    exact seqMassThreePotential_shift B₁ B₂ (by omega) (frameMass x)
  have hWs (s : ℕ) (hs : s ∈ Finset.range L) (hs0 : s ≠ 0) :
      W s = if 1 ≤ s ∧ 2 ≤ frameMass x s then massThreeWholeChange B₁ B₂ x s else 0 := by
    simp only [W]
    by_cases hp : 2 ≤ frameMass x s
    · rw [if_pos hp, if_pos ⟨by omega, hp⟩]
      exact massThree_whole_background hL B₁ B₂ x hmargin (by omega) (Finset.mem_range.mp hs) hp
    · rw [if_neg hp, if_neg (fun h => hp h.2)]
  rw [hgen]
  have hsum : (∑ s ∈ Finset.range L, W s) = W 0 + ∑ s ∈ Finset.range L,
      (if 1 ≤ s ∧ 2 ≤ frameMass x s then massThreeWholeChange B₁ B₂ x s else 0) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (NeZero.pos L)),
      ← Finset.add_sum_erase (Finset.range L)
        (fun s => if 1 ≤ s ∧ 2 ≤ frameMass x s then massThreeWholeChange B₁ B₂ x s else 0)
        (Finset.mem_range.mpr (NeZero.pos L)),
      if_neg (show ¬(1 ≤ 0 ∧ 2 ≤ frameMass x 0) by omega), zero_add]
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    exact hWs s (Finset.mem_of_mem_erase hs) (Finset.ne_of_mem_erase hs)
  rw [hsum, hW0]
  ring

/-- A trivial chip changes the class weights only by turning a bare pile of
three into a pile of two with one single. -/
theorem massThreeChipChange_trivial {L N : ℕ} [NeZero L] (hL : 3 ≤ L) (B₁ B₂ : ℝ)
    (x : State L N)
    (hmargin : N + 2 < 2 * largest x) {s : ℕ} (hs : s + 1 < L) (hone : 1 ≤ frameMass x s)
    (htwo : frameMass x s ≠ 2) (hempty : frameMass x (s + 1) = 0) :
    massThreeChipChange B₁ B₂ x (peakSite x + (s : Fin L)) =
      if 1 ≤ s then massThreeWeight B₁ B₂ (frameMass x s - 1) (frameClusterMass x s) -
        massThreeWeight B₁ B₂ (frameMass x s) (frameClusterMass x s) else 0 := by
  have hsL : s < L := by omega
  have hoff : peakOffset x (peakSite x + (s : Fin L)) = s :=
    ((peak_add_eq_iff x hsL _).mp rfl).symm
  have hocc : occ x (peakSite x + (s : Fin L)) = frameMass x s := rfl
  have hrear : peakSite x + (s : Fin L) ≠ peakSite x - 1 := by
    intro he
    have := congrArg (peakOffset x) he
    rw [hoff, peakOffset_peakSite_sub_one hL] at this
    omega
  unfold massThreeChipChange
  rw [dif_pos (by rw [hocc]; exact hone)]
  have hpeak := peakSite_chip_move x hmargin (peakSite x + (s : Fin L)) (by rw [hocc]; exact hone)
  have hcongr := seqMassThreePotential_congr B₁ B₂
    (frameMass_move_of_peak_eq x _ 1 _ hpeak hrear)
  unfold massThreePotential frameClusterMass
  rw [hcongr, hoff]
  exact seqMassThreePotential_trivial_chip B₁ B₂ (frameMass x) hs hone htwo hempty

/-! ### The combined potential -/

/-- The mass-three potential: the fine first moment, `1/w` per pile of two, and
the class weights of the clusters of mass three. -/
def massThreeLyapunov {L N : ℕ} [NeZero L] (w B₁ B₂ : ℝ) (x : State L N) : ℝ :=
  peakFrameMoment (fun s => (s : ℝ)) x + twoCount x / w + massThreePotential B₁ B₂ x

/-- The exact drift of the mass-three potential on the majority region. The
first two parts are those of `generator_firstMoment_add_twoCount`, the last
that of `generator_massThreePotential_eq`. -/
theorem generator_massThreeLyapunov_eq {L N : ℕ} [NeZero L] (hL : 3 ≤ L) {w : ℝ}
    (hw : w ≠ 0) (B₁ B₂ : ℝ) (x : State L N) (hmargin : N + 2 < 2 * largest x) :
    generator w (massThreeLyapunov w B₁ B₂) x =
      (w * occupiedCount x - singleCount x -
          (L : ℝ) * departureMassRate w (occ x (peakSite x - 1)) +
        (threeCount x - twoCount x + occupiedSingleCount x - occupiedTwoCount x) -
        (twoOccupiedCount x + pileTwoCount x) / w) +
      ((∑ s ∈ Finset.range L, if 1 ≤ s ∧ 2 ≤ frameMass x s then
          massThreeWholeChange B₁ B₂ x s else 0) -
        massThreeWeight B₁ B₂ (frameMass x 1) (frameClusterMass x 1) +
        w * ∑ i, massThreeChipChange B₁ B₂ x i) := by
  have hadd : generator w (massThreeLyapunov w B₁ B₂) x =
      generator w (fun y => peakFrameMoment (fun s => (s : ℝ)) y + twoCount y / w) x +
        generator w (massThreePotential B₁ B₂) x := by
    unfold generator massThreeLyapunov
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold atSite
    split_ifs <;> ring
  rw [hadd, generator_firstMoment_add_twoCount hL hw x hmargin,
    generator_massThreePotential_eq hL w B₁ B₂ x hmargin]

/-- On the ring, the class-weight change of a chip inside the background is
the change of the sequence of masses seen from the peak. The sequence lemmas
`seqMassThreePotential_dissolve`, `seqMassThreePotential_shed`,
`seqMassThreePotential_pile_onto_pile`, `seqMassThreePotential_pile_onto_single`,
`seqMassThreePotential_single_onto_pile` and
`seqMassThreePotential_single_onto_single` evaluate it in every case. -/
theorem massThreeChipChange_eq_seq {L N : ℕ} [NeZero L] (hL : 3 ≤ L) (B₁ B₂ : ℝ)
    (x : State L N) (hmargin : N + 2 < 2 * largest x) {s : ℕ} (hs : s + 1 < L)
    (hone : 1 ≤ frameMass x s) :
    massThreeChipChange B₁ B₂ x (peakSite x + (s : Fin L)) =
      seqMassThreePotential B₁ B₂ L (seqMove (frameMass x) s 1) -
        seqMassThreePotential B₁ B₂ L (frameMass x) := by
  have hsL : s < L := by omega
  have hoff : peakOffset x (peakSite x + (s : Fin L)) = s :=
    ((peak_add_eq_iff x hsL _).mp rfl).symm
  have hocc : occ x (peakSite x + (s : Fin L)) = frameMass x s := rfl
  have hrear : peakSite x + (s : Fin L) ≠ peakSite x - 1 := by
    intro he
    have := congrArg (peakOffset x) he
    rw [hoff, peakOffset_peakSite_sub_one hL] at this
    omega
  unfold massThreeChipChange
  rw [dif_pos (by rw [hocc]; exact hone)]
  have hpeak := peakSite_chip_move x hmargin (peakSite x + (s : Fin L)) (by rw [hocc]; exact hone)
  have hcongr := seqMassThreePotential_congr B₁ B₂
    (frameMass_move_of_peak_eq x _ 1 _ hpeak hrear)
  unfold massThreePotential
  rw [hcongr, hoff]

end
end Chipping
