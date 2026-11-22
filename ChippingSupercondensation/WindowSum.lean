import ChippingSupercondensation.WindowMotion
import ChippingSupercondensation.PeakFrame

/-! # Summing the variable-radius block bounds over the ring

`WindowMotion` bounds the generator of the price of one fixed block. This
module applies that bound to the block at every base site of the ring and adds
the peak-frame first moment, which pays for the singles of the light blocks.

* A light block whose last site is empty holds a group at some offset. Its
  internal clocks together with its first-moment share have the certified
  drift of `VariableWindow`, wherever the group sits in the block
  (`ring_drift_eq_shift`).
* The remaining contributions are arrivals across the first edge of the block
  and departures across its last edge. Each needs an occupied end site, and
  costs at most a constant times `priceBound w`.
* On a block holding four or more particles, departures across the last edge
  are the only moves that can raise the price (`generator_largeBlock_le`). The
  first-moment share adds at most `w` per occupied site of the block.

Summing over all bases, each occupied site is the site behind exactly one block
and the last site of exactly one block, while every bare triple isolated by
`W - 1` empty sites on both sides earns its credit in `W - 1` blocks
(`isolatedTripleCount_le`). `stationary_bareBlocks_le` is the resulting
identity-based inequality, without any majority assumption. The exit and
arrival terms together cost at most `12 priceBound w E[K]`, independently of
`W`, while the credit grows like `(W - 1)/64`. The linear moment enters as `W`
times `E[w K - S]`, which `stationary_bareBlocks_le_of_cutoff` bounds below on
the majority region. `stationary_isolatedTriples_le` collects the result.

The boundary term is small against the credit only once `W` is much larger
than `768 priceBound w`, which is of order `100 / w²`. The bound is therefore
useful only for rings much longer than that.
-/

namespace Chipping.VariableWindow
open scoped BigOperators
noncomputable section

/-! ## Groups at an arbitrary offset inside a block -/

theorem listValue_map_add (V : Group → ℝ) (l : List ℕ) (o : ℕ) :
    listValue V (l.map (· + o)) = listValue V l := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
    simp [listValue, Nat.add_sub_add_right]

/-- A slice translated by `o` sites. -/
def Slice.shift (s : Slice) (o : ℕ) : Slice :=
  ⟨s.left.map (· + o), s.site + o, s.mass, s.right.map (· + o)⟩

theorem Slice.shift_after (s : Slice) (o k : ℕ) :
    (s.shift o).after k = (s.after k).map (· + o) := by
  simp only [Slice.shift, Slice.after, List.map_append, List.map_replicate,
    Nat.add_right_comm]

private theorem sorted_map_add {l : List ℕ} (h : l.Sorted (· ≤ ·)) (o : ℕ) :
    (l.map (· + o)).Sorted (· ≤ ·) :=
  List.pairwise_map.mpr (h.imp fun hab => Nat.add_le_add_right hab o)

/-- `ring_drift_eq` for a group whose first particle sits at offset `o`. -/
theorem ring_drift_eq_shift {L N : ℕ} [NeZero L] (w : ℝ) (V : Group → ℝ) (base : Fin L)
    (width : ℕ) (hL : width ≤ L) (x : State L N) (g : Group) (o : ℕ)
    (hroom : o + g.span + 1 < width)
    (hx : blockParticles base width x = ((g.positions.map (· + o)) : Multiset ℕ)) :
    (g.slices.map fun s => atSite w (blockValue V base width) x (base + ((s.site + o : ℕ) : Fin L)) +
      WindowEight.firstMomentShare w (occ x (base + ((s.site + o : ℕ) : Fin L)))).sum =
      drift w V g := by
  rw [← sum_slice_drift]
  congr 1
  apply List.map_congr_left
  intro s hs
  obtain ⟨hbefore, hpos, hspan, hcount, hsorted⟩ := slice_facts g s hs
  have hx' : blockParticles base width x = ((s.shift o).after 0 : Multiset ℕ) := by
    rw [hx, Slice.shift_after, hbefore]
  have hm : occ x (base + ((s.site + o : ℕ) : Fin L)) = s.mass := by
    have h := congrArg (Multiset.count (s.site + o)) hx
    rw [count_blockParticles, if_pos (by omega), Multiset.coe_count,
      List.count_map_of_injective _ _ (add_left_injective o), ← hbefore, hcount] at h
    exact h
  have hsortedt (k : ℕ) (hk : k ≤ s.mass) : ((s.shift o).after k).Sorted (· ≤ ·) := by
    rw [Slice.shift_after]
    exact sorted_map_add (hsorted k hk) o
  have hv : blockValue V base width x = listValue V (s.after 0) := by
    rw [blockValue_of_sorted V base width x _ hx' (hsortedt 0 (Nat.zero_le _)),
      Slice.shift_after, listValue_map_add]
  have hmoved (k : ℕ) (hk : k ≤ s.mass) (ha : k ≤ occ x (base + ((s.site + o : ℕ) : Fin L))) :
      blockValue V base width (move x (base + ((s.site + o : ℕ) : Fin L)) k ha) =
        listValue V (s.after k) := by
    have hsite : (s.shift o).site + 1 < width := by simp only [Slice.shift]; omega
    have hb : blockParticles base width (move x (base + ((s.site + o : ℕ) : Fin L)) k ha) =
        ((s.shift o).after k : Multiset ℕ) :=
      block_move_after base width hL x (s.shift o) hsite hx' k hk ha
    rw [blockValue_of_sorted V base width _ _ hb (hsortedt k hk), Slice.shift_after,
      listValue_map_add]
  unfold atSite Slice.drift
  simp only [dif_pos (by omega : 1 ≤ occ x (base + ((s.site + o : ℕ) : Fin L))), hv,
    hmoved 1 hpos]
  by_cases h2 : 2 ≤ occ x (base + ((s.site + o : ℕ) : Fin L))
  · simp only [if_pos h2, if_pos (show 2 ≤ s.mass by omega), hm]
    rw [hmoved _ le_rfl hm.ge]
  · simp only [if_neg h2, if_neg (show ¬2 ≤ s.mass by omega), hm]

/-- The distinct sites of the slices are the distinct particle positions. -/
theorem slice_sites (g : Group) :
    (g.slices.map (·.site)).Nodup ∧ ∀ j, j ∈ g.slices.map (·.site) ↔ j ∈ g.positions := by
  rcases g with _ | (_ | a) | ⟨(_ | a), (_ | b)⟩ <;>
    simp [Group.slices, Group.positions]
  exact ⟨by omega, fun j => by constructor <;> intro h <;> omega⟩

/-- Summing a function of the block offsets that vanishes off the group. -/
theorem sum_range_eq_slices (g : Group) (o W : ℕ) (hroom : o + g.span + 1 < W) (φ : ℕ → ℝ)
    (hzero : ∀ j < W, j ∉ g.positions.map (· + o) → φ j = 0) :
    ∑ j ∈ Finset.range W, φ j = (g.slices.map fun s => φ (s.site + o)).sum := by
  classical
  obtain ⟨hnd, hmem⟩ := slice_sites g
  let l := (g.slices.map (·.site)).map (· + o)
  have hndl : l.Nodup := hnd.map (add_left_injective o)
  have hmeml (j : ℕ) : j ∈ l ↔ j ∈ g.positions.map (· + o) := by
    simp only [l, List.mem_map, hmem]
  have hlt (j : ℕ) (hj : j ∈ l) : j < W := by
    simp only [l, List.mem_map] at hj
    obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hj
    have := (slice_facts g s hs).2.2.1
    omega
  have hsub : l.toFinset ⊆ Finset.range W := fun j hj =>
    Finset.mem_range.mpr (hlt j (List.mem_toFinset.mp hj))
  rw [← Finset.sum_subset hsub (fun j hj hjl => hzero j (Finset.mem_range.mp hj)
    (fun h => hjl (List.mem_toFinset.mpr ((hmeml j).mpr h)))), List.sum_toFinset _ hndl]
  simp only [l, List.map_map]
  rfl

/-! ## The generator of a block price -/

section Block
variable {L N : ℕ} [NeZero L]

theorem natCast_fin_inj {a b : ℕ} (ha : a < L) (hb : b < L)
    (h : (a : Fin L) = (b : Fin L)) : a = b := by
  have := congrArg Fin.val h
  simpa [Fin.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

theorem block_site_ne_rear (base : Fin L) {W j : ℕ} (hWL : W < L) (hj : j < W) :
    base + (j : Fin L) ≠ base - 1 := by
  intro h
  have h' : ((j + 1 : ℕ) : Fin L) = ((L : ℕ) : Fin L) := by
    rw [Fin.natCast_self, Nat.cast_add, Nat.cast_one]
    linear_combination h
  have := congrArg Fin.val h'
  simp only [Fin.val_natCast, Nat.mod_self, Nat.mod_eq_of_lt (by omega : j + 1 < L)] at this
  omega

/-- A move away from the block and from the site behind it leaves the block
contents unchanged. -/
theorem blockParticles_move_outside (base : Fin L) (W : ℕ) (x : State L N)
    (i : Fin L) (hi : ∀ j < W, base + (j : Fin L) ≠ i) (hrear : i ≠ base - 1)
    (k : ℕ) (hk : k ≤ occ x i) :
    blockParticles base W (move x i k hk) = blockParticles base W x := by
  unfold blockParticles
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have hne : base + (j : Fin L) ≠ right i := by
    intro h
    rw [right_eq_add_one] at h
    rcases j with _ | j
    · apply hrear
      simp only [Nat.cast_zero, add_zero] at h
      rw [h, add_sub_cancel_right]
    · apply hi j (by omega)
      rw [Nat.cast_succ, ← add_assoc] at h
      exact add_right_cancel h
  rw [occ_move]
  simp [transfer, hi j hj', hne]

theorem atSite_outside_block (w : ℝ) (V : Group → ℝ) (base : Fin L) (W : ℕ)
    (x : State L N) (i : Fin L) (hi : ∀ j < W, base + (j : Fin L) ≠ i) (hrear : i ≠ base - 1) :
    atSite w (blockValue V base W) x i = 0 := by
  have h (k : ℕ) (hk : k ≤ occ x i) :
      blockValue V base W (move x i k hk) = blockValue V base W x := by
    unfold blockValue
    rw [blockParticles_move_outside base W x i hi hrear k hk]
  unfold atSite
  split_ifs <;> simp [h]

/-- Only the sites of the block and the site behind it can change its price. -/
theorem generator_block_eq (w : ℝ) (V : Group → ℝ) (base : Fin L) (W : ℕ) (hWL : W < L)
    (x : State L N) :
    generator w (blockValue V base W) x =
      (∑ j ∈ Finset.range W, atSite w (blockValue V base W) x (base + (j : Fin L))) +
        atSite w (blockValue V base W) x (base - 1) := by
  classical
  let f := atSite w (blockValue V base W) x
  let T := (Finset.range W).image fun j : ℕ => base + (j : Fin L)
  have hinj : Set.InjOn (fun j : ℕ => base + (j : Fin L)) (Finset.range W : Set ℕ) := by
    intro a ha b hb h
    exact natCast_fin_inj (by simp at ha; omega) (by simp at hb; omega) (add_left_cancel h)
  have hT : ∑ i ∈ T, f i = ∑ j ∈ Finset.range W, f (base + (j : Fin L)) :=
    Finset.sum_image (fun a ha b hb h => hinj ha hb h)
  have hrear : base - 1 ∈ Tᶜ := by
    simp only [T, Finset.mem_compl, Finset.mem_image, Finset.mem_range, not_exists, not_and]
    exact fun j hj => block_site_ne_rear base hWL hj
  have hcompl : ∑ i ∈ Tᶜ, f i = f (base - 1) := by
    apply Finset.sum_eq_single_of_mem _ hrear
    intro i hi hne
    apply atSite_outside_block w V base W x i _ hne
    intro j hj h
    exact Finset.mem_compl.mp hi (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, h⟩)
  unfold generator
  rw [← Finset.sum_add_sum_compl T f, hT, hcompl]

/-! ## Bounds for one block -/

/-- Occupation indicator of a site. -/
def occupiedAt (x : State L N) (i : Fin L) : ℝ := if 0 < occ x i then 1 else 0

omit [NeZero L] in
theorem occupiedAt_nonneg (x : State L N) (i : Fin L) : 0 ≤ occupiedAt x i := by
  unfold occupiedAt; split_ifs <;> norm_num

omit [NeZero L] in
theorem occupiedAt_le_one (x : State L N) (i : Fin L) : occupiedAt x i ≤ 1 := by
  unfold occupiedAt; split_ifs <;> norm_num

omit [NeZero L] in
/-- A function with values in `[0, B]` changes at a site by at most `(w + 1) B`. -/
theorem atSite_le_of_bounds {w B : ℝ} (hw : 0 ≤ w) (f : State L N → ℝ)
    (hf0 : ∀ y, 0 ≤ f y) (hfB : ∀ y, f y ≤ B) (x : State L N) (i : Fin L) :
    atSite w f x i ≤ (w + 1) * B * occupiedAt x i := by
  unfold atSite occupiedAt
  have hx0 := hf0 x
  have hB0 : 0 ≤ B := hx0.trans (hfB x)
  by_cases h1 : 1 ≤ occ x i
  · rw [dif_pos h1, if_pos (by omega : 0 < occ x i)]
    have hc := mul_le_mul_of_nonneg_left
      (show f (move x i 1 h1) - f x ≤ B by linarith [hfB (move x i 1 h1)]) hw
    split_ifs with h2
    · have hw2 := hfB (move x i (occ x i) le_rfl)
      nlinarith
    · nlinarith
  · rw [dif_neg h1, if_neg (by omega), if_neg (by omega : ¬ 0 < occ x i)]
    simp

theorem blockValue_nonneg {w : ℝ} (hw : 0 < w) (base : Fin L) (W : ℕ) (x : State L N) :
    0 ≤ blockValue (price w (radius w) (1/w)) base W x := by
  unfold blockValue
  generalize (blockParticles base W x).sort (· ≤ ·) = p
  rcases p with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;> simp only [listValue] <;>
    first | exact le_rfl | exact price_nonneg hw _

theorem four_le_priceBound {w : ℝ} (hw : 0 < w) : 4 ≤ priceBound w := by
  unfold priceBound
  have h1 : 0 ≤ 1 / (64 * w) := by positivity
  have h2 : (0 : ℝ) ≤ radius w := Nat.cast_nonneg _
  linarith

theorem card_blockParticles (base : Fin L) (W : ℕ) (x : State L N) :
    ((blockParticles base W x).card : ℝ) =
      ∑ j ∈ Finset.range W, (occ x (base + (j : Fin L)) : ℝ) := by
  simp [blockParticles, Multiset.card_sum]

theorem sum_occupiedAt_le_card (base : Fin L) (W : ℕ) (x : State L N) :
    ∑ j ∈ Finset.range W, occupiedAt x (base + (j : Fin L)) ≤ (blockParticles base W x).card := by
  rw [card_blockParticles]
  apply Finset.sum_le_sum
  intro j _
  unfold occupiedAt
  split_ifs with h
  · exact_mod_cast h
  · positivity

/-- The share of the linear moment allocated to the sites of a block. -/
def windowShare (w : ℝ) (base : Fin L) (W : ℕ) (x : State L N) : ℝ :=
  ∑ j ∈ Finset.range W, WindowEight.firstMomentShare w (occ x (base + (j : Fin L)))

theorem firstMomentShare_le {w : ℝ} (m : ℕ) :
    WindowEight.firstMomentShare w m ≤ w * (if 0 < m then 1 else 0) := by
  unfold WindowEight.firstMomentShare
  split_ifs <;> first | omega | linarith

theorem windowShare_le (w : ℝ) (base : Fin L) (W : ℕ) (x : State L N) :
    windowShare w base W x ≤ w * ∑ j ∈ Finset.range W, occupiedAt x (base + (j : Fin L)) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => firstMomentShare_le _

open Classical in
/-- The block holds exactly three particles, all on one site that is not the
last site of the block. -/
def bareInBlock (base : Fin L) (W : ℕ) (x : State L N) : ℝ :=
  if ∃ o : ℕ, o + 1 < W ∧ blockParticles base W x = (([o, o, o] : List ℕ) : Multiset ℕ)
  then 1 else 0

/-- The occupied sites of a block holding at least four particles. -/
def heavyOccupancy (base : Fin L) (W : ℕ) (x : State L N) : ℝ :=
  if 4 ≤ (blockParticles base W x).card then
    ∑ j ∈ Finset.range W, occupiedAt x (base + (j : Fin L)) else 0

theorem bareInBlock_nonneg (base : Fin L) (W : ℕ) (x : State L N) :
    0 ≤ bareInBlock base W x := by
  unfold bareInBlock; split_ifs <;> norm_num

theorem bareInBlock_le_one (base : Fin L) (W : ℕ) (x : State L N) :
    bareInBlock base W x ≤ 1 := by
  unfold bareInBlock; split_ifs <;> norm_num

theorem card_of_bareInBlock (base : Fin L) (W : ℕ) (x : State L N)
    (h : bareInBlock base W x ≠ 0) : (blockParticles base W x).card = 3 := by
  unfold bareInBlock at h
  split_ifs at h with hb
  · obtain ⟨o, _, ho⟩ := hb
    rw [ho]
    rfl
  · exact absurd rfl h

theorem heavyOccupancy_nonneg (base : Fin L) (W : ℕ) (x : State L N) :
    0 ≤ heavyOccupancy base W x := by
  unfold heavyOccupancy
  split_ifs
  · exact Finset.sum_nonneg fun j _ => occupiedAt_nonneg x _
  · exact le_rfl

/-- A group whose shifted positions form one site of three particles is a
bare triple. -/
theorem eq_bare_of_positions (g : Group) (o o' : ℕ)
    (h : ((g.positions.map (· + o)) : Multiset ℕ) = (([o', o', o'] : List ℕ) : Multiset ℕ)) :
    g = .three 0 0 := by
  have hp := Multiset.coe_eq_coe.mp h
  have hlen := hp.length_eq
  rcases g with _ | a | ⟨a, b⟩
  · simp [Group.positions] at hlen
  · simp [Group.positions] at hlen
  · have hm (j : ℕ) := hp.mem_iff (a := j)
    simp only [Group.positions, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    have h1 := (hm (0 + o)).mp (Or.inl rfl)
    have h2 := (hm (a + o)).mp (Or.inr (Or.inl rfl))
    have h3 := (hm (a + b + o)).mp (Or.inr (Or.inr rfl))
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    rw [ha, hb]

/-- A block with one to three particles and an empty last site holds one group
at some offset, with room before the last site. -/
theorem light_block_shape (base : Fin L) (W : ℕ) (x : State L N)
    (h1 : 1 ≤ (blockParticles base W x).card) (h3 : (blockParticles base W x).card ≤ 3)
    (hlast : occ x (base + ((W - 1 : ℕ) : Fin L)) = 0) :
    ∃ g : Group, ∃ o : ℕ, blockParticles base W x = ((g.positions.map (· + o)) : Multiset ℕ) ∧
      o + g.span + 1 < W := by
  set P := blockParticles base W x with hP
  have hmem (j : ℕ) (hj : j ∈ P) : j + 1 < W := by
    have hc := Multiset.count_pos.mpr hj
    rw [hP, count_blockParticles] at hc
    split_ifs at hc with hjW
    · have : j ≠ W - 1 := by
        rintro rfl
        rw [hlast] at hc
        omega
      omega
    · omega
  have hsort := Multiset.sort_eq (· ≤ ·) P
  have hsorted := Multiset.sort_sorted (· ≤ ·) P
  have hlen : (P.sort (· ≤ ·)).length = P.card := Multiset.length_sort _
  generalize P.sort (· ≤ ·) = l at hsort hsorted hlen
  have hmem' (j : ℕ) (hj : j ∈ l) : j + 1 < W :=
    hmem j (by rw [← hsort]; exact Multiset.mem_coe.mpr hj)
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
  · simp at hlen; omega
  · refine ⟨.one, a, ?_, ?_⟩
    · rw [← hsort]; simp [Group.positions]
    · have := hmem' a (by simp)
      simp only [Group.span]; omega
  · simp [List.Sorted] at hsorted
    refine ⟨.two (b - a), a, ?_, ?_⟩
    · rw [← hsort]
      congr 1
      simp [Group.positions]
      omega
    · have := hmem' b (by simp)
      simp only [Group.span]; omega
  · simp [List.Sorted] at hsorted
    refine ⟨.three (b - a) (c - b), a, ?_, ?_⟩
    · rw [← hsort]
      congr 1
      simp [Group.positions]
      omega
    · have := hmem' c (by simp)
      simp only [Group.span]; omega
  · simp at hlen; omega

omit [NeZero L] in
private theorem atSite_empty (w : ℝ) (f : State L N → ℝ) (x : State L N) (i : Fin L)
    (h : occ x i = 0) : atSite w f x i = 0 := by
  simp only [atSite, dif_neg (by omega : ¬ 1 ≤ occ x i), if_neg (by omega : ¬ 2 ≤ occ x i),
    add_zero]

/-- The generator of one block price together with the block's share of the
linear moment. A bare triple anywhere before the last site earns the credit
`1/64`. The remaining terms need an occupied site just behind the block, an
occupied last site, or a block of mass at least four. -/
theorem generator_blockPrice_add_share_le {w : ℝ} (hw : 0 < w) (hs : w ≤ 1/32)
    (base : Fin L) (W : ℕ) (hW : 2 ≤ W) (hWL : W < L) (x : State L N) :
    generator w (blockValue (price w (radius w) (1/w)) base W) x + windowShare w base W x ≤
      -(1/64) * bareInBlock base W x +
        6 * priceBound w *
          (occupiedAt x (base - 1) + occupiedAt x (base + ((W - 1 : ℕ) : Fin L))) +
        w * heavyOccupancy base W x := by
  obtain ⟨n, rfl⟩ : ∃ n, W = n + 1 := ⟨W - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  set V := price w (radius w) (1/w) with hV
  set F := blockValue (N := N) V base (n+1) with hF
  set B := priceBound w with hB
  have hpB : 4 ≤ B := four_le_priceBound hw
  have hF0 : ∀ y, 0 ≤ F y := blockValue_nonneg hw base (n+1)
  have hFB : ∀ y, F y ≤ B := blockValue_le hw base (n+1)
  have hsite (i : Fin L) : atSite w F x i ≤ (w + 1) * B * occupiedAt x i :=
    atSite_le_of_bounds hw.le F hF0 hFB x i
  have hsplit : generator w F x =
      (∑ j ∈ Finset.range (n+1), atSite w F x (base + (j : Fin L))) + atSite w F x (base - 1) :=
    generator_block_eq w V base (n+1) hWL x
  have hprev0 := occupiedAt_nonneg x (base - 1)
  have hlast0 := occupiedAt_nonneg x (base + (n : Fin L))
  have hbare0 := bareInBlock_nonneg base (n+1) x
  have hbare1 := bareInBlock_le_one base (n+1) x
  have hrear := hsite (base - 1)
  have hshare := windowShare_le w base (n+1) x
  have hocc := sum_occupiedAt_le_card base (n+1) x
  have hrear6 : (w + 1) * B * occupiedAt x (base - 1) ≤ 6 * B * occupiedAt x (base - 1) :=
    mul_le_mul_of_nonneg_right (by nlinarith) hprev0
  have hlast6 : (w + 1) * B * occupiedAt x (base + (n : Fin L)) ≤
      6 * B * occupiedAt x (base + (n : Fin L)) :=
    mul_le_mul_of_nonneg_right (by nlinarith) hlast0
  have hB0 : 0 ≤ 6 * B * occupiedAt x (base - 1) := by positivity
  have hL0 : 0 ≤ 6 * B * occupiedAt x (base + (n : Fin L)) := by positivity
  by_cases hq : 4 ≤ (blockParticles base (n+1) x).card
  · -- A heavy block: only departures across the last edge.
    have hg := generator_largeBlock_le hw base n (by omega) x hq
    dsimp only at hg
    have hexit : generator w F x ≤ (w + 1) * B * occupiedAt x (base + (n : Fin L)) := by
      refine hg.trans ?_
      unfold occupiedAt
      by_cases hm : 0 < occ x (base + (n : Fin L))
      · rw [if_pos hm]
        split_ifs <;> nlinarith
      · rw [if_neg hm]
        split_ifs <;> first | omega | simp
    have hb : bareInBlock base (n+1) x = 0 := by
      by_contra h
      have := card_of_bareInBlock base (n+1) x h
      omega
    have hh : heavyOccupancy base (n+1) x =
        ∑ j ∈ Finset.range (n+1), occupiedAt x (base + (j : Fin L)) := if_pos hq
    rw [hb, hh]
    linarith
  · have hh : heavyOccupancy base (n+1) x = 0 := if_neg hq
    rw [hh]
    by_cases hlast : occ x (base + (n : Fin L)) = 0
    · by_cases h0 : (blockParticles base (n+1) x).card = 0
      · -- An empty block: only arrivals from behind.
        have hempty (j : ℕ) (hj : j < n+1) : occ x (base + (j : Fin L)) = 0 := by
          have hc := card_blockParticles base (n+1) x
          rw [h0, Nat.cast_zero] at hc
          have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun (k : ℕ) _ =>
            Nat.cast_nonneg (α := ℝ) (occ x (base + (k : Fin L))))).mp hc.symm j
              (Finset.mem_range.mpr hj)
          exact_mod_cast hz
        have hin : ∑ j ∈ Finset.range (n+1), atSite w F x (base + (j : Fin L)) = 0 :=
          Finset.sum_eq_zero fun j hj => atSite_empty w F x _ (hempty j (Finset.mem_range.mp hj))
        have hsh : windowShare w base (n+1) x = 0 :=
          Finset.sum_eq_zero fun j hj => by
            rw [hempty j (Finset.mem_range.mp hj)]
            simp [WindowEight.firstMomentShare]
        have hb : bareInBlock base (n+1) x = 0 := by
          by_contra h
          have := card_of_bareInBlock base (n+1) x h
          omega
        rw [hsplit, hin, hsh, hb]
        linarith
      · -- One group with room: the certificate applies.
        obtain ⟨g, o, hgx, hroom⟩ := light_block_shape base (n+1) x (by omega) (by omega)
          (by rw [Nat.add_sub_cancel]; exact hlast)
        have hzero (j : ℕ) (hj : j < n+1) (hjg : j ∉ g.positions.map (· + o)) :
            atSite w F x (base + (j : Fin L)) +
              WindowEight.firstMomentShare w (occ x (base + (j : Fin L))) = 0 := by
          have hc := congrArg (Multiset.count j) hgx
          rw [count_blockParticles, if_pos hj, Multiset.coe_count,
            List.count_eq_zero_of_not_mem hjg] at hc
          rw [atSite_empty w F x _ hc, hc]
          simp [WindowEight.firstMomentShare]
        have hsum : ∑ j ∈ Finset.range (n+1), (atSite w F x (base + (j : Fin L)) +
              WindowEight.firstMomentShare w (occ x (base + (j : Fin L)))) =
            (g.slices.map fun s => atSite w F x (base + ((s.site + o : ℕ) : Fin L)) +
              WindowEight.firstMomentShare w (occ x (base + ((s.site + o : ℕ) : Fin L)))).sum :=
          sum_range_eq_slices g o (n+1) hroom
            (fun j => atSite w F x (base + (j : Fin L)) +
              WindowEight.firstMomentShare w (occ x (base + (j : Fin L)))) hzero
        have hdrift := ring_drift_eq_shift w V base (n+1) hWL.le x g o hroom hgx
        have hcert := smallRate_drift_le hw hs g
        have hbare : drift w V g ≤ -(1/64) * bareInBlock base (n+1) x := by
          unfold bareInBlock
          split_ifs with hb
          · obtain ⟨o', _, ho'⟩ := hb
            have hg3 := eq_bare_of_positions g o o' (hgx.symm.trans ho')
            rw [if_pos hg3] at hcert
            linarith
          · split_ifs at hcert <;> linarith
        have htotal : generator w F x + windowShare w base (n+1) x =
            drift w V g + atSite w F x (base - 1) := by
          rw [hsplit, ← hdrift, ← hsum]
          unfold windowShare
          rw [Finset.sum_add_distrib]
          ring
        rw [htotal]
        linarith
    · -- The last site is occupied: a crude bound by the three occupied sites.
      have hlast1 : occupiedAt x (base + (n : Fin L)) = 1 := by
        unfold occupiedAt
        rw [if_pos (Nat.pos_of_ne_zero hlast)]
      have hcard3 : ∑ j ∈ Finset.range (n+1), occupiedAt x (base + (j : Fin L)) ≤ 3 := by
        refine hocc.trans ?_
        exact_mod_cast (by omega : (blockParticles base (n+1) x).card ≤ 3)
      have hin : ∑ j ∈ Finset.range (n+1), atSite w F x (base + (j : Fin L)) ≤ (w + 1) * B * 3 :=
        calc _ ≤ ∑ j ∈ Finset.range (n+1), (w + 1) * B * occupiedAt x (base + (j : Fin L)) :=
              Finset.sum_le_sum fun j _ => hsite _
          _ = (w + 1) * B * ∑ j ∈ Finset.range (n+1), occupiedAt x (base + (j : Fin L)) := by
              rw [Finset.mul_sum]
          _ ≤ (w + 1) * B * 3 := mul_le_mul_of_nonneg_left hcard3 (by positivity)
      have hsh : windowShare w base (n+1) x ≤ w * 3 :=
        hshare.trans (mul_le_mul_of_nonneg_left hcard3 hw.le)
      have hcrude : (w + 1) * B * 3 + w * 3 + 1/64 ≤ 6 * B := by nlinarith
      rw [hsplit, hlast1]
      linarith

end Block

/-! ## Summing over all bases -/

section Ring
variable {L N : ℕ} [NeZero L]

theorem sum_shift (f : Fin L → ℝ) (d : Fin L) : ∑ base : Fin L, f (base + d) = ∑ i, f i :=
  Equiv.sum_comp (Equiv.addRight d) f

theorem sum_occupiedAt_shift (x : State L N) (d : Fin L) :
    ∑ base : Fin L, occupiedAt x (base + d) = occupiedCount x :=
  sum_shift (occupiedAt x) d

theorem sum_occupiedAt_sub_one (x : State L N) :
    ∑ base : Fin L, occupiedAt x (base - 1) = occupiedCount x := by
  simp_rw [sub_eq_add_neg]
  exact sum_occupiedAt_shift x (-1)

/-- Every site lies in exactly `W` blocks, so the block shares add up to `W`
times the drift `w K - S` of the linear moment. -/
theorem sum_windowShare (w : ℝ) (W : ℕ) (x : State L N) :
    ∑ base : Fin L, windowShare w base W x = (W : ℝ) * (w * occupiedCount x - singleCount x) := by
  let f := fun i : Fin L => WindowEight.firstMomentShare w (occ x i)
  calc
    _ = ∑ j ∈ Finset.range W, ∑ base : Fin L, f (base + (j : Fin L)) := by
      unfold windowShare
      rw [Finset.sum_comm]
    _ = ∑ _j ∈ Finset.range W, ∑ i, f i :=
      Finset.sum_congr rfl fun j _ => sum_shift f (j : Fin L)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      congr 1
      unfold occupiedCount singleCount
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [f, WindowEight.firstMomentShare]
      split_ifs <;> first | (exfalso; omega) | ring

open Classical in
/-- Sites holding exactly three particles whose `W - 1` neighbours on each
side are empty. -/
def isolatedTripleCount (W : ℕ) (x : State L N) : ℝ :=
  ∑ s : Fin L, if occ x s = 3 ∧ ∀ d : ℕ, 1 ≤ d → d < W →
    occ x (s + (d : Fin L)) = 0 ∧ occ x (s - (d : Fin L)) = 0 then 1 else 0

private theorem site_eq_base_add (s base : Fin L) : s = base + (((s - base).val : ℕ) : Fin L) := by
  rw [Fin.cast_val_eq_self, add_sub_cancel]

private theorem card_short_offsets (s : Fin L) (W : ℕ) (hWL : W ≤ L) :
    ∑ base : Fin L, (if (s - base).val + 1 < W then (1 : ℝ) else 0) = ((W - 1 : ℕ) : ℝ) := by
  classical
  have h := Equiv.sum_comp (Equiv.subLeft s) (fun d : Fin L => if d.val + 1 < W then (1 : ℝ) else 0)
  simp only [Equiv.subLeft_apply] at h
  rw [h, Fin.sum_univ_eq_sum_range (fun i => if i + 1 < W then (1 : ℝ) else 0) L, Finset.sum_boole]
  have hset : (Finset.range L).filter (fun i => i + 1 < W) = Finset.range (W - 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hset, Finset.card_range]

/-- An isolated bare triple fills the block at each of `W - 1` bases with
nothing else. -/
theorem isolatedTripleCount_le (W : ℕ) (hWL : W ≤ L) (x : State L N) :
    ((W - 1 : ℕ) : ℝ) * isolatedTripleCount W x ≤ ∑ base : Fin L, bareInBlock base W x := by
  classical
  let iso : Fin L → Prop := fun s => occ x s = 3 ∧ ∀ d : ℕ, 1 ≤ d → d < W →
    occ x (s + (d : Fin L)) = 0 ∧ occ x (s - (d : Fin L)) = 0
  let c : Fin L → Fin L → ℝ := fun base s => if iso s ∧ (s - base).val + 1 < W then 1 else 0
  have hfar (s : Fin L) (hs : iso s) (base : Fin L) (ho : (s - base).val + 1 < W) (j : ℕ)
      (hj : j < W) (hne : j ≠ (s - base).val) : occ x (base + (j : Fin L)) = 0 := by
    set o := (s - base).val with ho'
    have hs_eq := site_eq_base_add s base
    rw [← ho'] at hs_eq
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have h := (hs.2 (o - j) (by omega) (by omega)).2
      have he : s - ((o - j : ℕ) : Fin L) = base + (j : Fin L) := by
        rw [hs_eq, Nat.cast_sub hlt.le]
        ring
      rwa [he] at h
    · have h := (hs.2 (j - o) (by omega) (by omega)).1
      have he : s + ((j - o : ℕ) : Fin L) = base + (j : Fin L) := by
        rw [hs_eq, Nat.cast_sub hgt.le]
        ring
      rwa [he] at h
  have hsep (s s' base : Fin L) (hs : iso s) (hs' : iso s') (h1 : (s - base).val + 1 < W)
      (h2 : (s' - base).val + 1 < W) : s' = s := by
    by_contra hne
    have hoff : (s' - base).val ≠ (s - base).val := by
      intro h
      apply hne
      rw [site_eq_base_add s' base, site_eq_base_add s base, h]
    have h0 := hfar s hs base h1 _ (by omega) hoff
    rw [← site_eq_base_add s' base, hs'.1] at h0
    omega
  have hblock (base : Fin L) : ∑ s, c base s ≤ bareInBlock base W x := by
    by_cases hex : ∃ s, iso s ∧ (s - base).val + 1 < W
    · obtain ⟨s, hs, ho⟩ := hex
      have hbare : bareInBlock base W x = 1 := by
        unfold bareInBlock
        rw [if_pos]
        refine ⟨(s - base).val, ho, ?_⟩
        ext j
        rw [count_blockParticles, Multiset.coe_count]
        by_cases hj : j = (s - base).val
        · rw [hj, if_pos (by omega), ← site_eq_base_add s base, hs.1]
          simp
        · have hc : List.count j [(s - base).val, (s - base).val, (s - base).val] = 0 := by
            have hj' : (s - base).val ≠ j := fun h => hj h.symm
            simp [List.count_cons, hj']
          rw [hc]
          split_ifs with hjW
          · exact hfar s hs base ho j hjW hj
          · rfl
      rw [hbare]
      calc
        ∑ s', c base s' = c base s :=
          Finset.sum_eq_single s (fun s' _ hne => if_neg fun h => hne (hsep s s' base hs h.1 ho h.2))
            (by simp)
        _ ≤ 1 := by simp only [c]; split_ifs <;> norm_num
    · have h0 : ∀ s, c base s = 0 := fun s => if_neg fun h => hex ⟨s, h⟩
      simp only [h0, Finset.sum_const_zero]
      exact bareInBlock_nonneg base W x
  have hcol (s : Fin L) : ∑ base, c base s =
      ((W - 1 : ℕ) : ℝ) * (if iso s then 1 else 0) := by
    by_cases hs : iso s
    · rw [if_pos hs, mul_one, ← card_short_offsets s W hWL]
      exact Finset.sum_congr rfl fun base _ => by simp only [c, hs, true_and]
    · rw [if_neg hs, mul_zero]
      exact Finset.sum_eq_zero fun base _ => if_neg fun h => hs h.1
  calc
    ((W - 1 : ℕ) : ℝ) * isolatedTripleCount W x = ∑ s, ∑ base, c base s := by
      unfold isolatedTripleCount
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => (hcol s).symm
    _ = ∑ base, ∑ s, c base s := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum fun base _ => hblock base

/-- The block bound at every base, summed over the ring. -/
theorem sum_generator_blockPrice_le {w : ℝ} (hw : 0 < w) (hs : w ≤ 1/32) (W : ℕ)
    (hW : 2 ≤ W) (hWL : W < L) (x : State L N) :
    (∑ base : Fin L, generator w (blockValue (price w (radius w) (1/w)) base W) x) +
      (W : ℝ) * (w * occupiedCount x - singleCount x) ≤
    -(1/64) * (∑ base : Fin L, bareInBlock base W x) + 12 * priceBound w * occupiedCount x +
      w * ∑ base : Fin L, heavyOccupancy base W x := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun base _ =>
    generator_blockPrice_add_share_le hw hs base W hW hWL x
  rw [Finset.sum_add_distrib, sum_windowShare] at h
  have e : ∑ b : Fin L, (-(1/64) * bareInBlock b W x + 6 * priceBound w *
        (occupiedAt x (b - 1) + occupiedAt x (b + ((W - 1 : ℕ) : Fin L))) +
        w * heavyOccupancy b W x) =
      -(1/64) * (∑ b : Fin L, bareInBlock b W x) + 6 * priceBound w *
        ((∑ b : Fin L, occupiedAt x (b - 1)) +
          ∑ b : Fin L, occupiedAt x (b + ((W - 1 : ℕ) : Fin L))) +
        w * ∑ b : Fin L, heavyOccupancy b W x := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [e, sum_occupiedAt_sub_one, sum_occupiedAt_shift] at h
  linarith

/-- **Summed stationary bound.** Weighted bare triples, plus `W` times the
mean drift `w K - S` of the linear moment, are bounded by a boundary term of
order `priceBound w` per occupied site and by `w` times the occupied sites of
heavy blocks. No majority assumption is used. -/
theorem stationary_bareBlocks_le {w : ℝ} (hw : 0 < w) (hs : w ≤ 1/32)
    (μ : StationaryLaw L N w) (W : ℕ) (hW : 2 ≤ W) (hWL : W < L) :
    (1/64) * (∑ x, μ.weight x * ∑ base : Fin L, bareInBlock base W x) +
      (W : ℝ) * (∑ x, μ.weight x * (w * occupiedCount x - singleCount x)) ≤
    12 * priceBound w * (∑ x, μ.weight x * occupiedCount x) +
      w * (∑ x, μ.weight x * ∑ base : Fin L, heavyOccupancy base W x) := by
  set G := fun x : State L N =>
    ∑ base : Fin L, generator w (blockValue (price w (radius w) (1/w)) base W) x
  have hinv : ∑ x, μ.weight x * G x = 0 := by
    simp only [G, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun base _ => μ.invariant _
  have h := Finset.sum_le_sum (s := Finset.univ) fun x _ =>
    mul_le_mul_of_nonneg_left (sum_generator_blockPrice_le hw hs W hW hWL x) (μ.nonneg x)
  have eL : ∑ x, μ.weight x * (G x + (W : ℝ) * (w * occupiedCount x - singleCount x)) =
      ∑ x, μ.weight x * G x +
        (W : ℝ) * (∑ x, μ.weight x * (w * occupiedCount x - singleCount x)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have eR : ∑ x, μ.weight x * (-(1/64) * (∑ base : Fin L, bareInBlock base W x) +
        12 * priceBound w * occupiedCount x + w * ∑ base : Fin L, heavyOccupancy base W x) =
      -(1/64) * (∑ x, μ.weight x * ∑ base : Fin L, bareInBlock base W x) +
        12 * priceBound w * (∑ x, μ.weight x * occupiedCount x) +
        w * (∑ x, μ.weight x * ∑ base : Fin L, heavyOccupancy base W x) := by
    calc
      _ = ∑ x, (-(1/64) * (μ.weight x * ∑ base : Fin L, bareInBlock base W x) +
            12 * priceBound w * (μ.weight x * occupiedCount x) +
            w * (μ.weight x * ∑ base : Fin L, heavyOccupancy base W x)) :=
        Finset.sum_congr rfl fun x _ => by ring
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  change ∑ x, μ.weight x * (G x + _) ≤ _ at h
  rw [eL, eR, hinv] at h
  linarith

/-- The summed bound with the linear moment controlled on the majority region.
A cutoff from any band above half the mass is chosen as in
`exists_majority_cutoff_singles_rear_flux_le`. The singles outside the
majority region remain as an explicit term. -/
theorem stationary_bareBlocks_le_of_cutoff {w : ℝ} (hw : 0 < w) (hs : w ≤ 1/32) (hL : 3 ≤ L)
    (μ : StationaryLaw L N w) (W : ℕ) (hW : 2 ≤ W) (hWL : W < L)
    (a b : ℕ) (hab : a ≤ b) (ha : N < 2 * a) (hbN : b ≤ N) :
    ∃ t ∈ Finset.Icc a b,
      (1/64) * (∑ x, μ.weight x * ∑ base : Fin L, bareInBlock base W x) ≤
        12 * priceBound w * (∑ x, μ.weight x * occupiedCount x) +
        w * (∑ x, μ.weight x * ∑ base : Fin L, heavyOccupancy base W x) +
        (W : ℝ) * (w * ((L - 1 : ℕ) : ℝ) *
            ((∑ x, μ.weight x * ((N : ℝ) - (largest x : ℝ) + 1)) / ((b + 1 - a : ℕ) : ℝ)) +
          ∑ x, μ.weight x * (if t < largest x then 0 else singleCount x)) := by
  obtain ⟨t, ht, hflux⟩ := exists_majority_cutoff_singles_rear_flux_le hL hw.le μ a b hab ha hbN
  refine ⟨t, ht, ?_⟩
  have hsum := stationary_bareBlocks_le hw hs μ W hW hWL
  have hpoint (x : State L N) :
      μ.weight x * (singleCount x - w * occupiedCount x) ≤
        μ.weight x * (if t < largest x then
          singleCount x + (L : ℝ) * departureMassRate w (occ x (peakSite x - 1)) else 0) -
        w * (μ.weight x * (if t < largest x then occupiedCount x else 0)) +
        μ.weight x * (if t < largest x then 0 else singleCount x) := by
    have hK : 0 ≤ occupiedCount x :=
      Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
    have hq := departureMassRate_nonneg hw.le (occ x (peakSite x - 1))
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have hμ := μ.nonneg x
    split_ifs
    · nlinarith [mul_nonneg hμ (mul_nonneg hL0 hq)]
    · nlinarith [mul_nonneg hμ (mul_nonneg hw.le hK)]
  have hS := Finset.sum_le_sum (s := Finset.univ) fun x _ => hpoint x
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hS
  have eS : ∑ x, μ.weight x * (singleCount x - w * occupiedCount x) =
      -(∑ x, μ.weight x * (w * occupiedCount x - singleCount x)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [eS] at hS
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hfinal := mul_le_mul_of_nonneg_left (show
    -(∑ x, μ.weight x * (w * occupiedCount x - singleCount x)) ≤
      w * ((L - 1 : ℕ) : ℝ) *
          ((∑ x, μ.weight x * ((N : ℝ) - (largest x : ℝ) + 1)) / ((b + 1 - a : ℕ) : ℝ)) +
        ∑ x, μ.weight x * (if t < largest x then 0 else singleCount x) by linarith) hW0
  linarith

/-- Each site lies in `W` blocks, so heavy blocks hold at most `W` times the
occupied sites. -/
theorem sum_heavyOccupancy_le (W : ℕ) (x : State L N) :
    ∑ base : Fin L, heavyOccupancy base W x ≤ (W : ℝ) * occupiedCount x := by
  calc
    _ ≤ ∑ base : Fin L, ∑ j ∈ Finset.range W, occupiedAt x (base + (j : Fin L)) := by
      apply Finset.sum_le_sum
      intro base _
      unfold heavyOccupancy
      split_ifs
      · exact le_rfl
      · exact Finset.sum_nonneg fun j _ => occupiedAt_nonneg x _
    _ = ∑ j ∈ Finset.range W, ∑ base : Fin L, occupiedAt x (base + (j : Fin L)) :=
      Finset.sum_comm
    _ = _ := by
      simp only [sum_occupiedAt_shift, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Isolated bare triples.** In stationarity, bare triples whose `W - 1`
neighbours on each side are empty have mean number at most `64 / (W - 1)`
times the right side. The boundary term `12 priceBound w E[K]` does not grow
with `W`. The heavy-block share is at most `w W E[K]` and is of the order of
`w W` times the occupied sites lying within `W` of a heavy group. The last
term is `W` times the cutoff error of the linear moment on the majority region
plus the singles outside it. -/
theorem stationary_isolatedTriples_le {w : ℝ} (hw : 0 < w)
    (hs : w ≤ 1/32) (hL : 3 ≤ L) (μ : StationaryLaw L N w) (W : ℕ) (hW : 2 ≤ W) (hWL : W < L)
    (a b : ℕ) (hab : a ≤ b) (ha : N < 2 * a) (hbN : b ≤ N) :
    ∃ t ∈ Finset.Icc a b,
      ((W - 1 : ℕ) : ℝ) / 64 * (∑ x, μ.weight x * isolatedTripleCount W x) ≤
        12 * priceBound w * (∑ x, μ.weight x * occupiedCount x) +
        w * (∑ x, μ.weight x * ∑ base : Fin L, heavyOccupancy base W x) +
        (W : ℝ) * (w * ((L - 1 : ℕ) : ℝ) *
            ((∑ x, μ.weight x * ((N : ℝ) - (largest x : ℝ) + 1)) / ((b + 1 - a : ℕ) : ℝ)) +
          ∑ x, μ.weight x * (if t < largest x then 0 else singleCount x)) := by
  obtain ⟨t, ht, h⟩ := stationary_bareBlocks_le_of_cutoff hw hs hL μ W hW hWL a b hab ha hbN
  refine ⟨t, ht, le_trans ?_ h⟩
  have hpt := Finset.sum_le_sum (s := Finset.univ) fun x _ =>
    mul_le_mul_of_nonneg_left (isolatedTripleCount_le W hWL.le x) (μ.nonneg x)
  have e : ∑ x, μ.weight x * (((W - 1 : ℕ) : ℝ) * isolatedTripleCount W x) =
      ((W - 1 : ℕ) : ℝ) * ∑ x, μ.weight x * isolatedTripleCount W x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [e] at hpt
  linarith

end Ring

end
end Chipping.VariableWindow
