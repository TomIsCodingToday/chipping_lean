import ChippingSupercondensation.WindowSum

/-! # Summing an arbitrary certified block price over the ring

`WindowSum` sums the price of `VariableWindow` over all blocks of the ring. This
module does the same for any price `V` of the block contents, recorded as the
multiset of particle offsets in the block. It isolates what a certificate for
groups of at most `M` particles has to provide:

* `0 ≤ V ≤ B`, and `V` vanishes on contents of more than `M` particles;
* `contentDrift w V P ≤ -c * credit P` for every content of `1` to `M`
  particles. Here `contentDrift` is the generator of `V` under the moves of the
  particles of `P` alone, together with their share `w K - S` of the linear
  moment.

`stationary_contentBlocks_le` is the summed stationary bound. A mass-four or
higher certificate only has to prove the drift inequality for contents. The
ring embedding, the boundary terms and the exits from heavy blocks are handled
here once and for all.
-/

namespace Chipping.ContentWindow
open scoped BigOperators
open VariableWindow
noncomputable section

/-! ## Contents and their drift -/

/-- Move `k` particles from offset `j` to offset `j + 1`. -/
def shiftAt (j k : ℕ) (P : Multiset ℕ) : Multiset ℕ :=
  P - Multiset.replicate k j + Multiset.replicate k (j + 1)

/-- The generator of `V` under the moves of the particles of `P` alone, with
the share of the linear moment of each occupied offset. -/
def contentDrift (w : ℝ) (V : Multiset ℕ → ℝ) (P : Multiset ℕ) : ℝ :=
  ∑ j ∈ P.toFinset, (w * (V (shiftAt j 1 P) - V P) +
    (if 2 ≤ P.count j then V (shiftAt j (P.count j) P) - V P else 0) +
    WindowEight.firstMomentShare w (P.count j))

section Block
variable {L N : ℕ} [NeZero L]

/-- The price of the contents of the block of width `W` at `base`. -/
def contentValue (V : Multiset ℕ → ℝ) (base : Fin L) (W : ℕ) (x : State L N) : ℝ :=
  V (blockParticles base W x)

theorem atSite_outside_content (w : ℝ) (V : Multiset ℕ → ℝ) (base : Fin L) (W : ℕ)
    (x : State L N) (i : Fin L) (hi : ∀ j < W, base + (j : Fin L) ≠ i) (hrear : i ≠ base - 1) :
    atSite w (contentValue V base W) x i = 0 := by
  have h (k : ℕ) (hk : k ≤ occ x i) :
      contentValue V base W (move x i k hk) = contentValue V base W x := by
    unfold contentValue
    rw [blockParticles_move_outside base W x i hi hrear k hk]
  unfold atSite
  split_ifs <;> simp [h]

/-- Only the sites of the block and the site behind it can change its price. -/
theorem generator_content_eq (w : ℝ) (V : Multiset ℕ → ℝ) (base : Fin L) (W : ℕ) (hWL : W < L)
    (x : State L N) :
    generator w (contentValue V base W) x =
      (∑ j ∈ Finset.range W, atSite w (contentValue V base W) x (base + (j : Fin L))) +
        atSite w (contentValue V base W) x (base - 1) := by
  classical
  let f := atSite w (contentValue V base W) x
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
    apply atSite_outside_content w V base W x i _ hne
    intro j hj h
    exact Finset.mem_compl.mp hi (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, h⟩)
  unfold generator
  rw [← Finset.sum_add_sum_compl T f, hT, hcompl]

/-- A move inside the block shifts the moved particles by one offset. -/
theorem blockParticles_move_inside (base : Fin L) (W : ℕ) (hWL : W ≤ L) (x : State L N)
    (j : ℕ) (hj : j + 1 < W) (k : ℕ) (hk : k ≤ occ x (base + (j : Fin L))) :
    blockParticles base W (move x (base + (j : Fin L)) k hk) =
      shiftAt j k (blockParticles base W x) := by
  apply Multiset.ext.mpr
  intro i
  have hjk : k ≤ (blockParticles base W x).count j := by
    rw [count_blockParticles, if_pos (by omega)]
    exact hk
  rw [count_blockParticles, shiftAt, Multiset.count_add, Multiset.count_sub,
    Multiset.count_replicate, Multiset.count_replicate, count_blockParticles]
  by_cases hi : i < W
  · have hr : right (base + (j : Fin L)) = base + ((j + 1 : ℕ) : Fin L) := by
      rw [right_eq_add_one, Nat.cast_succ, add_assoc]
    have e1 : (base + (i : Fin L) = base + (j : Fin L)) ↔ i = j := by
      rw [add_right_inj]
      exact ⟨natCast_fin_inj (by omega) (by omega), fun h => h ▸ rfl⟩
    have e2 : (base + (i : Fin L) = base + ((j + 1 : ℕ) : Fin L)) ↔ i = j + 1 := by
      rw [add_right_inj]
      exact ⟨natCast_fin_inj (by omega) (by omega), fun h => h ▸ rfl⟩
    rw [if_pos hi, if_pos hi, occ_move]
    simp only [transfer, hr, e1, e2]
    by_cases h1 : i = j
    · subst h1; simp
    · by_cases h2 : i = j + 1
      · subst h2; simp
      · rw [if_neg h1, if_neg h2, if_neg (Ne.symm h1), if_neg (Ne.symm h2)]
  · rw [if_neg hi, if_neg hi]
    have h1 : j ≠ i := by omega
    have h2 : j + 1 ≠ i := by omega
    simp [h1, h2]

/-- Inside a block with an empty last site, the sites of the block contribute
exactly the content drift. -/
theorem sum_atSite_share_eq_contentDrift (w : ℝ) (V : Multiset ℕ → ℝ) (base : Fin L) (W : ℕ)
    (hWL : W ≤ L) (x : State L N) (hroom : ∀ j ∈ blockParticles base W x, j + 1 < W) :
    ∑ j ∈ Finset.range W, (atSite w (contentValue V base W) x (base + (j : Fin L)) +
      WindowEight.firstMomentShare w (occ x (base + (j : Fin L)))) =
      contentDrift w V (blockParticles base W x) := by
  classical
  set P := blockParticles base W x with hP
  have hcount (j : ℕ) (hj : j < W) : P.count j = occ x (base + (j : Fin L)) := by
    rw [hP, count_blockParticles, if_pos hj]
  have hsub : P.toFinset ⊆ Finset.range W := fun j hj =>
    Finset.mem_range.mpr (by have := hroom j (Multiset.mem_toFinset.mp hj); omega)
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro j hj
    have hjP := Multiset.mem_toFinset.mp hj
    have hjW := hroom j hjP
    have hc := hcount j (by omega)
    have h1 : 1 ≤ occ x (base + (j : Fin L)) := by
      rw [← hc]; exact Multiset.one_le_count_iff_mem.mpr hjP
    have hmv (k : ℕ) (hk : k ≤ occ x (base + (j : Fin L))) :
        contentValue V base W (move x (base + (j : Fin L)) k hk) = V (shiftAt j k P) := by
      unfold contentValue
      rw [blockParticles_move_inside base W hWL x j hjW k hk]
    have hcv : contentValue V base W x = V P := rfl
    unfold atSite
    rw [dif_pos h1, hmv 1 h1, hcv]
    by_cases h2 : 2 ≤ occ x (base + (j : Fin L))
    · rw [if_pos h2, if_pos (hc ▸ h2), hmv _ le_rfl, hc]
    · rw [if_neg h2, if_neg (hc ▸ h2), hc]
  · intro j hj hjP
    have hc := hcount j (Finset.mem_range.mp hj)
    have h0 : occ x (base + (j : Fin L)) = 0 := by
      rw [← hc]
      exact Multiset.count_eq_zero.mpr (fun h => hjP (Multiset.mem_toFinset.mpr h))
    simp only [atSite, dif_neg (by omega : ¬ 1 ≤ occ x (base + (j : Fin L))),
      if_neg (by omega : ¬ 2 ≤ occ x (base + (j : Fin L))), h0]
    simp [WindowEight.firstMomentShare]

/-- On a block holding more than `M` particles, a price that vanishes above `M`
can only rise through a departure from the last site. -/
theorem generator_heavy_le {w B : ℝ} (hw : 0 ≤ w) (V : Multiset ℕ → ℝ) (M : ℕ)
    (hV0 : ∀ P, 0 ≤ V P) (hVB : ∀ P, V P ≤ B) (hheavy : ∀ P, M < P.card → V P = 0)
    (base : Fin L) (n : ℕ) (x : State L N)
    (hq : M < (blockParticles base (n+1) x).card) :
    generator w (contentValue V base (n+1)) x ≤ (w + 1) * B * occupiedAt x (base + (n : Fin L)) := by
  let last : Fin L := base + n
  let F := contentValue (N := N) V base (n+1)
  have hzero : F x = 0 := hheavy _ hq
  have hB : 0 ≤ B := (hV0 ∅).trans (hVB ∅)
  have hout (i : Fin L) (hi : i ≠ last) (k : ℕ) (hk : k ≤ occ x i) : F (move x i k hk) = 0 := by
    have hd := windowMass_move (n+1) x i k hk last
    rw [← card_blockParticles_eq, ← card_blockParticles_eq, if_neg hi.symm] at hd
    apply hheavy
    have hle : ((blockParticles base (n+1) x).card : ℝ) ≤
        ((blockParticles base (n+1) (move x i k hk)).card : ℝ) := by
      split_ifs at hd <;> nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    exact hq.trans_le (by exact_mod_cast hle)
  unfold generator
  rw [Finset.sum_eq_single last]
  · change atSite w F x last ≤ _
    unfold atSite occupiedAt
    rw [hzero]
    by_cases h1 : 1 ≤ occ x last
    · rw [dif_pos h1, if_pos (by omega : 0 < occ x last)]
      have hc : F (move x last 1 h1) ≤ B := hVB _
      have hwc := mul_le_mul_of_nonneg_left hc hw
      split_ifs with h2
      · have hc2 : F (move x last (occ x last) le_rfl) ≤ B := hVB _
        linarith
      · linarith
    · rw [dif_neg h1, if_neg (by omega), if_neg (by omega : ¬ 0 < occ x last)]
      simp
  · intro i _ hi
    change atSite w F x i = 0
    unfold atSite
    split_ifs <;> simp only [hout i hi, hzero, sub_self, mul_zero, add_zero]
  · simp

open Classical in
/-- The credit of a light block whose last site is empty. -/
def creditInBlock (credit : Multiset ℕ → ℝ) (M : ℕ) (base : Fin L) (W : ℕ) (x : State L N) : ℝ :=
  if 1 ≤ (blockParticles base W x).card ∧ (blockParticles base W x).card ≤ M ∧
    occ x (base + ((W - 1 : ℕ) : Fin L)) = 0 then credit (blockParticles base W x) else 0

/-- The occupied sites of a block holding more than `M` particles. -/
def heavyOccupancyAbove (M : ℕ) (base : Fin L) (W : ℕ) (x : State L N) : ℝ :=
  if M < (blockParticles base W x).card then
    ∑ j ∈ Finset.range W, occupiedAt x (base + (j : Fin L)) else 0

theorem heavyOccupancyAbove_nonneg (M : ℕ) (base : Fin L) (W : ℕ) (x : State L N) :
    0 ≤ heavyOccupancyAbove M base W x := by
  unfold heavyOccupancyAbove
  split_ifs
  · exact Finset.sum_nonneg fun j _ => occupiedAt_nonneg x _
  · exact le_rfl

/-- The certified drift of the contents, with the boundary and heavy terms, for
one block. -/
theorem generator_content_add_share_le {w c B : ℝ} (hw : 0 < w) (V credit : Multiset ℕ → ℝ)
    (M : ℕ) (hM : 1 ≤ M) (hV0 : ∀ P, 0 ≤ V P) (hVB : ∀ P, V P ≤ B)
    (hheavy : ∀ P, M < P.card → V P = 0)
    (hcert : ∀ P : Multiset ℕ, 1 ≤ P.card → P.card ≤ M → contentDrift w V P ≤ -c * credit P)
    (base : Fin L) (W : ℕ) (hW : 1 ≤ W) (hWL : W < L) (x : State L N) :
    generator w (contentValue V base W) x + windowShare w base W x ≤
      -c * creditInBlock credit M base W x +
        (w + 1) * B * occupiedAt x (base - 1) +
        ((w + 1) * B + w) * M * occupiedAt x (base + ((W - 1 : ℕ) : Fin L)) +
        w * heavyOccupancyAbove M base W x := by
  obtain ⟨n, rfl⟩ : ∃ n, W = n + 1 := ⟨W - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  set F := contentValue (N := N) V base (n+1) with hF
  set P := blockParticles base (n+1) x with hP
  have hB : 0 ≤ B := (hV0 ∅).trans (hVB ∅)
  have hF0 : ∀ y, 0 ≤ F y := fun y => hV0 _
  have hFB : ∀ y, F y ≤ B := fun y => hVB _
  have hsite (i : Fin L) : atSite w F x i ≤ (w + 1) * B * occupiedAt x i :=
    atSite_le_of_bounds hw.le F hF0 hFB x i
  have hsplit : generator w F x =
      (∑ j ∈ Finset.range (n+1), atSite w F x (base + (j : Fin L))) + atSite w F x (base - 1) :=
    generator_content_eq w V base (n+1) hWL x
  have hprev0 := occupiedAt_nonneg x (base - 1)
  have hlast0 := occupiedAt_nonneg x (base + (n : Fin L))
  have hrear := hsite (base - 1)
  have hshare := windowShare_le w base (n+1) x
  have hocc := sum_occupiedAt_le_card base (n+1) x
  have hM0 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hwB : 0 ≤ (w + 1) * B := mul_nonneg (by linarith) hB
  have hcoef0 : 0 ≤ (w + 1) * B + w := by linarith
  have hcoef : (w + 1) * B ≤ ((w + 1) * B + w) * M :=
    calc (w + 1) * B ≤ ((w + 1) * B + w) * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hM0 hcoef0
  have hrear0 : 0 ≤ (w + 1) * B * occupiedAt x (base - 1) := mul_nonneg hwB hprev0
  have hlastc : 0 ≤ ((w + 1) * B + w) * M * occupiedAt x (base + (n : Fin L)) :=
    mul_nonneg (mul_nonneg hcoef0 (by linarith)) hlast0
  by_cases hq : M < P.card
  · have hg := generator_heavy_le hw.le V M hV0 hVB hheavy base n x hq
    have hc0 : creditInBlock credit M base (n+1) x = 0 := by
      unfold creditInBlock
      rw [← hP, if_neg (by omega)]
    have hh : heavyOccupancyAbove M base (n+1) x =
        ∑ j ∈ Finset.range (n+1), occupiedAt x (base + (j : Fin L)) := if_pos hq
    have hexit : (w + 1) * B * occupiedAt x (base + (n : Fin L)) ≤
        ((w + 1) * B + w) * M * occupiedAt x (base + (n : Fin L)) :=
      mul_le_mul_of_nonneg_right hcoef hlast0
    rw [hc0, hh]
    linarith
  · have hh : heavyOccupancyAbove M base (n+1) x = 0 := if_neg hq
    rw [hh]
    by_cases hlast : occ x (base + (n : Fin L)) = 0
    · by_cases h0 : P.card = 0
      · have hempty (j : ℕ) (hj : j < n+1) : occ x (base + (j : Fin L)) = 0 := by
          have hc := congrArg (Multiset.count j) (Multiset.card_eq_zero.mp h0)
          rw [hP, count_blockParticles, if_pos hj] at hc
          simpa using hc
        have hin : ∑ j ∈ Finset.range (n+1), atSite w F x (base + (j : Fin L)) = 0 :=
          Finset.sum_eq_zero fun j hj => by
            have h := hempty j (Finset.mem_range.mp hj)
            simp only [atSite, dif_neg (by omega : ¬ 1 ≤ occ x (base + (j : Fin L))),
              if_neg (by omega : ¬ 2 ≤ occ x (base + (j : Fin L))), add_zero]
        have hsh : windowShare w base (n+1) x = 0 :=
          Finset.sum_eq_zero fun j hj => by
            rw [hempty j (Finset.mem_range.mp hj)]
            simp [WindowEight.firstMomentShare]
        have hc0 : creditInBlock credit M base (n+1) x = 0 := by
          unfold creditInBlock
          rw [← hP, if_neg (by omega)]
        rw [hsplit, hin, hsh, hc0]
        linarith
      · have hroom (j : ℕ) (hj : j ∈ P) : j + 1 < n + 1 := by
          have hc := Multiset.count_pos.mpr hj
          rw [hP, count_blockParticles] at hc
          split_ifs at hc with hjW
          · have : j ≠ n := by
              rintro rfl
              rw [hlast] at hc
              omega
            omega
          · omega
        have hdrift := sum_atSite_share_eq_contentDrift w V base (n+1) hWL.le x hroom
        have hcert' := hcert P (by omega) (by omega)
        have hc1 : creditInBlock credit M base (n+1) x = credit P := by
          unfold creditInBlock
          rw [← hP, Nat.add_sub_cancel, if_pos ⟨by omega, by omega, hlast⟩]
        have htotal : generator w F x + windowShare w base (n+1) x =
            contentDrift w V P + atSite w F x (base - 1) := by
          rw [hsplit, ← hdrift]
          unfold windowShare
          rw [Finset.sum_add_distrib]
          ring
        rw [htotal, hc1]
        linarith
    · have hlast1 : occupiedAt x (base + (n : Fin L)) = 1 := by
        unfold occupiedAt
        rw [if_pos (Nat.pos_of_ne_zero hlast)]
      have hc0 : creditInBlock credit M base (n+1) x = 0 := by
        unfold creditInBlock
        rw [← hP, Nat.add_sub_cancel, if_neg (fun h => hlast h.2.2)]
      have hcardM : ∑ j ∈ Finset.range (n+1), occupiedAt x (base + (j : Fin L)) ≤ M :=
        hocc.trans (by exact_mod_cast (by omega : P.card ≤ M))
      have hin : ∑ j ∈ Finset.range (n+1), atSite w F x (base + (j : Fin L)) ≤
          (w + 1) * B * M :=
        calc _ ≤ ∑ j ∈ Finset.range (n+1), (w + 1) * B * occupiedAt x (base + (j : Fin L)) :=
              Finset.sum_le_sum fun j _ => hsite _
          _ = (w + 1) * B * ∑ j ∈ Finset.range (n+1), occupiedAt x (base + (j : Fin L)) := by
              rw [Finset.mul_sum]
          _ ≤ (w + 1) * B * M := mul_le_mul_of_nonneg_left hcardM hwB
      have hsh : windowShare w base (n+1) x ≤ w * M :=
        hshare.trans (mul_le_mul_of_nonneg_left hcardM hw.le)
      rw [hsplit, hlast1, hc0]
      linarith

end Block

/-! ## Summing over all bases -/

section Ring
variable {L N : ℕ} [NeZero L]

theorem sum_generator_content_le {w c B : ℝ} (hw : 0 < w) (V credit : Multiset ℕ → ℝ)
    (M : ℕ) (hM : 1 ≤ M) (hV0 : ∀ P, 0 ≤ V P) (hVB : ∀ P, V P ≤ B)
    (hheavy : ∀ P, M < P.card → V P = 0)
    (hcert : ∀ P : Multiset ℕ, 1 ≤ P.card → P.card ≤ M → contentDrift w V P ≤ -c * credit P)
    (W : ℕ) (hW : 1 ≤ W) (hWL : W < L) (x : State L N) :
    (∑ base : Fin L, generator w (contentValue V base W) x) +
      (W : ℝ) * (w * occupiedCount x - singleCount x) ≤
    -c * (∑ base : Fin L, creditInBlock credit M base W x) +
      (((w + 1) * B + w) * M + (w + 1) * B) * occupiedCount x +
      w * ∑ base : Fin L, heavyOccupancyAbove M base W x := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun base _ =>
    generator_content_add_share_le hw V credit M hM hV0 hVB hheavy hcert base W hW hWL x
  rw [Finset.sum_add_distrib, sum_windowShare] at h
  have e : ∑ b : Fin L, (-c * creditInBlock credit M b W x +
        (w + 1) * B * occupiedAt x (b - 1) +
        ((w + 1) * B + w) * M * occupiedAt x (b + ((W - 1 : ℕ) : Fin L)) +
        w * heavyOccupancyAbove M b W x) =
      -c * (∑ b : Fin L, creditInBlock credit M b W x) +
        (w + 1) * B * (∑ b : Fin L, occupiedAt x (b - 1)) +
        ((w + 1) * B + w) * M * (∑ b : Fin L, occupiedAt x (b + ((W - 1 : ℕ) : Fin L))) +
        w * ∑ b : Fin L, heavyOccupancyAbove M b W x := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [e, sum_occupiedAt_sub_one, sum_occupiedAt_shift] at h
  linarith

/-- **Summed stationary bound for any certified content price.** No majority
assumption is used. -/
theorem stationary_contentBlocks_le {w c B : ℝ} (hw : 0 < w) (V credit : Multiset ℕ → ℝ)
    (M : ℕ) (hM : 1 ≤ M) (hV0 : ∀ P, 0 ≤ V P) (hVB : ∀ P, V P ≤ B)
    (hheavy : ∀ P, M < P.card → V P = 0)
    (hcert : ∀ P : Multiset ℕ, 1 ≤ P.card → P.card ≤ M → contentDrift w V P ≤ -c * credit P)
    (μ : StationaryLaw L N w) (W : ℕ) (hW : 1 ≤ W) (hWL : W < L) :
    c * (∑ x, μ.weight x * ∑ base : Fin L, creditInBlock credit M base W x) +
      (W : ℝ) * (∑ x, μ.weight x * (w * occupiedCount x - singleCount x)) ≤
    (((w + 1) * B + w) * M + (w + 1) * B) * (∑ x, μ.weight x * occupiedCount x) +
      w * (∑ x, μ.weight x * ∑ base : Fin L, heavyOccupancyAbove M base W x) := by
  set G := fun x : State L N => ∑ base : Fin L, generator w (contentValue V base W) x
  have hinv : ∑ x, μ.weight x * G x = 0 := by
    simp only [G, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun base _ => μ.invariant _
  have h := Finset.sum_le_sum (s := Finset.univ) fun x _ =>
    mul_le_mul_of_nonneg_left
      (sum_generator_content_le hw V credit M hM hV0 hVB hheavy hcert W hW hWL x) (μ.nonneg x)
  have eL : ∑ x, μ.weight x * (G x + (W : ℝ) * (w * occupiedCount x - singleCount x)) =
      ∑ x, μ.weight x * G x +
        (W : ℝ) * (∑ x, μ.weight x * (w * occupiedCount x - singleCount x)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have eR : ∑ x, μ.weight x * (-c * (∑ base : Fin L, creditInBlock credit M base W x) +
        (((w + 1) * B + w) * M + (w + 1) * B) * occupiedCount x +
        w * ∑ base : Fin L, heavyOccupancyAbove M base W x) =
      -c * (∑ x, μ.weight x * ∑ base : Fin L, creditInBlock credit M base W x) +
        (((w + 1) * B + w) * M + (w + 1) * B) * (∑ x, μ.weight x * occupiedCount x) +
        w * (∑ x, μ.weight x * ∑ base : Fin L, heavyOccupancyAbove M base W x) := by
    calc
      _ = ∑ x, (-c * (μ.weight x * ∑ base : Fin L, creditInBlock credit M base W x) +
            (((w + 1) * B + w) * M + (w + 1) * B) * (μ.weight x * occupiedCount x) +
            w * (μ.weight x * ∑ base : Fin L, heavyOccupancyAbove M base W x)) :=
        Finset.sum_congr rfl fun x _ => by ring
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  change ∑ x, μ.weight x * (G x + _) ≤ _ at h
  rw [eL, eR, hinv] at h
  linarith

end Ring

/-! ## Certificates by mass

Moves inside a block never change its number of particles. The drift of a
content of `m` particles therefore involves the price only on contents of `m`
particles, and certificates can be proved one mass at a time. -/

theorem card_shiftAt (j k : ℕ) (P : Multiset ℕ) (hk : k ≤ P.count j) :
    (shiftAt j k P).card = P.card := by
  have hle : Multiset.replicate k j ≤ P := Multiset.le_count_iff_replicate_le.mp hk
  have hkP : k ≤ P.card := by
    simpa using Multiset.card_le_card hle
  rw [shiftAt, Multiset.card_add, Multiset.card_sub hle, Multiset.card_replicate,
    Multiset.card_replicate]
  omega

/-- The content drift of `P` depends only on the price of contents with as many
particles as `P`. -/
theorem contentDrift_congr {w : ℝ} {V V' : Multiset ℕ → ℝ} (P : Multiset ℕ)
    (h : ∀ Q : Multiset ℕ, Q.card = P.card → V Q = V' Q) :
    contentDrift w V P = contentDrift w V' P := by
  unfold contentDrift
  apply Finset.sum_congr rfl
  intro j hj
  have h1 : 1 ≤ P.count j := Multiset.one_le_count_iff_mem.mpr (Multiset.mem_toFinset.mp hj)
  rw [h _ (card_shiftAt j 1 P h1), h P rfl, h _ (card_shiftAt j _ P le_rfl)]

/-- A price assembled from one price for each number of particles. -/
def levelPrice (Vs : ℕ → Multiset ℕ → ℝ) (P : Multiset ℕ) : ℝ := Vs P.card P

theorem contentDrift_levelPrice (w : ℝ) (Vs : ℕ → Multiset ℕ → ℝ) (P : Multiset ℕ) :
    contentDrift w (levelPrice Vs) P = contentDrift w (Vs P.card) P :=
  contentDrift_congr P fun Q hQ => by simp only [levelPrice, hQ]

/-- **Summed bound from certificates proved mass by mass.** Each mass `m` from
`1` to `M` has its own price `Vs m`, bounded by `B` on contents of `m`
particles, and its own credit `credits m`. -/
theorem stationary_levelBlocks_le {L N : ℕ} [NeZero L] {w B : ℝ} (hw : 0 < w)
    (Vs credits : ℕ → Multiset ℕ → ℝ) (M : ℕ) (hM : 1 ≤ M)
    (hV0 : ∀ P : Multiset ℕ, P.card ≤ M → 0 ≤ Vs P.card P)
    (hVB : ∀ P : Multiset ℕ, P.card ≤ M → Vs P.card P ≤ B)
    (hcert : ∀ P : Multiset ℕ, 1 ≤ P.card → P.card ≤ M →
      contentDrift w (Vs P.card) P ≤ -credits P.card P)
    (μ : StationaryLaw L N w) (W : ℕ) (hW : 1 ≤ W) (hWL : W < L) :
    (∑ x, μ.weight x * ∑ base : Fin L,
        creditInBlock (fun P => credits P.card P) M base W x) +
      (W : ℝ) * (∑ x, μ.weight x * (w * occupiedCount x - singleCount x)) ≤
    (((w + 1) * B + w) * M + (w + 1) * B) * (∑ x, μ.weight x * occupiedCount x) +
      w * (∑ x, μ.weight x * ∑ base : Fin L, heavyOccupancyAbove M base W x) := by
  classical
  let V : Multiset ℕ → ℝ := levelPrice fun m P => if m ≤ M then Vs m P else 0
  have hB0 : 0 ≤ B := (hV0 0 (by simp)).trans (hVB 0 (by simp))
  have h0 : ∀ P, 0 ≤ V P := fun P => by
    simp only [V, levelPrice]
    split_ifs with h
    · exact hV0 P h
    · exact le_rfl
  have hB : ∀ P, V P ≤ B := fun P => by
    simp only [V, levelPrice]
    split_ifs with h
    · exact hVB P h
    · exact hB0
  have hheavy : ∀ P : Multiset ℕ, M < P.card → V P = 0 := fun P hP => by
    simp only [V, levelPrice, if_neg (not_le.mpr hP)]
  have hc : ∀ P : Multiset ℕ, 1 ≤ P.card → P.card ≤ M →
      contentDrift w V P ≤ -1 * (fun P : Multiset ℕ => credits P.card P) P := by
    intro P h1 hM'
    rw [contentDrift_levelPrice, neg_one_mul,
      show (fun Q => if P.card ≤ M then Vs P.card Q else 0) = Vs P.card from
        funext fun Q => if_pos hM']
    exact hcert P h1 hM'
  have h := stationary_contentBlocks_le (c := 1) hw V _ M hM h0 hB hheavy hc μ W hW hWL
  simpa only [one_mul] using h

/-! ## The variable-radius prices as a content price -/

/-- A price on groups extended to contents of at most three particles. -/
def groupContentPrice (V : Group → ℝ) (P : Multiset ℕ) : ℝ := listValue V (P.sort (· ≤ ·))

theorem contentValue_groupContentPrice {L N : ℕ} [NeZero L] (V : Group → ℝ) (base : Fin L)
    (W : ℕ) : contentValue (N := N) (groupContentPrice V) base W = blockValue V base W := rfl

private theorem groupContentPrice_coe (V : Group → ℝ) (l : List ℕ) (hl : l.Sorted (· ≤ ·)) :
    groupContentPrice V (l : Multiset ℕ) = listValue V l := by
  rw [groupContentPrice, Multiset.coe_sort, List.mergeSort_eq_self _ hl]

/-- Moving particles commutes with a common translation. -/
theorem shiftAt_map_add (a k o : ℕ) (Q : Multiset ℕ) :
    shiftAt (a + o) k (Q.map (· + o)) = (shiftAt a k Q).map (· + o) := by
  apply Multiset.ext.mpr
  intro i
  have hinj : Function.Injective (· + o : ℕ → ℕ) := add_left_injective o
  by_cases hi : o ≤ i
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + o := ⟨i - o, by omega⟩
    have e (R : Multiset ℕ) : (R.map (· + o)).count (j + o) = R.count j :=
      Multiset.count_map_eq_count' _ _ hinj _
    simp only [shiftAt, Multiset.count_add, Multiset.count_sub, Multiset.count_replicate, e]
    by_cases h1 : a = j <;> by_cases h2 : a + 1 = j <;> simp [h1, h2] <;> omega
  · have hz (R : Multiset ℕ) : (R.map (· + o)).count i = 0 :=
      Multiset.count_eq_zero.mpr (by simp only [Multiset.mem_map, not_exists, not_and]; omega)
    simp only [shiftAt, Multiset.count_add, Multiset.count_sub, Multiset.count_replicate, hz]
    rw [if_neg (by omega), if_neg (by omega)]

private theorem shiftAt_after (s : Slice) (k : ℕ) (hk : k ≤ s.mass) :
    shiftAt s.site k (s.after 0 : Multiset ℕ) = (s.after k : Multiset ℕ) := by
  apply Multiset.ext.mpr
  intro i
  simp only [shiftAt, Multiset.count_add, Multiset.count_sub, Multiset.count_replicate,
    Multiset.coe_count]
  rw [count_after s k i hk]
  by_cases h1 : s.site = i
  · subst h1
    simp
  · by_cases h2 : s.site + 1 = i
    · subst h2
      simp
    · rw [if_neg h1, if_neg h2, if_neg (Ne.symm h1), if_neg (Ne.symm h2)]

/-- The content drift of a translated group is the drift of `VariableWindow`. -/
theorem contentDrift_positions (w : ℝ) (V : Group → ℝ) (g : Group) (o : ℕ) :
    contentDrift w (groupContentPrice V) ((g.positions.map (· + o)) : Multiset ℕ) =
      drift w V g := by
  classical
  set P : Multiset ℕ := ((g.positions.map (· + o)) : Multiset ℕ) with hP
  obtain ⟨hnd, hmem⟩ := slice_sites g
  let l := (g.slices.map (·.site)).map (· + o)
  have hndl : l.Nodup := hnd.map (add_left_injective o)
  have hfin : P.toFinset = l.toFinset := by
    ext j
    simp only [hP, Multiset.mem_toFinset, Multiset.mem_coe, List.mem_toFinset, l,
      List.mem_map, hmem]
  rw [← sum_slice_drift, contentDrift, hfin, List.sum_toFinset _ hndl]
  simp only [l, List.map_map]
  congr 1
  apply List.map_congr_left
  intro s hs
  obtain ⟨hbefore, hpos, hspan, hcount, hsorted⟩ := slice_facts g s hs
  have hPs : P = ((s.after 0).map (· + o) : Multiset ℕ) := by rw [hP, hbefore]
  have hc : P.count (s.site + o) = s.mass := by
    rw [hP, Multiset.coe_count, List.count_map_of_injective _ _ (add_left_injective o),
      ← hbefore, hcount]
  have hval (k : ℕ) (hk : k ≤ s.mass) :
      groupContentPrice V (shiftAt (s.site + o) k P) = listValue V (s.after k) := by
    have e : shiftAt (s.site + o) k P = (((s.after k).map (· + o)) : Multiset ℕ) := by
      rw [hPs, ← Multiset.map_coe, shiftAt_map_add, shiftAt_after s k hk, Multiset.map_coe]
    rw [e, groupContentPrice_coe V _
      (List.pairwise_map.mpr ((hsorted k hk).imp fun h => Nat.add_le_add_right h o)),
      listValue_map_add]
  have hv0 : groupContentPrice V P = listValue V (s.after 0) := by
    have h := hval 0 (Nat.zero_le _)
    simpa [shiftAt] using h
  simp only [Function.comp, Slice.drift]
  rw [hc, hval 1 hpos, hv0]
  by_cases h2 : 2 ≤ s.mass
  · rw [if_pos h2, if_pos h2, hval _ le_rfl]
  · rw [if_neg h2, if_neg h2]

/-- Contents of one to three particles are translated groups. -/
theorem exists_group_of_card (P : Multiset ℕ) (h1 : 1 ≤ P.card) (h3 : P.card ≤ 3) :
    ∃ g : Group, ∃ o : ℕ, P = ((g.positions.map (· + o)) : Multiset ℕ) := by
  have hsort := Multiset.sort_eq (· ≤ ·) P
  have hsorted := Multiset.sort_sorted (· ≤ ·) P
  have hlen : (P.sort (· ≤ ·)).length = P.card := Multiset.length_sort _
  generalize P.sort (· ≤ ·) = l at hsort hsorted hlen
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
  · simp at hlen; omega
  · exact ⟨.one, a, by rw [← hsort]; simp [Group.positions]⟩
  · simp [List.Sorted] at hsorted
    refine ⟨.two (b - a), a, ?_⟩
    rw [← hsort]
    congr 1
    simp [Group.positions]
    omega
  · simp [List.Sorted] at hsorted
    refine ⟨.three (b - a) (c - b), a, ?_⟩
    rw [← hsort]
    congr 1
    simp [Group.positions]
    omega
  · simp at hlen; omega

open Classical in
/-- Credit for a content of three particles on one site. -/
def bareCredit (P : Multiset ℕ) : ℝ :=
  if ∃ o : ℕ, P = (([o, o, o] : List ℕ) : Multiset ℕ) then 1 else 0

/-- `VariableWindow` satisfies the hypotheses of the generic bound with
`M = 3`, credit `1/64` per bare triple and bound `priceBound w`. -/
theorem variableWindow_content_certificate {w : ℝ} (hw : 0 < w) (hs : w ≤ 1/32) :
    (∀ P, 0 ≤ groupContentPrice (price w (radius w) (1/w)) P) ∧
    (∀ P, groupContentPrice (price w (radius w) (1/w)) P ≤ priceBound w) ∧
    (∀ P : Multiset ℕ, 3 < P.card → groupContentPrice (price w (radius w) (1/w)) P = 0) ∧
    (∀ P : Multiset ℕ, 1 ≤ P.card → P.card ≤ 3 →
      contentDrift w (groupContentPrice (price w (radius w) (1/w))) P ≤
        -(1/64) * bareCredit P) := by
  refine ⟨fun P => ?_, fun P => ?_, fun P hP => ?_, fun P h1 h3 => ?_⟩
  · unfold groupContentPrice
    generalize P.sort (· ≤ ·) = p
    rcases p with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;> simp only [listValue] <;>
      first | exact le_rfl | exact price_nonneg hw _
  · unfold groupContentPrice
    generalize P.sort (· ≤ ·) = p
    rcases p with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
      first | apply price_le_priceBound hw |
        exact (price_nonneg hw .one).trans (price_le_priceBound hw .one)
  · exact listValue_zero_of_mass _ (Or.inr (by rw [Multiset.length_sort]; exact hP))
  · obtain ⟨g, o, rfl⟩ := exists_group_of_card P h1 h3
    rw [contentDrift_positions]
    have hcert := smallRate_drift_le hw hs g
    unfold bareCredit
    split_ifs with hb
    · obtain ⟨o2, ho2⟩ := hb
      rw [if_pos (eq_bare_of_positions g o o2 ho2)] at hcert
      linarith
    · split_ifs at hcert <;> linarith

/-- The summed bound of `WindowSum`, recovered from the generic theorem. -/
theorem stationary_variableWindow_contentBlocks_le {L N : ℕ} [NeZero L] {w : ℝ} (hw : 0 < w)
    (hs : w ≤ 1/32) (μ : StationaryLaw L N w) (W : ℕ) (hW : 1 ≤ W) (hWL : W < L) :
    (1/64) * (∑ x, μ.weight x * ∑ base : Fin L, creditInBlock bareCredit 3 base W x) +
      (W : ℝ) * (∑ x, μ.weight x * (w * occupiedCount x - singleCount x)) ≤
    (((w + 1) * priceBound w + w) * 3 + (w + 1) * priceBound w) *
        (∑ x, μ.weight x * occupiedCount x) +
      w * (∑ x, μ.weight x * ∑ base : Fin L, heavyOccupancyAbove 3 base W x) := by
  obtain ⟨h0, hB, hheavy, hcert⟩ := variableWindow_content_certificate hw hs
  have h := stationary_contentBlocks_le (c := 1/64) hw _ bareCredit 3 (by norm_num) h0 hB hheavy
    (fun P h1 h3 => by simpa using hcert P h1 h3) μ W hW hWL
  simpa using h

end
end Chipping.ContentWindow

