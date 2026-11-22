# Proving small-rate supercondensation in Lean

The conjecture concerns a ring at **fixed positive particle density**. For sufficiently small fixed chipping rate, does a single pile carry an asymptotically full fraction of the stationary mass? This guide contains the full Lean 4 formalisation, a reproducible project setup, and a first finite-volume identity to prove.

## 1. The precise claim

On a periodic ring with $L\ge 3$ sites and exactly $N$ particles, write $\eta_i$ for the mass at site $i$. All jumps go from $i$ to $i+1\pmod L$.

| Departure mass | Mass sent to the right | Rate |
|---|---:|---:|
| $0$ | No jump | $0$ |
| $1$ | $1$ | $w$ |
| $m\ge2$ | $1$ | $w$ |
| $m\ge2$ | $m$ | $1$ |

Let $M(\eta)=\max_i\eta_i$ and $B(\eta)=N-M(\eta)$. Ties have no effect on $B$. The conjecture is that there exists one $w_0\in(0,1]$ such that, for each fixed $0<w<w_0$, each $\rho>0$, each sequence $L_n\to\infty$ with $N_n/L_n\to\rho$, and each choice of stationary laws $\mu_n$ on those rings,

$$
\forall\varepsilon>0,\qquad \mu_n\!\left(B/N_n\ge\varepsilon\right)\longrightarrow 0.
$$

The choice of $w_0$ is independent of $\rho$. The statement leaves its value open. A proof at $N/L^2\to\infty$, or one that lets $w$ decrease with $L$, would address a different limit.

**What remains to prove.** The Lean declaration `SmallWSupercondensation` names a proposition. To prove it, one must supply a positive interval of rates, stationary-law existence on every finite ring in that interval, and the limit above. The checked theorem `tails_vanish_iff_mean_vanishes` reduces the limit to $\mathbb E_{\mu_n}[B/N_n]\to0$. Since $N_n/L_n\to\rho>0$, the research target can equivalently be written $\mathbb E_{\mu_n}[B]=o(L_n)$. This permits a diverging sublinear background.

## 2. Start a local project

Use a fresh directory, Git, and a Lean installation managed by Elan. The commands below use a POSIX shell. Save this Markdown file in the directory as `ChippingProofStarter.md`. The configuration pins Lean and mathlib to the versions used to check the formalisation. [Lean project setup](https://leanprover-community.github.io/install/project.html)

```sh
git init
printf '%s\n' 'leanprover/lean4:v4.19.0' > lean-toolchain
cat > lakefile.toml <<'TOML'
name = "chipping"
version = "0.1.0"
defaultTargets = ["ChippingSupercondensation"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.19.0"

[[lean_lib]]
name = "ChippingSupercondensation"
TOML

awk '/^```lean$/{p=1;next} p && /^```$/{exit} p' \
  ChippingProofStarter.md > ChippingSupercondensation.lean
lake update
lake exe cache get
lake build
```

The extraction command takes the complete Lean block in section 5. For a quick check after editing, run `lake env lean ChippingSupercondensation.lean`. Run `lake build` to refresh the compiled module before importing it from another file.

## 3. First proof session — occupied-site balance

Start with a finite identity that exercises both movement rules. Let $K$ count occupied sites and $D$ count sites of mass at least two. Let $A$ count directed bonds with both ends occupied and $C$ count directed bonds whose left site has mass at least two and whose right site is occupied. Each site contributes exactly one outgoing bond, including the wraparound bond.

**Target for every configuration.** With $Q$ the existing generator, prove
$$
(QK)(\eta)=wD(\eta)-wA(\eta)-C(\eta).
$$

The local computation is small enough to check by hand. Each entry is the change in $K$ after the indicated jump.

| Departure mass | Right neighbour | Chip | Whole-pile move |
|---|---|---:|---:|
| $1$ | Empty | $0$ | Inactive |
| $1$ | Occupied | $-1$ | Inactive |
| $\ge2$ | Empty | $+1$ | $0$ |
| $\ge2$ | Occupied | $0$ | $-1$ |

For Lean, define the four counts as real-valued sums of indicators so that `generator w K` has the right type and subtraction keeps its sign. First prove that `right i ≠ i` when $L\ge3$. For a move, every occupancy indicator away from these two sites cancels in the difference. Split on the source mass and destination occupancy, prove the local formula for `atSite`, and sum over $i$. For the stationary corollary, apply `μ.invariant K`, substitute the statewise identity and distribute the finite sum. The result is
$$
w\,\mathbb E_\mu[D]=w\,\mathbb E_\mu[A]+\mathbb E_\mu[C].
$$

**First prompt for Codex CLI.** Start `codex` in the project directory and paste the following.

> Read sections 1 and 3 of ChippingProofStarter.md. Extend ChippingSupercondensation.lean inside namespace Chipping. Define the four counts exactly as specified. Using the existing moves and generator, prove the statewise occupied-site balance for every ring with at least three sites. Derive its stationary corollary from StationaryLaw.invariant. Use no sorry or new axioms. Run lake build and report the theorem names and any remaining goals.

## 4. From a count identity to a mass estimate

The occupied-site identity is a first check on the generator. Two nonadjacent piles can each contain $N/2$ particles while $K=D=2$ and $A=C=0$ (for $N\ge4$ even and $L\ge4$). Small counts alone cannot bound $B$.

A mass-sensitive next observable is the probability that two particles sampled independently **with replacement** occupy different sites. For $N>0$, write $p_i=\eta_i/N$ and define $H=1-\sum_i p_i^2$. There is an elementary next Lean lemma,
$$
\frac{B}{N}\;\le\;H\;\le\;2\frac{B}{N}.
$$
Indeed, if $m=\max_i p_i$, then $m^2\le\sum_i p_i^2\le m\sum_i p_i=m$. Thus $1-m\le H\le(1-m)(1+m)$. Proving $\mathbb E[H]\to0$ would suffice and would also control mass dispersed over many small piles. This comparison is a proposed extension to the code below. The dynamical estimate on $H$ remains open.

A concrete generator calculation for this route is to set $S_2=\sum_i\eta_i^2$. Moving $k$ particles from a site of mass $a$ to its neighbour of mass $b$ changes $S_2$ by $2k(b-a+k)$. A whole-pile move therefore contributes $2ab$ and a chip contributes $2(b-a+1)$ before multiplication by its rate. These expressions give an exact stationary identity to investigate. A proof of supercondensation still needs an estimate uniform along the prescribed thermodynamic sequences.

## 5. Complete Lean formalisation

The block below is the checked baseline. It contains the conservative generator, stationarity, both tail/mean inequalities, their limiting equivalence, and the open conjecture. The additional targets in sections 3 and 4 are future work.

```lean
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Supercondensation for the totally asymmetric chipping process

Lean 4 and mathlib v4.19.0. Inside a project with that mathlib release, run
`lake env lean ChippingSupercondensation.lean`.

The ring has L sites and exactly N particles. Every occupied site chips one
particle to its right at rate w. A site with at least two particles also moves
its entire pile to the right at rate one.

The final declaration is an open proposition. The preceding lemmas verify the
conservative dynamics and two finite-volume estimates for its order parameter.
-/

namespace Chipping

open Filter
open scoped BigOperators Topology

noncomputable section

/-- A finite state space. The subtype enforces the canonical mass constraint. -/
abbrev State (L N : ℕ) :=
  {x : Fin L → Fin (N + 1) // ∑ i, (x i).val = N}

def occ {L N : ℕ} (x : State L N) (i : Fin L) : ℕ := (x.val i).val

def right {L : ℕ} (i : Fin L) : Fin L :=
  ⟨(i.val + 1) % L, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- Move k particles in the ambient natural-valued configuration. -/
def transfer {L : ℕ} (x : Fin L → ℕ) (i : Fin L) (k : ℕ) (j : Fin L) : ℕ :=
  (x j - (if j = i then k else 0)) + (if j = right i then k else 0)

theorem transfer_conserves {L : ℕ} (x : Fin L → ℕ) (i : Fin L) (k : ℕ)
    (hk : k ≤ x i) : ∑ j, transfer x i k j = ∑ j, x j := by
  have restore (j : Fin L) :
      (x j - (if j = i then k else 0)) + (if j = i then k else 0) = x j := by
    by_cases h : j = i
    · subst j
      simpa using Nat.sub_add_cancel hk
    · simp [h]
  calc
    ∑ j, transfer x i k j
        = ∑ j, ((x j - (if j = i then k else 0)) +
                  (if j = i then k else 0)) := by simp [transfer, Finset.sum_add_distrib]
    _ = ∑ j, x j := by simp_rw [restore]

/-- The generator can only call this move with k particles available. -/
def move {L N : ℕ} (x : State L N) (i : Fin L) (k : ℕ) (hk : k ≤ occ x i) :
    State L N := by
  let y := transfer (occ x) i k
  have hsum : ∑ j, y j = N := (transfer_conserves _ _ _ hk).trans x.property
  have hbound (j : Fin L) : y j ≤ N := by
    rw [← hsum]
    exact Finset.single_le_sum (fun t _ => Nat.zero_le (y t)) (Finset.mem_univ j)
  exact ⟨fun j => ⟨y j, Nat.lt_succ_of_le (hbound j)⟩, hsum⟩

/-- The contribution of the two possible departures from site i to Q f. -/
def atSite {L N : ℕ} (w : ℝ) (f : State L N → ℝ) (x : State L N) (i : Fin L) : ℝ :=
  (if h : 1 ≤ occ x i then w * (f (move x i 1 h) - f x) else 0) +
  (if 2 ≤ occ x i then f (move x i (occ x i) le_rfl) - f x else 0)

theorem singleton_atSite {L N : ℕ} (w : ℝ) (f : State L N → ℝ)
    (x : State L N) (i : Fin L) (h : occ x i = 1) :
    atSite w f x i = w * (f (move x i 1 (by omega)) - f x) := by
  have h₁ : 1 ≤ occ x i := by omega
  have h₂ : ¬ 2 ≤ occ x i := by omega
  simp [atSite, h₁, h₂]

def generator {L N : ℕ} (w : ℝ) (f : State L N → ℝ) (x : State L N) : ℝ :=
  ∑ i, atSite w f x i

/-- A stationary probability vector on the canonical sector, in weak form. -/
structure StationaryLaw (L N : ℕ) (w : ℝ) where
  weight : State L N → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  normalized : ∑ x, weight x = 1
  invariant : ∀ f : State L N → ℝ, ∑ x, weight x * generator w f x = 0

def largest {L N : ℕ} (x : State L N) : ℕ := Finset.univ.sup (occ x)

/-- The fraction of all particles outside one largest pile. Ties need no choice.
At N = 0 Lean's real division gives zero. Positive limiting density excludes
zero total mass eventually. -/
def backgroundFraction {L N : ℕ} (x : State L N) : ℝ :=
  ((N - largest x : ℕ) : ℝ) / (N : ℝ)

theorem backgroundFraction_nonneg {L N : ℕ} (x : State L N) :
    0 ≤ backgroundFraction x := by
  unfold backgroundFraction
  positivity

theorem backgroundFraction_le_one {L N : ℕ} (x : State L N) :
    backgroundFraction x ≤ 1 := by
  cases N with
  | zero => simp [backgroundFraction]
  | succ n =>
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((n+1 : ℕ) : ℝ))).2
    rw [one_mul]
    exact_mod_cast Nat.sub_le (n+1) (largest x)

def meanBackground {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) : ℝ :=
  ∑ x, μ.weight x * backgroundFraction x

def backgroundTail {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w) (ε : ℝ) : ℝ :=
  ∑ x, if ε ≤ backgroundFraction x then μ.weight x else 0

/-- Markov's inequality for the missing mass fraction, in product form. -/
theorem threshold_mul_tail_le_mean {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w)
    (ε : ℝ) : ε * backgroundTail μ ε ≤ meanBackground μ := by
  unfold backgroundTail meanBackground
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases h : ε ≤ backgroundFraction x
  · simpa [h, mul_comm ε] using mul_le_mul_of_nonneg_left h (μ.nonneg x)
  · simpa [h] using mul_nonneg (μ.nonneg x) (backgroundFraction_nonneg x)

/-- The converse estimate uses the deterministic bound B/N ≤ 1. -/
theorem mean_le_threshold_add_tail {L N : ℕ} {w : ℝ} (μ : StationaryLaw L N w)
    {ε : ℝ} (hε : 0 ≤ ε) : meanBackground μ ≤ ε + backgroundTail μ ε := by
  calc
    meanBackground μ ≤ ∑ x, (μ.weight x * ε +
        (if ε ≤ backgroundFraction x then μ.weight x else 0)) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases h : ε ≤ backgroundFraction x
      · simp only [if_pos h]
        have hle : μ.weight x * backgroundFraction x ≤ μ.weight x := by
          simpa using mul_le_mul_of_nonneg_left (backgroundFraction_le_one x) (μ.nonneg x)
        exact hle.trans (le_add_of_nonneg_left (mul_nonneg (μ.nonneg x) hε))
      · simp only [if_neg h, add_zero]
        exact mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge h)) (μ.nonneg x)
    _ = ε + backgroundTail μ ε := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, μ.normalized, one_mul]
      rfl

/-- A stationary first-moment estimate is exactly sufficient for the
probability formulation, along any sequence of rings and masses. -/
theorem tails_vanish_iff_mean_vanishes {L N : ℕ → ℕ} {w : ℝ}
    (μ : (n : ℕ) → StationaryLaw (L n) (N n) w) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => backgroundTail (μ n) ε) atTop (𝓝 0)) ↔
      Tendsto (fun n => meanBackground (μ n)) atTop (𝓝 0) := by
  have hm (n : ℕ) : 0 ≤ meanBackground (μ n) :=
    Finset.sum_nonneg (fun x _ => mul_nonneg ((μ n).nonneg x) (backgroundFraction_nonneg x))
  have ht (n : ℕ) (ε : ℝ) : 0 ≤ backgroundTail (μ n) ε := by
    unfold backgroundTail
    apply Finset.sum_nonneg
    intro x _
    split_ifs
    · exact (μ n).nonneg x
    · exact le_rfl
  constructor
  · intro h
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall (fun n => ha.trans_le (hm n))
    · intro b hb
      have half := half_pos hb
      filter_upwards [(tendsto_order.1 (h (b / 2) half)).2 (b / 2) half] with n hn
      have bound := mean_le_threshold_add_tail (μ n) half.le
      linarith
  · intro h ε hε
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall (fun n => ha.trans_le (ht n ε))
    · intro b hb
      filter_upwards [(tendsto_order.1 h).2 (ε * b) (mul_pos hε hb)] with n hn
      exact (mul_lt_mul_left hε).mp ((threshold_mul_tail_le_mean (μ n) ε).trans_lt hn)

/-- For every thermodynamic sequence at density ρ and every choice of stationary
law on those rings, the largest pile carries a fraction tending to one in
probability. Existence on each finite ring is included to exclude vacuity. -/
def SupercondensesAt (w ρ : ℝ) : Prop :=
  (∀ L N : ℕ, 3 ≤ L → Nonempty (StationaryLaw L N w)) ∧
  ∀ (L N : ℕ → ℕ), (∀ n, 3 ≤ L n) →
    Tendsto L atTop atTop →
    Tendsto (fun n => (N n : ℝ) / (L n : ℝ)) atTop (𝓝 ρ) →
    ∀ (μ : (n : ℕ) → StationaryLaw (L n) (N n) w),
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => backgroundTail (μ n) ε) atTop (𝓝 0)

/-- The small-w conjecture. The same w₀ works for every positive density. -/
def SmallWSupercondensation : Prop :=
  ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ ≤ 1 ∧
    ∀ w : ℝ, 0 < w → w < w₀ → ∀ ρ : ℝ, 0 < ρ → SupercondensesAt w ρ

end
end Chipping
```
