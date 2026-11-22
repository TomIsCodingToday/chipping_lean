import ChippingSupercondensation.Model
import ChippingSupercondensation.Basic
import ChippingSupercondensation.Stationary
import ChippingSupercondensation.Identities
import ChippingSupercondensation.LargestPile
import ChippingSupercondensation.Background
import ChippingSupercondensation.Coalescence
import ChippingSupercondensation.PileBirths
import ChippingSupercondensation.PeakFrame
import ChippingSupercondensation.Clusters
import ChippingSupercondensation.PileCount
import ChippingSupercondensation.MassThree

/-!
# Supercondensation for the totally asymmetric chipping process

Lean 4 and mathlib v4.19.0. This root module imports the whole development, so
`import ChippingSupercondensation` provides every declaration. The modules are,
in dependency order:

* `Model`: the dynamics, stationary laws, the order parameter `B/N`, and the
  open propositions `SupercondensesAt` and `SmallWSupercondensation`.
* `Basic`: shared lemmas about ring sites and moves.
* `Stationary`: existence, uniqueness and rotation invariance of stationary
  laws; reduction of `SupercondensesAt` to the mean particle separation.
* `Identities`: exact stationary identities and the directional balance.
* `LargestPile`: drift of the largest pile and tracking of a majority pile.
* `Background`: occupied pairs, background mass, capped masses, threshold pairs.
* `Coalescence`: coalescing dynamics of piles above a cutoff and the bound of
  two large piles by births.
* `PileBirths`: the gap-product weights and the nearby chip-birth estimate.
* `PeakFrame`: exact drift of any offset-weighted background moment in the
  frame of a majority pile, and the stationary balance of singles against
  the chip rate and the inflow into the peak from behind.
* `Clusters`: piles with the singles they will sweep, in the frame of a
  majority pile; the exact drift of anchor-weighted moments, in which only
  exceptional chips contribute.
* `PileCount`: the exact balance of the number of piles; piles of two are at
  most `w` times the occupied sites, and the background reduces to piles of
  three or more.
* `MassThree`: cluster masses under whole moves and trivial chips, and the
  exact drift of state-dependent weights for clusters of mass three.

`Coalescence` depends only on `Identities` and the modules before it.
`PileBirths` imports both `Background` and `Coalescence`. `PeakFrame` depends
only on `LargestPile` and the modules before it, `Clusters` and `PileCount`
import `PeakFrame`, and `MassThree` imports both.
-/
