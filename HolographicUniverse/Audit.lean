import HolographicUniverse.Basic
import HolographicUniverse.Bulk
import HolographicUniverse.Integrals
import HolographicUniverse.Zeta
import HolographicUniverse.InducedFluid
import HolographicUniverse.Pressure
import HolographicUniverse.Constraints
import HolographicUniverse.Perturbations
import HolographicUniverse.ObsData
import HolographicUniverse.Model
import HolographicUniverse.Acceleration
import HolographicUniverse.Instances

/-!
# Axiom audit (ROADMAP M0.1)

The definition of done for a theorem in this project is: no `sorry`, and no axioms beyond Lean's
three standard ones (`propext`, `Classical.choice`, `Quot.sound`). This file enforces that at
build time, so CI fails if a `sorry` or a new `axiom` enters the library.

Two checks:

1. `audit_axioms` walks **every** declaration in every imported `HolographicUniverse.*` module
   and fails if any of them depends on a non-standard axiom. New theorems are covered without
   editing this file, as long as their module is imported above.
2. A `#print axioms` listing for the headline theorems, pinned with `#guard_msgs`. This is the
   human-readable record. It also fails if a headline theorem is renamed or deleted.

When adding a module, add its import here and to `HolographicUniverse.lean`.
-/

open Lean Elab Command

namespace WhiteHole.Audit

/-- The axioms a finished theorem may depend on. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `audit_axioms` checks every declaration of every imported module whose name starts with
`HolographicUniverse`. It fails if a declaration depends on an axiom outside `standardAxioms`
(`sorryAx` included), or if it finds no declarations to check. -/
elab "audit_axioms" : command => do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  for h : i in [0:env.header.moduleNames.size] do
    unless (`HolographicUniverse).isPrefixOf env.header.moduleNames[i] do continue
    let some data := env.header.moduleData[i]? | continue
    for c in data.constNames do
      checked := checked + 1
      let extra := (← collectAxioms c).filter (!standardAxioms.contains ·)
      unless extra.isEmpty do bad := bad.push (c, extra)
  if checked == 0 then
    throwError "audit_axioms: found no HolographicUniverse declarations to check"
  unless bad.isEmpty do
    let lines := bad.map fun (c, axs) => m!"  {c} depends on {axs}"
    throwError "audit_axioms: non-standard axioms in {bad.size} of {checked} declarations:\n\
      {MessageData.joinSep lines.toList "\n"}"

end WhiteHole.Audit

/-! ## 1. Whole-library check -/

audit_axioms

/-! ## 2. Headline theorems -/

open WhiteHole

/-- info: 'WhiteHole.Couplings.sqrt_eq_rc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Couplings.sqrt_eq_rc

/-- info: 'WhiteHole.rhoBH_scaling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rhoBH_scaling

/-- info: 'WhiteHole.outside_horizon_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms outside_horizon_iff

/-- info: 'WhiteHole.isInduced_of_junction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isInduced_of_junction

/-- info: 'WhiteHole.isInduced_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isInduced_iff

/-- info: 'WhiteHole.normal_branch_requires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms normal_branch_requires

/-- info: 'WhiteHole.pressure_of_continuity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pressure_of_continuity

/-- info: 'WhiteHole.eq33' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq33

/-- info: 'WhiteHole.eq34' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq34

/-- info: 'WhiteHole.eq35' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq35

/-- info: 'WhiteHole.integral_univ_inv_one_add_sq_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integral_univ_inv_one_add_sq_sq

/-- info: 'WhiteHole.riemannZeta_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms riemannZeta_five

/-- info: 'WhiteHole.zeta5_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zeta5_bounds

/-- info: 'WhiteHole.eq48_leading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq48_leading

/-- info: 'WhiteHole.ampCoeff_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ampCoeff_bounds

/-- info: 'WhiteHole.eq48_eq49' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq48_eq49

/-- info: 'WhiteHole.eq49' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq49

/-- info: 'WhiteHole.eq49_planck2013_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq49_planck2013_sharp

/-- info: 'WhiteHole.eq49_planck2018' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq49_planck2018

/-- info: 'WhiteHole.planck2013_planck2018_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms planck2013_planck2018_disjoint

/-- info: 'WhiteHole.ObsData.eq51' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ObsData.eq51

/-- info: 'WhiteHole.eq51' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq51

/-- info: 'WhiteHole.BraneCosmology.branches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.branches

/-- info: 'WhiteHole.BraneCosmology.pressure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.pressure

/-- info: 'WhiteHole.differentiableAt_deriv_of_sq_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms differentiableAt_deriv_of_sq_eq

/-- info: 'WhiteHole.accel_of_friedmann' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms accel_of_friedmann

/-- info: 'WhiteHole.BraneCosmology.accelAt_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.accelAt_of_ne

/-- info: 'WhiteHole.BraneCosmology.static_not_accelAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.static_not_accelAt

/-- info: 'WhiteHole.BraneCosmology.deSitter_accelAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.deSitter_accelAt

/-- info: 'WhiteHole.BraneCosmology.nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.nonempty

/-- info: 'WhiteHole.BraneCosmology.exists_normal_branch_eps_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.exists_normal_branch_eps_neg

/-- info: 'WhiteHole.BraneCosmology.deSitter_selfAccelerating' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.deSitter_selfAccelerating
