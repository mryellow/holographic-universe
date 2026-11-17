import HolographicUniverse.Basic
import HolographicUniverse.Bulk
import HolographicUniverse.Integrals
import HolographicUniverse.Zeta
import HolographicUniverse.InducedFluid
import HolographicUniverse.Pressure
import HolographicUniverse.GeneralBulk
import HolographicUniverse.Constraints
import HolographicUniverse.Perturbations
import HolographicUniverse.ObsData
import HolographicUniverse.Monopoles
import HolographicUniverse.ScaleInvariance
import HolographicUniverse.Model
import HolographicUniverse.Acceleration
import HolographicUniverse.Instances
import HolographicUniverse.Orientation
import HolographicUniverse.History
import HolographicUniverse.Singularity
import HolographicUniverse.Bounce
import HolographicUniverse.Dynamics
import HolographicUniverse.LocalExistence
import HolographicUniverse.TurningPoint
import HolographicUniverse.MaximalSolution

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

/-- info: 'WhiteHole.eq50' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq50

/-- info: 'WhiteHole.M5_cube_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms M5_cube_le

/-- info: 'WhiteHole.spectralIndex_powerLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spectralIndex_powerLaw

/-- info: 'WhiteHole.spectralIndex_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spectralIndex_comp

/-- info: 'WhiteHole.leadingSpectrum_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leadingSpectrum_ns

/-- info: 'WhiteHole.ObsData.not_fits_of_locallyConst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ObsData.not_fits_of_locallyConst

/-- info: 'WhiteHole.leading_order_ruled_out_planck2013' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leading_order_ruled_out_planck2013

/-- info: 'WhiteHole.leading_order_ruled_out_planck2018' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leading_order_ruled_out_planck2018

/-- info: 'WhiteHole.planck2013_ns_excludes_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms planck2013_ns_excludes_one

/-- info: 'WhiteHole.planck2018_ns_excludes_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms planck2018_ns_excludes_one

/-- info: 'WhiteHole.eq51_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq51_numeric

/-- info: 'WhiteHole.hubble_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hubble_le

/-- info: 'WhiteHole.eq52' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq52

/-- info: 'WhiteHole.eq52_below_GUT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq52_below_GUT

/-- info: 'WhiteHole.Tb_le_planck2013' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tb_le_planck2013

/-- info: 'WhiteHole.Tb_le_planck2018' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tb_le_planck2018

/-- info: 'WhiteHole.pressure_of_timelike_junction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pressure_of_timelike_junction

/-- info: 'WhiteHole.eq27_of_dropped_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq27_of_dropped_sign

/-- info: 'WhiteHole.orientation_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms orientation_iff

/-- info: 'WhiteHole.orientation_plus_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms orientation_plus_branch

/-- info: 'WhiteHole.orientation_minus_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms orientation_minus_branch

/-- info: 'WhiteHole.minkowski_normal_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms minkowski_normal_branch

/-- info: 'WhiteHole.rhoTilde_eq_zero_inside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rhoTilde_eq_zero_inside

/-- info: 'WhiteHole.BraneCosmology.ρt_sign_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.ρt_sign_const

/-- info: 'WhiteHole.BraneCosmology.normal_branch_no_crossing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.normal_branch_no_crossing

/-- info: 'WhiteHole.BraneCosmology.radiation_era_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.radiation_era_ratio

/-- info: 'WhiteHole.BraneCosmology.matter_era_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.matter_era_ratio

/-- info: 'WhiteHole.BraneCosmology.ratio_antitoneOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.ratio_antitoneOn

/-- info: 'WhiteHole.BraneCosmology.eps_of_singularity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.eps_of_singularity

/-- info: 'WhiteHole.BraneCosmology.matter_era_growth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.matter_era_growth_le

/-- info: 'WhiteHole.BraneCosmology.matter_era_growth_le_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.matter_era_growth_le_small

/-- info: 'WhiteHole.sign_change_inside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_change_inside

/-- info: 'WhiteHole.sign_const_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_const_outside

/-- info: 'WhiteHole.isInduced_eq_rhoS_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isInduced_eq_rhoS_iff

/-- info: 'WhiteHole.branches_meet_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms branches_meet_iff

/-- info: 'WhiteHole.BraneCosmology.singularity_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.singularity_iff

/-- info: 'WhiteHole.BraneCosmology.singularity_inside_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.singularity_inside_iff

/-- info: 'WhiteHole.BraneCosmology.singularity_strictly_inside_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.singularity_strictly_inside_iff

/-- info: 'WhiteHole.BraneCosmology.singularity_inside_iff_curvature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.singularity_inside_iff_curvature

/-- info: 'WhiteHole.BraneCosmology.singularity_inside_of_rc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.singularity_inside_of_rc

/-- info: 'WhiteHole.BraneCosmology.scale_factor_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.scale_factor_floor

/-- info: 'WhiteHole.rhoBulk_blacken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rhoBulk_blacken

/-- info: 'WhiteHole.isInduced_of_bulk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isInduced_of_bulk

/-- info: 'WhiteHole.isInduced_of_junction_f' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isInduced_of_junction_f

/-- info: 'WhiteHole.pressure_of_continuity_bulk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pressure_of_continuity_bulk

/-- info: 'WhiteHole.pressureTildeBulk_radiation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pressureTildeBulk_radiation

/-- info: 'WhiteHole.BulkCosmology.isInduced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BulkCosmology.isInduced

/-- info: 'WhiteHole.BulkCosmology.reality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BulkCosmology.reality

/-- info: 'WhiteHole.BulkCosmology.branches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BulkCosmology.branches

/-- info: 'WhiteHole.BulkCosmology.pressure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BulkCosmology.pressure

/-- info: 'WhiteHole.BulkCosmology.singularity_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BulkCosmology.singularity_iff

/-- info: 'WhiteHole.BulkCosmology.singularity_inside_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BulkCosmology.singularity_inside_iff

/-- info: 'WhiteHole.BulkCosmology.singularity_inside_iff_curvature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BulkCosmology.singularity_inside_iff_curvature

/-- info: 'WhiteHole.BraneCosmology.toBulk_rhoBulk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.toBulk_rhoBulk

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

/-- info: 'WhiteHole.exists_expanding_radiation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_expanding_radiation

/-- info: 'WhiteHole.BraneCosmology.radiationBounce_accelAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.radiationBounce_accelAt

/-- info: 'WhiteHole.BraneCosmology.radiationBounce_pressure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.radiationBounce_pressure

/-- info: 'WhiteHole.BraneCosmology.radiationBounce_selfAccelerating' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.radiationBounce_selfAccelerating

/-- info: 'WhiteHole.BraneCosmology.radiationBounce_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.radiationBounce_outside

/-- info: 'WhiteHole.BraneCosmology.rho_barotropic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.rho_barotropic

/-- info: 'WhiteHole.BraneCosmology.branch_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.branch_fixed

/-- info: 'WhiteHole.BraneCosmology.reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.reduction

/-- info: 'WhiteHole.BraneCosmology.radiationBounce_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.radiationBounce_reduction

/-- info: 'WhiteHole.BraneCosmology.isSolution_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.isSolution_of_ne

/-- info: 'WhiteHole.BraneCosmology.static_not_isSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.static_not_isSolution

/-- info: 'WhiteHole.BraneCosmology.radiationBounce_isSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.radiationBounce_isSolution

/-- info: 'WhiteHole.exists_local_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_local_solution

/-- info: 'WhiteHole.local_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms local_unique

/-- info: 'WhiteHole.BraneCosmology.locally_determined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.locally_determined

/-- info: 'WhiteHole.hasDerivAt_friedmannF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_friedmannF

/-- info: 'WhiteHole.BraneCosmology.accel_eq_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.accel_eq_deriv

/-- info: 'WhiteHole.local_unique₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms local_unique₂

/-- info: 'WhiteHole.exists_local_solution₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_local_solution₂

/-- info: 'WhiteHole.BraneCosmology.locally_determined₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.locally_determined₂

/-- info: 'WhiteHole.BraneCosmology.equilibrium_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.equilibrium_of_rest

/-- info: 'WhiteHole.BraneCosmology.radiationBounce_determined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.radiationBounce_determined

/-- info: 'WhiteHole.IsSolOn.eqOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsSolOn.eqOn

/-- info: 'WhiteHole.exists_local_mem_of_isCompact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_local_mem_of_isCompact

/-- info: 'WhiteHole.exists_isMaximalSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_isMaximalSolution

/-- info: 'WhiteHole.IsMaximalSolution.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsMaximalSolution.unique

/-- info: 'WhiteHole.IsMaximalSolution.eventually_not_mem_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsMaximalSolution.eventually_not_mem_right

/-- info: 'WhiteHole.IsMaximalSolution.eventually_not_mem_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsMaximalSolution.eventually_not_mem_left

/-- info: 'WhiteHole.IsMaximalSolution.eq_univ_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsMaximalSolution.eq_univ_of_mem

/-- info: 'WhiteHole.IsMaximalSolution.energy₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsMaximalSolution.energy₂

/-- info: 'WhiteHole.IsMaximalSolution.eq_univ_of_fst_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsMaximalSolution.eq_univ_of_fst_mem

/-- info: 'WhiteHole.exists_maximal_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_maximal_history

/-- info: 'WhiteHole.BraneCosmology.maximal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.maximal_eq
