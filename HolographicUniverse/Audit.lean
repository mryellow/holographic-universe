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
import HolographicUniverse.FromSolution
import HolographicUniverse.NormalBranch
import HolographicUniverse.Horizon
import HolographicUniverse.Asymptotics
import HolographicUniverse.AdSBulk
import HolographicUniverse.ChargedBulk
import HolographicUniverse.ThermalIntegral
import HolographicUniverse.NextOrder
import HolographicUniverse.RadialIntegrals
import HolographicUniverse.SecondOrder
import HolographicUniverse.BlueTilt
import HolographicUniverse.Cascade
import HolographicUniverse.DarkRadiation
import HolographicUniverse.Running
import HolographicUniverse.Jeans
import HolographicUniverse.Boost
import HolographicUniverse.Golden

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

/-- info: 'WhiteHole.hasDerivAt_rhoTildeX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_rhoTildeX

/-- info: 'WhiteHole.junction_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms junction_sq

/-- info: 'WhiteHole.BraneCosmology.ofSolution_isSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.ofSolution_isSolution

/-- info: 'WhiteHole.BraneCosmology.exists_of_maximal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.exists_of_maximal

/-- info: 'WhiteHole.exists_nonpos_of_strictAnti_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_nonpos_of_strictAnti_deriv

/-- info: 'WhiteHole.BraneCosmology.not_isSolution_normal_eps_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.not_isSolution_normal_eps_neg

/-- info: 'WhiteHole.BraneCosmology.not_isSolution_minus_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.not_isSolution_minus_branch

/-- info: 'WhiteHole.exists_first_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_first_exit

/-- info: 'WhiteHole.BraneCosmology.deriv_ne_zero_of_inside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.deriv_ne_zero_of_inside

/-- info: 'WhiteHole.BraneCosmology.white_hole_past' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.white_hole_past

/-- info: 'WhiteHole.BraneCosmology.black_hole_future' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.black_hole_future

/-- info: 'WhiteHole.BraneCosmology.exists_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.exists_exit

/-- info: 'WhiteHole.BraneCosmology.exists_unique_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.exists_unique_exit

/-- info: 'WhiteHole.BraneCosmology.hubble_sq_at_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.hubble_sq_at_horizon

/-- info: 'WhiteHole.tendsto_rhoTilde' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_rhoTilde

/-- info: 'WhiteHole.abs_rhoTilde_minus_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_rhoTilde_minus_le

/-- info: 'WhiteHole.tendsto_pressureTilde_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_pressureTilde_atTop

/-- info: 'WhiteHole.BraneCosmology.tendsto_late' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.tendsto_late

/-- info: 'WhiteHole.BraneCosmology.expands_of_self_acc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.expands_of_self_acc

/-- info: 'WhiteHole.BraneCosmology.tendsto_deSitter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.tendsto_deSitter

/-- info: 'WhiteHole.BraneCosmology.tendsto_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.tendsto_normal

/-- info: 'WhiteHole.BraneCosmology.normal_branch_frw_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.normal_branch_frw_of_le

/-- info: 'WhiteHole.BraneCosmology.singularity_at_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.singularity_at_rest

/-- info: 'WhiteHole.BraneCosmology.singularity_outside_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.singularity_outside_of_le

/-- info: 'WhiteHole.rhoBulk_blackenAdS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rhoBulk_blackenAdS

/-- info: 'WhiteHole.pressureTildeBulk_extra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pressureTildeBulk_extra

/-- info: 'WhiteHole.BulkCosmology.pressure_AdS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BulkCosmology.pressure_AdS

/-- info: 'WhiteHole.BulkCosmology.reality_AdS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BulkCosmology.reality_AdS

/-- info: 'WhiteHole.BulkCosmology.tendsto_hubble_sq_AdS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BulkCosmology.tendsto_hubble_sq_AdS

/-- info: 'WhiteHole.BulkCosmology.not_tendsto_atTop_normal_AdS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BulkCosmology.not_tendsto_atTop_normal_AdS

/-- info: 'WhiteHole.rhoBulk_blackenRN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rhoBulk_blackenRN

/-- info: 'WhiteHole.rhoBulk_RN_neg_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rhoBulk_RN_neg_iff

/-- info: 'WhiteHole.blackenRN_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blackenRN_pos

/-- info: 'WhiteHole.BulkCosmology.pressure_RN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BulkCosmology.pressure_RN

/-- info: 'WhiteHole.BulkCosmology.reality_RN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BulkCosmology.reality_RN

/-- info: 'WhiteHole.BulkCosmology.tendsto_rhoBulk_RN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BulkCosmology.tendsto_rhoBulk_RN

/-- info: 'WhiteHole.BulkCosmology.singularity_hubble_lt_RN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BulkCosmology.singularity_hubble_lt_RN

/-- info: 'WhiteHole.hasSum_bose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasSum_bose

/-- info: 'WhiteHole.integral_bose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integral_bose

/-- info: 'WhiteHole.thermalM_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thermalM_zero

/-- info: 'WhiteHole.thermalM_zero_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thermalM_zero_bounds

/-- info: 'WhiteHole.eq48_leading_thermalM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq48_leading_thermalM

/-- info: 'WhiteHole.BraneCosmology.normal_branch_frw_rc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.normal_branch_frw_rc

/-- info: 'WhiteHole.BraneCosmology.normal_branch_frw_rc_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.normal_branch_frw_rc_of_le

/-- info: 'WhiteHole.thermalM_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thermalM_eq

/-- info: 'WhiteHole.convexOn_thermalA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms convexOn_thermalA

/-- info: 'WhiteHole.thermalA_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thermalA_zero_le

/-- info: 'WhiteHole.thermalB_le_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thermalB_le_zero

/-- info: 'WhiteHole.ObsData.not_fits_of_deriv_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ObsData.not_fits_of_deriv_nonneg

/-- info: 'WhiteHole.integral_pow_mul_series' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integral_pow_mul_series

/-- info: 'WhiteHole.integral_dphiB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integral_dphiB

/-- info: 'WhiteHole.integral_dphiB_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integral_dphiB_sq

/-- info: 'WhiteHole.integral_dphiB_sq_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integral_dphiB_sq_lt

/-- info: 'WhiteHole.hasDerivAt_phiB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_phiB

/-- info: 'WhiteHole.hasDerivAt_deriv_mRay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_deriv_mRay

/-- info: 'WhiteHole.deriv_mRay_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deriv_mRay_zero

/-- info: 'WhiteHole.secondOrderCoeff_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms secondOrderCoeff_pos

/-- info: 'WhiteHole.next_order_blue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms next_order_blue

/-- info: 'WhiteHole.ObsData.not_fits_next_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ObsData.not_fits_next_order

/-- info: 'WhiteHole.strictAntiOn_phiB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms strictAntiOn_phiB

/-- info: 'WhiteHole.b1_add_a1_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms b1_add_a1_pos

/-- info: 'WhiteHole.strictMonoOn_mRay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms strictMonoOn_mRay

/-- info: 'WhiteHole.thermalM_eq_mRay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thermalM_eq_mRay

/-- info: 'WhiteHole.thermalM_lt_of_norm_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thermalM_lt_of_norm_lt

/-- info: 'WhiteHole.spectralIndex_thermal_gt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spectralIndex_thermal_gt_one

/-- info: 'WhiteHole.ObsData.not_fits_thermal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ObsData.not_fits_thermal

/-- info: 'WhiteHole.spectralIndex_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spectralIndex_mul

/-- info: 'WhiteHole.spectralIndex_thermal_mul_gt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spectralIndex_thermal_mul_gt_one

/-- info: 'WhiteHole.ObsData.not_fits_thermal_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ObsData.not_fits_thermal_mul

/-- info: 'WhiteHole.spatialCoeff_quarter_le_third' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spatialCoeff_quarter_le_third

/-- info: 'WhiteHole.newtonCoeff_third_le_quarter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms newtonCoeff_third_le_quarter

/-- info: 'WhiteHole.cascadeL_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cascadeL_nonneg

/-- info: 'WhiteHole.cascadeG_monotoneOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cascadeG_monotoneOn

/-- info: 'WhiteHole.ObsData.not_fits_cascade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ObsData.not_fits_cascade

/-- info: 'WhiteHole.spectralIndex_thermal_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spectralIndex_thermal_mul

/-- info: 'WhiteHole.ObsData.Fits.factor_slope_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ObsData.Fits.factor_slope_lt

/-- info: 'WhiteHole.ObsData.Fits.deriv_factor_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ObsData.Fits.deriv_factor_neg

/-- info: 'WhiteHole.planck2018_factor_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms planck2018_factor_slope

/-- info: 'WhiteHole.integral_sq_coord_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integral_sq_coord_div

/-- info: 'WhiteHole.integral_radial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integral_radial

/-- info: 'WhiteHole.abs_dphiB_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_dphiB_le_exp

/-- info: 'WhiteHole.BraneCosmology.abs_frw_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.abs_frw_sub_le

/-- info: 'WhiteHole.BraneCosmology.darkRadiation_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.darkRadiation_le

/-- info: 'WhiteHole.BraneCosmology.abs_deltaNeff_bbn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.abs_deltaNeff_bbn

/-- info: 'WhiteHole.BraneCosmology.abs_deltaNeff_recombination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BraneCosmology.abs_deltaNeff_recombination

/-- info: 'WhiteHole.BulkCosmology.abs_frw_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BulkCosmology.abs_frw_sub_le

/-- info: 'WhiteHole.runningIndex_le_of_tilt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runningIndex_le_of_tilt

/-- info: 'WhiteHole.RunningData.not_fits_of_tilt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RunningData.not_fits_of_tilt

/-- info: 'WhiteHole.planck2018Running_not_fits_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms planck2018Running_not_fits_local

/-- info: 'WhiteHole.runningIndex_le_local_planck2018' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runningIndex_le_local_planck2018

/-- info: 'WhiteHole.runningIndex_jeans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runningIndex_jeans

/-- info: 'WhiteHole.planck2018Running_not_fits_jeans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms planck2018Running_not_fits_jeans

/-- info: 'WhiteHole.spectralIndex_jeansProjected_above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spectralIndex_jeansProjected_above

/-- info: 'WhiteHole.tendsto_log_jeansProjected_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_log_jeansProjected_budget

/-- info: 'WhiteHole.runningIndex_boost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runningIndex_boost

/-- info: 'WhiteHole.abs_boostTilt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_boostTilt_le

/-- info: 'WhiteHole.BulkCosmology.abs_deltaNeff_bbn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BulkCosmology.abs_deltaNeff_bbn

/-- info: 'WhiteHole.golden_jeans_running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms golden_jeans_running

/-- info: 'WhiteHole.golden_boost_running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms golden_boost_running
