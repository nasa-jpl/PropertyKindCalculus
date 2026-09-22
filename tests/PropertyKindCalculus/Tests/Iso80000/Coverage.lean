/-
`Tests.Iso80000.Coverage` — the two Dimension-library censuses over every part of ISO 80000.

**Generated. Do not edit by hand** — regenerate with `scripts/gen-iso80000-coverage.py`,
which runs the censuses and writes this file from their output.

**Records, generated from the compiler.** Every pin below is the command's own output, captured
by a driver (`lake env lean`) over the catalogue's root import and written here verbatim — not
typed. A change in what a part individuates, or in how it dimensions a kind, is therefore a
visible diff in this file; a part's report is re-pinned only when the change it records has
been read and accepted.

**Gates, only where they pass.** A `_clean` command is pinned over a part exactly when that
part's report ends `clean` (or is empty). Where the report records a violation, there is no
gate, and the record is a *finding awaiting a maintainer's decision*, not a blessing of it —
pinning a violation and gating on it are different acts, and the second is what the library's
`_clean` discipline exists to prevent (`#kind_dimensional_clean`'s docstring). What the current
findings mean, and what decisions they wait on, is `METHODOLOGY_TEMPLATES.md` §5 — not this
header, which the generator overwrites.

Summary of the records below, derived from them by the generator:

  * `#kind_examination_coverage` (M6):
      Part1  no dimension-one kinds in the given namespaces
      Part2  no dimension-one kinds in the given namespaces
      Part3  6 dimension-one kind(s): 0 individuated, 6 UNINDIVIDUATED — examination-coverage violation
      Part4  11 dimension-one kind(s): 0 individuated, 11 UNINDIVIDUATED — examination-coverage violation
      Part5  11 dimension-one kind(s): 0 individuated, 11 UNINDIVIDUATED — examination-coverage violation
      Part6  12 dimension-one kind(s): 0 individuated, 12 UNINDIVIDUATED — examination-coverage violation
      Part7  27 dimension-one kind(s): 0 individuated, 27 UNINDIVIDUATED — examination-coverage violation
      Part8  4 dimension-one kind(s): 0 individuated, 4 UNINDIVIDUATED — examination-coverage violation
      Part9  31 dimension-one kind(s): 0 individuated, 31 UNINDIVIDUATED — examination-coverage violation
      Part10 31 dimension-one kind(s): 0 individuated, 31 UNINDIVIDUATED — examination-coverage violation
      Part11 115 dimension-one kind(s): 115 individuated — clean
      Part12 9 dimension-one kind(s): 0 individuated, 9 UNINDIVIDUATED — examination-coverage violation
      Part13 27 dimension-one kind(s): 0 individuated, 27 UNINDIVIDUATED — examination-coverage violation
    totals: 115 [individuated], 169 ⚠ UNINDIVIDUATED
    gated (`#kind_examination_clean`): Part1, Part2, Part11
  * `#kind_dimensional_coverage` (M10):
      Part1  2 kind edge(s), all dimensionally coherent — clean
      Part2  no authored kind edges in the given namespaces
      Part3  6 kind edge(s), all dimensionally coherent — clean
      Part4  7 kind edge(s), all dimensionally coherent — clean
      Part5  7 kind edge(s): 6 coherent, 1 CONFLICTING — dimensional-coverage violation
      Part6  9 kind edge(s), all dimensionally coherent — clean
      Part7  5 kind edge(s), all dimensionally coherent — clean
      Part8  5 kind edge(s), all dimensionally coherent — clean
      Part9  5 kind edge(s), all dimensionally coherent — clean
      Part10 5 kind edge(s), all dimensionally coherent — clean
      Part11 no authored kind edges in the given namespaces
      Part12 2 kind edge(s), all dimensionally coherent — clean
      Part13 3 kind edge(s), all dimensionally coherent — clean
    totals: 55 [coherent], 1 ⚠ CONFLICTING
    gated (`#kind_dimensional_clean`): Part1, Part2, Part3, Part4, Part6, Part7, Part8, Part9, Part10, Part11, Part12, Part13

Both commands record `AuditReceipt`s (`PropertyKindCalculus.AuditReceipt`) over each part.
-/

module

public import PropertyKindCalculus.Iso80000
meta import PropertyKindCalculus.Iso80000
public import PropertyKindCalculus.ExaminationCoverage
meta import PropertyKindCalculus.ExaminationCoverage

-- No namespace: the dimensional rows pretty-print kinds relative to the current namespace,
-- and the driver that produced these pins ran with none. Nothing here is declared.

/-! ## `#kind_examination_coverage` — M6, part by part -/

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

/--
info: examination coverage — no dimension-one kinds in the given namespaces
-/

#guard_msgs (whitespace := lax) in
#kind_examination_coverage PropertyKindCalculus.Iso80000.Part1

-- Part1 is clean: the census as an invariant, with no message to re-bless
#guard_msgs in
#kind_examination_clean PropertyKindCalculus.Iso80000.Part1

/--
info: examination coverage — no dimension-one kinds in the given namespaces
-/
#guard_msgs (whitespace := lax) in
#kind_examination_coverage PropertyKindCalculus.Iso80000.Part2

-- Part2 is clean: the census as an invariant, with no message to re-bless
#guard_msgs in
#kind_examination_clean PropertyKindCalculus.Iso80000.Part2

/--
info: examination coverage:
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part3.logarithmicDecrement (logarithmic decrement)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part3.phaseAngle (phase angle)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part3.planeAngle (plane angle)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part3.rotation (rotation)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part3.rotationalDisplacement (rotational displacement)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part3.solidAngle (solid angle)
6 dimension-one kind(s): 0 individuated, 6 UNINDIVIDUATED — examination-coverage violation
-/
#guard_msgs (whitespace := lax) in
#kind_examination_coverage PropertyKindCalculus.Iso80000.Part3

/--
info: examination coverage:
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part4.dragCoefficient (drag coefficient)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part4.efficiency (efficiency)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part4.kineticFrictionFactor (kinetic friction factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part4.poissonNumber (Poisson number)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part4.relativeLinearStrain (relative linear strain)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part4.relativeMassDensity (relative mass density)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part4.relativeVolumeStrain (relative volume strain)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part4.rollingResistanceFactor (rolling resistance factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part4.shearStrain (shear strain)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part4.staticFrictionFactor (static friction factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part4.strain (strain)
11 dimension-one kind(s): 0 individuated, 11 UNINDIVIDUATED — examination-coverage violation
-/
#guard_msgs (whitespace := lax) in
#kind_examination_coverage PropertyKindCalculus.Iso80000.Part4

/--
info: examination coverage:
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part5.efficiency (efficiency)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part5.isentropicExponent (isentropic exponent)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part5.massFractionOfDryMatter (mass fraction of dry matter)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part5.massFractionOfWater (mass fraction of water)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part5.massRatioOfWaterToDryMatter (mass ratio of water to dry matter)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part5.massRatioOfWaterVapourToDryGas (mass ratio of water vapour to dry gas)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part5.maximumEfficiency (maximum efficiency)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part5.ratioOfSpecificHeatCapacities (ratio of specific heat capacities)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part5.relativeHumidity (relative humidity)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part5.relativeMassConcentrationOfVapour (relative mass concentration of vapour)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part5.relativeMassRatioOfVapour (relative mass ratio of vapour)
11 dimension-one kind(s): 0 individuated, 11 UNINDIVIDUATED — examination-coverage violation
-/
#guard_msgs (whitespace := lax) in
#kind_examination_coverage PropertyKindCalculus.Iso80000.Part5

/--
info: examination coverage:
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part6.couplingFactor (coupling factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part6.electricSusceptibility (electric susceptibility)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part6.leakageFactor (leakage factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part6.lossAngle (loss angle)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part6.lossFactor (loss factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part6.magneticSusceptibility (magnetic susceptibility)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part6.numberOfTurns (number of turns in a winding)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part6.phaseDifference (phase difference)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part6.powerFactor (power factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part6.qualityFactor (quality factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part6.relativePermeability (relative permeability)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part6.relativePermittivity (relative permittivity)
12 dimension-one kind(s): 0 individuated, 12 UNINDIVIDUATED — examination-coverage violation
-/
#guard_msgs (whitespace := lax) in
#kind_examination_coverage PropertyKindCalculus.Iso80000.Part6

/--
info: examination coverage:
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.absorptance (absorptance)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.chromaticity1931 (chromaticity coordinates in the CIE 1931 standard system)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.chromaticity1964 (chromaticity coordinates in the CIE 1964 standard system)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.colourMatching1931 (CIE colour-matching functions for the CIE 1931 standard observer)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.colourMatching1964 (CIE colour-matching functions for the CIE 1964 standard observer)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.emissivity (emissivity)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.luminanceFactor (luminance factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.luminousAbsorptance (luminous absorptance)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.luminousEfficacy (luminous efficacy of radiation)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.luminousEfficacyOfSource (luminous efficacy of a source)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.luminousEfficiency (luminous efficiency)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.luminousReflectance (luminous reflectance)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.luminousTransmittance (luminous transmittance)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.maximumLuminousEfficacy (maximum luminous efficacy)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.napierianAbsorbance (Napierian absorbance)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.opticalDensity (transmittance optical density)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.photonNumber (photon number)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.radianceFactor (radiance factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.reflectance (reflectance)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.reflectanceFactor (reflectance factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.refractiveIndex (refractive index)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.spectralEmissivity (emissivity at a specified wavelength)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.spectralLuminousEfficacy (spectral luminous efficacy)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.spectralLuminousEfficiency (spectral luminous efficiency)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.transmittance (transmittance)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.tristimulus1931 (tristimulus values for the CIE 1931 standard observer)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part7.tristimulus1964 (tristimulus values for the CIE 1964 standard observer)
27 dimension-one kind(s): 0 individuated, 27 UNINDIVIDUATED — examination-coverage violation
-/
#guard_msgs (whitespace := lax) in
#kind_examination_coverage PropertyKindCalculus.Iso80000.Part7

/--
info: examination coverage:
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part8.logFrequencyRange (logarithmic frequency range)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part8.soundExposureLevel (sound exposure level)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part8.soundPowerLevel (sound power level)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part8.soundPressureLevel (sound pressure level)
4 dimension-one kind(s): 0 individuated, 4 UNINDIVIDUATED — examination-coverage violation
-/
#guard_msgs (whitespace := lax) in
#kind_examination_coverage PropertyKindCalculus.Iso80000.Part8

/--
info: examination coverage:
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.absoluteActivity (absolute activity)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.activityCoefficient (activity coefficient)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.activityFactor (activity factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.activityOfSolute (activity of solute)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.activityOfSolvent (activity of solvent)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.amountOfSubstance (amount of substance)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.canonicalPartition (canonical partition function)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.degeneracy (degeneracy)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.degreeOfDissociation (degree of dissociation)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.equilibriumConstantConcentration (equilibrium constant (concentration basis))
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.equilibriumConstantPressure (equilibrium constant (pressure basis))
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.extentOfReaction (extent of reaction)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.grandCanonicalPartition (grand-canonical partition function)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.massFraction (mass fraction)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.microcanonicalPartition (microcanonical partition function)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.moleFraction (mole fraction)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.molecularPartition (molecular partition function)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.numberOfEntities (number of entities)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.opticalRotationAngle (angle of optical rotation)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.osmoticCoefficient (osmotic coefficient of solvent)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.relativeAtomicMass (relative atomic mass)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.standardAbsoluteActivityMixture (standard absolute activity in a mixture)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.standardAbsoluteActivitySolution (standard absolute activity in a solution)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.standardAbsoluteActivitySolvent (standard absolute activity of solvent)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.standardEquilibriumConstant (standard equilibrium constant)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.statisticalWeight (statistical weight of subsystem)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.stoichiometricNumber (stoichiometric number)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.thermalDiffusionFactor (thermal diffusion factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.thermalDiffusionRatio (thermal diffusion ratio)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.transportNumber (transport number of the ion)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part9.volumeFraction (volume fraction)
31 dimension-one kind(s): 0 individuated, 31 UNINDIVIDUATED — examination-coverage violation
-/
#guard_msgs (whitespace := lax) in
#kind_examination_coverage PropertyKindCalculus.Iso80000.Part9

/--
info: examination coverage:
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.atomicNumber (atomic number)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.averageLogarithmicEnergyDecrement (average logarithmic energy decrement)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.bindingFraction (binding fraction)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.chargeNumber (charge number)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.fastFissionFactor (fast fission factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.gFactorNucleus (g factor of nucleus)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.hyperfineQuantumNumber (hyperfine structure quantum number)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.infiniteMultiplicationFactor (infinite multiplication factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.internalConversionFactor (internal conversion factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.landeFactor (Landé factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.lethargy (lethargy)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.magneticQuantumNumber (magnetic quantum number)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.multiplicationFactor (multiplication factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.neutronNumber (neutron number)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.neutronYieldPerAbsorption (neutron yield per absorption)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.neutronYieldPerFission (neutron yield per fission)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.nonLeakageProbability (non-leakage probability)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.nuclearSpinQuantumNumber (nuclear spin quantum number)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.nucleonNumber (nucleon number)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.orbitalQuantumNumber (orbital angular momentum quantum number)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.packingFraction (packing fraction)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.principalQuantumNumber (principal quantum number)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.qualityFactor (quality factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.quantumNumber (quantum number)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.relativeMassDefect (relative mass defect)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.relativeMassExcess (relative mass excess)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.resonanceEscapeProbability (resonance escape probability)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.spinQuantumNumber (spin quantum number)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.thermalUtilizationFactor (thermal utilization factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.totalAngularMomentumQuantumNumber (total angular momentum quantum number)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part10.totalIonization (total ionization)
31 dimension-one kind(s): 0 individuated, 31 UNINDIVIDUATED — examination-coverage violation
-/
#guard_msgs (whitespace := lax) in
#kind_examination_coverage PropertyKindCalculus.Iso80000.Part10

/--
info: examination coverage:
[individuated] PropertyKindCalculus.Iso80000.Part11.absorptionNumber (absorption number) — principle: mass-transfer: mass flow rate / surface area, gas absorption
[individuated] PropertyKindCalculus.Iso80000.Part11.alfven (Alfvén number) — principle: magnetohydrodynamics: flow speed / Alfvén wave speed
[individuated] PropertyKindCalculus.Iso80000.Part11.ampere (Ampère number) — principle: magnetohydrodynamics: electric surface current / magnetic field
[individuated] PropertyKindCalculus.Iso80000.Part11.archimedes (Archimedes number) — principle: mass-transfer: buoyancy forces / viscous forces, density difference
[individuated] PropertyKindCalculus.Iso80000.Part11.arrhenius (Arrhenius number) — principle: miscellaneous: chemical activation energy / thermal energy
[individuated] PropertyKindCalculus.Iso80000.Part11.atwood (Atwood number) — principle: mass-transfer: density difference / density sum, two fluids
[individuated] PropertyKindCalculus.Iso80000.Part11.bagnold (Bagnold number) — principle: momentum-transfer: drag and gravitational force / inertial force
[individuated] PropertyKindCalculus.Iso80000.Part11.bagnoldSolid (Bagnold number) — principle: momentum-transfer: drag force / viscous force, solid particles
[individuated] PropertyKindCalculus.Iso80000.Part11.batchelor (Batchelor number) — principle: magnetohydrodynamics: inertia / magneto-dynamic diffusion
[individuated] PropertyKindCalculus.Iso80000.Part11.bejanEntropy (Bejan number) — principle: heat-transfer: heat-transfer efficiency / entropy generation
[individuated] PropertyKindCalculus.Iso80000.Part11.bejanHeat (Bejan number) — principle: heat-transfer: mechanical work / frictional and thermal-diffusion losses
[individuated] PropertyKindCalculus.Iso80000.Part11.bejanMass (Bejan number) — principle: mass-transfer: mechanical work / frictional and diffusion losses
[individuated] PropertyKindCalculus.Iso80000.Part11.bejanMomentum (Bejan number) — principle: momentum-transfer: mechanical work / frictional energy loss
[individuated] PropertyKindCalculus.Iso80000.Part11.bingham (Bingham number) — principle: momentum-transfer: yield stress / viscous stress
[individuated] PropertyKindCalculus.Iso80000.Part11.biotHeat (Biot number) — principle: heat-transfer: internal / surface thermal resistance
[individuated] PropertyKindCalculus.Iso80000.Part11.biotMass (Biot number) — principle: mass-transfer: interface / interior mass transfer rate
[individuated] PropertyKindCalculus.Iso80000.Part11.blake (Blake number) — principle: momentum-transfer: inertial force / viscous force, porous medium
[individuated] PropertyKindCalculus.Iso80000.Part11.bodenstein (Bodenstein number) — principle: momentum-transfer: convective / diffusive matter transfer
[individuated] PropertyKindCalculus.Iso80000.Part11.boltzmann (Boltzmann number) — principle: heat-transfer: convective heat / radiant heat
[individuated] PropertyKindCalculus.Iso80000.Part11.bond (Bond number) — principle: mass-transfer: gravitational and inertial force / capillary force
[individuated] PropertyKindCalculus.Iso80000.Part11.brinkman (Brinkman number) — principle: heat-transfer: viscous heat production / wall heat conduction
[individuated] PropertyKindCalculus.Iso80000.Part11.capillary (capillary number) — principle: mass-transfer: gravitational forces / capillary forces
[individuated] PropertyKindCalculus.Iso80000.Part11.carnot (Carnot number) — principle: heat-transfer: maximum thermodynamic (Carnot) efficiency
[individuated] PropertyKindCalculus.Iso80000.Part11.cauchy (Cauchy number) — principle: constants-of-matter: inertia forces / compression forces
[individuated] PropertyKindCalculus.Iso80000.Part11.cavitation (cavitation number) — principle: mass-transfer: static-vapour head / dynamic head
[individuated] PropertyKindCalculus.Iso80000.Part11.chandrasekhar (Chandrasekhar number) — principle: magnetohydrodynamics: Lorentz force / viscous force
[individuated] PropertyKindCalculus.Iso80000.Part11.clausius (Clausius number) — principle: heat-transfer: kinetic energy transfer / thermal conduction
[individuated] PropertyKindCalculus.Iso80000.Part11.compressibility (compressibility number) — principle: constants-of-matter: real-gas / ideal-gas compressibility factor
[individuated] PropertyKindCalculus.Iso80000.Part11.cowling (Cowling number) — principle: magnetohydrodynamics: magnetic / kinematic energy density
[individuated] PropertyKindCalculus.Iso80000.Part11.darcyFriction (Darcy friction factor) — principle: momentum-transfer: pressure loss / pipe-wall friction
[individuated] PropertyKindCalculus.Iso80000.Part11.dean (Dean number) — principle: momentum-transfer: centrifugal force / inertial force, curved pipe
[individuated] PropertyKindCalculus.Iso80000.Part11.deborah (Deborah number) — principle: constants-of-matter: relaxation time / observation time
[individuated] PropertyKindCalculus.Iso80000.Part11.dragCoefficient (drag coefficient) — principle: momentum-transfer: drag force / inertial force
[individuated] PropertyKindCalculus.Iso80000.Part11.dynamicCapillary (dynamic capillary number) — principle: mass-transfer: viscous force / capillary force, interface
[individuated] PropertyKindCalculus.Iso80000.Part11.eckert (Eckert number) — principle: heat-transfer: kinetic energy / enthalpy difference
[individuated] PropertyKindCalculus.Iso80000.Part11.ekman (Ekman number) — principle: momentum-transfer: viscous forces / Coriolis forces
[individuated] PropertyKindCalculus.Iso80000.Part11.elasticity (elasticity number) — principle: momentum-transfer: relaxation time / diffusion time
[individuated] PropertyKindCalculus.Iso80000.Part11.electricFieldParameter (electric field parameter) — principle: magnetohydrodynamics: Coulomb force / Lorentz force
[individuated] PropertyKindCalculus.Iso80000.Part11.euler (Euler number) — principle: momentum-transfer: pressure drop / kinetic energy per volume
[individuated] PropertyKindCalculus.Iso80000.Part11.expansionNumber (expansion number) — principle: mass-transfer: buoyancy force / inertial force, rising bubbles
[individuated] PropertyKindCalculus.Iso80000.Part11.fanning (Fanning number) — principle: momentum-transfer: wall shear stress / dynamic pressure
[individuated] PropertyKindCalculus.Iso80000.Part11.fourierHeat (Fourier number) — principle: heat-transfer: heat conduction rate / thermal storage rate
[individuated] PropertyKindCalculus.Iso80000.Part11.fourierMass (Fourier number) — principle: mass-transfer: diffusive mass transfer / storage rate
[individuated] PropertyKindCalculus.Iso80000.Part11.froudeHeat (Froude number) — principle: heat-transfer: gravitational forces / thermodiffusion forces
[individuated] PropertyKindCalculus.Iso80000.Part11.froudeMomentum (Froude number) — principle: momentum-transfer: inertial forces / gravitational forces
[individuated] PropertyKindCalculus.Iso80000.Part11.galilei (Galilei number) — principle: momentum-transfer: gravitational force / viscous force, fluid film
[individuated] PropertyKindCalculus.Iso80000.Part11.goertler (Goertler number) — principle: momentum-transfer: centrifugal effects / viscous effects, boundary layer
[individuated] PropertyKindCalculus.Iso80000.Part11.graetzHeat (Graetz number) — principle: heat-transfer: convective / conductive heat, laminar pipe
[individuated] PropertyKindCalculus.Iso80000.Part11.graetzMass (Graetz number) — principle: mass-transfer: advective / radial diffusive mass transfer
[individuated] PropertyKindCalculus.Iso80000.Part11.grashofMagnetic (Grashof magnetic number) — principle: magnetohydrodynamics: thermo-magnetic buoyancy / viscous force
[individuated] PropertyKindCalculus.Iso80000.Part11.grashofMass (Grashof number) — principle: mass-transfer: buoyancy forces / viscous forces, natural convection
[individuated] PropertyKindCalculus.Iso80000.Part11.grashofThermal (Grashof number) — principle: momentum-transfer: thermal buoyancy forces / viscous forces
[individuated] PropertyKindCalculus.Iso80000.Part11.hagen (Hagen number) — principle: momentum-transfer: pressure-gradient force / viscous force
[individuated] PropertyKindCalculus.Iso80000.Part11.hall (Hall number) — principle: magnetohydrodynamics: gyrofrequency / collision frequency
[individuated] PropertyKindCalculus.Iso80000.Part11.hartmann (Hartmann number) — principle: magnetohydrodynamics: magnetically induced stress / viscous force
[individuated] PropertyKindCalculus.Iso80000.Part11.heatTransferNumber (heat transfer number) — principle: heat-transfer: heat flow / kinetic energy of flow
[individuated] PropertyKindCalculus.Iso80000.Part11.hedstrom (Hedström number) — principle: momentum-transfer: yield stress / viscous stress, at flow limit
[individuated] PropertyKindCalculus.Iso80000.Part11.hooke (Hooke number) — principle: constants-of-matter: inertia forces / linear-stress forces
[individuated] PropertyKindCalculus.Iso80000.Part11.jFactorHeat (j-factor) — principle: heat-transfer: heat transfer / mass transfer, Colburn analogy
[individuated] PropertyKindCalculus.Iso80000.Part11.jouleMagnetic (Joule magnetic number) — principle: magnetohydrodynamics: Joule heating / magnetic field energy
[individuated] PropertyKindCalculus.Iso80000.Part11.knudsen (Knudsen number) — principle: momentum-transfer: mean free path / characteristic length
[individuated] PropertyKindCalculus.Iso80000.Part11.lagrange (Lagrange number) — principle: momentum-transfer: mechanical work / frictional energy loss, Lagrange form
[individuated] PropertyKindCalculus.Iso80000.Part11.landauGinzburg (Landau-Ginzburg number) — principle: miscellaneous: penetration depth / coherence length
[individuated] PropertyKindCalculus.Iso80000.Part11.laplace (Laplace number) — principle: momentum-transfer: capillary force / viscous force, free surface
[individuated] PropertyKindCalculus.Iso80000.Part11.laval (Laval number) — principle: momentum-transfer: flow speed / critical sound speed, nozzle throat
[individuated] PropertyKindCalculus.Iso80000.Part11.lewis (Lewis number) — principle: constants-of-matter: thermal diffusivity / diffusion coefficient
[individuated] PropertyKindCalculus.Iso80000.Part11.liftCoefficient (lift coefficient) — principle: momentum-transfer: lift force / inertial force
[individuated] PropertyKindCalculus.Iso80000.Part11.lockhartMartinelli (Lockhart-Martinelli parameter) — principle: mass-transfer: two-phase mass-flow-rate ratio by density
[individuated] PropertyKindCalculus.Iso80000.Part11.lorentz (Lorentz number) — principle: constants-of-matter: electrical conductivity / thermal conductivity
[individuated] PropertyKindCalculus.Iso80000.Part11.lundquist (Lundquist number) — principle: magnetohydrodynamics: Alfvén speed / magneto-dynamic diffusion speed
[individuated] PropertyKindCalculus.Iso80000.Part11.mach (Mach number) — principle: momentum-transfer: speed of flow / speed of sound
[individuated] PropertyKindCalculus.Iso80000.Part11.magneticNumber (magnetic number) — principle: magnetohydrodynamics: magnetic body force / viscous force
[individuated] PropertyKindCalculus.Iso80000.Part11.magneticPressure (magnetic pressure number) — principle: magnetohydrodynamics: gas pressure / magnetic pressure
[individuated] PropertyKindCalculus.Iso80000.Part11.marangoni (Marangoni number) — principle: mass-transfer: surface-tension convection / thermal diffusion
[individuated] PropertyKindCalculus.Iso80000.Part11.massTransferFactor (mass transfer factor) — principle: mass-transfer: interface mass transfer / parallel flux, Chilton-Colburn
[individuated] PropertyKindCalculus.Iso80000.Part11.morton (Morton number) — principle: mass-transfer: gravitational forces / viscous forces, bubbles
[individuated] PropertyKindCalculus.Iso80000.Part11.naze (Naze number) — principle: magnetohydrodynamics: Alfvén wave speed / sound speed
[individuated] PropertyKindCalculus.Iso80000.Part11.nusseltElectric (Nusselt electric number) — principle: magnetohydrodynamics: convective / diffusive ion current
[individuated] PropertyKindCalculus.Iso80000.Part11.nusseltHeat (Nusselt number) — principle: heat-transfer: convective / conductive heat transfer at a surface
[individuated] PropertyKindCalculus.Iso80000.Part11.nusseltMass (Nusselt number) — principle: mass-transfer: mass flux / molecular-diffusion flux
[individuated] PropertyKindCalculus.Iso80000.Part11.ohnesorge (Ohnesorge number) — principle: constants-of-matter: viscous force / root of inertia times capillary force
[individuated] PropertyKindCalculus.Iso80000.Part11.pecletHeat (Péclet number) — principle: heat-transfer: convective / conductive heat transfer rate
[individuated] PropertyKindCalculus.Iso80000.Part11.pecletMass (Péclet number) — principle: mass-transfer: advective / diffusive mass transfer rate
[individuated] PropertyKindCalculus.Iso80000.Part11.poiseuille (Poiseuille number) — principle: momentum-transfer: pressure force / viscous force, pipe flow
[individuated] PropertyKindCalculus.Iso80000.Part11.pomerantsev (Pomerantsev number) — principle: heat-transfer: generated heat / conducted heat in a body
[individuated] PropertyKindCalculus.Iso80000.Part11.powerNumber (power number) — principle: momentum-transfer: agitator power / inertial power
[individuated] PropertyKindCalculus.Iso80000.Part11.prandtl (Prandtl number) — principle: constants-of-matter: kinematic viscosity / thermal diffusivity
[individuated] PropertyKindCalculus.Iso80000.Part11.prandtlMagnetic (Prandtl magnetic number) — principle: magnetohydrodynamics: kinematic viscosity / magnetic viscosity
[individuated] PropertyKindCalculus.Iso80000.Part11.rayleigh (Rayleigh number) — principle: heat-transfer: thermal buoyancy forces / viscous forces, free convection
[individuated] PropertyKindCalculus.Iso80000.Part11.reech (Reech number) — principle: momentum-transfer: object speed / wave speed, submerged
[individuated] PropertyKindCalculus.Iso80000.Part11.reynolds (Reynolds number) — principle: momentum-transfer: inertial forces / viscous forces
[individuated] PropertyKindCalculus.Iso80000.Part11.reynoldsElectric (Reynolds electric number) — principle: magnetohydrodynamics: fluid speed / charged-particle drift speed
[individuated] PropertyKindCalculus.Iso80000.Part11.reynoldsMagnetic (Reynolds magnetic number) — principle: magnetohydrodynamics: inertial force / magneto-dynamic viscous force
[individuated] PropertyKindCalculus.Iso80000.Part11.richardson (Richardson number) — principle: momentum-transfer: potential energy / kinetic energy
[individuated] PropertyKindCalculus.Iso80000.Part11.roberts (Roberts number) — principle: magnetohydrodynamics: thermal diffusivity / magnetic viscosity
[individuated] PropertyKindCalculus.Iso80000.Part11.rossby (Rossby number) — principle: momentum-transfer: inertial forces / Coriolis forces
[individuated] PropertyKindCalculus.Iso80000.Part11.schmidt (Schmidt number) — principle: constants-of-matter: kinematic viscosity / diffusion coefficient
[individuated] PropertyKindCalculus.Iso80000.Part11.sommerfeld (Sommerfeld number) — principle: momentum-transfer: viscous force / load force, lubrication
[individuated] PropertyKindCalculus.Iso80000.Part11.stantonHeat (Stanton number) — principle: heat-transfer: wall heat transfer / fluid heat-capacity flow
[individuated] PropertyKindCalculus.Iso80000.Part11.stantonMass (Stanton number) — principle: mass-transfer: perpendicular / parallel surface mass transfer
[individuated] PropertyKindCalculus.Iso80000.Part11.stark (Stark number) — principle: heat-transfer: radiant heat / conductive heat
[individuated] PropertyKindCalculus.Iso80000.Part11.stefan (Stefan number) — principle: heat-transfer: sensible heat / latent heat, phase change
[individuated] PropertyKindCalculus.Iso80000.Part11.stokesDrag (Stokes number) — principle: momentum-transfer: drag force / internal friction force, particles
[individuated] PropertyKindCalculus.Iso80000.Part11.stokesGravity (Stokes number) — principle: momentum-transfer: viscous force / gravity force, settling particles
[individuated] PropertyKindCalculus.Iso80000.Part11.stokesPlasma (Stokes number) — principle: momentum-transfer: friction force / inertial force, particles in flow
[individuated] PropertyKindCalculus.Iso80000.Part11.stokesRotameter (Stokes number) — principle: momentum-transfer: drag / inertia, rotameter calibration
[individuated] PropertyKindCalculus.Iso80000.Part11.stokesVibrating (Stokes number) — principle: momentum-transfer: friction force / inertial force, vibrating particles
[individuated] PropertyKindCalculus.Iso80000.Part11.strouhal (Strouhal number) — principle: momentum-transfer: characteristic frequency / characteristic speed
[individuated] PropertyKindCalculus.Iso80000.Part11.stuart (Stuart number) — principle: magnetohydrodynamics: magnetic force / inertial force
[individuated] PropertyKindCalculus.Iso80000.Part11.stuartElectrical (Stuart electrical number) — principle: magnetohydrodynamics: electric / kinematic energy density
[individuated] PropertyKindCalculus.Iso80000.Part11.taylor (Taylor number) — principle: momentum-transfer: centrifugal force / viscous force, rotating flow
[individuated] PropertyKindCalculus.Iso80000.Part11.thrustCoefficient (thrust coefficient) — principle: momentum-transfer: thrust force / inertial force
[individuated] PropertyKindCalculus.Iso80000.Part11.weber (Weber number) — principle: momentum-transfer: inertial forces / surface-tension forces
[individuated] PropertyKindCalculus.Iso80000.Part11.weissenberg (Weissenberg number) — principle: constants-of-matter: shear rate times relaxation time
[individuated] PropertyKindCalculus.Iso80000.Part11.womersley (Womersley number) — principle: momentum-transfer: inertial forces / viscous forces, oscillating flow
115 dimension-one kind(s): 115 individuated — clean
-/
#guard_msgs (whitespace := lax) in
#kind_examination_coverage PropertyKindCalculus.Iso80000.Part11

-- Part11 is clean: the census as an invariant, with no message to re-bless
#guard_msgs in
#kind_examination_clean PropertyKindCalculus.Iso80000.Part11

/--
info: examination coverage:
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part12.atomicScatteringFactor (atomic scattering factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part12.braggAngle (Bragg angle)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part12.debyeWallerFactor (Debye-Waller factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part12.grueneisenParameter (Grüneisen parameter)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part12.longRangeOrderParameter (long-range order parameter)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part12.mobilityRatio (mobility ratio)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part12.shortRangeOrderParameter (short-range order parameter)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part12.structureFactor (structure factor)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part12.thermodynamicGrueneisenParameter (thermodynamic Grüneisen parameter)
9 dimension-one kind(s): 0 individuated, 9 UNINDIVIDUATED — examination-coverage violation
-/
#guard_msgs (whitespace := lax) in
#kind_examination_coverage PropertyKindCalculus.Iso80000.Part12

/--
info: examination coverage:
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.channelCapacityPerCharacter (channel capacity per character)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.characterMeanEntropy (character mean entropy)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.characterMeanTransinformationContent (character mean transinformation content)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.conditionalEntropy (conditional entropy)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.conditionalInformationContent (conditional information content)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.decisionContent (decision content)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.entropy (entropy)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.equivalentBinaryStorageCapacity (equivalent binary storage capacity)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.equivocation (equivocation)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.errorProbability (error probability)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.hammingDistance (Hamming distance)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.informationContent (information content)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.irrelevance (irrelevance)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.jointInformationContent (joint information content)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.lossProbability (loss probability)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.maximumEntropy (maximum entropy)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.meanQueueLength (mean queue length)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.meanTransinformationContent (mean transinformation content)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.redundancy (redundancy)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.relativeEntropy (relative entropy)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.relativeRedundancy (relative redundancy)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.storageCapacity (storage capacity)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.trafficCarriedIntensity (traffic carried intensity)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.trafficIntensity (traffic intensity)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.trafficOfferedIntensity (traffic offered intensity)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.transinformationContent (transinformation content)
⚠ UNINDIVIDUATED PropertyKindCalculus.Iso80000.Part13.waitingProbability (waiting probability)
27 dimension-one kind(s): 0 individuated, 27 UNINDIVIDUATED — examination-coverage violation
-/
#guard_msgs (whitespace := lax) in
#kind_examination_coverage PropertyKindCalculus.Iso80000.Part13

/-! ## `#kind_dimensional_coverage` — M10, part by part -/

/--
info: dimensional coverage:
[coherent] PropertyKindCalculus.Iso80000.Part6.voltage.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part6.electricCurrent.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part6.resistance.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part6.voltage.kind LTMCTDimensionBase · PropertyKindCalculus.Iso80000.Part6.electricCurrent.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part6.power.kind LTMCTDimensionBase
2 kind edge(s), all dimensionally coherent — clean
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage PropertyKindCalculus.Iso80000.Part1

-- Part1 is clean: the coverage invariant, with no message to re-bless
#guard_msgs in
#kind_dimensional_clean PropertyKindCalculus.Iso80000.Part1

/--
info: dimensional coverage — no authored kind edges in the given namespaces
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage PropertyKindCalculus.Iso80000.Part2

-- Part2 is clean: the coverage invariant, with no message to re-bless
#guard_msgs in
#kind_dimensional_clean PropertyKindCalculus.Iso80000.Part2

/--
info: dimensional coverage:
[coherent] 1 / PropertyKindCalculus.Iso80000.Part3.periodDuration.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part3.frequency.kind LTMCTDimensionBase
[coherent] 1 / PropertyKindCalculus.Iso80000.Part3.radiusOfCurvature.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part3.curvature.kind LTMCTDimensionBase
[coherent] 1 / PropertyKindCalculus.Iso80000.Part3.wavelength.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part3.repetency.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part3.length.kind LTMCTDimensionBase · PropertyKindCalculus.Iso80000.Part3.length.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part3.area.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part3.pathLength.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part3.duration.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part3.speed.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part3.pathLength.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part3.radius.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part3.planeAngle.kind LTMCTDimensionBase
6 kind edge(s), all dimensionally coherent — clean
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage PropertyKindCalculus.Iso80000.Part3

-- Part3 is clean: the coverage invariant, with no message to re-bless
#guard_msgs in
#kind_dimensional_clean PropertyKindCalculus.Iso80000.Part3

/--
info: dimensional coverage:
[coherent] 1 / PropertyKindCalculus.Iso80000.Part4.massDensity.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part4.specificVolume.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part4.dynamicViscosity.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part4.massDensity.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part4.kinematicViscosity.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part4.force.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part3.area.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part4.pressure.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part4.mass.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part3.volume.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part4.massDensity.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part4.mass.kind LTMCTDimensionBase · PropertyKindCalculus.Iso80000.Part3.velocity.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part4.momentum.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part4.normalStress.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part4.relativeLinearStrain.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part4.modulusOfElasticity.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part4.power.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part4.power.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part4.efficiency.kind LTMCTDimensionBase
7 kind edge(s), all dimensionally coherent — clean
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage PropertyKindCalculus.Iso80000.Part4

-- Part4 is clean: the coverage invariant, with no message to re-bless
#guard_msgs in
#kind_dimensional_clean PropertyKindCalculus.Iso80000.Part4

/--
info: dimensional coverage:
[coherent] 1 / PropertyKindCalculus.Iso80000.Part5.coefficientOfHeatTransfer.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part5.thermalInsulance.kind LTMCTDimensionBase
[coherent] 1 / PropertyKindCalculus.Iso80000.Part5.thermalResistance.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part5.thermalConductance.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part5.heat.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part5.thermodynamicTemperature.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part5.heatCapacity.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part5.heatCapacity.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part4.mass.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part5.specificHeatCapacity.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part5.heatFlowRate.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part3.area.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part5.densityOfHeatFlowRate.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part5.specificHeatCapacityConstantPressure.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part5.specificHeatCapacityConstantVolume.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part5.ratioOfSpecificHeatCapacities.kind LTMCTDimensionBase
⚠ CONFLICTING PropertyKindCalculus.Iso80000.Part5.entropy.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part4.mass.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part5.specificEntropy.kind LTMCTDimensionBase — disagreeing DimensionedKinds for: PropertyKindCalculus.Iso80000.Part5.entropy.kind LTMCTDimensionBase
7 kind edge(s): 6 coherent, 1 CONFLICTING — dimensional-coverage violation
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage PropertyKindCalculus.Iso80000.Part5

/--
info: dimensional coverage:
[coherent] 1 / PropertyKindCalculus.Iso80000.Part6.conductivity.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part6.resistivity.kind LTMCTDimensionBase
[coherent] 1 / PropertyKindCalculus.Iso80000.Part6.impedance.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part6.admittance.kind LTMCTDimensionBase
[coherent] 1 / PropertyKindCalculus.Iso80000.Part6.reluctance.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part6.permeance.kind LTMCTDimensionBase
[coherent] 1 / PropertyKindCalculus.Iso80000.Part6.resistance.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part6.conductance.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part6.activePower.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part6.apparentPower.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part6.powerFactor.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part6.electricCharge.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part3.duration.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part6.electricCurrent.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part6.electricCharge.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part6.voltage.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part6.capacitance.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part6.voltage.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part6.electricCurrent.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part6.resistance.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part6.voltage.kind LTMCTDimensionBase · PropertyKindCalculus.Iso80000.Part6.electricCurrent.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part6.power.kind LTMCTDimensionBase
9 kind edge(s), all dimensionally coherent — clean
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage PropertyKindCalculus.Iso80000.Part6

-- Part6 is clean: the coverage invariant, with no message to re-bless
#guard_msgs in
#kind_dimensional_clean PropertyKindCalculus.Iso80000.Part6

/--
info: dimensional coverage:
[coherent] PropertyKindCalculus.Iso80000.Part7.luminousFlux.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part7.radiantFlux.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part7.luminousEfficacy.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part7.photonNumber.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part3.duration.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part7.photonFlux.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part7.radiantEnergy.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part3.duration.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part7.radiantFlux.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part7.radiantFlux.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part3.area.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part7.irradiance.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part7.radiantFlux.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part3.solidAngle.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part7.radiantIntensity.kind LTMCTDimensionBase
5 kind edge(s), all dimensionally coherent — clean
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage PropertyKindCalculus.Iso80000.Part7

-- Part7 is clean: the coverage invariant, with no message to re-bless
#guard_msgs in
#kind_dimensional_clean PropertyKindCalculus.Iso80000.Part7

/--
info: dimensional coverage:
[coherent] PropertyKindCalculus.Iso80000.Part8.particleDisplacement.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part3.duration.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part8.particleVelocity.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part8.particleVelocity.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part3.duration.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part8.particleAcceleration.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part8.soundPressure.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part8.particleVelocity.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part8.characteristicImpedance.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part8.soundPressure.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part8.volumeFlowRate.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part8.acousticImpedance.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part8.soundPressure.kind LTMCTDimensionBase · PropertyKindCalculus.Iso80000.Part8.particleVelocity.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part8.soundIntensity.kind LTMCTDimensionBase
5 kind edge(s), all dimensionally coherent — clean
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage PropertyKindCalculus.Iso80000.Part8

-- Part8 is clean: the coverage invariant, with no message to re-bless
#guard_msgs in
#kind_dimensional_clean PropertyKindCalculus.Iso80000.Part8

/--
info: dimensional coverage:
[coherent] PropertyKindCalculus.Iso80000.Part3.volume.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part9.amountOfSubstance.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part9.molarVolume.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part4.mass.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part9.amountOfSubstance.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part9.molarMass.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part5.internalEnergy.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part9.amountOfSubstance.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part9.molarInternalEnergy.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part9.amountOfSubstance.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part3.volume.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part9.amountConcentration.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part9.amountOfSubstance.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part4.mass.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part9.molality.kind LTMCTDimensionBase
5 kind edge(s), all dimensionally coherent — clean
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage PropertyKindCalculus.Iso80000.Part9

-- Part9 is clean: the coverage invariant, with no message to re-bless
#guard_msgs in
#kind_dimensional_clean PropertyKindCalculus.Iso80000.Part9

/--
info: dimensional coverage:
[coherent] 1 / PropertyKindCalculus.Iso80000.Part10.decayConstant.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part10.meanLife.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part10.absorbedDose.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part3.duration.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part10.absorbedDoseRate.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part10.absorbedDose.kind LTMCTDimensionBase · PropertyKindCalculus.Iso80000.Part10.qualityFactor.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part10.doseEquivalent.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part10.activity.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part4.mass.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part10.specificActivity.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part10.linearAttenuationCoefficient.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part4.massDensity.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part10.massAttenuationCoefficient.kind LTMCTDimensionBase
5 kind edge(s), all dimensionally coherent — clean
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage PropertyKindCalculus.Iso80000.Part10

-- Part10 is clean: the coverage invariant, with no message to re-bless
#guard_msgs in
#kind_dimensional_clean PropertyKindCalculus.Iso80000.Part10

/--
info: dimensional coverage — no authored kind edges in the given namespaces
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage PropertyKindCalculus.Iso80000.Part11

-- Part11 is clean: the coverage invariant, with no message to re-bless
#guard_msgs in
#kind_dimensional_clean PropertyKindCalculus.Iso80000.Part11

/--
info: dimensional coverage:
[coherent] PropertyKindCalculus.Iso80000.Part12.seebeckCoefficient.kind LTMCTDimensionBase · PropertyKindCalculus.Iso80000.Part5.thermodynamicTemperature.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part12.peltierCoefficient.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part12.thermoelectricVoltage.kind LTMCTDimensionBase / PropertyKindCalculus.Iso80000.Part5.thermodynamicTemperature.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part12.seebeckCoefficient.kind LTMCTDimensionBase
2 kind edge(s), all dimensionally coherent — clean
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage PropertyKindCalculus.Iso80000.Part12

-- Part12 is clean: the coverage invariant, with no message to re-bless
#guard_msgs in
#kind_dimensional_clean PropertyKindCalculus.Iso80000.Part12

/--
info: dimensional coverage:
[coherent] 1 / PropertyKindCalculus.Iso80000.Part13.binaryDigitRate.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part13.periodOfBinaryDigits.kind LTMCTDimensionBase
[coherent] 1 / PropertyKindCalculus.Iso80000.Part13.transferRate.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part13.periodOfDataElements.kind LTMCTDimensionBase
[coherent] PropertyKindCalculus.Iso80000.Part13.carrierPower.kind LTMCTDimensionBase · PropertyKindCalculus.Iso80000.Part13.periodOfBinaryDigits.kind LTMCTDimensionBase → PropertyKindCalculus.Iso80000.Part13.signalEnergyPerBinaryDigit.kind LTMCTDimensionBase
3 kind edge(s), all dimensionally coherent — clean
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage PropertyKindCalculus.Iso80000.Part13

-- Part13 is clean: the coverage invariant, with no message to re-bless
#guard_msgs in
#kind_dimensional_clean PropertyKindCalculus.Iso80000.Part13

end -- pkc-blanket-expose
end -- pkc-blanket
