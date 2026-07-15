/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Base.Gate
public import QuantumAlg.Util.Asymptotics
public import Cslib.Algorithms.Lean.TimeM

/-!
# Trusted cost annotations

This module connects Lean-QuantumAlg theorem endpoints to CSLib's `TimeM`
interface. A value of `Timed α` returns an object of type `α` and carries a
trusted natural-number cost annotation.

The cost annotation is intentionally not derived from the Lean evaluator or from
matrix dimensions. Following CSLib's `TimeM` convention, correctness is proved
on `.ret`, while `.time` records the selected model. In the current quantum
algorithm bridge, one unit means one oracle query for the single-query
Walsh-Hadamard algorithms, and one good/bad-plane iterate for amplitude
amplification and Grover.

This is an operator-level bridge over the existing pure-state and gate
semantics. Fuller quantum program logics, such as density-operator or
Hoare-style semantics for quantum while programs, are future extensions rather
than prerequisites for this TimeM layer.

The structured classical-operation taxonomy mirrors the source obligations that
must remain concrete in RSA/ECC resource theorems: continued-fraction and gcd
post-processing in Shor order finding [Sho95, source.tex:1124-1148,
1614-1633], reversible modular arithmetic and clean work registers [VBE95,
9511018.tex:83-106, 274-316, 423-428] [Bea02, arxivfact.tex:97-118], short-DLP
factoring reductions [EH17, source.tex:806-842, 878-953], and published
resource-envelope fields that are treated as source-backed estimates until an
exact or explicit-upper-bound pass discharges them [GE19, main.tex:70-79,
710-733].
-/

@[expose] public section

namespace QuantumAlg

universe u

/-- A CSLib `TimeM` computation with natural-number cost. -/
abbrev Timed (α : Type u) := Cslib.Algorithms.Lean.TimeM ℕ α

namespace Timed

/-- Attach a trusted cost to a return value. -/
def trusted {α : Type u} (cost : ℕ) (ret : α) : Timed α := ⟨ret, cost⟩

@[simp]
theorem trusted_ret {α : Type u} (cost : ℕ) (ret : α) :
    (trusted cost ret).ret = ret := rfl

@[simp]
theorem trusted_time {α : Type u} (cost : ℕ) (ret : α) :
    (trusted cost ret).time = cost := rfl

end Timed

/-- A trusted resource profile for registered theorem endpoints.

The fields are intentionally lightweight counters. They record the resource
model claimed beside a correctness theorem, not a derivation from Lean
evaluation. -/
structure ResourceProfile where
  /-- Trusted oracle-query count in the selected endpoint model. -/
  oracleQueries : ℕ
  /-- Trusted Hadamard-gate count for circuit statements. -/
  hadamardGates : ℕ
  /-- Trusted count of elementary non-Hadamard gates. -/
  elementaryGates : ℕ
  /-- Trusted count of classical side computations. -/
  classicalOps : ℕ
deriving DecidableEq

namespace ResourceProfile

/-- The empty resource profile. -/
def zero : ResourceProfile where
  oracleQueries := 0
  hadamardGates := 0
  elementaryGates := 0
  classicalOps := 0

/-- Sequential composition adds every resource counter. -/
def sequential (left right : ResourceProfile) : ResourceProfile where
  oracleQueries := left.oracleQueries + right.oracleQueries
  hadamardGates := left.hadamardGates + right.hadamardGates
  elementaryGates := left.elementaryGates + right.elementaryGates
  classicalOps := left.classicalOps + right.classicalOps

/-- Tensor/parallel circuit composition uses the same additive counters. -/
def tensor (left right : ResourceProfile) : ResourceProfile :=
  sequential left right

/-- Repeat a resource profile `k` times. -/
def scale (k : ℕ) (profile : ResourceProfile) : ResourceProfile where
  oracleQueries := k * profile.oracleQueries
  hadamardGates := k * profile.hadamardGates
  elementaryGates := k * profile.elementaryGates
  classicalOps := k * profile.classicalOps

/-- Exact counter claim used by supporting public theorem statements. -/
def HasExactCounts (profile : ResourceProfile)
    (oracleQueries hadamardGates elementaryGates classicalOps : ℕ) : Prop :=
  profile.oracleQueries = oracleQueries ∧
    profile.hadamardGates = hadamardGates ∧
    profile.elementaryGates = elementaryGates ∧
    profile.classicalOps = classicalOps

@[ext]
theorem ext {left right : ResourceProfile}
    (horacle : left.oracleQueries = right.oracleQueries)
    (hhadamard : left.hadamardGates = right.hadamardGates)
    (helementary : left.elementaryGates = right.elementaryGates)
    (hclassical : left.classicalOps = right.classicalOps) :
    left = right := by
  cases left
  cases right
  simp_all

@[simp]
theorem sequential_oracleQueries (left right : ResourceProfile) :
    (sequential left right).oracleQueries =
      left.oracleQueries + right.oracleQueries := rfl

@[simp]
theorem sequential_hadamardGates (left right : ResourceProfile) :
    (sequential left right).hadamardGates =
      left.hadamardGates + right.hadamardGates := rfl

@[simp]
theorem sequential_elementaryGates (left right : ResourceProfile) :
    (sequential left right).elementaryGates =
      left.elementaryGates + right.elementaryGates := rfl

@[simp]
theorem sequential_classicalOps (left right : ResourceProfile) :
    (sequential left right).classicalOps =
      left.classicalOps + right.classicalOps := rfl

@[simp]
theorem tensor_oracleQueries (left right : ResourceProfile) :
    (tensor left right).oracleQueries =
      left.oracleQueries + right.oracleQueries := rfl

@[simp]
theorem tensor_hadamardGates (left right : ResourceProfile) :
    (tensor left right).hadamardGates =
      left.hadamardGates + right.hadamardGates := rfl

@[simp]
theorem tensor_elementaryGates (left right : ResourceProfile) :
    (tensor left right).elementaryGates =
      left.elementaryGates + right.elementaryGates := rfl

@[simp]
theorem tensor_classicalOps (left right : ResourceProfile) :
    (tensor left right).classicalOps =
      left.classicalOps + right.classicalOps := rfl

@[simp]
theorem scale_oracleQueries (k : ℕ) (profile : ResourceProfile) :
    (scale k profile).oracleQueries = k * profile.oracleQueries := rfl

@[simp]
theorem scale_hadamardGates (k : ℕ) (profile : ResourceProfile) :
    (scale k profile).hadamardGates = k * profile.hadamardGates := rfl

@[simp]
theorem scale_elementaryGates (k : ℕ) (profile : ResourceProfile) :
    (scale k profile).elementaryGates = k * profile.elementaryGates := rfl

@[simp]
theorem scale_classicalOps (k : ℕ) (profile : ResourceProfile) :
    (scale k profile).classicalOps = k * profile.classicalOps := rfl

end ResourceProfile

/-! ### Classical arithmetic operation taxonomy -/

/-- Whether a parameterized natural-number resource count is an exact count or
an explicit upper bound. Both cases are concrete functions into `ℕ`, which keeps
final resource statements out of asymptotic notation. -/
inductive ClassicalCountKind where
  | exactCount
  | explicitUpperBound
deriving DecidableEq

/-- A concrete natural-number count as a function of problem parameters. -/
structure ClassicalCountSpec (Params : Type u) where
  /-- Whether this concrete count is exact or an explicit upper bound. -/
  kind : ClassicalCountKind
  /-- Natural-number count as a function of the parameter record. -/
  count : Params → ℕ

namespace ClassicalCountSpec

/-- Mark a parameterized count as exact. -/
def exactCount {Params : Type u} (count : Params → ℕ) : ClassicalCountSpec Params where
  kind := .exactCount
  count := count

/-- Mark a parameterized count as an explicit upper-bound function. -/
def explicitUpperBound {Params : Type u} (count : Params → ℕ) :
    ClassicalCountSpec Params where
  kind := .explicitUpperBound
  count := count

@[simp]
theorem exactCount_kind {Params : Type u} (count : Params → ℕ) :
    (exactCount count).kind = .exactCount := rfl

@[simp]
theorem exactCount_count {Params : Type u} (count : Params → ℕ) :
    (exactCount count).count = count := rfl

@[simp]
theorem explicitUpperBound_kind {Params : Type u} (count : Params → ℕ) :
    (explicitUpperBound count).kind = .explicitUpperBound := rfl

@[simp]
theorem explicitUpperBound_count {Params : Type u} (count : Params → ℕ) :
    (explicitUpperBound count).count = count := rfl

end ClassicalCountSpec

/-- Bit- and integer-level classical arithmetic operations. -/
structure BitIntegerOperationProfile where
  /-- Classical-operation count for comparisons. -/
  comparisons : ℕ
  /-- Classical-operation count for shifts. -/
  shifts : ℕ
  /-- Classical-operation count for additions. -/
  additions : ℕ
  /-- Classical-operation count for subtractions. -/
  subtractions : ℕ
  /-- Classical-operation count for multiplications. -/
  multiplications : ℕ
  /-- Classical-operation count for divisions. -/
  divisions : ℕ
  /-- Classical-operation count for modular reductions. -/
  modularReductions : ℕ
deriving DecidableEq

namespace BitIntegerOperationProfile

/-- Empty bit/integer operation profile. -/
def zero : BitIntegerOperationProfile where
  comparisons := 0
  shifts := 0
  additions := 0
  subtractions := 0
  multiplications := 0
  divisions := 0
  modularReductions := 0

/-- Componentwise addition for sequential classical work. -/
def sequential (left right : BitIntegerOperationProfile) : BitIntegerOperationProfile where
  comparisons := left.comparisons + right.comparisons
  shifts := left.shifts + right.shifts
  additions := left.additions + right.additions
  subtractions := left.subtractions + right.subtractions
  multiplications := left.multiplications + right.multiplications
  divisions := left.divisions + right.divisions
  modularReductions := left.modularReductions + right.modularReductions

/-- Repeat a bit/integer operation profile `k` times. -/
def scale (k : ℕ) (profile : BitIntegerOperationProfile) : BitIntegerOperationProfile where
  comparisons := k * profile.comparisons
  shifts := k * profile.shifts
  additions := k * profile.additions
  subtractions := k * profile.subtractions
  multiplications := k * profile.multiplications
  divisions := k * profile.divisions
  modularReductions := k * profile.modularReductions

/-- Total scalar operation count obtained by summing every bit/integer family. -/
def total (profile : BitIntegerOperationProfile) : ℕ :=
  profile.comparisons + profile.shifts + profile.additions + profile.subtractions +
    profile.multiplications + profile.divisions + profile.modularReductions

@[simp]
theorem total_sequential (left right : BitIntegerOperationProfile) :
    (sequential left right).total = left.total + right.total := by
  simp [total, sequential]
  omega

@[simp]
theorem total_scale (k : ℕ) (profile : BitIntegerOperationProfile) :
    (scale k profile).total = k * profile.total := by
  simp [total, scale]
  ring_nf

end BitIntegerOperationProfile

/-- Number-theoretic classical post-processing operations. -/
structure NumberTheoreticOperationProfile where
  /-- Classical-operation count for greatest-common-divisor computations. -/
  gcds : ℕ
  /-- Classical-operation count for extended Euclidean computations. -/
  extendedEuclidean : ℕ
  /-- Classical-operation count for continued fractions. -/
  continuedFractions : ℕ
  /-- Classical-operation count for rational reconstructions. -/
  rationalReconstructions : ℕ
deriving DecidableEq

namespace NumberTheoreticOperationProfile

/-- Empty number-theoretic operation profile. -/
def zero : NumberTheoreticOperationProfile where
  gcds := 0
  extendedEuclidean := 0
  continuedFractions := 0
  rationalReconstructions := 0

/-- Componentwise addition for sequential number-theoretic work. -/
def sequential (left right : NumberTheoreticOperationProfile) :
    NumberTheoreticOperationProfile where
  gcds := left.gcds + right.gcds
  extendedEuclidean := left.extendedEuclidean + right.extendedEuclidean
  continuedFractions := left.continuedFractions + right.continuedFractions
  rationalReconstructions := left.rationalReconstructions + right.rationalReconstructions

/-- Repeat a number-theoretic operation profile `k` times. -/
def scale (k : ℕ) (profile : NumberTheoreticOperationProfile) :
    NumberTheoreticOperationProfile where
  gcds := k * profile.gcds
  extendedEuclidean := k * profile.extendedEuclidean
  continuedFractions := k * profile.continuedFractions
  rationalReconstructions := k * profile.rationalReconstructions

/-- Total scalar operation count obtained by summing every number-theoretic family. -/
def total (profile : NumberTheoreticOperationProfile) : ℕ :=
  profile.gcds + profile.extendedEuclidean + profile.continuedFractions +
    profile.rationalReconstructions

@[simp]
theorem total_sequential (left right : NumberTheoreticOperationProfile) :
    (sequential left right).total = left.total + right.total := by
  simp [total, sequential]
  omega

@[simp]
theorem total_scale (k : ℕ) (profile : NumberTheoreticOperationProfile) :
    (scale k profile).total = k * profile.total := by
  simp [total, scale]
  ring_nf

end NumberTheoreticOperationProfile

/-- Modular and finite-field classical arithmetic operations. -/
structure ModularFieldOperationProfile where
  /-- Classical-operation count for additions. -/
  additions : ℕ
  /-- Classical-operation count for subtractions. -/
  subtractions : ℕ
  /-- Classical-operation count for negations. -/
  negations : ℕ
  /-- Classical-operation count for doublings. -/
  doublings : ℕ
  /-- Classical-operation count for multiplications. -/
  multiplications : ℕ
  /-- Classical-operation count for squarings. -/
  squarings : ℕ
  /-- Classical-operation count for inversions. -/
  inversions : ℕ
  /-- Classical-operation count for divisions. -/
  divisions : ℕ
deriving DecidableEq

namespace ModularFieldOperationProfile

/-- Empty modular/field operation profile. -/
def zero : ModularFieldOperationProfile where
  additions := 0
  subtractions := 0
  negations := 0
  doublings := 0
  multiplications := 0
  squarings := 0
  inversions := 0
  divisions := 0

/-- Componentwise addition for sequential modular/field work. -/
def sequential (left right : ModularFieldOperationProfile) :
    ModularFieldOperationProfile where
  additions := left.additions + right.additions
  subtractions := left.subtractions + right.subtractions
  negations := left.negations + right.negations
  doublings := left.doublings + right.doublings
  multiplications := left.multiplications + right.multiplications
  squarings := left.squarings + right.squarings
  inversions := left.inversions + right.inversions
  divisions := left.divisions + right.divisions

/-- Repeat a modular/field operation profile `k` times. -/
def scale (k : ℕ) (profile : ModularFieldOperationProfile) :
    ModularFieldOperationProfile where
  additions := k * profile.additions
  subtractions := k * profile.subtractions
  negations := k * profile.negations
  doublings := k * profile.doublings
  multiplications := k * profile.multiplications
  squarings := k * profile.squarings
  inversions := k * profile.inversions
  divisions := k * profile.divisions

/-- Total scalar operation count obtained by summing every modular/field family. -/
def total (profile : ModularFieldOperationProfile) : ℕ :=
  profile.additions + profile.subtractions + profile.negations + profile.doublings +
    profile.multiplications + profile.squarings + profile.inversions + profile.divisions

@[simp]
theorem total_sequential (left right : ModularFieldOperationProfile) :
    (sequential left right).total = left.total + right.total := by
  simp [total, sequential]
  omega

@[simp]
theorem total_scale (k : ℕ) (profile : ModularFieldOperationProfile) :
    (scale k profile).total = k * profile.total := by
  simp [total, scale]
  ring_nf

end ModularFieldOperationProfile

/-- Group, lookup, precomputation, and classical-control operation families. -/
structure GroupControlOperationProfile where
  /-- Classical-operation count for finite cyclic group operations. -/
  finiteCyclicGroupOps : ℕ
  /-- Classical-operation count for elliptic curve group operations. -/
  ellipticCurveGroupOps : ℕ
  /-- Classical-operation count for lookup table operations. -/
  lookupTableOps : ℕ
  /-- Classical-operation count for precompute operations. -/
  precomputeOps : ℕ
  /-- Classical-operation count for control rewrite operations. -/
  controlRewriteOps : ℕ
deriving DecidableEq

namespace GroupControlOperationProfile

/-- Empty group/control operation profile. -/
def zero : GroupControlOperationProfile where
  finiteCyclicGroupOps := 0
  ellipticCurveGroupOps := 0
  lookupTableOps := 0
  precomputeOps := 0
  controlRewriteOps := 0

/-- Componentwise addition for sequential group/control work. -/
def sequential (left right : GroupControlOperationProfile) : GroupControlOperationProfile where
  finiteCyclicGroupOps := left.finiteCyclicGroupOps + right.finiteCyclicGroupOps
  ellipticCurveGroupOps := left.ellipticCurveGroupOps + right.ellipticCurveGroupOps
  lookupTableOps := left.lookupTableOps + right.lookupTableOps
  precomputeOps := left.precomputeOps + right.precomputeOps
  controlRewriteOps := left.controlRewriteOps + right.controlRewriteOps

/-- Repeat a group/control operation profile `k` times. -/
def scale (k : ℕ) (profile : GroupControlOperationProfile) : GroupControlOperationProfile where
  finiteCyclicGroupOps := k * profile.finiteCyclicGroupOps
  ellipticCurveGroupOps := k * profile.ellipticCurveGroupOps
  lookupTableOps := k * profile.lookupTableOps
  precomputeOps := k * profile.precomputeOps
  controlRewriteOps := k * profile.controlRewriteOps

/-- Total scalar operation count obtained by summing every group/control family. -/
def total (profile : GroupControlOperationProfile) : ℕ :=
  profile.finiteCyclicGroupOps + profile.ellipticCurveGroupOps +
    profile.lookupTableOps + profile.precomputeOps + profile.controlRewriteOps

@[simp]
theorem total_sequential (left right : GroupControlOperationProfile) :
    (sequential left right).total = left.total + right.total := by
  simp [total, sequential]
  omega

@[simp]
theorem total_scale (k : ℕ) (profile : GroupControlOperationProfile) :
    (scale k profile).total = k * profile.total := by
  simp [total, scale]
  ring_nf

end GroupControlOperationProfile

/-- Classical arithmetic profile used by exact-resource statements that need to
keep post-processing, modular/field arithmetic, group work, precomputation, and
control rewrites separate before projecting to a scalar `classicalOps` count. -/
structure ClassicalArithmeticProfile where
  /-- Bit integer component of this record. -/
  bitInteger : BitIntegerOperationProfile
  /-- Number theoretic component of this record. -/
  numberTheoretic : NumberTheoreticOperationProfile
  /-- Modular field component of this record. -/
  modularField : ModularFieldOperationProfile
  /-- Group control component of this record. -/
  groupControl : GroupControlOperationProfile
deriving DecidableEq

namespace ClassicalArithmeticProfile

/-- Empty classical arithmetic operation profile. -/
def zero : ClassicalArithmeticProfile where
  bitInteger := BitIntegerOperationProfile.zero
  numberTheoretic := NumberTheoreticOperationProfile.zero
  modularField := ModularFieldOperationProfile.zero
  groupControl := GroupControlOperationProfile.zero

/-- Carry a scalar classical-control bound in the structured taxonomy. This is
used when a source gives only a total control/rewrite operation bound rather
than a family-by-family breakdown. -/
def ofControlRewriteOps (count : ℕ) : ClassicalArithmeticProfile where
  bitInteger := BitIntegerOperationProfile.zero
  numberTheoretic := NumberTheoreticOperationProfile.zero
  modularField := ModularFieldOperationProfile.zero
  groupControl := { GroupControlOperationProfile.zero with controlRewriteOps := count }

/-- Componentwise addition for sequential classical arithmetic work. -/
def sequential (left right : ClassicalArithmeticProfile) : ClassicalArithmeticProfile where
  bitInteger := BitIntegerOperationProfile.sequential left.bitInteger right.bitInteger
  numberTheoretic :=
    NumberTheoreticOperationProfile.sequential left.numberTheoretic right.numberTheoretic
  modularField := ModularFieldOperationProfile.sequential left.modularField right.modularField
  groupControl := GroupControlOperationProfile.sequential left.groupControl right.groupControl

/-- Repeat a classical arithmetic profile `k` times. -/
def scale (k : ℕ) (profile : ClassicalArithmeticProfile) : ClassicalArithmeticProfile where
  bitInteger := BitIntegerOperationProfile.scale k profile.bitInteger
  numberTheoretic := NumberTheoreticOperationProfile.scale k profile.numberTheoretic
  modularField := ModularFieldOperationProfile.scale k profile.modularField
  groupControl := GroupControlOperationProfile.scale k profile.groupControl

/-- Project the structured classical arithmetic profile to one scalar count. -/
def total (profile : ClassicalArithmeticProfile) : ℕ :=
  profile.bitInteger.total + profile.numberTheoretic.total + profile.modularField.total +
    profile.groupControl.total

@[simp]
theorem total_ofControlRewriteOps (count : ℕ) :
    (ofControlRewriteOps count).total = count := by
  simp [ofControlRewriteOps, total, GroupControlOperationProfile.total,
    BitIntegerOperationProfile.zero, NumberTheoreticOperationProfile.zero,
    ModularFieldOperationProfile.zero, GroupControlOperationProfile.zero,
    BitIntegerOperationProfile.total, NumberTheoreticOperationProfile.total,
    ModularFieldOperationProfile.total]

@[simp]
theorem total_sequential (left right : ClassicalArithmeticProfile) :
    (sequential left right).total = left.total + right.total := by
  simp [total, sequential]
  omega

@[simp]
theorem total_scale (k : ℕ) (profile : ClassicalArithmeticProfile) :
    (scale k profile).total = k * profile.total := by
  simp [total, scale]
  ring_nf

/-- Replace the scalar classical counter in a quantum resource profile with the
total of a structured classical arithmetic profile. -/
def toResourceProfile (quantum : ResourceProfile) (classical : ClassicalArithmeticProfile) :
    ResourceProfile :=
  { quantum with classicalOps := classical.total }

/-- Exact structured classical arithmetic claim. -/
def HasExactCounts (profile expected : ClassicalArithmeticProfile) : Prop :=
  profile = expected

@[simp]
theorem zero_total : zero.total = 0 := rfl

@[simp]
theorem toResourceProfile_classicalOps
    (quantum : ResourceProfile) (classical : ClassicalArithmeticProfile) :
    (toResourceProfile quantum classical).classicalOps = classical.total := rfl

@[simp]
theorem toResourceProfile_oracleQueries
    (quantum : ResourceProfile) (classical : ClassicalArithmeticProfile) :
    (toResourceProfile quantum classical).oracleQueries = quantum.oracleQueries := rfl

@[simp]
theorem toResourceProfile_hadamardGates
    (quantum : ResourceProfile) (classical : ClassicalArithmeticProfile) :
    (toResourceProfile quantum classical).hadamardGates = quantum.hadamardGates := rfl

@[simp]
theorem toResourceProfile_elementaryGates
    (quantum : ResourceProfile) (classical : ClassicalArithmeticProfile) :
    (toResourceProfile quantum classical).elementaryGates = quantum.elementaryGates := rfl

end ClassicalArithmeticProfile

/-! ### Modular-arithmetic exact-resource profiles -/

/-- Exact-resource dimensions used by reversible modular-arithmetic circuit
statements. The fields are concrete natural-number counters; downstream theorem
statements can instantiate them with exact functions or explicit upper-bound
functions of the problem parameters. -/
structure ModularArithmeticResourceProfile where
  /-- Total logical qubits/register footprint counted by the circuit statement. -/
  logicalQubits : ℕ
  /-- Qubits used for encoded input/output data registers. -/
  dataQubits : ℕ
  /-- Qubits used as workspace or clean ancilla registers. -/
  workQubits : ℕ
  /-- Oracle or black-box subroutine queries. -/
  oracleQueries : ℕ
  /-- Hadamard gates, when the arithmetic model counts them separately. -/
  hadamardGates : ℕ
  /-- Toffoli gate count. -/
  toffoliGates : ℕ
  /-- T gate count. -/
  tGates : ℕ
  /-- CNOT gate count. -/
  cnotGates : ℕ
  /-- Other one-qubit gates counted by the selected arithmetic model. -/
  singleQubitGates : ℕ
  /-- Maximal circuit depth in the selected gate model. -/
  circuitDepth : ℕ
  /-- Toffoli-depth component, when available separately from total depth. -/
  toffoliDepth : ℕ
  /-- Structured classical accounting for precomputation, lookup generation,
  validation, and post-processing associated with the circuit family. -/
  classicalArithmetic : ClassicalArithmeticProfile
deriving DecidableEq

namespace ModularArithmeticResourceProfile

/-- Empty modular-arithmetic resource profile. -/
def zero : ModularArithmeticResourceProfile where
  logicalQubits := 0
  dataQubits := 0
  workQubits := 0
  oracleQueries := 0
  hadamardGates := 0
  toffoliGates := 0
  tGates := 0
  cnotGates := 0
  singleQubitGates := 0
  circuitDepth := 0
  toffoliDepth := 0
  classicalArithmetic := ClassicalArithmeticProfile.zero

/-- Projection of the named gate-family counters to the older scalar elementary
gate counter. -/
def elementaryGateCount (profile : ModularArithmeticResourceProfile) : ℕ :=
  profile.toffoliGates + profile.tGates + profile.cnotGates + profile.singleQubitGates

/-- Forget the modular-arithmetic-specific dimensions and keep the coarse
resource counters used by existing circuit statements. -/
def toResourceProfile (profile : ModularArithmeticResourceProfile) : ResourceProfile where
  oracleQueries := profile.oracleQueries
  hadamardGates := profile.hadamardGates
  elementaryGates := profile.elementaryGateCount
  classicalOps := profile.classicalArithmetic.total

/-- Sequential composition reuses the larger live footprint while adding all
query, gate, depth, and classical counters. -/
def sequential (left right : ModularArithmeticResourceProfile) :
    ModularArithmeticResourceProfile where
  logicalQubits := max left.logicalQubits right.logicalQubits
  dataQubits := max left.dataQubits right.dataQubits
  workQubits := max left.workQubits right.workQubits
  oracleQueries := left.oracleQueries + right.oracleQueries
  hadamardGates := left.hadamardGates + right.hadamardGates
  toffoliGates := left.toffoliGates + right.toffoliGates
  tGates := left.tGates + right.tGates
  cnotGates := left.cnotGates + right.cnotGates
  singleQubitGates := left.singleQubitGates + right.singleQubitGates
  circuitDepth := left.circuitDepth + right.circuitDepth
  toffoliDepth := left.toffoliDepth + right.toffoliDepth
  classicalArithmetic :=
    ClassicalArithmeticProfile.sequential left.classicalArithmetic right.classicalArithmetic

/-- Parallel/tensor composition allocates both live footprints while composing
depths by maximum and adding counted work. -/
def parallel (left right : ModularArithmeticResourceProfile) :
    ModularArithmeticResourceProfile where
  logicalQubits := left.logicalQubits + right.logicalQubits
  dataQubits := left.dataQubits + right.dataQubits
  workQubits := left.workQubits + right.workQubits
  oracleQueries := left.oracleQueries + right.oracleQueries
  hadamardGates := left.hadamardGates + right.hadamardGates
  toffoliGates := left.toffoliGates + right.toffoliGates
  tGates := left.tGates + right.tGates
  cnotGates := left.cnotGates + right.cnotGates
  singleQubitGates := left.singleQubitGates + right.singleQubitGates
  circuitDepth := max left.circuitDepth right.circuitDepth
  toffoliDepth := max left.toffoliDepth right.toffoliDepth
  classicalArithmetic :=
    ClassicalArithmeticProfile.sequential left.classicalArithmetic right.classicalArithmetic

/-- Repeat a modular-arithmetic profile sequentially. Positive repetition reuses
the same live footprint and scales counted work; zero repetitions are empty. -/
def repeatSequential : ℕ → ModularArithmeticResourceProfile → ModularArithmeticResourceProfile
  | 0, _ => zero
  | k + 1, profile =>
      { logicalQubits := profile.logicalQubits
        dataQubits := profile.dataQubits
        workQubits := profile.workQubits
        oracleQueries := (k + 1) * profile.oracleQueries
        hadamardGates := (k + 1) * profile.hadamardGates
        toffoliGates := (k + 1) * profile.toffoliGates
        tGates := (k + 1) * profile.tGates
        cnotGates := (k + 1) * profile.cnotGates
        singleQubitGates := (k + 1) * profile.singleQubitGates
        circuitDepth := (k + 1) * profile.circuitDepth
        toffoliDepth := (k + 1) * profile.toffoliDepth
        classicalArithmetic :=
          ClassicalArithmeticProfile.scale (k + 1) profile.classicalArithmetic }

@[simp]
theorem zero_logicalQubits : zero.logicalQubits = 0 := rfl

@[simp]
theorem zero_toResourceProfile : zero.toResourceProfile = ResourceProfile.zero := rfl

@[simp]
theorem toResourceProfile_oracleQueries (profile : ModularArithmeticResourceProfile) :
    profile.toResourceProfile.oracleQueries = profile.oracleQueries := rfl

@[simp]
theorem toResourceProfile_hadamardGates (profile : ModularArithmeticResourceProfile) :
    profile.toResourceProfile.hadamardGates = profile.hadamardGates := rfl

@[simp]
theorem toResourceProfile_elementaryGates (profile : ModularArithmeticResourceProfile) :
    profile.toResourceProfile.elementaryGates = profile.elementaryGateCount := rfl

@[simp]
theorem toResourceProfile_classicalOps (profile : ModularArithmeticResourceProfile) :
    profile.toResourceProfile.classicalOps = profile.classicalArithmetic.total := rfl

@[simp]
theorem sequential_logicalQubits (left right : ModularArithmeticResourceProfile) :
    (sequential left right).logicalQubits = max left.logicalQubits right.logicalQubits := rfl

@[simp]
theorem sequential_dataQubits (left right : ModularArithmeticResourceProfile) :
    (sequential left right).dataQubits = max left.dataQubits right.dataQubits := rfl

@[simp]
theorem sequential_workQubits (left right : ModularArithmeticResourceProfile) :
    (sequential left right).workQubits = max left.workQubits right.workQubits := rfl

@[simp]
theorem sequential_oracleQueries (left right : ModularArithmeticResourceProfile) :
    (sequential left right).oracleQueries = left.oracleQueries + right.oracleQueries := rfl

@[simp]
theorem sequential_hadamardGates (left right : ModularArithmeticResourceProfile) :
    (sequential left right).hadamardGates = left.hadamardGates + right.hadamardGates := rfl

@[simp]
theorem sequential_toffoliGates (left right : ModularArithmeticResourceProfile) :
    (sequential left right).toffoliGates = left.toffoliGates + right.toffoliGates := rfl

@[simp]
theorem sequential_tGates (left right : ModularArithmeticResourceProfile) :
    (sequential left right).tGates = left.tGates + right.tGates := rfl

@[simp]
theorem sequential_cnotGates (left right : ModularArithmeticResourceProfile) :
    (sequential left right).cnotGates = left.cnotGates + right.cnotGates := rfl

@[simp]
theorem sequential_singleQubitGates (left right : ModularArithmeticResourceProfile) :
    (sequential left right).singleQubitGates =
      left.singleQubitGates + right.singleQubitGates := rfl

@[simp]
theorem sequential_circuitDepth (left right : ModularArithmeticResourceProfile) :
    (sequential left right).circuitDepth = left.circuitDepth + right.circuitDepth := rfl

@[simp]
theorem sequential_toffoliDepth (left right : ModularArithmeticResourceProfile) :
    (sequential left right).toffoliDepth = left.toffoliDepth + right.toffoliDepth := rfl

@[simp]
theorem sequential_classicalArithmetic (left right : ModularArithmeticResourceProfile) :
    (sequential left right).classicalArithmetic =
      ClassicalArithmeticProfile.sequential
        left.classicalArithmetic right.classicalArithmetic := rfl

@[simp]
theorem parallel_logicalQubits (left right : ModularArithmeticResourceProfile) :
    (parallel left right).logicalQubits = left.logicalQubits + right.logicalQubits := rfl

@[simp]
theorem parallel_dataQubits (left right : ModularArithmeticResourceProfile) :
    (parallel left right).dataQubits = left.dataQubits + right.dataQubits := rfl

@[simp]
theorem parallel_workQubits (left right : ModularArithmeticResourceProfile) :
    (parallel left right).workQubits = left.workQubits + right.workQubits := rfl

@[simp]
theorem parallel_oracleQueries (left right : ModularArithmeticResourceProfile) :
    (parallel left right).oracleQueries = left.oracleQueries + right.oracleQueries := rfl

@[simp]
theorem parallel_hadamardGates (left right : ModularArithmeticResourceProfile) :
    (parallel left right).hadamardGates = left.hadamardGates + right.hadamardGates := rfl

@[simp]
theorem parallel_toffoliGates (left right : ModularArithmeticResourceProfile) :
    (parallel left right).toffoliGates = left.toffoliGates + right.toffoliGates := rfl

@[simp]
theorem parallel_tGates (left right : ModularArithmeticResourceProfile) :
    (parallel left right).tGates = left.tGates + right.tGates := rfl

@[simp]
theorem parallel_cnotGates (left right : ModularArithmeticResourceProfile) :
    (parallel left right).cnotGates = left.cnotGates + right.cnotGates := rfl

@[simp]
theorem parallel_singleQubitGates (left right : ModularArithmeticResourceProfile) :
    (parallel left right).singleQubitGates =
      left.singleQubitGates + right.singleQubitGates := rfl

@[simp]
theorem parallel_circuitDepth (left right : ModularArithmeticResourceProfile) :
    (parallel left right).circuitDepth = max left.circuitDepth right.circuitDepth := rfl

@[simp]
theorem parallel_toffoliDepth (left right : ModularArithmeticResourceProfile) :
    (parallel left right).toffoliDepth = max left.toffoliDepth right.toffoliDepth := rfl

@[simp]
theorem parallel_classicalArithmetic (left right : ModularArithmeticResourceProfile) :
    (parallel left right).classicalArithmetic =
      ClassicalArithmeticProfile.sequential
        left.classicalArithmetic right.classicalArithmetic := rfl

@[simp]
theorem repeatSequential_zero (profile : ModularArithmeticResourceProfile) :
    repeatSequential 0 profile = zero := rfl

@[simp]
theorem repeatSequential_succ (k : ℕ) (profile : ModularArithmeticResourceProfile) :
    repeatSequential (k + 1) profile =
      { logicalQubits := profile.logicalQubits
        dataQubits := profile.dataQubits
        workQubits := profile.workQubits
        oracleQueries := (k + 1) * profile.oracleQueries
        hadamardGates := (k + 1) * profile.hadamardGates
        toffoliGates := (k + 1) * profile.toffoliGates
        tGates := (k + 1) * profile.tGates
        cnotGates := (k + 1) * profile.cnotGates
        singleQubitGates := (k + 1) * profile.singleQubitGates
        circuitDepth := (k + 1) * profile.circuitDepth
        toffoliDepth := (k + 1) * profile.toffoliDepth
        classicalArithmetic :=
          ClassicalArithmeticProfile.scale (k + 1) profile.classicalArithmetic } :=
  rfl

/-- Fieldwise concrete upper-bound relation for modular-arithmetic resource
profiles. The structured classical profile is compared through its scalar total,
so theorem statements can expose an exact or upper-bound operation count without
using asymptotic notation. -/
structure SupportsUpperBound
    (profile bound : ModularArithmeticResourceProfile) : Prop where
  logicalQubits_le : profile.logicalQubits ≤ bound.logicalQubits
  dataQubits_le : profile.dataQubits ≤ bound.dataQubits
  workQubits_le : profile.workQubits ≤ bound.workQubits
  oracleQueries_le : profile.oracleQueries ≤ bound.oracleQueries
  hadamardGates_le : profile.hadamardGates ≤ bound.hadamardGates
  toffoliGates_le : profile.toffoliGates ≤ bound.toffoliGates
  tGates_le : profile.tGates ≤ bound.tGates
  cnotGates_le : profile.cnotGates ≤ bound.cnotGates
  singleQubitGates_le : profile.singleQubitGates ≤ bound.singleQubitGates
  circuitDepth_le : profile.circuitDepth ≤ bound.circuitDepth
  toffoliDepth_le : profile.toffoliDepth ≤ bound.toffoliDepth
  classicalOps_le : profile.classicalArithmetic.total ≤ bound.classicalArithmetic.total

namespace SupportsUpperBound

/-- Every profile supports itself as an exact bound. -/
theorem refl (profile : ModularArithmeticResourceProfile) :
    SupportsUpperBound profile profile where
  logicalQubits_le := le_rfl
  dataQubits_le := le_rfl
  workQubits_le := le_rfl
  oracleQueries_le := le_rfl
  hadamardGates_le := le_rfl
  toffoliGates_le := le_rfl
  tGates_le := le_rfl
  cnotGates_le := le_rfl
  singleQubitGates_le := le_rfl
  circuitDepth_le := le_rfl
  toffoliDepth_le := le_rfl
  classicalOps_le := le_rfl

/-- Sequential composition preserves fieldwise upper bounds. -/
theorem sequential {left right leftBound rightBound : ModularArithmeticResourceProfile}
    (hleft : SupportsUpperBound left leftBound)
    (hright : SupportsUpperBound right rightBound) :
    SupportsUpperBound (ModularArithmeticResourceProfile.sequential left right)
      (ModularArithmeticResourceProfile.sequential leftBound rightBound) where
  logicalQubits_le := max_le_max hleft.logicalQubits_le hright.logicalQubits_le
  dataQubits_le := max_le_max hleft.dataQubits_le hright.dataQubits_le
  workQubits_le := max_le_max hleft.workQubits_le hright.workQubits_le
  oracleQueries_le := Nat.add_le_add hleft.oracleQueries_le hright.oracleQueries_le
  hadamardGates_le := Nat.add_le_add hleft.hadamardGates_le hright.hadamardGates_le
  toffoliGates_le := Nat.add_le_add hleft.toffoliGates_le hright.toffoliGates_le
  tGates_le := Nat.add_le_add hleft.tGates_le hright.tGates_le
  cnotGates_le := Nat.add_le_add hleft.cnotGates_le hright.cnotGates_le
  singleQubitGates_le := Nat.add_le_add hleft.singleQubitGates_le hright.singleQubitGates_le
  circuitDepth_le := Nat.add_le_add hleft.circuitDepth_le hright.circuitDepth_le
  toffoliDepth_le := Nat.add_le_add hleft.toffoliDepth_le hright.toffoliDepth_le
  classicalOps_le := by
    simpa using Nat.add_le_add hleft.classicalOps_le hright.classicalOps_le

/-- Parallel/tensor composition preserves fieldwise upper bounds. -/
theorem parallel {left right leftBound rightBound : ModularArithmeticResourceProfile}
    (hleft : SupportsUpperBound left leftBound)
    (hright : SupportsUpperBound right rightBound) :
    SupportsUpperBound (ModularArithmeticResourceProfile.parallel left right)
      (ModularArithmeticResourceProfile.parallel leftBound rightBound) where
  logicalQubits_le := Nat.add_le_add hleft.logicalQubits_le hright.logicalQubits_le
  dataQubits_le := Nat.add_le_add hleft.dataQubits_le hright.dataQubits_le
  workQubits_le := Nat.add_le_add hleft.workQubits_le hright.workQubits_le
  oracleQueries_le := Nat.add_le_add hleft.oracleQueries_le hright.oracleQueries_le
  hadamardGates_le := Nat.add_le_add hleft.hadamardGates_le hright.hadamardGates_le
  toffoliGates_le := Nat.add_le_add hleft.toffoliGates_le hright.toffoliGates_le
  tGates_le := Nat.add_le_add hleft.tGates_le hright.tGates_le
  cnotGates_le := Nat.add_le_add hleft.cnotGates_le hright.cnotGates_le
  singleQubitGates_le := Nat.add_le_add hleft.singleQubitGates_le hright.singleQubitGates_le
  circuitDepth_le := max_le_max hleft.circuitDepth_le hright.circuitDepth_le
  toffoliDepth_le := max_le_max hleft.toffoliDepth_le hright.toffoliDepth_le
  classicalOps_le := by
    simpa using Nat.add_le_add hleft.classicalOps_le hright.classicalOps_le

/-- Repeating a sequential block preserves fieldwise upper bounds. -/
theorem repeatSequential {k : ℕ} {profile bound : ModularArithmeticResourceProfile}
    (h : SupportsUpperBound profile bound) :
    SupportsUpperBound (ModularArithmeticResourceProfile.repeatSequential k profile)
      (ModularArithmeticResourceProfile.repeatSequential k bound) := by
  cases k with
  | zero =>
      exact refl ModularArithmeticResourceProfile.zero
  | succ k =>
      refine
        { logicalQubits_le := ?_
          dataQubits_le := ?_
          workQubits_le := ?_
          oracleQueries_le := ?_
          hadamardGates_le := ?_
          toffoliGates_le := ?_
          tGates_le := ?_
          cnotGates_le := ?_
          singleQubitGates_le := ?_
          circuitDepth_le := ?_
          toffoliDepth_le := ?_
          classicalOps_le := ?_ }
      · simpa using h.logicalQubits_le
      · simpa using h.dataQubits_le
      · simpa using h.workQubits_le
      · simpa using Nat.mul_le_mul_left (k + 1) h.oracleQueries_le
      · simpa using Nat.mul_le_mul_left (k + 1) h.hadamardGates_le
      · simpa using Nat.mul_le_mul_left (k + 1) h.toffoliGates_le
      · simpa using Nat.mul_le_mul_left (k + 1) h.tGates_le
      · simpa using Nat.mul_le_mul_left (k + 1) h.cnotGates_le
      · simpa using Nat.mul_le_mul_left (k + 1) h.singleQubitGates_le
      · simpa using Nat.mul_le_mul_left (k + 1) h.circuitDepth_le
      · simpa using Nat.mul_le_mul_left (k + 1) h.toffoliDepth_le
      · simpa using Nat.mul_le_mul_left (k + 1) h.classicalOps_le

end SupportsUpperBound

theorem elementaryGateCount_sequential (left right : ModularArithmeticResourceProfile) :
    (sequential left right).elementaryGateCount =
      left.elementaryGateCount + right.elementaryGateCount := by
  simp [elementaryGateCount]
  omega

theorem elementaryGateCount_parallel (left right : ModularArithmeticResourceProfile) :
    (parallel left right).elementaryGateCount =
      left.elementaryGateCount + right.elementaryGateCount := by
  simp [elementaryGateCount]
  omega

private theorem toResourceProfile_sequential (left right : ModularArithmeticResourceProfile) :
    (sequential left right).toResourceProfile =
      ResourceProfile.sequential left.toResourceProfile right.toResourceProfile := by
  ext <;> simp [toResourceProfile, ResourceProfile.sequential,
    elementaryGateCount_sequential]

private theorem toResourceProfile_parallel (left right : ModularArithmeticResourceProfile) :
    (parallel left right).toResourceProfile =
      ResourceProfile.sequential left.toResourceProfile right.toResourceProfile := by
  ext <;> simp [toResourceProfile, ResourceProfile.sequential,
    elementaryGateCount_parallel]

/-- Projecting a repeated modular-arithmetic profile to the coarse circuit
resource tuple is the same as scaling the projected coarse profile. -/
theorem toResourceProfile_repeatSequential
    (k : ℕ) (profile : ModularArithmeticResourceProfile) :
    (repeatSequential k profile).toResourceProfile =
      ResourceProfile.scale k profile.toResourceProfile := by
  cases k with
  | zero =>
      ext <;> simp [ResourceProfile.zero, ResourceProfile.scale]
  | succ k =>
      ext <;> simp [toResourceProfile, ResourceProfile.scale, elementaryGateCount]
      all_goals ring_nf

end ModularArithmeticResourceProfile

/-! ### Counted gate words -/

/-- A small circuit word boundary for endpoints whose correctness and resource
counts must refer to the same constructed unitary.  The word deliberately keeps
only its evaluated gate and derived resource profile; richer syntax can be
introduced later without changing public theorem statements. -/
structure CountedGateWord (R : Register) where
  /-- Evaluated gate represented by the counted word. -/
  matrix : Gate R
  /-- Trusted resource counters attached to the same word. -/
  resources : ResourceProfile

namespace CountedGateWord

/-- A counted word with explicit resources for an already-built gate. -/
def ofGate {R : Register} (gate : Gate R) (resources : ResourceProfile) :
    CountedGateWord R where
  matrix := gate
  resources := resources

/-- Sequential composition evaluates by multiplying the gates and adds the
resource counters from the same syntax boundary. -/
def sequential {R : Register} (left right : CountedGateWord R) : CountedGateWord R where
  matrix := left.matrix * right.matrix
  resources := ResourceProfile.sequential left.resources right.resources

@[simp]
theorem sequential_matrix {R : Register} (left right : CountedGateWord R) :
    (sequential left right).matrix = left.matrix * right.matrix := rfl

@[simp]
theorem sequential_resources {R : Register} (left right : CountedGateWord R) :
    (sequential left right).resources =
      ResourceProfile.sequential left.resources right.resources := rfl

end CountedGateWord

/-- Gate counts for fixed circuit statements with named gate families. -/
structure CircuitGateProfile where
  /-- Number of Hadamard gates. -/
  hadamardGates : ℕ
  /-- Number of controlled phase gates. -/
  controlledPhaseGates : ℕ
  /-- Number of swap gates. -/
  swapGates : ℕ
deriving DecidableEq

namespace CircuitGateProfile

/-- Exact fixed-circuit gate-count claim. -/
def HasExactCounts (profile : CircuitGateProfile)
    (hadamardGates controlledPhaseGates swapGates : ℕ) : Prop :=
  profile.hadamardGates = hadamardGates ∧
    profile.controlledPhaseGates = controlledPhaseGates ∧
    profile.swapGates = swapGates

end CircuitGateProfile

/-- A return value paired with a trusted resource profile. -/
structure Profiled (α : Type u) where
  /-- The profiled return value. -/
  ret : α
  /-- Trusted resources associated with the return value. -/
  resources : ResourceProfile

namespace Profiled

/-- Attach a trusted resource profile to a return value. -/
def trusted {α : Type u} (resources : ResourceProfile) (ret : α) : Profiled α :=
  ⟨ret, resources⟩

@[simp]
theorem trusted_ret {α : Type u} (resources : ResourceProfile) (ret : α) :
    (trusted resources ret).ret = ret := rfl

@[simp]
theorem trusted_resources {α : Type u} (resources : ResourceProfile) (ret : α) :
    (trusted resources ret).resources = resources := rfl

end Profiled

/-- Communication resources for protocol statements. -/
structure CommunicationProfile where
  /-- Classical bits communicated by the protocol. -/
  classicalBits : ℕ
  /-- Qubits transmitted by the protocol. -/
  transmittedQubits : ℕ
  /-- Shared Bell pairs consumed or produced by the protocol. -/
  bellPairs : ℕ
deriving DecidableEq

namespace CommunicationProfile

/-- Exact communication-resource claim for protocol supporting theorems. -/
def HasExactCounts (profile : CommunicationProfile)
    (classicalBits transmittedQubits bellPairs : ℕ) : Prop :=
  profile.classicalBits = classicalBits ∧
    profile.transmittedQubits = transmittedQubits ∧
    profile.bellPairs = bellPairs

@[simp]
theorem hasExactCounts_mk (classicalBits transmittedQubits bellPairs : ℕ) :
    HasExactCounts
      { classicalBits := classicalBits, transmittedQubits := transmittedQubits,
        bellPairs := bellPairs }
      classicalBits transmittedQubits bellPairs := by
  simp [HasExactCounts]

end CommunicationProfile

end QuantumAlg
