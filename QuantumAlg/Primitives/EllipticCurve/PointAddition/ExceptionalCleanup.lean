/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.ExceptionalCleanup.Branch
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.ExceptionalCleanup.Selector

/-!
# Total clean generic affine translation

This module closes the finite exceptional branch of the clean in-place
generic point-addition translation.  A reversible equality selector chooses
between the ordinary addition dagger and a fixed-coordinate exceptional
cleanup, then is recomputed to restore every selector wire.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace GenericPointAddition
namespace ExceptionalCleanup

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

variable [params : Arithmetic.VariableModularMul.Parameters]

variable {E : PrimeFieldShortWeierstrass params.modulus.val}
  [Fact params.modulus.val.Prime]
  {Q : AffinePoint E}

/-- Primitive gate specification on the complete exceptional-cleanup carrier. -/
abbrev Gate := EncodedBit.GateSpec Layout.rawEncoding

/-- Common four-stage translation prefix, lifted to the selector carrier. -/
def prefixGates : List Gate :=
  Layout.liftPipelineGates
    (Pipeline.translationPrefixGates (Pipeline.pointWords Q)
      (Pipeline.pointWords (AffinePoint.negate Q)))

/-- Final fixed-point unload, lifted to the selector carrier. -/
def unloadGates : List Gate :=
  Layout.liftPipelineGates
    (PointAddition.PortFrame.unloadConstantGates Pipeline.auxEncoding
      params.width (Pipeline.pointWords (AffinePoint.negate Q)))

/-- Uncontrolled total translation schedule before adding the public control. -/
def baseGates : List Gate :=
  prefixGates (E := E) (Q := Q) ++
    (Selector.compareGates (Pipeline.pointWords Q).1 ++
      (Branch.cleanupGates (E := E) (Q := Q) ++
        (Selector.compareGates (Pipeline.pointWords Q).1 ++
          unloadGates (E := E) (Q := Q))))

/-- Folded action of the uncontrolled total translation schedule. -/
def baseStep : Layout.RawRegisters → Layout.RawRegisters :=
  EncodedBit.GateSpec.stepList (baseGates (E := E) (Q := Q))

omit [Fact params.modulus.val.Prime] in
private lemma prefixGates_bitDisjoint_controlBit :
    ∀ gate, gate ∈ prefixGates (E := E) (Q := Q) →
      EncodedBit.GateSpec.bitDisjoint Layout.controlBit gate := by
  simpa only [prefixGates, Layout.controlBit] using
    Layout.liftPipelineGates_bitDisjoint_liftPipelineBit Pipeline.controlBit
      (Pipeline.translationPrefixGates (Pipeline.pointWords Q)
        (Pipeline.pointWords (AffinePoint.negate Q)))
      (fun gate hgate => by
        simp only [Pipeline.translationPrefixGates, List.mem_append] at hgate
        rcases hgate with ((hload | haddition) | hswap) | hreplace
        · exact PointAddition.PortFrame.loadConstantGates_bitDisjoint_controlBit
            Pipeline.auxEncoding params.width (Pipeline.pointWords Q) gate hload
        · exact Pipeline.additionGates_bitDisjoint_controlBit gate haddition
        · exact
            PointAddition.PortFrame.swapMutableOutputGates_bitDisjoint_controlBit
              Pipeline.auxEncoding params.width gate hswap
        · exact
            PointAddition.PortFrame.replaceConstantGates_bitDisjoint_controlBit
              Pipeline.auxEncoding params.width (Pipeline.pointWords Q)
              (Pipeline.pointWords (AffinePoint.negate Q)) gate hreplace)

omit [Fact params.modulus.val.Prime] in
private lemma prefixGates_bitDisjoint_controlWorkBit :
    ∀ gate, gate ∈ prefixGates (E := E) (Q := Q) →
      EncodedBit.GateSpec.bitDisjoint Layout.controlWorkBit gate := by
  simpa only [prefixGates, Layout.controlWorkBit] using
    Layout.liftPipelineGates_bitDisjoint_liftPipelineBit
      Pipeline.controlWorkBit
      (Pipeline.translationPrefixGates (Pipeline.pointWords Q)
        (Pipeline.pointWords (AffinePoint.negate Q)))
      (fun gate hgate => by
        simp only [Pipeline.translationPrefixGates, List.mem_append] at hgate
        rcases hgate with ((hload | haddition) | hswap) | hreplace
        · exact
            PointAddition.PortFrame.loadConstantGates_bitDisjoint_controlWorkBit
              Pipeline.auxEncoding params.width (Pipeline.pointWords Q) gate
              hload
        · exact Pipeline.additionGates_bitDisjoint_controlWorkBit gate
            haddition
        · exact
            PointAddition.PortFrame.swapMutableOutputGates_bitDisjoint_controlWorkBit
              Pipeline.auxEncoding params.width gate hswap
        · exact
            PointAddition.PortFrame.replaceConstantGates_bitDisjoint_controlWorkBit
              Pipeline.auxEncoding params.width (Pipeline.pointWords Q)
              (Pipeline.pointWords (AffinePoint.negate Q)) gate hreplace)

omit [Fact params.modulus.val.Prime] in
private lemma unloadGates_bitDisjoint_controlBit :
    ∀ gate, gate ∈ unloadGates (E := E) (Q := Q) →
      EncodedBit.GateSpec.bitDisjoint Layout.controlBit gate := by
  simpa only [unloadGates, Layout.controlBit] using
    Layout.liftPipelineGates_bitDisjoint_liftPipelineBit Pipeline.controlBit
      (PointAddition.PortFrame.unloadConstantGates Pipeline.auxEncoding
        params.width (Pipeline.pointWords (AffinePoint.negate Q)))
      (fun gate hgate =>
        PointAddition.PortFrame.unloadConstantGates_bitDisjoint_controlBit
          Pipeline.auxEncoding params.width
          (Pipeline.pointWords (AffinePoint.negate Q)) gate hgate)

omit [Fact params.modulus.val.Prime] in
private lemma unloadGates_bitDisjoint_controlWorkBit :
    ∀ gate, gate ∈ unloadGates (E := E) (Q := Q) →
      EncodedBit.GateSpec.bitDisjoint Layout.controlWorkBit gate := by
  simpa only [unloadGates, Layout.controlWorkBit] using
    Layout.liftPipelineGates_bitDisjoint_liftPipelineBit
      Pipeline.controlWorkBit
      (PointAddition.PortFrame.unloadConstantGates Pipeline.auxEncoding
        params.width (Pipeline.pointWords (AffinePoint.negate Q)))
      (fun gate hgate =>
        PointAddition.PortFrame.unloadConstantGates_bitDisjoint_controlWorkBit
          Pipeline.auxEncoding params.width
          (Pipeline.pointWords (AffinePoint.negate Q)) gate hgate)

/-- The public control is physically disjoint from every uncontrolled cleanup
gate. -/
lemma baseGates_bitDisjoint_controlBit :
    ∀ gate, gate ∈ baseGates (E := E) (Q := Q) →
      EncodedBit.GateSpec.bitDisjoint Layout.controlBit gate := by
  intro gate hgate
  rw [baseGates] at hgate
  rcases List.mem_append.mp hgate with hgate | hgate
  · exact prefixGates_bitDisjoint_controlBit gate hgate
  · rcases List.mem_append.mp hgate with hgate | hgate
    · exact Selector.compareGates_bitDisjoint_controlBit _ gate hgate
    · rcases List.mem_append.mp hgate with hgate | hgate
      · exact Branch.cleanupGates_bitDisjoint_controlBit gate hgate
      · rcases List.mem_append.mp hgate with hgate | hgate
        · exact Selector.compareGates_bitDisjoint_controlBit _ gate hgate
        · exact unloadGates_bitDisjoint_controlBit gate hgate

/-- The clean outer-control work bit is physically disjoint from every
uncontrolled cleanup gate. -/
lemma baseGates_bitDisjoint_controlWorkBit :
    ∀ gate, gate ∈ baseGates (E := E) (Q := Q) →
      EncodedBit.GateSpec.bitDisjoint Layout.controlWorkBit gate := by
  intro gate hgate
  rw [baseGates] at hgate
  rcases List.mem_append.mp hgate with hgate | hgate
  · exact prefixGates_bitDisjoint_controlWorkBit gate hgate
  · rcases List.mem_append.mp hgate with hgate | hgate
    · exact Selector.compareGates_bitDisjoint_controlWorkBit _ gate hgate
    · rcases List.mem_append.mp hgate with hgate | hgate
      · exact Branch.cleanupGates_bitDisjoint_controlWorkBit gate hgate
      · rcases List.mem_append.mp hgate with hgate | hgate
        · exact Selector.compareGates_bitDisjoint_controlWorkBit _ gate hgate
        · exact unloadGates_bitDisjoint_controlWorkBit gate hgate

/-- Literal X/CNOT/Toffoli public-control lift of the total cleanup schedule. -/
def translationGates : List Gate :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    Layout.controlBit Layout.controlWorkBit (baseGates (E := E) (Q := Q))
    baseGates_bitDisjoint_controlBit baseGates_bitDisjoint_controlWorkBit
    Layout.controlBit_wire_ne_controlWorkBit

/-- Folded action of the complete publicly controlled translation. -/
def translationStep : Layout.RawRegisters → Layout.RawRegisters :=
  EncodedBit.GateSpec.controlledListWithWorkStep
    Layout.controlBit Layout.controlWorkBit (baseGates (E := E) (Q := Q))
    baseGates_bitDisjoint_controlBit baseGates_bitDisjoint_controlWorkBit
    Layout.controlBit_wire_ne_controlWorkBit

/-- Production circuit compiled from the literal total translation list. -/
def translationProgram :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Layout.rawEncoding.width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (translationGates (E := E) (Q := Q))

/-- Computational-basis state of the actual canonical physical layout. -/
def encodedKet (state : Layout.RawRegisters) :
    NormalizedVector
      (QubitLayout.canonical Layout.rawEncoding.width).toQuantum.register :=
  NormalizedVector.ket
    ((QubitLayout.canonical Layout.rawEncoding.width).basisEquiv.symm
      (Layout.rawEncoding.encode state))

/-- A false public control makes the complete translation a no-op. -/
lemma translationStep_eq_self_of_control_false
    (state : Layout.RawRegisters)
    (hcontrol : Layout.controlBit.get state = false) :
    translationStep (E := E) (Q := Q) state = state := by
  simpa only [translationStep] using
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
      Layout.controlBit Layout.controlWorkBit (baseGates (E := E) (Q := Q))
      baseGates_bitDisjoint_controlBit baseGates_bitDisjoint_controlWorkBit
      Layout.controlBit_wire_ne_controlWorkBit state hcontrol

/-- A true public control and clean decomposition work bit execute the total
uncontrolled cleanup schedule exactly. -/
lemma translationStep_eq_base_of_control_true
    (state : Layout.RawRegisters)
    (hcontrol : Layout.controlBit.get state = true)
    (hwork : Layout.controlWorkBit.get state = false) :
    translationStep (E := E) (Q := Q) state =
      EncodedBit.GateSpec.stepList (baseGates (E := E) (Q := Q)) state := by
  simpa only [translationStep] using
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
      Layout.controlBit Layout.controlWorkBit (baseGates (E := E) (Q := Q))
      baseGates_bitDisjoint_controlBit baseGates_bitDisjoint_controlWorkBit
      Layout.controlBit_wire_ne_controlWorkBit state hcontrol hwork

/-- The production circuit realizes the literal controlled translation step. -/
lemma translationProgram_realizes :
    UnitaryCircuit.Realizes Layout.rawEncoding (translationProgram (E := E) (Q := Q)) environment
      (translationStep (E := E) (Q := Q)) := by
  simpa only [translationProgram, translationGates, translationStep] using
    EncodedBit.GateSpec.controlledListWithWorkWitness (environment := environment)
      (QubitLayout.canonical _) .empty Layout.controlBit Layout.controlWorkBit
      (baseGates (E := E) (Q := Q))
      baseGates_bitDisjoint_controlBit baseGates_bitDisjoint_controlWorkBit
      Layout.controlBit_wire_ne_controlWorkBit

private lemma prefixStep_clean
    (control : Bool) (P : GenericPointAddition.Input E Q) :
    EncodedBit.GateSpec.stepList (prefixGates (E := E) (Q := Q))
        (Layout.translationBoundaryRegisters control (Pipeline.pointWords P.1)
          (PointAddition.PortFrame.zeroPoint params.width)
          (PointAddition.PortFrame.zeroPoint params.width)) =
      Layout.selectedBoundaryRegisters control (Pipeline.resultWords P)
        (Pipeline.pointWords (AffinePoint.negate Q))
        (Pipeline.pointWords P.1) false := by
  unfold prefixGates
  rw [Layout.stepList_liftPipelineGates]
  apply Prod.ext
  · exact Pipeline.translationPrefixGates_clean control P
  · rfl

omit [Fact params.modulus.val.Prime] in
private lemma compareStep_selectedBoundary_of_eq
    (constant : Fin (2 ^ params.width)) (control : Bool)
    (mutable loaded output : PointAddition.PortFrame.PointWords params.width)
    (selector : Bool) (hmatch : mutable.1 = constant) :
    Selector.compareStep constant
        (Layout.selectedBoundaryRegisters control mutable loaded output
          selector) =
      Layout.selectedBoundaryRegisters control mutable loaded output
        (!selector) := by
  rw [Selector.compareStep_eq_selectorFlip (params := params) constant
    (Layout.selectedBoundaryRegisters control mutable loaded output selector)
    (by
      intro work
      exact Layout.zeroWorkBit_get_selectedBoundary
        control mutable loaded output selector work)
    (Layout.paddingLeftBit_get_selectedBoundary
      control mutable loaded output selector)
    (Layout.paddingRightBit_get_selectedBoundary
      control mutable loaded output selector)]
  simp only [Layout.mutableXPort_read_selectedBoundary]
  rw [Layout.selectorBit_flip_selectedBoundary control mutable loaded output selector]
  simp [hmatch]

omit [Fact params.modulus.val.Prime] in
private lemma compareStep_selectedBoundary_of_ne
    (constant : Fin (2 ^ params.width)) (control : Bool)
    (mutable loaded output : PointAddition.PortFrame.PointWords params.width)
    (selector : Bool) (hmatch : mutable.1 ≠ constant) :
    Selector.compareStep constant
        (Layout.selectedBoundaryRegisters control mutable loaded output
          selector) =
      Layout.selectedBoundaryRegisters control mutable loaded output selector := by
  rw [Selector.compareStep_eq_selectorFlip (params := params) constant
    (Layout.selectedBoundaryRegisters control mutable loaded output selector)
    (by
      intro work
      exact Layout.zeroWorkBit_get_selectedBoundary
        control mutable loaded output selector work)
    (Layout.paddingLeftBit_get_selectedBoundary
      control mutable loaded output selector)
    (Layout.paddingRightBit_get_selectedBoundary
      control mutable loaded output selector)]
  simp only [Layout.mutableXPort_read_selectedBoundary]
  simp [hmatch]

omit [Fact params.modulus.val.Prime] in
private lemma unloadStep_clean
    (control : Bool)
    (mutable : PointAddition.PortFrame.PointWords params.width) :
    EncodedBit.GateSpec.stepList (unloadGates (E := E) (Q := Q))
        (Layout.selectedBoundaryRegisters control mutable
          (Pipeline.pointWords (AffinePoint.negate Q))
          (PointAddition.PortFrame.zeroPoint params.width) false) =
      Layout.translationBoundaryRegisters control mutable
        (PointAddition.PortFrame.zeroPoint params.width)
        (PointAddition.PortFrame.zeroPoint params.width) := by
  unfold unloadGates
  rw [Layout.stepList_liftPipelineGates]
  apply Prod.ext
  · change PointAddition.PortFrame.unloadConstantStep Pipeline.auxEncoding
        params.width (Pipeline.pointWords (AffinePoint.negate Q))
        (control,
          (((mutable,
              (Pipeline.pointWords (AffinePoint.negate Q),
                PointAddition.PortFrame.zeroPoint params.width)),
            ParameterizedPointAddition.blankRegisters), false)) =
      (control,
        (((mutable,
            (PointAddition.PortFrame.zeroPoint params.width,
              PointAddition.PortFrame.zeroPoint params.width)),
          ParameterizedPointAddition.blankRegisters), false))
    exact PointAddition.PortFrame.unloadConstantStep_at Pipeline.auxEncoding
      params.width (Pipeline.pointWords (AffinePoint.negate Q)) control mutable
      (PointAddition.PortFrame.zeroPoint params.width)
      ParameterizedPointAddition.blankRegisters false
  · rfl

/-- The uncontrolled schedule implements the clean in-place group shift for
every input in the locked generic forward domain.  No reverse-domain premise
is required: the selector routes its unique finite exceptional case through
the fixed-coordinate cleanup. -/
lemma baseStep_clean (control : Bool)
    (P : GenericPointAddition.Input E Q) :
    baseStep (E := E) (Q := Q)
        (Layout.translationBoundaryRegisters control (Pipeline.pointWords P.1)
          (PointAddition.PortFrame.zeroPoint params.width)
          (PointAddition.PortFrame.zeroPoint params.width)) =
      Layout.translationBoundaryRegisters control (Pipeline.resultWords P)
        (PointAddition.PortFrame.zeroPoint params.width)
        (PointAddition.PortFrame.zeroPoint params.width) := by
  unfold baseStep baseGates
  simp only [EncodedBit.GateSpec.stepList_append]
  rw [prefixStep_clean control P]
  change EncodedBit.GateSpec.stepList (unloadGates (E := E) (Q := Q))
      (Selector.compareStep (Pipeline.pointWords Q).1
        (Branch.cleanupStep (E := E) (Q := Q)
          (Selector.compareStep (Pipeline.pointWords Q).1
            (Layout.selectedBoundaryRegisters control (Pipeline.resultWords P)
              (Pipeline.pointWords (AffinePoint.negate Q))
              (Pipeline.pointWords P.1) false)))) = _
  by_cases hmatch : (Pipeline.resultWords P).1 = (Pipeline.pointWords Q).1
  · rw [compareStep_selectedBoundary_of_eq _ _ _ _ _ false hmatch]
    simp only [Bool.not_false]
    rw [Branch.cleanupStep_exceptional_selectedBoundary control P hmatch]
    rw [compareStep_selectedBoundary_of_eq _ _ _ _ _ true hmatch]
    simp only [Bool.not_true]
    exact unloadStep_clean control (Pipeline.resultWords P)
  · rw [compareStep_selectedBoundary_of_ne _ _ _ _ _ false hmatch]
    rw [Branch.cleanupStep_normal_selectedBoundary control P hmatch]
    rw [compareStep_selectedBoundary_of_ne _ _ _ _ _ false hmatch]
    exact unloadStep_clean control (Pipeline.resultWords P)

/-- The complete literal translation is the identity for a false public
control and a clean in-place group shift for a true public control, with no
additional reverse-domain assumption. -/
lemma translationStep_clean (control : Bool)
    (P : GenericPointAddition.Input E Q) :
    translationStep (E := E) (Q := Q)
        (Layout.translationBoundaryRegisters control (Pipeline.pointWords P.1)
          (PointAddition.PortFrame.zeroPoint params.width)
          (PointAddition.PortFrame.zeroPoint params.width)) =
      Layout.translationBoundaryRegisters control
        (if control then Pipeline.resultWords P else Pipeline.pointWords P.1)
        (PointAddition.PortFrame.zeroPoint params.width)
        (PointAddition.PortFrame.zeroPoint params.width) := by
  cases control with
  | false =>
      have hfalse := translationStep_eq_self_of_control_false
        (E := E) (Q := Q)
        (Layout.translationBoundaryRegisters false (Pipeline.pointWords P.1)
          (PointAddition.PortFrame.zeroPoint params.width)
          (PointAddition.PortFrame.zeroPoint params.width)) (by rfl)
      simpa using hfalse
  | true =>
      rw [translationStep_eq_base_of_control_true (E := E) (Q := Q)
        (Layout.translationBoundaryRegisters true (Pipeline.pointWords P.1)
          (PointAddition.PortFrame.zeroPoint params.width)
          (PointAddition.PortFrame.zeroPoint params.width)) (by rfl) (by rfl)]
      simpa only [baseStep, Bool.true_eq, ↓reduceIte] using
        baseStep_clean true P

/-- Basis-state endpoint for the production total translation circuit. -/
lemma translationProgram_clean_ket (control : Bool)
    (P : GenericPointAddition.Input E Q) :
    (translationProgram (E := E) (Q := Q)).applyNormalized environment
        (encodedKet (Layout.translationBoundaryRegisters control
          (Pipeline.pointWords P.1)
          (PointAddition.PortFrame.zeroPoint params.width)
          (PointAddition.PortFrame.zeroPoint params.width))) =
      encodedKet (Layout.translationBoundaryRegisters control
        (if control then Pipeline.resultWords P else Pipeline.pointWords P.1)
        (PointAddition.PortFrame.zeroPoint params.width)
        (PointAddition.PortFrame.zeroPoint params.width)) := by
  have h := (translationProgram_realizes (environment := environment)
    (E := E) (Q := Q)).apply_encoded_ket
    (Layout.translationBoundaryRegisters control (Pipeline.pointWords P.1)
      (PointAddition.PortFrame.zeroPoint params.width)
      (PointAddition.PortFrame.zeroPoint params.width))
  rw [translationStep_clean control P] at h
  simpa only [encodedKet] using h

/-! ## Literal resource coordinates -/

omit [Fact params.modulus.val.Prime] in
/-- Exact leaf count of the common translation prefix. -/
lemma prefixGates_length :
    (prefixGates (E := E) (Q := Q)).length =
      (PointAddition.PortFrame.loadConstantGates Pipeline.auxEncoding
        params.width (Pipeline.pointWords Q)).length +
      Pipeline.additionGates.length + 6 * params.width +
      (PointAddition.PortFrame.replaceConstantGates Pipeline.auxEncoding
        params.width (Pipeline.pointWords Q)
        (Pipeline.pointWords (AffinePoint.negate Q))).length := by
  let loadGates : List (EncodedBit.GateSpec Pipeline.rawEncoding) :=
    PointAddition.PortFrame.loadConstantGates Pipeline.auxEncoding
      params.width (Pipeline.pointWords Q)
  let swapGates : List (EncodedBit.GateSpec Pipeline.rawEncoding) :=
    PointAddition.PortFrame.swapMutableOutputGates Pipeline.auxEncoding
      params.width
  let replaceGates : List (EncodedBit.GateSpec Pipeline.rawEncoding) :=
    PointAddition.PortFrame.replaceConstantGates Pipeline.auxEncoding
      params.width (Pipeline.pointWords Q)
      (Pipeline.pointWords (AffinePoint.negate Q))
  change (Layout.liftPipelineGates
      (loadGates ++ Pipeline.additionGates ++ swapGates ++ replaceGates)).length =
    loadGates.length + Pipeline.additionGates.length + 6 * params.width +
      replaceGates.length
  have hswap : swapGates.length = 6 * params.width := by
    simpa only [swapGates, Pipeline.rawEncoding] using
      PointAddition.PortFrame.swapMutableOutputGates_length
        Pipeline.auxEncoding params.width
  rw [Layout.liftPipelineGates_length]
  simp only [List.length_append]
  omega

omit [Fact params.modulus.val.Prime] in
/-- Exact X coordinate of the common translation prefix. -/
lemma prefixGates_xMultiplicity_sum :
    ((prefixGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.xMultiplicity).sum =
      (PointAddition.PortFrame.loadConstantGates Pipeline.auxEncoding
        params.width (Pipeline.pointWords Q)).length +
      (Pipeline.additionGates.map
        EncodedBit.GateSpec.xMultiplicity).sum +
      (PointAddition.PortFrame.replaceConstantGates Pipeline.auxEncoding
        params.width (Pipeline.pointWords Q)
        (Pipeline.pointWords (AffinePoint.negate Q))).length := by
  let loadGates : List (EncodedBit.GateSpec Pipeline.rawEncoding) :=
    PointAddition.PortFrame.loadConstantGates Pipeline.auxEncoding
      params.width (Pipeline.pointWords Q)
  let swapGates : List (EncodedBit.GateSpec Pipeline.rawEncoding) :=
    PointAddition.PortFrame.swapMutableOutputGates Pipeline.auxEncoding
      params.width
  let replaceGates : List (EncodedBit.GateSpec Pipeline.rawEncoding) :=
    PointAddition.PortFrame.replaceConstantGates Pipeline.auxEncoding
      params.width (Pipeline.pointWords Q)
      (Pipeline.pointWords (AffinePoint.negate Q))
  change ((Layout.liftPipelineGates
      (loadGates ++ Pipeline.additionGates ++ swapGates ++ replaceGates)).map
        EncodedBit.GateSpec.xMultiplicity).sum =
    loadGates.length +
      (Pipeline.additionGates.map EncodedBit.GateSpec.xMultiplicity).sum +
      replaceGates.length
  rw [Layout.liftPipelineGates_xMultiplicity_sum]
  simp only [List.map_append, List.sum_append]
  have hloadC :
      (loadGates.map EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
    simpa only [loadGates, Pipeline.rawEncoding] using
      PointAddition.PortFrame.loadConstantGates_cnotMultiplicity_sum
        Pipeline.auxEncoding params.width (Pipeline.pointWords Q)
  have hloadT :
      (loadGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
    simpa only [loadGates, Pipeline.rawEncoding] using
      PointAddition.PortFrame.loadConstantGates_toffoliMultiplicity_sum
        Pipeline.auxEncoding params.width (Pipeline.pointWords Q)
  have hloadCoordinates := EncodedBit.GateSpec.length_eq_multiplicity_sums
    loadGates
  have hswapLength : swapGates.length = 6 * params.width := by
    simpa only [swapGates, Pipeline.rawEncoding] using
      PointAddition.PortFrame.swapMutableOutputGates_length
        Pipeline.auxEncoding params.width
  have hswapC :
      (swapGates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
        6 * params.width := by
    simpa only [swapGates, Pipeline.rawEncoding] using
      PointAddition.PortFrame.swapMutableOutputGates_cnotMultiplicity_sum
        Pipeline.auxEncoding params.width
  have hswapT :
      (swapGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
    simpa only [swapGates, Pipeline.rawEncoding] using
      PointAddition.PortFrame.swapMutableOutputGates_toffoliMultiplicity_sum
        Pipeline.auxEncoding params.width
  have hswapCoordinates := EncodedBit.GateSpec.length_eq_multiplicity_sums
    swapGates
  have hreplaceC :
      (replaceGates.map EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
    simpa only [replaceGates, Pipeline.rawEncoding] using
      PointAddition.PortFrame.replaceConstantGates_cnotMultiplicity_sum
        Pipeline.auxEncoding params.width (Pipeline.pointWords Q)
        (Pipeline.pointWords (AffinePoint.negate Q))
  have hreplaceT :
      (replaceGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
    simpa only [replaceGates, Pipeline.rawEncoding] using
      PointAddition.PortFrame.replaceConstantGates_toffoliMultiplicity_sum
        Pipeline.auxEncoding params.width (Pipeline.pointWords Q)
        (Pipeline.pointWords (AffinePoint.negate Q))
  have hreplaceCoordinates := EncodedBit.GateSpec.length_eq_multiplicity_sums
    replaceGates
  omega

omit [Fact params.modulus.val.Prime] in
/-- Exact CNOT coordinate of the common translation prefix. -/
lemma prefixGates_cnotMultiplicity_sum :
    ((prefixGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.cnotMultiplicity).sum =
      6 * params.width +
        (Pipeline.additionGates.map
          EncodedBit.GateSpec.cnotMultiplicity).sum := by
  let loadGates : List (EncodedBit.GateSpec Pipeline.rawEncoding) :=
    PointAddition.PortFrame.loadConstantGates Pipeline.auxEncoding
      params.width (Pipeline.pointWords Q)
  let swapGates : List (EncodedBit.GateSpec Pipeline.rawEncoding) :=
    PointAddition.PortFrame.swapMutableOutputGates Pipeline.auxEncoding
      params.width
  let replaceGates : List (EncodedBit.GateSpec Pipeline.rawEncoding) :=
    PointAddition.PortFrame.replaceConstantGates Pipeline.auxEncoding
      params.width (Pipeline.pointWords Q)
      (Pipeline.pointWords (AffinePoint.negate Q))
  change ((Layout.liftPipelineGates
      (loadGates ++ Pipeline.additionGates ++ swapGates ++ replaceGates)).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
    6 * params.width +
      (Pipeline.additionGates.map EncodedBit.GateSpec.cnotMultiplicity).sum
  rw [Layout.liftPipelineGates_cnotMultiplicity_sum]
  simp only [List.map_append, List.sum_append]
  have hload :
      (loadGates.map EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
    simpa only [loadGates, Pipeline.rawEncoding] using
      PointAddition.PortFrame.loadConstantGates_cnotMultiplicity_sum
        Pipeline.auxEncoding params.width (Pipeline.pointWords Q)
  have hswap :
      (swapGates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
        6 * params.width := by
    simpa only [swapGates, Pipeline.rawEncoding] using
      PointAddition.PortFrame.swapMutableOutputGates_cnotMultiplicity_sum
        Pipeline.auxEncoding params.width
  have hreplace :
      (replaceGates.map EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
    simpa only [replaceGates, Pipeline.rawEncoding] using
      PointAddition.PortFrame.replaceConstantGates_cnotMultiplicity_sum
        Pipeline.auxEncoding params.width (Pipeline.pointWords Q)
        (Pipeline.pointWords (AffinePoint.negate Q))
  omega

omit [Fact params.modulus.val.Prime] in
/-- Exact Toffoli coordinate of the common translation prefix. -/
lemma prefixGates_toffoliMultiplicity_sum :
    ((prefixGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum =
      (Pipeline.additionGates.map
        EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  let loadGates : List (EncodedBit.GateSpec Pipeline.rawEncoding) :=
    PointAddition.PortFrame.loadConstantGates Pipeline.auxEncoding
      params.width (Pipeline.pointWords Q)
  let swapGates : List (EncodedBit.GateSpec Pipeline.rawEncoding) :=
    PointAddition.PortFrame.swapMutableOutputGates Pipeline.auxEncoding
      params.width
  let replaceGates : List (EncodedBit.GateSpec Pipeline.rawEncoding) :=
    PointAddition.PortFrame.replaceConstantGates Pipeline.auxEncoding
      params.width (Pipeline.pointWords Q)
      (Pipeline.pointWords (AffinePoint.negate Q))
  change ((Layout.liftPipelineGates
      (loadGates ++ Pipeline.additionGates ++ swapGates ++ replaceGates)).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
    (Pipeline.additionGates.map
      EncodedBit.GateSpec.toffoliMultiplicity).sum
  rw [Layout.liftPipelineGates_toffoliMultiplicity_sum]
  simp only [List.map_append, List.sum_append]
  have hload :
      (loadGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
    simpa only [loadGates, Pipeline.rawEncoding] using
      PointAddition.PortFrame.loadConstantGates_toffoliMultiplicity_sum
        Pipeline.auxEncoding params.width (Pipeline.pointWords Q)
  have hswap :
      (swapGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
    simpa only [swapGates, Pipeline.rawEncoding] using
      PointAddition.PortFrame.swapMutableOutputGates_toffoliMultiplicity_sum
        Pipeline.auxEncoding params.width
  have hreplace :
      (replaceGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
    simpa only [replaceGates, Pipeline.rawEncoding] using
      PointAddition.PortFrame.replaceConstantGates_toffoliMultiplicity_sum
        Pipeline.auxEncoding params.width (Pipeline.pointWords Q)
        (Pipeline.pointWords (AffinePoint.negate Q))
  omega

omit [Fact params.modulus.val.Prime] in
/-- Lifting the final unload preserves its exact leaf count. -/
lemma unloadGates_length :
    (unloadGates (E := E) (Q := Q)).length =
      (PointAddition.PortFrame.unloadConstantGates Pipeline.auxEncoding
        params.width (Pipeline.pointWords (AffinePoint.negate Q))).length := by
  let sourceGates : List (EncodedBit.GateSpec Pipeline.rawEncoding) :=
    PointAddition.PortFrame.unloadConstantGates Pipeline.auxEncoding
      params.width (Pipeline.pointWords (AffinePoint.negate Q))
  change (Layout.liftPipelineGates sourceGates).length = sourceGates.length
  exact Layout.liftPipelineGates_length sourceGates

omit [Fact params.modulus.val.Prime] in
/-- The final unload consists entirely of X leaves. -/
lemma unloadGates_xMultiplicity_sum :
    ((unloadGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.xMultiplicity).sum =
      (PointAddition.PortFrame.unloadConstantGates Pipeline.auxEncoding
        params.width (Pipeline.pointWords (AffinePoint.negate Q))).length := by
  let sourceGates : List (EncodedBit.GateSpec Pipeline.rawEncoding) :=
    PointAddition.PortFrame.unloadConstantGates Pipeline.auxEncoding
      params.width (Pipeline.pointWords (AffinePoint.negate Q))
  change ((Layout.liftPipelineGates sourceGates).map
    EncodedBit.GateSpec.xMultiplicity).sum = sourceGates.length
  rw [Layout.liftPipelineGates_xMultiplicity_sum]
  have hc : (sourceGates.map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
    simpa only [sourceGates, Pipeline.rawEncoding] using
      PointAddition.PortFrame.unloadConstantGates_cnotMultiplicity_sum
        Pipeline.auxEncoding params.width
        (Pipeline.pointWords (AffinePoint.negate Q))
  have ht : (sourceGates.map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
    simpa only [sourceGates, Pipeline.rawEncoding] using
      PointAddition.PortFrame.unloadConstantGates_toffoliMultiplicity_sum
        Pipeline.auxEncoding params.width
        (Pipeline.pointWords (AffinePoint.negate Q))
  have hcoordinates := EncodedBit.GateSpec.length_eq_multiplicity_sums
    sourceGates
  omega

omit [Fact params.modulus.val.Prime] in
/-- The final unload contains no CNOT leaves. -/
lemma unloadGates_cnotMultiplicity_sum :
    ((unloadGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  let sourceGates : List (EncodedBit.GateSpec Pipeline.rawEncoding) :=
    PointAddition.PortFrame.unloadConstantGates Pipeline.auxEncoding
      params.width (Pipeline.pointWords (AffinePoint.negate Q))
  change ((Layout.liftPipelineGates sourceGates).map
    EncodedBit.GateSpec.cnotMultiplicity).sum = 0
  rw [Layout.liftPipelineGates_cnotMultiplicity_sum]
  simpa only [sourceGates, Pipeline.rawEncoding] using
    PointAddition.PortFrame.unloadConstantGates_cnotMultiplicity_sum
      Pipeline.auxEncoding params.width
        (Pipeline.pointWords (AffinePoint.negate Q))

omit [Fact params.modulus.val.Prime] in
/-- The final unload contains no Toffoli leaves. -/
lemma unloadGates_toffoliMultiplicity_sum :
    ((unloadGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  let sourceGates : List (EncodedBit.GateSpec Pipeline.rawEncoding) :=
    PointAddition.PortFrame.unloadConstantGates Pipeline.auxEncoding
      params.width (Pipeline.pointWords (AffinePoint.negate Q))
  change ((Layout.liftPipelineGates sourceGates).map
    EncodedBit.GateSpec.toffoliMultiplicity).sum = 0
  rw [Layout.liftPipelineGates_toffoliMultiplicity_sum]
  simpa only [sourceGates, Pipeline.rawEncoding] using
    PointAddition.PortFrame.unloadConstantGates_toffoliMultiplicity_sum
      Pipeline.auxEncoding params.width
        (Pipeline.pointWords (AffinePoint.negate Q))

/-- Exact leaf ledger of the uncontrolled total cleanup schedule. -/
lemma baseGates_length :
    (baseGates (E := E) (Q := Q)).length =
      (PointAddition.PortFrame.loadConstantGates Pipeline.auxEncoding
        params.width (Pipeline.pointWords Q)).length +
      (PointAddition.PortFrame.replaceConstantGates Pipeline.auxEncoding
        params.width (Pipeline.pointWords Q)
        (Pipeline.pointWords (AffinePoint.negate Q))).length +
      (PointAddition.PortFrame.unloadConstantGates Pipeline.auxEncoding
        params.width (Pipeline.pointWords (AffinePoint.negate Q))).length +
      2 * Pipeline.additionGates.length +
      2 * (Pipeline.additionGates.map
        EncodedBit.GateSpec.toffoliMultiplicity).sum +
      Branch.exceptionalGateCount (E := E) (Q := Q) +
      4 * (EncodedBit.Word.constantOneIndices
        (Pipeline.pointWords Q).1).length +
      14 * params.width + 12 := by
  unfold baseGates
  simp only [List.length_append, prefixGates_length,
    Selector.compareGates_length, Branch.cleanupGates_length,
    unloadGates_length]
  omega

/-- Width-closed leaf bound of the uncontrolled total cleanup schedule. -/
lemma baseGates_length_le :
    (baseGates (E := E) (Q := Q)).length ≤
      26 * params.width + 12 + 2 * Pipeline.additionGates.length +
        2 * (Pipeline.additionGates.map
          EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  rw [baseGates_length]
  have hload := PointAddition.PortFrame.loadConstantGates_length_le
    Pipeline.auxEncoding params.width (Pipeline.pointWords Q)
  have hreplace := PointAddition.PortFrame.replaceConstantGates_length_le
    Pipeline.auxEncoding params.width (Pipeline.pointWords Q)
    (Pipeline.pointWords (AffinePoint.negate Q))
  have hunload := PointAddition.PortFrame.unloadConstantGates_length_le
    Pipeline.auxEncoding params.width
    (Pipeline.pointWords (AffinePoint.negate Q))
  have hselector := EncodedBit.Word.constantOneIndices_length_le
    (Pipeline.pointWords Q).1
  have hexceptional := Branch.exceptionalGateCount_le (E := E) (Q := Q)
  omega

/-- Exact X coordinate of the uncontrolled total cleanup schedule. -/
lemma baseGates_xMultiplicity_sum :
    ((baseGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.xMultiplicity).sum =
      (PointAddition.PortFrame.loadConstantGates Pipeline.auxEncoding
        params.width (Pipeline.pointWords Q)).length +
      (PointAddition.PortFrame.replaceConstantGates Pipeline.auxEncoding
        params.width (Pipeline.pointWords Q)
        (Pipeline.pointWords (AffinePoint.negate Q))).length +
      (PointAddition.PortFrame.unloadConstantGates Pipeline.auxEncoding
        params.width (Pipeline.pointWords (AffinePoint.negate Q))).length +
      (Pipeline.additionGates.map
        EncodedBit.GateSpec.xMultiplicity).sum +
      4 * (EncodedBit.Word.constantOneIndices
        (Pipeline.pointWords Q).1).length +
      4 * params.width + 10 := by
  unfold baseGates
  simp only [List.map_append, List.sum_append,
    prefixGates_xMultiplicity_sum, Selector.compareGates_xMultiplicity_sum,
    Branch.cleanupGates_xMultiplicity_sum, unloadGates_xMultiplicity_sum]
  omega

/-- Width/addition-list bound for the uncontrolled X coordinate. -/
lemma baseGates_xMultiplicity_sum_le :
    ((baseGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.xMultiplicity).sum ≤
      Pipeline.additionGates.length + 14 * params.width + 10 := by
  rw [baseGates_xMultiplicity_sum]
  have hload := PointAddition.PortFrame.loadConstantGates_length_le
    Pipeline.auxEncoding params.width (Pipeline.pointWords Q)
  have hreplace := PointAddition.PortFrame.replaceConstantGates_length_le
    Pipeline.auxEncoding params.width (Pipeline.pointWords Q)
    (Pipeline.pointWords (AffinePoint.negate Q))
  have hunload := PointAddition.PortFrame.unloadConstantGates_length_le
    Pipeline.auxEncoding params.width
    (Pipeline.pointWords (AffinePoint.negate Q))
  have hselector := EncodedBit.Word.constantOneIndices_length_le
    (Pipeline.pointWords Q).1
  have hcoordinates := EncodedBit.GateSpec.length_eq_multiplicity_sums
    Pipeline.additionGates
  omega

/-- Exact CNOT coordinate of the uncontrolled total cleanup schedule. -/
lemma baseGates_cnotMultiplicity_sum :
    ((baseGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.cnotMultiplicity).sum =
      6 * params.width +
      (Pipeline.additionGates.map
        EncodedBit.GateSpec.cnotMultiplicity).sum +
      (Pipeline.additionGates.map
        EncodedBit.GateSpec.xMultiplicity).sum +
      Branch.exceptionalGateCount (E := E) (Q := Q) := by
  unfold baseGates
  simp only [List.map_append, List.sum_append,
    prefixGates_cnotMultiplicity_sum,
    Selector.compareGates_cnotMultiplicity_sum,
    Branch.cleanupGates_cnotMultiplicity_sum,
    unloadGates_cnotMultiplicity_sum]
  omega

/-- Width/addition-list bound for the uncontrolled CNOT coordinate. -/
lemma baseGates_cnotMultiplicity_sum_le :
    ((baseGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.cnotMultiplicity).sum ≤
      Pipeline.additionGates.length + 8 * params.width := by
  rw [baseGates_cnotMultiplicity_sum]
  have hexceptional := Branch.exceptionalGateCount_le (E := E) (Q := Q)
  have hcoordinates := EncodedBit.GateSpec.length_eq_multiplicity_sums
    Pipeline.additionGates
  omega

/-- Exact Toffoli coordinate of the uncontrolled total cleanup schedule. -/
lemma baseGates_toffoliMultiplicity_sum :
    ((baseGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum =
      4 * params.width + 2 +
      (Pipeline.additionGates.map
        EncodedBit.GateSpec.cnotMultiplicity).sum +
      4 * (Pipeline.additionGates.map
        EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  unfold baseGates
  simp only [List.map_append, List.sum_append,
    prefixGates_toffoliMultiplicity_sum,
    Selector.compareGates_toffoliMultiplicity_sum,
    Branch.cleanupGates_toffoliMultiplicity_sum,
    unloadGates_toffoliMultiplicity_sum]
  omega

/-- Exact physical leaf count after the public clean-work control lift. -/
lemma translationGates_length :
    (translationGates (E := E) (Q := Q)).length =
      (baseGates (E := E) (Q := Q)).length +
        2 * ((baseGates (E := E) (Q := Q)).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  unfold translationGates
  exact EncodedBit.GateSpec.controlledListWithWorkGates_length_eq
    Layout.controlBit Layout.controlWorkBit (baseGates (E := E) (Q := Q))
    baseGates_bitDisjoint_controlBit baseGates_bitDisjoint_controlWorkBit
    Layout.controlBit_wire_ne_controlWorkBit

/-- The public clean-work control lift contains no physical X leaves. -/
lemma translationGates_xMultiplicity_sum :
    ((translationGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  unfold translationGates
  exact EncodedBit.GateSpec.controlledListWithWorkGates_xMultiplicity_sum
    Layout.controlBit Layout.controlWorkBit (baseGates (E := E) (Q := Q))
    baseGates_bitDisjoint_controlBit baseGates_bitDisjoint_controlWorkBit
    Layout.controlBit_wire_ne_controlWorkBit

/-- Exact CNOT coordinate after the public clean-work control lift. -/
lemma translationGates_cnotMultiplicity_sum :
    ((translationGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.cnotMultiplicity).sum =
      ((baseGates (E := E) (Q := Q)).map
        EncodedBit.GateSpec.xMultiplicity).sum := by
  unfold translationGates
  exact EncodedBit.GateSpec.controlledListWithWorkGates_cnotMultiplicity_sum
    Layout.controlBit Layout.controlWorkBit (baseGates (E := E) (Q := Q))
    baseGates_bitDisjoint_controlBit baseGates_bitDisjoint_controlWorkBit
    Layout.controlBit_wire_ne_controlWorkBit

/-- Exact Toffoli coordinate after the public clean-work control lift. -/
lemma translationGates_toffoliMultiplicity_sum :
    ((translationGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum =
      ((baseGates (E := E) (Q := Q)).map
        EncodedBit.GateSpec.cnotMultiplicity).sum +
      3 * ((baseGates (E := E) (Q := Q)).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  unfold translationGates
  exact EncodedBit.GateSpec.controlledListWithWorkGates_toffoliMultiplicity_sum
    Layout.controlBit Layout.controlWorkBit (baseGates (E := E) (Q := Q))
    baseGates_bitDisjoint_controlBit baseGates_bitDisjoint_controlWorkBit
    Layout.controlBit_wire_ne_controlWorkBit

/-- Coordinate-specific leaf bound for the complete controlled translation. -/
lemma translationGates_length_le_additionCoordinates :
    (translationGates (E := E) (Q := Q)).length ≤
      34 * params.width + 16 + 2 * Pipeline.additionGates.length +
      2 * (Pipeline.additionGates.map
        EncodedBit.GateSpec.cnotMultiplicity).sum +
      10 * (Pipeline.additionGates.map
        EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  rw [translationGates_length, baseGates_toffoliMultiplicity_sum]
  have hbase := baseGates_length_le (E := E) (Q := Q)
  omega

/-- Coordinate-specific CNOT bound for the complete controlled translation. -/
lemma translationGates_cnotMultiplicity_sum_le_additionCoordinates :
    ((translationGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.cnotMultiplicity).sum ≤
      Pipeline.additionGates.length + 14 * params.width + 10 := by
  rw [translationGates_cnotMultiplicity_sum]
  exact baseGates_xMultiplicity_sum_le (E := E) (Q := Q)

/-- Coordinate-specific Toffoli bound for the complete controlled
translation.  The generic-addition length is used exactly once to account for
its X coordinate; it is not reclassified wholesale as Toffoli work. -/
lemma translationGates_toffoliMultiplicity_sum_le_additionCoordinates :
    ((translationGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
      20 * params.width + 6 + Pipeline.additionGates.length +
      3 * (Pipeline.additionGates.map
        EncodedBit.GateSpec.cnotMultiplicity).sum +
      11 * (Pipeline.additionGates.map
        EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  rw [translationGates_toffoliMultiplicity_sum,
    baseGates_cnotMultiplicity_sum,
    baseGates_toffoliMultiplicity_sum]
  have hexceptional := Branch.exceptionalGateCount_le (E := E) (Q := Q)
  have hcoordinates := EncodedBit.GateSpec.length_eq_multiplicity_sums
    Pipeline.additionGates
  omega

/-- Closed field-width/arithmetic-ledger leaf bound for the complete
controlled translation. -/
def translationGateLengthBoundFor (fieldWidth : Nat) : Nat :=
  34 * fieldWidth + 16 + 2 * Pipeline.additionGateLengthBoundFor fieldWidth +
    2 * Pipeline.additionCnotBoundFor fieldWidth +
      10 * Pipeline.additionToffoliBoundFor fieldWidth

/-- The complete controlled-translation leaf bound at the active field width. -/
def translationGateLengthBound : Nat :=
  translationGateLengthBoundFor params.width

/-- Closed field-width/arithmetic-ledger CNOT bound for the complete
controlled translation. -/
def translationCnotBoundFor (fieldWidth : Nat) : Nat :=
  Pipeline.additionGateLengthBoundFor fieldWidth + 14 * fieldWidth + 10

/-- The complete controlled-translation CNOT bound at the active field width. -/
def translationCnotBound : Nat :=
  translationCnotBoundFor params.width

/-- Closed field-width/arithmetic-ledger Toffoli bound for the complete
controlled translation. -/
def translationToffoliBoundFor (fieldWidth : Nat) : Nat :=
  20 * fieldWidth + 6 + Pipeline.additionGateLengthBoundFor fieldWidth +
    3 * Pipeline.additionCnotBoundFor fieldWidth +
      11 * Pipeline.additionToffoliBoundFor fieldWidth

/-- The complete controlled-translation Toffoli bound at the active field width. -/
def translationToffoliBound : Nat :=
  translationToffoliBoundFor params.width

/-- The complete literal gate list obeys its closed leaf bound. -/
lemma translationGates_length_le :
    (translationGates (E := E) (Q := Q)).length ≤
      translationGateLengthBound := by
  have htranslation :=
    translationGates_length_le_additionCoordinates (E := E) (Q := Q)
  have hlength := Pipeline.additionGates_length_le
  have hcnot := Pipeline.additionGates_cnotMultiplicity_sum_le
  have htoffoli := Pipeline.additionGates_toffoliMultiplicity_sum_le
  simp only [Pipeline.additionGateLengthBound] at hlength
  simp only [Pipeline.additionCnotBound] at hcnot
  simp only [Pipeline.additionToffoliBound] at htoffoli
  unfold translationGateLengthBound translationGateLengthBoundFor
  omega

/-- The complete literal gate list obeys its closed CNOT bound. -/
lemma translationGates_cnotMultiplicity_sum_le :
    ((translationGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.cnotMultiplicity).sum ≤ translationCnotBound := by
  have htranslation :=
    translationGates_cnotMultiplicity_sum_le_additionCoordinates
      (E := E) (Q := Q)
  have hlength := Pipeline.additionGates_length_le
  simp only [Pipeline.additionGateLengthBound] at hlength
  unfold translationCnotBound translationCnotBoundFor
  omega

/-- The complete literal gate list obeys its closed Toffoli bound. -/
lemma translationGates_toffoliMultiplicity_sum_le :
    ((translationGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
      translationToffoliBound := by
  have htranslation :=
    translationGates_toffoliMultiplicity_sum_le_additionCoordinates
      (E := E) (Q := Q)
  have hlength := Pipeline.additionGates_length_le
  have hcnot := Pipeline.additionGates_cnotMultiplicity_sum_le
  have htoffoli := Pipeline.additionGates_toffoliMultiplicity_sum_le
  simp only [Pipeline.additionGateLengthBound] at hlength
  simp only [Pipeline.additionCnotBound] at hcnot
  simp only [Pipeline.additionToffoliBound] at htoffoli
  unfold translationToffoliBound translationToffoliBoundFor
  omega

/-- Program X count projected from the actual literal gate list. -/
lemma translationProgram_x_count_eq :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (translationProgram (E := E) (Q := Q)).eventCost =
      ((translationGates (E := E) (Q := Q)).map
        EncodedBit.GateSpec.xMultiplicity).sum := by
  simpa only [translationProgram] using
    (EncodedBit.GateSpec.programList_x_count_eq_sum
      (QubitLayout.canonical _) .empty (translationGates (E := E) (Q := Q)))

/-- Program CNOT count projected from the actual literal gate list. -/
lemma translationProgram_cnot_count_eq :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (translationProgram (E := E) (Q := Q)).eventCost =
      ((translationGates (E := E) (Q := Q)).map
        EncodedBit.GateSpec.cnotMultiplicity).sum := by
  simpa only [translationProgram] using
    (EncodedBit.GateSpec.programList_cnot_count_eq_sum
      (QubitLayout.canonical _) .empty (translationGates (E := E) (Q := Q)))

/-- Program Toffoli count projected from the actual literal gate list. -/
lemma translationProgram_toffoli_count_eq :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (translationProgram (E := E) (Q := Q)).eventCost =
      ((translationGates (E := E) (Q := Q)).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  simpa only [translationProgram] using
    (EncodedBit.GateSpec.programList_toffoli_count_eq_sum
      (QubitLayout.canonical _) .empty (translationGates (E := E) (Q := Q)))

/-- The complete program contains no physical X event. -/
lemma translationProgram_x_count_zero :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (translationProgram (E := E) (Q := Q)).eventCost = 0 := by
  rw [translationProgram_x_count_eq, translationGates_xMultiplicity_sum]

/-- The complete program obeys its closed CNOT bound. -/
lemma translationProgram_cnot_count_le :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (translationProgram (E := E) (Q := Q)).eventCost ≤
      translationCnotBound := by
  rw [translationProgram_cnot_count_eq]
  exact translationGates_cnotMultiplicity_sum_le (E := E) (Q := Q)

/-- The complete program obeys its closed Toffoli bound. -/
lemma translationProgram_toffoli_count_le :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (translationProgram (E := E) (Q := Q)).eventCost ≤
      translationToffoliBound := by
  rw [translationProgram_toffoli_count_eq]
  exact translationGates_toffoliMultiplicity_sum_le (E := E) (Q := Q)

/-- The program event-depth expression is the ordered literal primitive-event
schedule. -/
lemma translationProgram_eventDepth :
    (translationProgram (E := E) (Q := Q)).eventDepth =
      EncodedBit.GateSpec.depthOfEvents
        ((translationGates (E := E) (Q := Q)).map
          (EncodedBit.GateSpec.event .empty)) := by
  simpa only [translationProgram] using
    (EncodedBit.GateSpec.programList_eventDepth
      (QubitLayout.canonical _) .empty (translationGates (E := E) (Q := Q)))

/-- Under unit primitive durations, sequential event depth is the actual
literal gate-list length. -/
lemma translationProgram_unitDepth_eq :
    (translationProgram (E := E) (Q := Q)).evaluatedEventDepth
      (fun _ => 1) = (translationGates (E := E) (Q := Q)).length := by
  simpa only [translationProgram] using
    (EncodedBit.GateSpec.programList_evaluatedEventDepth_unit
      (QubitLayout.canonical _) .empty (translationGates (E := E) (Q := Q)))

/-- Under unit primitive durations, the program obeys the closed leaf/depth
bound. -/
lemma translationProgram_unitDepth_le :
    (translationProgram (E := E) (Q := Q)).evaluatedEventDepth
      (fun _ => 1) ≤ translationGateLengthBound := by
  rw [translationProgram_unitDepth_eq]
  exact translationGates_length_le (E := E) (Q := Q)

end

end ExceptionalCleanup
end GenericPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
