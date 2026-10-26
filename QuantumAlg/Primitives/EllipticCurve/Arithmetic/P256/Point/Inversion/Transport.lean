/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Correctness
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Resident

/-!
# Typed specialization of the complete generic resident inversion frame

Only a proved equality of the original word widths is transported.
The generic resident encoding already has exactly the original physical
point order. No instruction, permutation, initialization hypothesis or
state component is changed by specializing its width.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Inversion

noncomputable section

namespace Transport

private lemma frame_width : Frame.payloadWidth = 256 := rfl

section

attribute [local irreducible] Frame.payloadWidth

private def programAt {width : Nat} (same : width = Frame.payloadWidth)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.encoding
        width).width).toQuantum) : Native.Circuit := by
  cases same
  exact body

private def stateAt {width : Nat} (same : width = Frame.payloadWidth)
    (value : MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.Data width) : Frame.Raw := by
  cases same
  exact value

private lemma residentKet_eq
    (value : MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.Data Frame.payloadWidth) :
    NormalizedVector.ket
        ((QubitLayout.canonical
          (MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.encoding
            Frame.payloadWidth).width).basisEquiv.symm
          ((MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.encoding
            Frame.payloadWidth).encode value)) = Native.ket value := by
  rfl

private lemma programAt_apply {width : Nat} (same : width = Frame.payloadWidth)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.encoding
        width).width).toQuantum) (environment : OracleModel.empty.Interpretation)
    (initial final : MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.Data width)
    (actual : body.applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.encoding width).encode
          initial))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.encoding width).encode final))) :
    (programAt same body).applyNormalized environment (Native.ket (stateAt same initial)) =
      Native.ket (stateAt same final) := by
  cases same
  have retained :=
    (congrArg (body.applyNormalized environment) (residentKet_eq initial)).symm.trans
      (actual.trans (residentKet_eq final))
  simpa only [programAt, stateAt, Frame.encoding, Frame.encodingAt, Frame.controlsEncoding,
    MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.encoding,
    MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.flagsEncoding] using retained

private lemma programAt_eventTrace {width : Nat} (same : width = Frame.payloadWidth)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.encoding
        width).width).toQuantum) : (programAt same body).eventTrace = body.eventTrace := by
  cases same
  rfl

private lemma programAt_quantumTime {width : Nat} (same : width = Frame.payloadWidth)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.encoding
        width).width).toQuantum) :
    (programAt same body).evaluatedEventDepth Resource.Event.quantumDuration =
      body.evaluatedEventDepth Resource.Event.quantumDuration := by
  cases same
  rfl

end

def program {width : Nat} (same : width = 256)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.encoding
        width).width).toQuantum) : Native.Circuit :=
  programAt (same.trans frame_width.symm) body

def state {width : Nat} (same : width = 256)
    (value : MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.Data width) : Frame.Raw :=
  stateAt (same.trans frame_width.symm) value

lemma state_refl
    (value : MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.Data 256) :
    state rfl value = value := rfl

lemma program_apply {width : Nat} (same : width = 256)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.encoding
        width).width).toQuantum) (environment : OracleModel.empty.Interpretation)
    (initial final : MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.Data width)
    (actual : body.applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.encoding width).encode
          initial))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.encoding width).encode final))) :
    (program same body).applyNormalized environment (Native.ket (state same initial)) =
      Native.ket (state same final) :=
  programAt_apply (same.trans frame_width.symm) body environment initial final actual

lemma state_value {width : Nat} (same : width = 256)
    (value : MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.Data width) :
    Frame.work2 (state same value) =
      Fin.cast (congrArg (fun size => 2 ^ size) same)
        (MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.value value) := by
  cases same
  simp only [state, Frame.work2,
    stateAt, MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.value, Fin.cast_eq_self]

lemma state_numerator {width : Nat} (same : width = 256)
    (value : MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.Data width) :
    Frame.numerator (state same value) =
      Fin.cast (congrArg (fun size => 2 ^ size) same) value.1.2 := by
  cases same
  rfl

lemma state_flags {width : Nat} (same : width = 256)
    (value : MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.Data width) :
    (state same value).2 = value.2 := by
  cases same
  rfl

lemma program_eventTrace {width : Nat} (same : width = 256)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.encoding
        width).width).toQuantum) : (program same body).eventTrace = body.eventTrace :=
  programAt_eventTrace (same.trans frame_width.symm) body

lemma program_quantumTime {width : Nat} (same : width = 256)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.encoding
        width).width).toQuantum) :
    (program same body).evaluatedEventDepth Resource.Event.quantumDuration =
      body.evaluatedEventDepth Resource.Event.quantumDuration :=
  programAt_quantumTime (same.trans frame_width.symm) body

end Transport

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Inversion
