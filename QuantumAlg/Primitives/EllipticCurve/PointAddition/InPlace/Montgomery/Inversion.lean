/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.InPlace.ArithmeticLift
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.Compact.Inversion

/-!
# Montgomery inversion on the in-place point carrier

The complete compact Montgomery--Kaliski inversion ledger is lifted through
the outer point fields without adding any wire.  Its clean endpoint changes
only the compact public target `t0`; the mutable coordinates, persistent slope,
input word, sole history word, counter, and borrowed VBE workspace return to
their input values.  This is the physical operation used at Algorithm 1's
steps 3/6 and 12/14 [RNSL17, ECDLP.tex:516,519,525,527].
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace GenericPointAddition
namespace InPlace
namespace MontgomeryInversion

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Nat.FixedWidth
open MAU.Inversion
open MAU.Inversion.MK
open MAU.Inversion.MK.Circuit

/-- Clean point-carrier boundary for one compact inversion call. -/
def inversionState
    (fieldTail counterTail : Nat)
    (control : Bool) (mutableY «λ» : Word fieldTail.succ)
    (p input target : Word fieldTail.succ) :
    Layout.Registers fieldTail.succ (counterTail + 2) where
  control := control
  mutableY := mutableY
  «λ» := «λ»
  arithmetic := CompactCertificate.compactInitialRegisters
    fieldTail counterTail p input target

/-- Literal compact inversion ledger lifted into the point carrier. -/
def gates
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ (counterTail + 2))) :=
  ArithmeticLift.gates fieldTail.succ (counterTail + 2)
    (CompactInversion.compactInversionGates fieldTail counterTail p
      hfit hcapacity hwidth)

/-- Circuit compiled from the lifted literal inversion ledger. -/
def program
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (Layout.encoding fieldTail.succ (counterTail + 2)).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (gates fieldTail counterTail p hfit hcapacity hwidth)

/-- Folded action of the lifted inversion ledger. -/
def step
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ) :
    Layout.Registers fieldTail.succ (counterTail + 2) ->
      Layout.Registers fieldTail.succ (counterTail + 2) :=
  EncodedBit.GateSpec.stepList
    (gates fieldTail counterTail p hfit hcapacity hwidth)

/-- The lifted circuit realizes its exact ordered gate-list action. -/
lemma realizes
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ) :
    UnitaryCircuit.Realizes (Layout.encoding fieldTail.succ (counterTail + 2))
      (program fieldTail counterTail p hfit hcapacity hwidth) environment
      (step fieldTail counterTail p hfit hcapacity hwidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (gates fieldTail counterTail p hfit hcapacity hwidth)

/-- Lifting preserves the literal number of primitive gates. -/
@[simp] lemma gates_length
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ) :
    (gates fieldTail counterTail p hfit hcapacity hwidth).length =
      (CompactInversion.compactInversionGates fieldTail counterTail p
        hfit hcapacity hwidth).length := by
  simp [gates]

/-- Lifting preserves the complete strict primitive event trace. -/
lemma gates_map_event
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ) :
    (gates fieldTail counterTail p hfit hcapacity hwidth).map
        (EncodedBit.GateSpec.event .empty) =
      (CompactInversion.compactInversionGates fieldTail counterTail p
        hfit hcapacity hwidth).map (EncodedBit.GateSpec.event .empty) := by
  exact ArithmeticLift.gates_map_event fieldTail.succ (counterTail + 2)
    (CompactInversion.compactInversionGates fieldTail counterTail p
      hfit hcapacity hwidth)

set_option maxHeartbeats 1200000 in
-- The proof specializes the complete fixed-round compact endpoint once.
/-- A clean coprime inversion call changes only `t0`.  The returned word is
the exact runtime-count-corrected Montgomery--Kaliski residue from the compact
physical ledger. -/
lemma step_cleanEndpoint
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ)
    (hcounterWidth : counterTail + 2 =
      Nat.clog 2 (2 * fieldTail.succ))
    (control : Bool) (mutableY «λ» : Word fieldTail.succ)
    (p input target : Word fieldTail.succ)
    (hpOdd : p.val % 2 = 1) (hinput : 0 < input.val)
    (hcoprime : Nat.Coprime p.val input.val)
    (htarget : target.val < p.val) :
    let seed := CompactCertificate.compactInitialRegisters
      fieldTail counterTail p input target
    let folded := CompactCertificate.compactFoldStep
      fieldTail counterTail hfit seed
    let hpPos : 0 < p.val := by omega
    let reduced := CompactCorrection.canonicalResidueWord
      fieldTail p.val hpPos p.isLt folded.core.rCoeff
    let corrected := CompactCorrection.correctionResiduePrefix
      fieldTail p.val hpPos p.isLt folded.core.counter.val fieldTail.succ
        reduced
    let correctedLow := CompactCorrection.truncateFixedWord
      fieldTail.succ corrected
    let updated := CompactCorrection.modularDifferenceWord
      fieldTail p.val hpPos p.isLt target correctedLow
    step fieldTail counterTail p.val hfit hcapacity hwidth
        (inversionState fieldTail counterTail control mutableY «λ» p input
          target) =
      inversionState fieldTail counterTail control mutableY «λ» p input
        updated := by
  let seed := CompactCertificate.compactInitialRegisters
    fieldTail counterTail p input target
  let folded := CompactCertificate.compactFoldStep
    fieldTail counterTail hfit seed
  let hpPos : 0 < p.val := by omega
  let reduced := CompactCorrection.canonicalResidueWord
    fieldTail p.val hpPos p.isLt folded.core.rCoeff
  let corrected := CompactCorrection.correctionResiduePrefix
    fieldTail p.val hpPos p.isLt folded.core.counter.val fieldTail.succ reduced
  let correctedLow := CompactCorrection.truncateFixedWord fieldTail.succ
    corrected
  let updated := CompactCorrection.modularDifferenceWord
    fieldTail p.val hpPos p.isLt target correctedLow
  have hcompact := CompactInversion.compactInversionStep_cleanEndpoint
    fieldTail counterTail hfit hcapacity hwidth hcounterWidth p input target
      hpOdd hinput hcoprime htarget
  dsimp only at hcompact
  change step fieldTail counterTail p.val hfit hcapacity hwidth
      (inversionState fieldTail counterTail control mutableY «λ» p input
        target) =
    inversionState fieldTail counterTail control mutableY «λ» p input
      updated
  rw [step, gates, ArithmeticLift.gates_stepList]
  change
    { control := control
      mutableY := mutableY
      «λ» := «λ»
      arithmetic := CompactInversion.compactInversionStep fieldTail counterTail
        p.val hfit hcapacity hwidth seed } =
      inversionState fieldTail counterTail control mutableY «λ» p input
        updated
  rw [hcompact]
  rfl

end
end MontgomeryInversion
end InPlace
end GenericPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
