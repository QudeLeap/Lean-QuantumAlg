/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Resident.Seed
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Inversion

/-!
# Paid fixed small-source initialization for the original P-256 point frame

This specializes the proved generic quantum preparation by the original
word-size equality. The modulus alone fixes its X instructions. No point,
input residue, good offset, classical preprocessing or measured outcome
selects these instructions. All original physical systems remain present.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Inversion.Seed

noncomputable section

open MAU.Inversion.SharedEEA MAU.Inversion.SharedEEA.Scanned

private lemma length_positive : 0 < modulus.size.size := by
  rw [modulus_size]
  decide

/-- The same generic fixed X layer on the complete original point bank. -/
def program : Native.Circuit :=
  Transport.program modulus_size
    (ControlledResidentSeed.program modulus.size length_positive
      (ControlledResidentSeed.tail modulus))

/-- Complete zero source workspace before its actual paid native initialization. -/
def blank (input numerator : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : Frame.Controls) : Frame.Raw :=
  Transport.state modulus_size
    (ControlledResidentSeed.blank modulus.size
      (InitialPortProgram.inputFrame modulus input).secondWord pool flags numerator)

/-- The native preparation produces the exact complete initial frame required by inversion. -/
lemma program_blank (environment : OracleModel.empty.Interpretation)
    (input numerator : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : Frame.Controls) :
    program.applyNormalized environment (Native.ket (blank input numerator pool flags)) =
      Native.ket (Inversion.initial input numerator pool flags) := by
  have actual := ControlledResidentSeed.program_blank modulus.size length_positive
    (ControlledResidentSeed.tail modulus) environment
    (InitialPortProgram.inputFrame modulus input).secondWord pool flags numerator
  rw [ControlledResidentSeed.seeded_initial] at actual
  exact Transport.program_apply modulus_size _ environment _ _ actual

/-- Every actually emitted X occurrence remains in the placed program ledger. -/
lemma program_eventTrace : program.eventTrace =
    List.replicate
      (EncodedBit.Word.constantOneIndices
        (ResidentSeed.constant (ControlledResidentSeed.tail modulus))).length
      (.gate .singleQubit) := by
  rw [program, Transport.program_eventTrace, ControlledResidentSeed.program_eventTrace,
    ResidentSeed.program_eventTrace]

/-- The actual native parallel preparation retains its generic one-step upper bound. -/
lemma program_quantumTime_le :
    program.evaluatedEventDepth Resource.Event.quantumDuration ≤ 1 := by
  rw [program, Transport.program_quantumTime]
  exact ControlledResidentSeed.program_quantumTime_le _ _ _

/-- The same independently identified four original physical positions bound the native X count. -/
lemma xCount_le :
    (EncodedBit.Word.constantOneIndices
      (ResidentSeed.constant (ControlledResidentSeed.tail modulus))).length ≤ 4 :=
  ResidentSeed.seed_count_le _

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Inversion.Seed
