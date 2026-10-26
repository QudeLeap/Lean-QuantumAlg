/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Resources

/-!
# Complete actual two-exponent measured recycling resource bounds

Both exponent streams accumulate their real measured arithmetic stages,
physical control readouts and triangular stored feedback charges. Their
complete original allocated context remains resident on every actual path
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Resources

noncomputable section

open Execution

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- Every literal suffix retains each measured stage and each preceding-bit feedback opportunity. -/
lemma measuredExponentSuffix_events (wide : 2 ≤ width) (large : 5 ≤ width)
    (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (odd : modulus.getLsbD 0 = true) (unit : (ZMod modulus.toNat)ˣ)
    (remaining position : Nat) (bounded : position + remaining ≤ bits)
    (path : (exponentSuffix base noQuantum m ell width wide inverse outputs modulus unit
      remaining position bounded).Path) :
    (exponentSuffix base noQuantum m ell width wide inverse outputs modulus unit
      remaining position bounded).resourcePool path ≤ suffixBudget width remaining position := by
  induction remaining generalizing position with
  | zero =>
      simp [exponentSuffix, Circuit.resourcePool, Circuit.eventTrace, suffixBudget, feedbackWork]
  | succ remaining ih =>
      have head := measuredStage_events base noQuantum m ell width wide large inverse outputs
        modulus positive odd unit ⟨position, by omega⟩ path.1
      have tail := ih (position + 1) (by omega) path.2
      have full :
          (exponentSuffix base noQuantum m ell width wide inverse outputs modulus unit
            (remaining + 1) position bounded).resourcePool path ≤
              stageBudget width position + suffixBudget width remaining (position + 1) := by
        simpa only [exponentSuffix, Circuit.resourcePool, Circuit.eventTrace,
          ResourcePool.ofList_append] using add_le_add head tail
      refine full.trans_eq ?_
      simp only [suffixBudget, stageBudget, measuredFeedbackWork_succ, succ_nsmul, add_nsmul]
      ac_rfl

private lemma suffix_time_formula (width remaining position : Nat) :
    stageTime width position + suffixTime width remaining (position + 1) =
      suffixTime width (remaining + 1) position := by
  unfold stageTime suffixTime
  rw [measuredFeedbackWork_succ,
    Nat.succ_mul remaining ((160 * width ^ 2 - 255 * width) + 3)]
  omega

/-- All actual suffix stages retain their complete sequential quantum-duration bound. -/
lemma measuredExponentSuffix_time (wide : 2 ≤ width) (large : 5 ≤ width)
    (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (odd : modulus.getLsbD 0 = true) (unit : (ZMod modulus.toNat)ˣ)
    (remaining position : Nat) (bounded : position + remaining ≤ bits)
    (path : (exponentSuffix base noQuantum m ell width wide inverse outputs modulus unit
      remaining position bounded).Path) :
    (exponentSuffix base noQuantum m ell width wide inverse outputs modulus unit
      remaining position bounded).quantumTime path ≤ suffixTime width remaining position := by
  induction remaining generalizing position with
  | zero => exact (Circuit.quantumTime_id _ path).le.trans (Nat.zero_le _)
  | succ remaining ih =>
      have head := measuredStage_time base noQuantum m ell width wide large inverse outputs
        modulus positive odd unit ⟨position, by omega⟩ path.1
      have tail := ih (position + 1) (by omega) path.2
      exact (Nat.add_le_add head tail).trans_eq (suffix_time_formula width remaining position)

/-- One complete actual exponent has every measured arithmetic stage and triangular feedback. -/
lemma measuredExponent_events (wide : 2 ≤ width) (large : 5 ≤ width)
    (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (odd : modulus.getLsbD 0 = true) (unit : (ZMod modulus.toNat)ˣ)
    (path : (exponentCode base noQuantum m ell width wide inverse outputs modulus unit).Path) :
    (exponentCode base noQuantum m ell width wide inverse outputs modulus unit).resourcePool path ≤
      bits • baseBudget width + bits.choose 2 • oneQubit := by
  simpa only [exponentCode, suffixBudget, feedbackWork, Nat.mul_zero, Nat.zero_add] using
    measuredExponentSuffix_events base noQuantum m ell width wide large inverse outputs
      modulus positive odd unit bits 0 (by omega) path

/-- The actual exponent retains measured arithmetic and all paid control/feedback gate time. -/
lemma measuredExponent_time (wide : 2 ≤ width) (large : 5 ≤ width)
    (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (odd : modulus.getLsbD 0 = true) (unit : (ZMod modulus.toNat)ˣ)
    (path : (exponentCode base noQuantum m ell width wide inverse outputs modulus unit).Path) :
    (exponentCode base noQuantum m ell width wide inverse outputs modulus unit).quantumTime path ≤
      bits * ((160 * width ^ 2 - 255 * width) + 3) + bits.choose 2 := by
  simpa only [exponentCode, suffixTime, feedbackWork, Nat.mul_zero, Nat.zero_add] using
    measuredExponentSuffix_time base noQuantum m ell width wide large inverse outputs
      modulus positive odd unit bits 0 (by omega) path

/-- The complete member retains both measured exponent streams and their separate feedback. -/
lemma measuredMember_events (wide : 2 ≤ width) (large : 5 ≤ width)
    (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (odd : modulus.getLsbD 0 = true) (generator target : (ZMod modulus.toNat)ˣ)
    (path : (member base noQuantum m ell width wide modulus generator target).Path) :
    (member base noQuantum m ell width wide modulus generator target).resourcePool path ≤
      memberBudget m ell width := by
  have first := measuredExponent_events base noQuantum m ell width wide large true
    (firstCell base noQuantum m ell width) modulus positive odd generator path.1
  have second := measuredExponent_events base noQuantum m ell width wide large true
    (secondCell base noQuantum m ell width) modulus positive odd target⁻¹ path.2
  have full : (member base noQuantum m ell width wide modulus generator target).resourcePool path ≤
      ((ell + m) • baseBudget width + (ell + m).choose 2 • oneQubit) +
        (ell • baseBudget width + ell.choose 2 • oneQubit) := by
    simpa only [member, Circuit.resourcePool, Circuit.eventTrace, ResourcePool.ofList_append] using
      add_le_add first second
  refine full.trans_eq ?_
  simp only [memberBudget, resultBits, add_nsmul]
  ac_rfl

private lemma member_time_formula (m ell width : Nat) :
    ((ell + m) * ((160 * width ^ 2 - 255 * width) + 3) + (ell + m).choose 2) +
      (ell * ((160 * width ^ 2 - 255 * width) + 3) + ell.choose 2) =
        memberTime m ell width := by
  simp only [memberTime, resultBits, Nat.add_mul]
  omega

/-- Both actual exponent streams execute sequentially on their same original physical bank. -/
lemma measuredMember_time (wide : 2 ≤ width) (large : 5 ≤ width)
    (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (odd : modulus.getLsbD 0 = true) (generator target : (ZMod modulus.toNat)ˣ)
    (path : (member base noQuantum m ell width wide modulus generator target).Path) :
    (member base noQuantum m ell width wide modulus generator target).quantumTime path ≤
      memberTime m ell width := by
  have first := measuredExponent_time base noQuantum m ell width wide large true
    (firstCell base noQuantum m ell width) modulus positive odd generator path.1
  have second := measuredExponent_time base noQuantum m ell width wide large true
    (secondCell base noQuantum m ell width) modulus positive odd target⁻¹ path.2
  exact (Nat.add_le_add first second).trans_eq (member_time_formula m ell width)

/-- The actual full member keeps both real cell banks and the complete constant-workspace frame. -/
lemma measuredMember_resident (wide : 2 ≤ width) (modulus : BitVec width)
    (generator target : (ZMod modulus.toNat)ˣ)
    (path : (member base noQuantum m ell width wide modulus generator target).Path) :
    (member base noQuantum m ell width wide modulus generator target).peakResidentSpace path =
      (resultBits m ell + (width - 2)) • SpacePool.ofShape (.finite 2) +
        (SpacePool.ofQuantumLayout
          (MAU.Multiplication.Gidney.Measured.Physical.qubits width).toQuantum +
            base.residentSpace) := by
  rw [Circuit.fixed_peakResidentSpace, context_resident]

/-- Only the actual measured multiplication can emit a native Toffoli in the complete member. -/
lemma measuredMember_toffoli_bound (wide : 2 ≤ width) (large : 5 ≤ width)
    (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (odd : modulus.getLsbD 0 = true) (generator target : (ZMod modulus.toNat)ˣ)
    (path : (member base noQuantum m ell width wide modulus generator target).Path) :
    ResourcePool.count (model := model) (.gate .toffoli)
      ((member base noQuantum m ell width wide modulus generator target).resourcePool path) ≤
        resultBits m ell * (28 * width ^ 2 - 45 * width) := by
  have bound := ResourcePool.le_iff_count.mp
    (measuredMember_events base noQuantum m ell width wide large modulus positive odd
      generator target path) (.gate .toffoli)
  simpa [memberBudget, baseBudget, arithmeticBudget,
    MAU.Multiplication.Gidney.Measured.Layout.multiplicationBudget,
    MAU.Addition.Gidney.Measured.Instruction.coordinatePool, oneQubit, oneMeasurement] using bound

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Resources
