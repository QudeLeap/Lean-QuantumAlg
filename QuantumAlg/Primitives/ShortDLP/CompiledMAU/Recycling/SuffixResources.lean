/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Resources
import QuantumAlg.Core.Execution.Time

/-!
# Whole chronological suffixes and both recycled exponent streams

The original recursive schedule accumulates both exponent streams serially.
Their independent phase opportunities sum to choose 2 of each width, with
zero-width streams included. The existing bank and retained result cells
remain the only live resources during every complete member path.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Resources

noncomputable section

open Execution

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- Every actual suffix path pays the original stages and their preceding feedback bits. -/
lemma exponentSuffix_events (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) (remaining position : Nat)
    (bounded : position + remaining ≤ bits)
    (path : (exponentSuffix base noQuantum m ell width inverse outputs N unit
      remaining position bounded).Path) :
    (exponentSuffix base noQuantum m ell width inverse outputs N unit
      remaining position bounded).resourcePool path ≤ suffixBudget width remaining position := by
  induction remaining generalizing position with
  | zero =>
      simp [exponentSuffix, Circuit.resourcePool, Circuit.eventTrace, suffixBudget, feedbackWork]
  | succ remaining ih =>
      have head := stage_events base noQuantum m ell width inverse outputs N unit
        ⟨position, by omega⟩ path.1
      have tail := ih (position + 1) (by omega) path.2
      refine (seq_events _ _ path _ _ head tail).trans_eq ?_
      simp only [suffixBudget, stageBudget, feedbackWork_succ, succ_nsmul, add_nsmul]
      ac_rfl

/-- The actual suffix quantum time accumulates the original serial arithmetic bound. -/
lemma exponentSuffix_time (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) (remaining position : Nat)
    (bounded : position + remaining ≤ bits)
    (path : (exponentSuffix base noQuantum m ell width inverse outputs N unit
      remaining position bounded).Path) :
    (exponentSuffix base noQuantum m ell width inverse outputs N unit
      remaining position bounded).quantumTime path ≤ suffixTime width remaining position := by
  induction remaining generalizing position with
  | zero =>
      exact (Circuit.quantumTime_id (model := model)
        (Context base noQuantum m ell width) path).le.trans (Nat.zero_le _)
  | succ remaining ih =>
      have head := stage_time base noQuantum m ell width inverse outputs N unit
        ⟨position, by omega⟩ path.1
      have tail := ih (position + 1) (by omega) path.2
      have full :
          (exponentSuffix base noQuantum m ell width inverse outputs N unit
            (remaining + 1) position bounded).quantumTime path ≤
            stageTime width position + suffixTime width remaining (position + 1) :=
        Nat.add_le_add head tail
      refine full.trans_eq ?_
      simp only [stageTime, suffixTime, feedbackWork_succ, Nat.succ_mul]
      omega

/-- Complete suffixes, including the empty suffix, retain exactly the same live bank and cells. -/
lemma exponentSuffix_spaces (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) (remaining position : Nat)
    (bounded : position + remaining ≤ bits)
    (path : (exponentSuffix base noQuantum m ell width inverse outputs N unit
      remaining position bounded).Path) :
    (exponentSuffix base noQuantum m ell width inverse outputs N unit
      remaining position bounded).peakResidentSpace path =
        (Context base noQuantum m ell width).residentSpace ∧
      (exponentSuffix base noQuantum m ell width inverse outputs N unit
        remaining position bounded).peakAuxiliarySpace path =
          (Context base noQuantum m ell width).auxiliarySpace := by
  induction remaining generalizing position with
  | zero => exact ⟨Circuit.peakResidentSpace_id path, Circuit.peakAuxiliarySpace_id path⟩
  | succ remaining ih =>
      exact seq_spaces _ _ path
        (stage_spaces base noQuantum m ell width inverse outputs N unit
          ⟨position, by omega⟩ path.1)
        (ih (position + 1) (by omega) path.2)

/-- A complete exponent has its width's triangular feedback allowance. -/
lemma exponent_events (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ)
    (path : (exponentCode base noQuantum m ell width inverse outputs N unit).Path) :
    (exponentCode base noQuantum m ell width inverse outputs N unit).resourcePool path ≤
      bits • baseBudget width + bits.choose 2 • oneQubit := by
  simpa only [exponentCode, suffixBudget, feedbackWork, Nat.mul_zero, Nat.zero_add] using
    exponentSuffix_events base noQuantum m ell width inverse outputs N unit bits 0 (by omega) path

/-- The original exponent time remains a bound on this complete sequential execution. -/
lemma exponent_time (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ)
    (path : (exponentCode base noQuantum m ell width inverse outputs N unit).Path) :
    (exponentCode base noQuantum m ell width inverse outputs N unit).quantumTime path ≤
      bits * (MAU.Multiplication.Gidney.controlledTimeBound width + 3) + bits.choose 2 := by
  simpa only [exponentCode, suffixTime, feedbackWork, Nat.mul_zero, Nat.zero_add] using
    exponentSuffix_time base noQuantum m ell width inverse outputs N unit bits 0 (by omega) path

/-- The two original exponent streams retain separate triangular feedback charges. -/
lemma member_events (N : Nat) (generator target : (ZMod N)ˣ)
    (path : (member base noQuantum m ell width N generator target).Path) :
    (member base noQuantum m ell width N generator target).resourcePool path ≤
      memberBudget m ell width := by
  have first := exponent_events base noQuantum m ell width true
    (firstCell base noQuantum m ell width) N generator path.1
  have second := exponent_events base noQuantum m ell width true
    (secondCell base noQuantum m ell width) N target⁻¹ path.2
  refine (seq_events _ _ path _ _ first second).trans_eq ?_
  simp only [memberBudget, resultBits, add_nsmul]
  ac_rfl

/-- Both exponents run in sequence; no arithmetic or feedback time is counted in parallel. -/
lemma member_time (N : Nat) (generator target : (ZMod N)ˣ)
    (path : (member base noQuantum m ell width N generator target).Path) :
    (member base noQuantum m ell width N generator target).quantumTime path ≤
      memberTime m ell width := by
  have first := exponent_time base noQuantum m ell width true
    (firstCell base noQuantum m ell width) N generator path.1
  have second := exponent_time base noQuantum m ell width true
    (secondCell base noQuantum m ell width) N target⁻¹ path.2
  have full : (member base noQuantum m ell width N generator target).quantumTime path ≤
      ((ell + m) * (MAU.Multiplication.Gidney.controlledTimeBound width + 3) +
        (ell + m).choose 2) +
      (ell * (MAU.Multiplication.Gidney.controlledTimeBound width + 3) + ell.choose 2) :=
    Nat.add_le_add first second
  refine full.trans_eq ?_
  simp only [memberTime, resultBits, Nat.add_mul]
  omega

/-- One control, two arithmetic words and the already retained output bits stay resident. -/
lemma member_resident (N : Nat) (generator target : (ZMod N)ˣ)
    (path : (member base noQuantum m ell width N generator target).Path) :
    (member base noQuantum m ell width N generator target).peakResidentSpace path =
      resultBits m ell • SpacePool.ofShape (.finite 2) +
        (SpacePool.ofQuantumLayout (Arithmetic.layout width).toQuantum + base.residentSpace) := by
  have spaces := seq_spaces _ _ path
    (exponentSuffix_spaces base noQuantum m ell width true
      (firstCell base noQuantum m ell width) N generator (ell + m) 0 (by omega) path.1)
    (exponentSuffix_spaces base noQuantum m ell width true
      (secondCell base noQuantum m ell width) N target⁻¹ ell 0 (by omega) path.2)
  exact spaces.1.trans (context_resident base noQuantum m ell width)

/-- Auxiliary peaks reuse the same owned arithmetic bank, adding no quantum workspace per bit. -/
lemma member_auxiliary (N : Nat) (generator target : (ZMod N)ˣ)
    (path : (member base noQuantum m ell width N generator target).Path) :
    (member base noQuantum m ell width N generator target).peakAuxiliarySpace path =
      resultBits m ell • SpacePool.ofShape (.finite 2) +
        (SpacePool.ofQuantumLayout (Arithmetic.layout width).toQuantum + base.auxiliarySpace) := by
  have spaces := seq_spaces _ _ path
    (exponentSuffix_spaces base noQuantum m ell width true
      (firstCell base noQuantum m ell width) N generator (ell + m) 0 (by omega) path.1)
    (exponentSuffix_spaces base noQuantum m ell width true
      (secondCell base noQuantum m ell width) N target⁻¹ ell 0 (by omega) path.2)
  exact spaces.2.trans (context_auxiliary base noQuantum m ell width)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Resources
