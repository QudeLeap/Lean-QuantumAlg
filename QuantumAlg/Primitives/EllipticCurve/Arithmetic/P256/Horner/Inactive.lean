/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Product

/-!
# Actual inactive clean Horner execution on arbitrary source words

Only the target and three real arithmetic flags are initialized. The source,
multiplier and complete retained caller component have arbitrary values.
Every actual selected addition is disabled; actual target doublings retain
zero. No canonical-source promise is needed in this branch.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)
  (multiplier : QuantumMultiplier saved) (outer : EncodedBit saved)
  (outerMultiplier : ∀ index,
    (operandSavedBit saved outer).wire ≠
      (operandMultiplierBit saved (multiplier.ports index)).wire)

/-- A disabled real latch/add/unlatch stage retains arbitrary original words and work. -/
lemma stage_inactive (port : MultiplierPort saved)
    (separate : (operandSavedBit saved outer).wire ≠ (operandMultiplierBit saved port).wire)
    (source target : Word) (reduction work : Bool) (retained : Saved)
    (disabled : outer.get retained = false) :
    stepList (stageGates saved port outer separate)
        ((((source, target), reduction), (false, work)), retained) =
      ((((source, target), reduction), (false, work)), retained) := by
  have latch := latch_step saved port outer source target reduction false work retained
  simp only [disabled, Bool.false_and, Bool.xor_false] at latch
  let state : OperandRegisters Saved :=
    ((((source, target), reduction), (false, work)), retained)
  have body : stepList (operandAdditionGates saved) state = state :=
    (operandAdditionGates_step saved state).trans
      (congrArg (fun originalPrefix : Controlled.SelectedRegisters => (originalPrefix, retained))
        (Controlled.controlledAddition_of_selector_false state.1 rfl))
  have actual := Selection.gates_step (operandSavedBit saved outer)
    (operandMultiplierBit saved port) (operandLatchBit saved) separate
    (operandSaved_latch_ne saved outer) (operandMultiplier_latch_ne saved port)
    (operandAdditionGates saved) state
  have afterBody := (congrArg (stepList (operandAdditionGates saved)) latch).trans body
  exact actual.trans ((congrArg
    (toffoliStep (operandSavedBit saved outer) (operandMultiplierBit saved port)
      (operandLatchBit saved)) afterBody).trans latch)

private lemma cleanRound_inactive (source : Word) (retained : Saved)
    (disabled : outer.get retained = false) (index : Fin width) :
    cleanRoundStep saved multiplier outer outerMultiplier index
        ((((source, zeroWord), false), (false, false)), retained) =
      ((((source, zeroWord), false), (false, false)), retained) := by
  have addition := stage_inactive saved outer (multiplier.ports (highIndex index))
    (outerMultiplier (highIndex index)) source zeroWord false false retained disabled
  by_cases first : index.val = 0
  · exact (if_pos first).trans addition
  · have doubled := operandDoubling_clean_canonical saved source zeroWord zeroWord_canonical
      false false retained
    rw [doubledWord_zero] at doubled
    exact (if_neg first).trans ((congrArg
      (stepList (stageGates saved (multiplier.ports (highIndex index)) outer
        (outerMultiplier (highIndex index)))) doubled).trans addition)

private lemma stepList_fixed {Data : Type} (steps : List (Data → Data)) (state : Data)
    (fixed : ∀ step ∈ steps, step state = state) :
    UnitaryCircuit.Realizes.stepList steps state = state := by
  induction steps with
  | nil => rfl
  | cons first rest ih =>
      change UnitaryCircuit.Realizes.stepList rest (first state) = state
      rw [fixed first (List.mem_cons_self)]
      exact ih (fun step present => fixed step (List.mem_cons_of_mem first present))

/-- The complete actual raw schedule is identity on every inactive clean-target label. -/
lemma clean_inactive (source : Word) (retained : Saved)
    (disabled : outer.get retained = false) :
    cleanStep saved multiplier outer outerMultiplier
        ((((source, zeroWord), false), (false, false)), retained) =
      ((((source, zeroWord), false), (false, false)), retained) := by
  apply stepList_fixed
  intro step present
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  exact cleanRound_inactive saved multiplier outer outerMultiplier source retained disabled index

/-- Full native ket equality retains arbitrary source and multiplier values with exact phase. -/
lemma cleanProgram_inactive (environment : OracleModel.empty.Interpretation)
    (source : Word) (retained : Saved) (disabled : outer.get retained = false) :
    (cleanProgram saved multiplier outer outerMultiplier).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((operandEncoding saved).encode
            ((((source, zeroWord), false), (false, false)), retained)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((operandEncoding saved).encode
          ((((source, zeroWord), false), (false, false)), retained))) :=
  ((clean_realizes saved multiplier outer outerMultiplier environment).apply_encoded_ket _).trans
    (congrArg (fun state => NormalizedVector.ket
      ((QubitLayout.canonical _).basisEquiv.symm ((operandEncoding saved).encode state)))
        (clean_inactive saved multiplier outer outerMultiplier source retained disabled))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner
