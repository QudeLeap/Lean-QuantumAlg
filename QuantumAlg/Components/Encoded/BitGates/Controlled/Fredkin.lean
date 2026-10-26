/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.SwapLaws

/-!
# A one-Toffoli controlled exchange on arbitrary encoded inputs

Conjugating one Toffoli by two CNOTs exchanges the targets exactly when the
control is set. No target or control is required to be initially zero. This
native decomposition and its counts are project derivations for the source's
location-controlled exchange [LYL+26, sec_EEA/sub_opt.tex:18-19,52-59].
-/

namespace QuantumAlg.EncodedBit

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- One Toffoli and two CNOTs, with their complete actual physical supports. -/
def fredkinGates (control left right : EncodedBit encoding)
    (cl : control.wire ≠ left.wire) (cr : control.wire ≠ right.wire)
    (lr : left.wire ≠ right.wire) : List (GateSpec encoding) :=
  [.cnot left right lr, .toffoli control right left cr cl lr.symm, .cnot left right lr]

/-- The exact conditional exchange acts on every complete input label. -/
lemma fredkin_step_eq_if (control left right : EncodedBit encoding)
    (cl : control.wire ≠ left.wire) (cr : control.wire ≠ right.wire)
    (lr : left.wire ≠ right.wire) (state : Data) :
    GateSpec.stepList (fredkinGates control left right cl cr lr) state =
      if control.get state then swapStep left right lr state else state := by
  simp only [fredkinGates, swapStep, swapGates, GateSpec.stepList, GateSpec.step, id_eq]
  cases hc : control.get state <;> cases hl : left.get state <;> cases hr : right.get state <;>
    simp [cnotStep, toffoliStep, hc, hl, hr, get_flip_self,
      get_flip_of_wire_ne right control cr.symm, get_flip_of_wire_ne right left lr.symm,
      flip_flip, flip_comm]

/-- The new native word retains the full action of the original controlled swap. -/
lemma fredkin_step_eq_controlledSwap (control left right : EncodedBit encoding)
    (cl : control.wire ≠ left.wire) (cr : control.wire ≠ right.wire)
    (lr : left.wire ≠ right.wire) (state : Data) :
    GateSpec.stepList (fredkinGates control left right cl cr lr) state =
      controlledSwapStep control left right cl cr lr state := by
  rw [fredkin_step_eq_if, controlledSwapStep_eq_if]

/-- Place the three actual elementary gates without allocating any additional wire. -/
def fredkinProgram (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (control left right : EncodedBit encoding)
    (cl : control.wire ≠ left.wire) (cr : control.wire ≠ right.wire)
    (lr : left.wire ≠ right.wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles (fredkinGates control left right cl cr lr)

/-- Exact amplitudes retain the conditional swap and all surrounding correlations. -/
lemma fredkin_realizes (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (control left right : EncodedBit encoding)
    (cl : control.wire ≠ left.wire) (cr : control.wire ≠ right.wire)
    (lr : left.wire ≠ right.wire) (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding (fredkinProgram physical oracles control left right cl cr lr)
      environment
      (fun state => if control.get state then swapStep left right lr state else state) :=
  GateSpec.realizesList_congrStep physical oracles _
    (fredkin_step_eq_if control left right cl cr lr) environment

/-- The gate word has two CNOT occurrences, independently of all input values. -/
lemma fredkin_cnot_count (control left right : EncodedBit encoding)
    (cl : control.wire ≠ left.wire) (cr : control.wire ≠ right.wire)
    (lr : left.wire ≠ right.wire) :
    ((fredkinGates control left right cl cr lr).map GateSpec.cnotMultiplicity).sum = 2 := by
  simp [fredkinGates, GateSpec.cnotMultiplicity]

/-- Exactly one Toffoli is executed on both control branches. -/
lemma fredkin_toffoli_count (control left right : EncodedBit encoding)
    (cl : control.wire ≠ left.wire) (cr : control.wire ≠ right.wire)
    (lr : left.wire ≠ right.wire) :
    ((fredkinGates control left right cl cr lr).map GateSpec.toffoliMultiplicity).sum = 1 := by
  simp [fredkinGates, GateSpec.toffoliMultiplicity]

/-- The single native exchange has three sequential elementary dependencies. -/
lemma fredkin_unitDepth (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (control left right : EncodedBit encoding)
    (cl : control.wire ≠ left.wire) (cr : control.wire ≠ right.wire)
    (lr : left.wire ≠ right.wire) :
    (fredkinProgram physical oracles control left right cl cr lr).evaluatedEventDepth
      (fun _ => 1) = 3 := by
  rw [fredkinProgram, GateSpec.programList_evaluatedEventDepth_unit]
  rfl

end

end QuantumAlg.EncodedBit
