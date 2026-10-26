/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Complement
import all QuantumAlg.Components.Encoded.BitGates.Parallel
import Mathlib.Data.List.OfFn

/-!
# Actual parallel complement of the borrowed HRS word

The original one-X-per-bit word executes on disjoint physical targets. It keeps
the complete complement action required by [HRS16, paper.tex:219-224].
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

open EncodedBit.GateSpec

/-- Distinct borrowed bits remain disjoint after the actual physical placement. -/
lemma hrsComplement_independent (n : Nat) (physical : QubitLayout (TTK.encoding n).width) :
    (complementGates n).Pairwise (fun first second =>
      Disjoint (physicalSupport physical first) (physicalSupport physical second)) := by
  rw [complementGates, List.pairwise_ofFn]
  intro i j before
  rw [physicalSupport_x, physicalSupport_x, Finset.disjoint_singleton]
  exact TTK.ttkLeftLeft_disjoint n i j (ne_of_lt before)

/-- One real parallel X layer on the original borrowed word, without new systems. -/
def parallelComplementProgram (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (TTK.encoding n).width).toQuantum :=
  parallelProgramList (QubitLayout.canonical _) .empty (complementGates n)
    (hrsComplement_independent n (QubitLayout.canonical _))

/-- Parallel complement retains each source X event in its original traversal order. -/
lemma hrsParallelComplement_eventTrace (n : Nat) :
    (parallelComplementProgram n).eventTrace = (complementProgram n).eventTrace :=
  parallelProgramList_eventTrace _ _ _ _

/-- The full actual operator retains the same finite word complement and relative phases. -/
lemma hrsParallelComplement_realizes (n : Nat)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (TTK.encoding n) (parallelComplementProgram n) environment
      complementOutput :=
  (parallelProgramList_realizes _ _ _ _ environment).congrStep (hrsComplement_step n)

/-- Every nonempty borrowed word is complemented in one real native layer. -/
lemma hrsParallelComplement_unitDepth (n : Nat) :
    (parallelComplementProgram n).evaluatedEventDepth (fun _ => 1) =
      if n = 0 then 0 else 1 := by
  rw [parallelComplementProgram, parallelProgramList_unitDepth]
  simp only [complementGates, List.ofFn_eq_nil_iff]

end

end QuantumAlg.MAU.Addition.HRS
