/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Seeded.Posterior
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Circuit
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Extraction
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Seeded
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Carrier
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Layout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.ParameterLayout
import all QuantumAlg.Primitives.ShortDLP.BornProbability.Distribution
import all QuantumAlg.Primitives.ShortDLP.Layout
import all QuantumAlg.Primitives.ShortDLP.Measurement
import all QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Core.Measure.Distribution

/-!
# Born identification of the actual seeded branch weight

The actual compiled column is summed over its complete physical measurement
fiber. On the original arithmetic domain, all workspace rows outside the
clean unit image vanish, and injectivity gives the same sum over units.
The final probability is the existing compiled outcome PMF, followed by its
proved equality with the ideal source PMF. The complete partner/reference
posterior remains the matrix in SeededPosterior; only an explicitly stated
partial trace has this scalar coefficient. These mathematical frequency
labels do not implement or replace the paid output packing instruction.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.SeededBorn

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (m ell width : Nat) (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val]

/-- The original terminal readout label for the unchanged pair of full frequencies. -/
def sourceOutcome (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    ShortDLP.Outcome (registerParameters m ell width) :=
  BornProbability.shortDLPMeasurementOutcome (registerParameters m ell width)
    (prodEquiv (first, second))

omit [NeZero modulus.val] in
/-- The existing evolved state is precisely the actual compiled unit-one input column. -/
lemma compiled_seed_column (generator target : (ZMod modulus.val)ˣ)
    (output : Fin (2 ^ totalQubits (registerParameters m ell width))) :
    (CompiledMAU.evolvedState m ell width modulus.val generator target).normalized output =
      ((compiledCircuit m ell width modulus.val generator target).binaryMatrix environment) output
        (cleanLabel m ell width modulus.val 0 0 1) := by
  cases Subsingleton.elim environment OracleModel.emptyInterpretation
  exact HilbertOperator.applyVec_ket
    (((compiledCircuit m ell width modulus.val generator target).binaryMatrix
      OracleModel.emptyInterpretation) :
      HilbertOperator (Qubits (totalQubits (registerParameters m ell width))))
    (tripleIndex (registerParameters m ell width) 0 0 (cleanUnitLabel width modulus.val 1))
    output

/-- Clean branch rows are entries of that same actual evolved vector. -/
lemma actualKraus_seed_entry (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell))
    (value : (Carrier.units modulus.val).Index) :
    FullWordCircuit.actualKraus (environment := environment) m ell width modulus generator target
      first second value 1 =
      (CompiledMAU.evolvedState m ell width modulus.val generator target).normalized
        (cleanLabel m ell width modulus.val first second value) :=
  (compiled_seed_column m ell width modulus generator target
    (cleanLabel m ell width modulus.val first second value)).symm

omit [NeZero modulus.val] in
/-- The complete physical workspace fiber gives the original compiled Born weight. -/
lemma compiled_probability_workspace (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    (∑ workspace : Fin (2 ^ workspaceBits width),
      ‖(CompiledMAU.evolvedState m ell width modulus.val generator target).normalized
        (tripleIndex (registerParameters m ell width) first second workspace)‖ ^ 2) =
      ((ShortDLP.measurement (registerParameters m ell width)).outcomePMF
        (CompiledMAU.evolvedState m ell width modulus.val generator target)
        (sourceOutcome m ell width first second)).toReal := by
  symm
  rw [TerminalZMeasure.outcomePMF_apply, sourceOutcome,
    BornProbability.shortDLPMeasurement_fiber, Finset.sum_map,
    ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro workspace _
  rw [ENNReal.toReal_ofReal (sq_nonneg _)]
  rfl

private lemma clean_workspace_sum
    (nontrivial : 1 < modulus.val) (fits : modulus.val < 2 ^ width)
    (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    (∑ value : (Carrier.units modulus.val).Index,
      ‖(CompiledMAU.evolvedState m ell width modulus.val generator target).normalized
        (tripleIndex (registerParameters m ell width) first second
          (cleanUnitLabel width modulus.val value))‖ ^ 2) =
      ∑ workspace : Fin (2 ^ workspaceBits width),
        ‖(CompiledMAU.evolvedState m ell width modulus.val generator target).normalized
          (tripleIndex (registerParameters m ell width) first second workspace)‖ ^ 2 := by
  let weight (workspace : Fin (2 ^ workspaceBits width)) : ℝ :=
    ‖(CompiledMAU.evolvedState m ell width modulus.val generator target).normalized
      (tripleIndex (registerParameters m ell width) first second workspace)‖ ^ 2
  change (∑ value : (Carrier.units modulus.val).Index,
    weight (cleanUnitLabel width modulus.val value)) = ∑ workspace, weight workspace
  calc
    _ = ∑ workspace ∈ Finset.univ.image (cleanUnitLabel width modulus.val),
        weight workspace :=
      (Finset.sum_image (cleanUnitLabel_injective width modulus.val nontrivial fits).injOn).symm
    _ = ∑ workspace, weight workspace := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro workspace _ absent
      have outside : workspace ∉ Set.range (cleanUnitLabel width modulus.val) := by
        rintro ⟨value, same⟩
        exact absent (Finset.mem_image.mpr ⟨value, Finset.mem_univ _, same⟩)
      have zero := FullWordExtraction.compiled_outside_clean
        (environment := OracleModel.emptyInterpretation) m ell width modulus
        nontrivial fits generator target first second workspace 1 outside
      dsimp only [weight]
      rw [compiled_seed_column (environment := OracleModel.emptyInterpretation) m ell width modulus
        generator target, zero]
      simp only [norm_zero, zero_pow (by decide : 2 ≠ 0)]

/-- The actual unit-one branch norm is the original compiled circuit's outcome probability. -/
lemma branchWeight_eq_compiled
    (nontrivial : 1 < modulus.val) (fits : modulus.val < 2 ^ width)
    (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    SeededPosterior.branchWeight (environment := environment) m ell width modulus generator target
      first second =
      ((ShortDLP.measurement (registerParameters m ell width)).outcomePMF
        (CompiledMAU.evolvedState m ell width modulus.val generator target)
        (sourceOutcome m ell width first second)).toReal := by
  unfold SeededPosterior.branchWeight
  simp_rw [actualKraus_seed_entry m ell width modulus generator target,
    cleanLabel_eq_tripleIndex]
  exact (clean_workspace_sum m ell width modulus nontrivial fits generator target
    first second).trans
      (compiled_probability_workspace m ell width modulus generator target first second)

/-- The same branch weight agrees with the original ideal Born PMF on its arithmetic domain. -/
lemma branchWeight_eq_ideal
    (nontrivial : 1 < modulus.val) (fits : modulus.val < 2 ^ width)
    (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    SeededPosterior.branchWeight (environment := environment) m ell width modulus generator target
      first second =
      ((ShortDLP.measurement (registerParameters m ell width)).outcomePMF
        (BornProbability.evolvedState (unitEncoding width modulus.val nontrivial fits)
          generator target) (sourceOutcome m ell width first second)).toReal :=
  (branchWeight_eq_compiled m ell width modulus nontrivial fits generator target
    first second).trans
      (congrArg (fun distribution => (distribution (sourceOutcome m ell width first second)).toReal)
        (CompiledMAU.outcomePMF_eq_ideal m ell width modulus.val generator target nontrivial fits))

/-- Contracting only the partner retains the actual Store density and both reference indices. -/
lemma actualSigma_reference_eq_compiled {ctx : RuntimeCtx .quantum}
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (original : Store ctx)
    (nontrivial : 1 < modulus.val) (fits : modulus.val < 2 ^ width)
    (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell))
    (leftRef rightRef : Reference.Index) :
    (∑ value : (Carrier.units modulus.val).Index,
      FullWordCircuit.actualSigma (environment := environment) m ell width modulus generator target
        first second Reference
        (FullWordSeeded.seedDensity width modulus state original).matrix
          (value, leftRef) (value, rightRef)) =
      (((ShortDLP.measurement (registerParameters m ell width)).outcomePMF
          (CompiledMAU.evolvedState m ell width modulus.val generator target)
          (sourceOutcome m ell width first second)).toReal : ℂ) *
        (state.filterClassical (fun entry => entry.1 = original)).referenceMarginal.matrix
          leftRef rightRef := by
  rw [SeededPosterior.actualSigma_reference_entry,
    branchWeight_eq_compiled m ell width modulus nontrivial fits]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.SeededBorn
