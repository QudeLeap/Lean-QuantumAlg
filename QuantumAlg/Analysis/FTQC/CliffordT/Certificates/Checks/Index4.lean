/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic
public import QuantumAlg.Analysis.FTQC.CliffordT.CertificateData

/-!
# Kernel verification of synthesized rotation candidates

Generated accumulator checkpoints split long word reductions into eight-letter steps.
Each step and the final rational error bound are proved by kernel computation.
The final theorem rewrites the original checker, retaining its semantic soundness.
-/

section

namespace QuantumAlg.CliffordT
private def word4Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word4State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word4Step0 :
    word4Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word4State1 := by decide +kernel

private def word4Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word4State2 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word4Step1 :
    word4Chunk1.foldl (fun acc a => a.applyPacked acc)
      word4State1 = word4State2 := by decide +kernel

private def word4Chunk2 : List Letter := [.h, .s, .s, .s, .s, .h, .t, .h]
private def word4State3 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word4Step2 :
    word4Chunk2.foldl (fun acc a => a.applyPacked acc)
      word4State2 = word4State3 := by decide +kernel

private def word4Chunk3 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word4State4 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word4Step3 :
    word4Chunk3.foldl (fun acc a => a.applyPacked acc)
      word4State3 = word4State4 := by decide +kernel

private def word4Chunk4 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word4State5 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word4Step4 :
    word4Chunk4.foldl (fun acc a => a.applyPacked acc)
      word4State4 = word4State5 := by decide +kernel

private def word4Chunk5 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word4State6 : PackedMat2 :=
    ⟨⟨⟨((-5 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((-7 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-9 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((-5 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((9 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word4Step5 :
    word4Chunk5.foldl (fun acc a => a.applyPacked acc)
      word4State5 = word4State6 := by decide +kernel

private def word4Chunk6 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word4State7 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((-5 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word4Step6 :
    word4Chunk6.foldl (fun acc a => a.applyPacked acc)
      word4State6 = word4State7 := by decide +kernel

private def word4Chunk7 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word4State8 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 5),
        ((9 : Dyadic) * half ^ 5)⟩,
       ⟨((-3 : Dyadic) * half ^ 5),
        ((11 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((-23 : Dyadic) * half ^ 5),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 4),
        ((11 : Dyadic) * half ^ 5)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 5)⟩,
       ⟨((5 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩⟩
private lemma word4Step7 :
    word4Chunk7.foldl (fun acc a => a.applyPacked acc)
      word4State7 = word4State8 := by decide +kernel

private def word4Chunk8 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word4State9 : PackedMat2 :=
    ⟨⟨⟨((-35 : Dyadic) * half ^ 6),
        ((19 : Dyadic) * half ^ 6)⟩,
       ⟨((23 : Dyadic) * half ^ 6),
        ((23 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-19 : Dyadic) * half ^ 6),
        ((-3 : Dyadic) * half ^ 5)⟩,
       ⟨((11 : Dyadic) * half ^ 6),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((19 : Dyadic) * half ^ 6),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((11 : Dyadic) * half ^ 6),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-35 : Dyadic) * half ^ 6),
        ((19 : Dyadic) * half ^ 6)⟩,
       ⟨((-23 : Dyadic) * half ^ 6),
        ((-23 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word4Step8 :
    word4Chunk8.foldl (fun acc a => a.applyPacked acc)
      word4State8 = word4State9 := by decide +kernel

private def word4Chunk9 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word4State10 : PackedMat2 :=
    ⟨⟨⟨((23 : Dyadic) * half ^ 7),
        ((-43 : Dyadic) * half ^ 7)⟩,
       ⟨((7 : Dyadic) * half ^ 7),
        ((19 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-27 : Dyadic) * half ^ 7),
        ((-25 : Dyadic) * half ^ 6)⟩,
       ⟨((-57 : Dyadic) * half ^ 7),
        ((11 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-61 : Dyadic) * half ^ 7),
        ((15 : Dyadic) * half ^ 7)⟩,
       ⟨((39 : Dyadic) * half ^ 7),
        ((21 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((81 : Dyadic) * half ^ 7),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-5 : Dyadic) * half ^ 7),
        ((15 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word4Step9 :
    word4Chunk9.foldl (fun acc a => a.applyPacked acc)
      word4State9 = word4State10 := by decide +kernel

private def word4Chunk10 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word4State11 : PackedMat2 :=
    ⟨⟨⟨((-9 : Dyadic) * half ^ 6),
        ((-13 : Dyadic) * half ^ 7)⟩,
       ⟨((63 : Dyadic) * half ^ 7),
        ((7 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-9 : Dyadic) * half ^ 6),
        (0 : Dyadic)⟩,
       ⟨((9 : Dyadic) * half ^ 7),
        ((-75 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 7),
        ((-75 : Dyadic) * half ^ 7)⟩,
       ⟨((-9 : Dyadic) * half ^ 6),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-63 : Dyadic) * half ^ 7),
        ((-7 : Dyadic) * half ^ 7)⟩,
       ⟨((9 : Dyadic) * half ^ 6),
        ((13 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word4Step10 :
    word4Chunk10.foldl (fun acc a => a.applyPacked acc)
      word4State10 = word4State11 := by decide +kernel

private def word4Chunk11 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word4State12 : PackedMat2 :=
    ⟨⟨⟨((-7 : Dyadic) * half ^ 7),
        ((-77 : Dyadic) * half ^ 9)⟩,
       ⟨((71 : Dyadic) * half ^ 8),
        ((109 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((11 : Dyadic) * half ^ 8),
        ((195 : Dyadic) * half ^ 9)⟩,
       ⟨((-87 : Dyadic) * half ^ 7),
        ((63 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-11 : Dyadic) * half ^ 8),
        ((-195 : Dyadic) * half ^ 9)⟩,
       ⟨((-87 : Dyadic) * half ^ 7),
        ((63 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 7),
        ((-77 : Dyadic) * half ^ 9)⟩,
       ⟨((-71 : Dyadic) * half ^ 8),
        ((-109 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word4Step11 :
    word4Chunk11.foldl (fun acc a => a.applyPacked acc)
      word4State11 = word4State12 := by decide +kernel

private def word4Chunk12 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word4State13 : PackedMat2 :=
    ⟨⟨⟨((13 : Dyadic) * half ^ 9),
        ((-205 : Dyadic) * half ^ 10)⟩,
       ⟨((-45 : Dyadic) * half ^ 6),
        ((65 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-11 : Dyadic) * half ^ 7),
        ((313 : Dyadic) * half ^ 10)⟩,
       ⟨((-147 : Dyadic) * half ^ 9),
        ((-271 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((21 : Dyadic) * half ^ 9),
        ((-191 : Dyadic) * half ^ 10)⟩,
       ⟨((73 : Dyadic) * half ^ 7),
        ((103 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((35 : Dyadic) * half ^ 8),
        ((347 : Dyadic) * half ^ 10)⟩,
       ⟨((135 : Dyadic) * half ^ 9),
        ((-373 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word4Step12 :
    word4Chunk12.foldl (fun acc a => a.applyPacked acc)
      word4State12 = word4State13 := by decide +kernel

private def word4Chunk13 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word4State14 : PackedMat2 :=
    ⟨⟨⟨((111 : Dyadic) * half ^ 10),
        ((137 : Dyadic) * half ^ 10)⟩,
       ⟨((225 : Dyadic) * half ^ 10),
        ((-327 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((447 : Dyadic) * half ^ 10),
        ((97 : Dyadic) * half ^ 9)⟩,
       ⟨((-675 : Dyadic) * half ^ 10),
        ((21 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-447 : Dyadic) * half ^ 10),
        ((-97 : Dyadic) * half ^ 9)⟩,
       ⟨((-675 : Dyadic) * half ^ 10),
        ((21 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((111 : Dyadic) * half ^ 10),
        ((137 : Dyadic) * half ^ 10)⟩,
       ⟨((-225 : Dyadic) * half ^ 10),
        ((327 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word4Step13 :
    word4Chunk13.foldl (fun acc a => a.applyPacked acc)
      word4State13 = word4State14 := by decide +kernel

private def word4Chunk14 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word4State15 : PackedMat2 :=
    ⟨⟨⟨((143 : Dyadic) * half ^ 11),
        ((413 : Dyadic) * half ^ 10)⟩,
       ⟨((547 : Dyadic) * half ^ 11),
        ((-175 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((1247 : Dyadic) * half ^ 11),
        ((-99 : Dyadic) * half ^ 11)⟩,
       ⟨((-155 : Dyadic) * half ^ 11),
        ((-163 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((553 : Dyadic) * half ^ 11),
        ((701 : Dyadic) * half ^ 11)⟩,
       ⟨((751 : Dyadic) * half ^ 11),
        ((-273 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-1001 : Dyadic) * half ^ 11),
        ((101 : Dyadic) * half ^ 10)⟩,
       ⟨((651 : Dyadic) * half ^ 11),
        ((345 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word4Step14 :
    word4Chunk14.foldl (fun acc a => a.applyPacked acc)
      word4State14 = word4State15 := by decide +kernel

private def word4Chunk15 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word4State16 : PackedMat2 :=
    ⟨⟨⟨((27 : Dyadic) * half ^ 7),
        ((-19 : Dyadic) * half ^ 9)⟩,
       ⟨((499 : Dyadic) * half ^ 11),
        ((25 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-385 : Dyadic) * half ^ 10),
        ((827 : Dyadic) * half ^ 11)⟩,
       ⟨((651 : Dyadic) * half ^ 11),
        ((361 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((651 : Dyadic) * half ^ 11),
        ((361 : Dyadic) * half ^ 10)⟩,
       ⟨((-385 : Dyadic) * half ^ 10),
        ((827 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-499 : Dyadic) * half ^ 11),
        ((-25 : Dyadic) * half ^ 7)⟩,
       ⟨((-27 : Dyadic) * half ^ 7),
        ((19 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word4Step15 :
    word4Chunk15.foldl (fun acc a => a.applyPacked acc)
      word4State15 = word4State16 := by decide +kernel

private def word4Chunk16 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word4State17 : PackedMat2 :=
    ⟨⟨⟨((-275 : Dyadic) * half ^ 9),
        ((183 : Dyadic) * half ^ 13)⟩,
       ⟨((1127 : Dyadic) * half ^ 12),
        ((2267 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((1327 : Dyadic) * half ^ 12),
        ((-2053 : Dyadic) * half ^ 13)⟩,
       ⟨((99 : Dyadic) * half ^ 11),
        ((2889 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-209 : Dyadic) * half ^ 11),
        ((-1525 : Dyadic) * half ^ 13)⟩,
       ⟨((2471 : Dyadic) * half ^ 12),
        ((-1129 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((1225 : Dyadic) * half ^ 12),
        ((-1073 : Dyadic) * half ^ 13)⟩,
       ⟨((-521 : Dyadic) * half ^ 11),
        ((-3327 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word4Step16 :
    word4Chunk16.foldl (fun acc a => a.applyPacked acc)
      word4State16 = word4State17 := by decide +kernel

private def word4Chunk17 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word4State18 : PackedMat2 :=
    ⟨⟨⟨((-2271 : Dyadic) * half ^ 13),
        ((-2307 : Dyadic) * half ^ 13)⟩,
       ⟨((265 : Dyadic) * half ^ 13),
        ((2663 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-4451 : Dyadic) * half ^ 13),
        ((-13 : Dyadic) * half ^ 12)⟩,
       ⟨((3089 : Dyadic) * half ^ 13),
        ((-981 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-4451 : Dyadic) * half ^ 13),
        ((-13 : Dyadic) * half ^ 12)⟩,
       ⟨((-3089 : Dyadic) * half ^ 13),
        ((981 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((2271 : Dyadic) * half ^ 13),
        ((2307 : Dyadic) * half ^ 13)⟩,
       ⟨((265 : Dyadic) * half ^ 13),
        ((2663 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word4Step17 :
    word4Chunk17.foldl (fun acc a => a.applyPacked acc)
      word4State17 = word4State18 := by decide +kernel

private def word4Chunk18 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word4State19 : PackedMat2 :=
    ⟨⟨⟨((-6867 : Dyadic) * half ^ 14),
        ((-5615 : Dyadic) * half ^ 14)⟩,
       ⟨((4991 : Dyadic) * half ^ 14),
        ((-1453 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-3497 : Dyadic) * half ^ 14),
        ((-743 : Dyadic) * half ^ 13)⟩,
       ⟨((-3405 : Dyadic) * half ^ 14),
        ((4331 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((5817 : Dyadic) * half ^ 14),
        ((23 : Dyadic) * half ^ 13)⟩,
       ⟨((2845 : Dyadic) * half ^ 14),
        ((-3451 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((197 : Dyadic) * half ^ 14),
        ((-5929 : Dyadic) * half ^ 14)⟩,
       ⟨((11427 : Dyadic) * half ^ 14),
        ((469 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word4Step18 :
    word4Chunk18.foldl (fun acc a => a.applyPacked acc)
      word4State18 = word4State19 := by decide +kernel

private def word4Chunk19 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word4State20 : PackedMat2 :=
    ⟨⟨⟨((-13065 : Dyadic) * half ^ 14),
        ((1355 : Dyadic) * half ^ 14)⟩,
       ⟨((117 : Dyadic) * half ^ 10),
        ((-1363 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-4337 : Dyadic) * half ^ 14),
        ((-5103 : Dyadic) * half ^ 14)⟩,
       ⟨((-111 : Dyadic) * half ^ 12),
        ((-1519 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((3311 : Dyadic) * half ^ 13),
        ((4781 : Dyadic) * half ^ 15)⟩,
       ⟨((7 : Dyadic) * half ^ 5),
        ((3893 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-1371 : Dyadic) * half ^ 14),
        ((-11193 : Dyadic) * half ^ 15)⟩,
       ⟨((4081 : Dyadic) * half ^ 14),
        ((-14937 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word4Step19 :
    word4Chunk19.foldl (fun acc a => a.applyPacked acc)
      word4State19 = word4State20 := by decide +kernel

private def word4Chunk20 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word4State21 : PackedMat2 :=
    ⟨⟨⟨((-723 : Dyadic) * half ^ 12),
        ((-25459 : Dyadic) * half ^ 16)⟩,
       ⟨((-22101 : Dyadic) * half ^ 15),
        ((2561 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-8391 : Dyadic) * half ^ 15),
        ((5557 : Dyadic) * half ^ 16)⟩,
       ⟨((-179 : Dyadic) * half ^ 9),
        ((3843 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-8391 : Dyadic) * half ^ 15),
        ((5557 : Dyadic) * half ^ 16)⟩,
       ⟨((179 : Dyadic) * half ^ 9),
        ((-3843 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((723 : Dyadic) * half ^ 12),
        ((25459 : Dyadic) * half ^ 16)⟩,
       ⟨((-22101 : Dyadic) * half ^ 15),
        ((2561 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word4Step20 :
    word4Chunk20.foldl (fun acc a => a.applyPacked acc)
      word4State20 = word4State21 := by decide +kernel

private def word4Chunk21 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word4State22 : PackedMat2 :=
    ⟨⟨⟨((-247 : Dyadic) * half ^ 9),
        ((9453 : Dyadic) * half ^ 17)⟩,
       ⟨((-5121 : Dyadic) * half ^ 16),
        ((-3151 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((6601 : Dyadic) * half ^ 16),
        ((75165 : Dyadic) * half ^ 17)⟩,
       ⟨((-4071 : Dyadic) * half ^ 14),
        ((13107 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-5517 : Dyadic) * half ^ 13),
        ((9683 : Dyadic) * half ^ 17)⟩,
       ⟨((-31029 : Dyadic) * half ^ 16),
        ((-22885 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((3151 : Dyadic) * half ^ 16),
        ((-36737 : Dyadic) * half ^ 17)⟩,
       ⟨((3151 : Dyadic) * half ^ 15),
        ((-26495 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word4Step21 :
    word4Chunk21.foldl (fun acc a => a.applyPacked acc)
      word4State21 = word4State22 := by decide +kernel

private def word4Chunk22 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word4State23 : PackedMat2 :=
    ⟨⟨⟨((-855 : Dyadic) * half ^ 16),
        ((-23487 : Dyadic) * half ^ 17)⟩,
       ⟨((-14083 : Dyadic) * half ^ 16),
        ((9297 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((48285 : Dyadic) * half ^ 16),
        ((1623 : Dyadic) * half ^ 17)⟩,
       ⟨((12831 : Dyadic) * half ^ 15),
        ((4143 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((48285 : Dyadic) * half ^ 16),
        ((1623 : Dyadic) * half ^ 17)⟩,
       ⟨((-12831 : Dyadic) * half ^ 15),
        ((-4143 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((855 : Dyadic) * half ^ 16),
        ((23487 : Dyadic) * half ^ 17)⟩,
       ⟨((-14083 : Dyadic) * half ^ 16),
        ((9297 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word4Step22 :
    word4Chunk22.foldl (fun acc a => a.applyPacked acc)
      word4State22 = word4State23 := by decide +kernel

private def word4Chunk23 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word4State24 : PackedMat2 :=
    ⟨⟨⟨((-37003 : Dyadic) * half ^ 18),
        ((-112845 : Dyadic) * half ^ 18)⟩,
       ⟨((87615 : Dyadic) * half ^ 18),
        ((-18569 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-34377 : Dyadic) * half ^ 18),
        ((16265 : Dyadic) * half ^ 16)⟩,
       ⟨((69039 : Dyadic) * half ^ 18),
        ((66175 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((1115 : Dyadic) * half ^ 18),
        ((12927 : Dyadic) * half ^ 16)⟩,
       ⟨((131235 : Dyadic) * half ^ 18),
        ((17331 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-38569 : Dyadic) * half ^ 18),
        ((-62309 : Dyadic) * half ^ 18)⟩,
       ⟨((187121 : Dyadic) * half ^ 18),
        ((-12653 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word4Step23 :
    word4Chunk23.foldl (fun acc a => a.applyPacked acc)
      word4State23 = word4State24 := by decide +kernel

private def word4Chunk24 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word4State25 : PackedMat2 :=
    ⟨⟨⟨((-221487 : Dyadic) * half ^ 18),
        ((-15297 : Dyadic) * half ^ 18)⟩,
       ⟨((11287 : Dyadic) * half ^ 16),
        ((-4569 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-79651 : Dyadic) * half ^ 18),
        ((20761 : Dyadic) * half ^ 18)⟩,
       ⟨((-349 : Dyadic) * half ^ 16),
        ((60317 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-40539 : Dyadic) * half ^ 17),
        ((81047 : Dyadic) * half ^ 19)⟩,
       ⟨((9889 : Dyadic) * half ^ 16),
        ((78255 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-51849 : Dyadic) * half ^ 18),
        ((-176339 : Dyadic) * half ^ 19)⟩,
       ⟨((21255 : Dyadic) * half ^ 18),
        ((-266635 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word4Step24 :
    word4Chunk24.foldl (fun acc a => a.applyPacked acc)
      word4State24 = word4State25 := by decide +kernel

private def word4Chunk25 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word4State26 : PackedMat2 :=
    ⟨⟨⟨((277245 : Dyadic) * half ^ 19),
        ((-204459 : Dyadic) * half ^ 20)⟩,
       ⟨((-39985 : Dyadic) * half ^ 16),
        ((-13195 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-44999 : Dyadic) * half ^ 17),
        ((-271005 : Dyadic) * half ^ 20)⟩,
       ⟨((-42325 : Dyadic) * half ^ 19),
        ((-87055 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-44999 : Dyadic) * half ^ 17),
        ((-271005 : Dyadic) * half ^ 20)⟩,
       ⟨((42325 : Dyadic) * half ^ 19),
        ((87055 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-277245 : Dyadic) * half ^ 19),
        ((204459 : Dyadic) * half ^ 20)⟩,
       ⟨((-39985 : Dyadic) * half ^ 16),
        ((-13195 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word4Step25 :
    word4Chunk25.foldl (fun acc a => a.applyPacked acc)
      word4State25 = word4State26 := by decide +kernel

private def word4Chunk26 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word4State27 : PackedMat2 :=
    ⟨⟨⟨((295417 : Dyadic) * half ^ 20),
        ((419345 : Dyadic) * half ^ 20)⟩,
       ⟨((221725 : Dyadic) * half ^ 20),
        ((-465637 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((48565 : Dyadic) * half ^ 20),
        ((-119349 : Dyadic) * half ^ 19)⟩,
       ⟨((52829 : Dyadic) * half ^ 20),
        ((-85615 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((16867 : Dyadic) * half ^ 18),
        ((533 : Dyadic) * half ^ 18)⟩,
       ⟨((-51241 : Dyadic) * half ^ 17),
        ((50697 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((442491 : Dyadic) * half ^ 19),
        ((18423 : Dyadic) * half ^ 19)⟩,
       ⟨((11573 : Dyadic) * half ^ 18),
        ((-258571 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word4Step26 :
    word4Chunk26.foldl (fun acc a => a.applyPacked acc)
      word4State26 = word4State27 := by decide +kernel

private def word4Chunk27 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word4State28 : PackedMat2 :=
    ⟨⟨⟨((420669 : Dyadic) * half ^ 21),
        ((-22023 : Dyadic) * half ^ 19)⟩,
       ⟨((75965 : Dyadic) * half ^ 21),
        ((904855 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-390587 : Dyadic) * half ^ 21),
        ((873433 : Dyadic) * half ^ 21)⟩,
       ⟨((-709609 : Dyadic) * half ^ 21),
        ((-109029 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((1309549 : Dyadic) * half ^ 21),
        ((159511 : Dyadic) * half ^ 21)⟩,
       ⟨((-437317 : Dyadic) * half ^ 21),
        ((275049 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((992947 : Dyadic) * half ^ 21),
        ((-2693 : Dyadic) * half ^ 15)⟩,
       ⟨((816763 : Dyadic) * half ^ 21),
        ((248317 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word4Step27 :
    word4Chunk27.foldl (fun acc a => a.applyPacked acc)
      word4State27 = word4State28 := by decide +kernel

private def word4Chunk28 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word4State29 : PackedMat2 :=
    ⟨⟨⟨((-616541 : Dyadic) * half ^ 22),
        ((125279 : Dyadic) * half ^ 19)⟩,
       ⟨((1542533 : Dyadic) * half ^ 22),
        ((1091271 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((1111307 : Dyadic) * half ^ 22),
        ((1019113 : Dyadic) * half ^ 22)⟩,
       ⟨((2304411 : Dyadic) * half ^ 22),
        ((-476901 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-1972915 : Dyadic) * half ^ 22),
        ((74569 : Dyadic) * half ^ 19)⟩,
       ⟨((65311 : Dyadic) * half ^ 22),
        ((1707859 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-89039 : Dyadic) * half ^ 22),
        ((-1079537 : Dyadic) * half ^ 22)⟩,
       ⟨((-2093503 : Dyadic) * half ^ 22),
        ((-115749 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word4Step28 :
    word4Chunk28.foldl (fun acc a => a.applyPacked acc)
      word4State28 = word4State29 := by decide +kernel

private def word4Chunk29 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word4State30 : PackedMat2 :=
    ⟨⟨⟨((-115155 : Dyadic) * half ^ 19),
        ((-377005 : Dyadic) * half ^ 22)⟩,
       ⟨((227347 : Dyadic) * half ^ 22),
        ((381413 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((319087 : Dyadic) * half ^ 21),
        ((789095 : Dyadic) * half ^ 21)⟩,
       ⟨((-706419 : Dyadic) * half ^ 22),
        ((1081439 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((706419 : Dyadic) * half ^ 22),
        ((-1081439 : Dyadic) * half ^ 21)⟩,
       ⟨((-319087 : Dyadic) * half ^ 21),
        ((-789095 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((227347 : Dyadic) * half ^ 22),
        ((381413 : Dyadic) * half ^ 21)⟩,
       ⟨((-115155 : Dyadic) * half ^ 19),
        ((-377005 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word4Step29 :
    word4Chunk29.foldl (fun acc a => a.applyPacked acc)
      word4State29 = word4State30 := by decide +kernel

private def word4Chunk30 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word4State31 : PackedMat2 :=
    ⟨⟨⟨((260481 : Dyadic) * half ^ 23),
        ((-6245985 : Dyadic) * half ^ 24)⟩,
       ⟨((-350235 : Dyadic) * half ^ 21),
        ((-6129935 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-36137 : Dyadic) * half ^ 20),
        ((-4611891 : Dyadic) * half ^ 24)⟩,
       ⟨((4164421 : Dyadic) * half ^ 23),
        ((-1991631 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-3301761 : Dyadic) * half ^ 23),
        ((3875325 : Dyadic) * half ^ 24)⟩,
       ⟨((-655065 : Dyadic) * half ^ 22),
        ((-4453517 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((773495 : Dyadic) * half ^ 20),
        ((1140459 : Dyadic) * half ^ 24)⟩,
       ⟨((58025 : Dyadic) * half ^ 23),
        ((-1661421 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word4Step30 :
    word4Chunk30.foldl (fun acc a => a.applyPacked acc)
      word4State30 = word4State31 := by decide +kernel

private def word4Chunk31 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word4State32 : PackedMat2 :=
    ⟨⟨⟨((-5134141 : Dyadic) * half ^ 24),
        ((1019503 : Dyadic) * half ^ 24)⟩,
       ⟨((-10033875 : Dyadic) * half ^ 24),
        ((-3528117 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-9036793 : Dyadic) * half ^ 24),
        ((239357 : Dyadic) * half ^ 20)⟩,
       ⟨((-3681667 : Dyadic) * half ^ 24),
        ((-301623 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((9036793 : Dyadic) * half ^ 24),
        ((-239357 : Dyadic) * half ^ 20)⟩,
       ⟨((-3681667 : Dyadic) * half ^ 24),
        ((-301623 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-5134141 : Dyadic) * half ^ 24),
        ((1019503 : Dyadic) * half ^ 24)⟩,
       ⟨((10033875 : Dyadic) * half ^ 24),
        ((3528117 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word4Step31 :
    word4Chunk31.foldl (fun acc a => a.applyPacked acc)
      word4State31 = word4State32 := by decide +kernel

private def word4Chunk32 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word4State33 : PackedMat2 :=
    ⟨⟨⟨((7036677 : Dyadic) * half ^ 25),
        ((1071539 : Dyadic) * half ^ 25)⟩,
       ⟨((-9567155 : Dyadic) * half ^ 25),
        ((-7686801 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((15888711 : Dyadic) * half ^ 25),
        ((-2690217 : Dyadic) * half ^ 24)⟩,
       ⟨((-8941163 : Dyadic) * half ^ 25),
        ((7732053 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-13112487 : Dyadic) * half ^ 25),
        ((12414937 : Dyadic) * half ^ 25)⟩,
       ⟨((-2351619 : Dyadic) * half ^ 25),
        ((-1736887 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-16445141 : Dyadic) * half ^ 25),
        ((-2075479 : Dyadic) * half ^ 23)⟩,
       ⟨((-14302063 : Dyadic) * half ^ 25),
        ((-1265239 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word4Step32 :
    word4Chunk32.foldl (fun acc a => a.applyPacked acc)
      word4State32 = word4State33 := by decide +kernel

private def word4Chunk33 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word4State34 : PackedMat2 :=
    ⟨⟨⟨((5162849 : Dyadic) * half ^ 24),
        ((7339113 : Dyadic) * half ^ 25)⟩,
       ⟨((-19799619 : Dyadic) * half ^ 25),
        ((-1557591 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-2846715 : Dyadic) * half ^ 24),
        ((-451059 : Dyadic) * half ^ 22)⟩,
       ⟨((19194747 : Dyadic) * half ^ 25),
        ((-6625029 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((19194747 : Dyadic) * half ^ 25),
        ((-6625029 : Dyadic) * half ^ 25)⟩,
       ⟨((-2846715 : Dyadic) * half ^ 24),
        ((-451059 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((19799619 : Dyadic) * half ^ 25),
        ((1557591 : Dyadic) * half ^ 25)⟩,
       ⟨((-5162849 : Dyadic) * half ^ 24),
        ((-7339113 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word4Step33 :
    word4Chunk33.foldl (fun acc a => a.applyPacked acc)
      word4State33 = word4State34 := by decide +kernel

private def word4Chunk34 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word4State35 : PackedMat2 :=
    ⟨⟨⟨((9391343 : Dyadic) * half ^ 24),
        ((5312215 : Dyadic) * half ^ 27)⟩,
       ⟨((30213409 : Dyadic) * half ^ 26),
        ((1102543 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((9314859 : Dyadic) * half ^ 26),
        ((-1305993 : Dyadic) * half ^ 27)⟩,
       ⟨((-2840461 : Dyadic) * half ^ 22),
        ((4856205 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-887553 : Dyadic) * half ^ 25),
        ((36132517 : Dyadic) * half ^ 27)⟩,
       ⟨((3081099 : Dyadic) * half ^ 26),
        ((-54762235 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((3207379 : Dyadic) * half ^ 26),
        ((67778781 : Dyadic) * half ^ 27)⟩,
       ⟨((526209 : Dyadic) * half ^ 24),
        ((7351963 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word4Step34 :
    word4Chunk34.foldl (fun acc a => a.applyPacked acc)
      word4State34 = word4State35 := by decide +kernel

private def word4Chunk35 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word4State36 : PackedMat2 :=
    ⟨⟨⟨((-15586335 : Dyadic) * half ^ 27),
        ((2272569 : Dyadic) * half ^ 23)⟩,
       ⟨((84115291 : Dyadic) * half ^ 27),
        ((15220707 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((6576011 : Dyadic) * half ^ 27),
        ((4230649 : Dyadic) * half ^ 27)⟩,
       ⟨((44384473 : Dyadic) * half ^ 27),
        ((-45549101 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((6576011 : Dyadic) * half ^ 27),
        ((4230649 : Dyadic) * half ^ 27)⟩,
       ⟨((-44384473 : Dyadic) * half ^ 27),
        ((45549101 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((15586335 : Dyadic) * half ^ 27),
        ((-2272569 : Dyadic) * half ^ 23)⟩,
       ⟨((84115291 : Dyadic) * half ^ 27),
        ((15220707 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word4Step35 :
    word4Chunk35.foldl (fun acc a => a.applyPacked acc)
      word4State35 = word4State36 := by decide +kernel

private def word4Chunk36 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word4State37 : PackedMat2 :=
    ⟨⟨⟨((-61172833 : Dyadic) * half ^ 28),
        ((-13561759 : Dyadic) * half ^ 27)⟩,
       ⟨((3978041 : Dyadic) * half ^ 28),
        ((145956637 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-30003485 : Dyadic) * half ^ 28),
        ((2274299 : Dyadic) * half ^ 28)⟩,
       ⟨((-151324709 : Dyadic) * half ^ 28),
        ((3587661 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((12076345 : Dyadic) * half ^ 28),
        ((-15165153 : Dyadic) * half ^ 26)⟩,
       ⟨((16624943 : Dyadic) * half ^ 28),
        ((-90664097 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-173080155 : Dyadic) * half ^ 28),
        ((-32575437 : Dyadic) * half ^ 28)⟩,
       ⟨((-118833119 : Dyadic) * half ^ 28),
        ((7149349 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word4Step36 :
    word4Chunk36.foldl (fun acc a => a.applyPacked acc)
      word4State36 = word4State37 := by decide +kernel

private def word4Chunk37 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word4State38 : PackedMat2 :=
    ⟨⟨⟨((-3527699 : Dyadic) * half ^ 26),
        ((-209403769 : Dyadic) * half ^ 29)⟩,
       ⟨((19853933 : Dyadic) * half ^ 27),
        ((-8794833 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((47350237 : Dyadic) * half ^ 28),
        ((-71477647 : Dyadic) * half ^ 29)⟩,
       ⟨((-2640119 : Dyadic) * half ^ 28),
        ((-295007047 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((183242347 : Dyadic) * half ^ 28),
        ((-22355059 : Dyadic) * half ^ 28)⟩,
       ⟨((-27941175 : Dyadic) * half ^ 26),
        ((-12497589 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-109099301 : Dyadic) * half ^ 28),
        ((12798535 : Dyadic) * half ^ 28)⟩,
       ⟨((-25076117 : Dyadic) * half ^ 26),
        ((-26909331 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word4Step37 :
    word4Chunk37.foldl (fun acc a => a.applyPacked acc)
      word4State37 = word4State38 := by decide +kernel

private def word4Chunk38 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word4State39 : PackedMat2 :=
    ⟨⟨⟨((-4357797 : Dyadic) * half ^ 25),
        ((-66733719 : Dyadic) * half ^ 30)⟩,
       ⟨((-89847639 : Dyadic) * half ^ 27),
        ((-2614077 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((189719933 : Dyadic) * half ^ 29),
        ((-253821969 : Dyadic) * half ^ 30)⟩,
       ⟨((-266488263 : Dyadic) * half ^ 29),
        ((-159716679 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-51692331 : Dyadic) * half ^ 27),
        ((-38384165 : Dyadic) * half ^ 29)⟩,
       ⟨((-47052645 : Dyadic) * half ^ 29),
        ((114052049 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((17336949 : Dyadic) * half ^ 28),
        ((107278827 : Dyadic) * half ^ 28)⟩,
       ⟨((32059821 : Dyadic) * half ^ 29),
        ((-72416451 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word4Step38 :
    word4Chunk38.foldl (fun acc a => a.applyPacked acc)
      word4State38 = word4State39 := by decide +kernel

private def word4Chunk39 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word4State40 : PackedMat2 :=
    ⟨⟨⟨((85887513 : Dyadic) * half ^ 30),
        ((-213603757 : Dyadic) * half ^ 31)⟩,
       ⟨((-59695737 : Dyadic) * half ^ 29),
        ((-329306635 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((1479381 : Dyadic) * half ^ 25),
        ((968271853 : Dyadic) * half ^ 31)⟩,
       ⟨((62063075 : Dyadic) * half ^ 30),
        ((-1076464299 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-1479381 : Dyadic) * half ^ 25),
        ((-968271853 : Dyadic) * half ^ 31)⟩,
       ⟨((62063075 : Dyadic) * half ^ 30),
        ((-1076464299 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((85887513 : Dyadic) * half ^ 30),
        ((-213603757 : Dyadic) * half ^ 31)⟩,
       ⟨((59695737 : Dyadic) * half ^ 29),
        ((329306635 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word4Step39 :
    word4Chunk39.foldl (fun acc a => a.applyPacked acc)
      word4State39 = word4State40 := by decide +kernel

private def word4Chunk40 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word4State41 : PackedMat2 :=
    ⟨⟨⟨((-232753169 : Dyadic) * half ^ 29),
        ((381456131 : Dyadic) * half ^ 31)⟩,
       ⟨((-7517027 : Dyadic) * half ^ 27),
        ((23950273 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((121352031 : Dyadic) * half ^ 28),
        ((149374275 : Dyadic) * half ^ 31)⟩,
       ⟨((101318045 : Dyadic) * half ^ 30),
        ((546910845 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((121352031 : Dyadic) * half ^ 28),
        ((149374275 : Dyadic) * half ^ 31)⟩,
       ⟨((-101318045 : Dyadic) * half ^ 30),
        ((-546910845 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((232753169 : Dyadic) * half ^ 29),
        ((-381456131 : Dyadic) * half ^ 31)⟩,
       ⟨((-7517027 : Dyadic) * half ^ 27),
        ((23950273 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word4Step40 :
    word4Chunk40.foldl (fun acc a => a.applyPacked acc)
      word4State40 = word4State41 := by decide +kernel

private def word4Chunk41 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word4State42 : PackedMat2 :=
    ⟨⟨⟨((400311837 : Dyadic) * half ^ 32),
        ((250100203 : Dyadic) * half ^ 30)⟩,
       ⟨((554351865 : Dyadic) * half ^ 32),
        ((-426879541 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-1307356513 : Dyadic) * half ^ 32),
        ((1131247743 : Dyadic) * half ^ 32)⟩,
       ⟨((1509651375 : Dyadic) * half ^ 32),
        ((1341394265 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((1307356513 : Dyadic) * half ^ 32),
        ((-1131247743 : Dyadic) * half ^ 32)⟩,
       ⟨((1509651375 : Dyadic) * half ^ 32),
        ((1341394265 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((400311837 : Dyadic) * half ^ 32),
        ((250100203 : Dyadic) * half ^ 30)⟩,
       ⟨((-554351865 : Dyadic) * half ^ 32),
        ((426879541 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word4Step41 :
    word4Chunk41.foldl (fun acc a => a.applyPacked acc)
      word4State41 = word4State42 := by decide +kernel

private def word4Chunk42 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word4State43 : PackedMat2 :=
    ⟨⟨⟨((1236303237 : Dyadic) * half ^ 33),
        ((699326057 : Dyadic) * half ^ 33)⟩,
       ⟨((-5487366499 : Dyadic) * half ^ 33),
        ((726802623 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-1955074865 : Dyadic) * half ^ 33),
        ((-642932691 : Dyadic) * half ^ 31)⟩,
       ⟨((668314665 : Dyadic) * half ^ 33),
        ((3118230969 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-5689961733 : Dyadic) * half ^ 33),
        ((-1311694765 : Dyadic) * half ^ 33)⟩,
       ⟨((-546500205 : Dyadic) * half ^ 33),
        ((160845025 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((754279189 : Dyadic) * half ^ 33),
        ((-840458717 : Dyadic) * half ^ 31)⟩,
       ⟨((2152931303 : Dyadic) * half ^ 33),
        ((-2125531631 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word4Step42 :
    word4Chunk42.foldl (fun acc a => a.applyPacked acc)
      word4State42 = word4State43 := by decide +kernel

private def word4Chunk43 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word4State44 : PackedMat2 :=
    ⟨⟨⟨((1232735937 : Dyadic) * half ^ 32),
        ((-2789032773 : Dyadic) * half ^ 34)⟩,
       ⟨((434399883 : Dyadic) * half ^ 31),
        ((-7906271411 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-3524039715 : Dyadic) * half ^ 33),
        ((-5772631891 : Dyadic) * half ^ 34)⟩,
       ⟨((-602989713 : Dyadic) * half ^ 33),
        ((-449810853 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-602989713 : Dyadic) * half ^ 33),
        ((-449810853 : Dyadic) * half ^ 34)⟩,
       ⟨((-3524039715 : Dyadic) * half ^ 33),
        ((-5772631891 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-434399883 : Dyadic) * half ^ 31),
        ((7906271411 : Dyadic) * half ^ 34)⟩,
       ⟨((-1232735937 : Dyadic) * half ^ 32),
        ((2789032773 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word4Step43 :
    word4Chunk43.foldl (fun acc a => a.applyPacked acc)
      word4State43 = word4State44 := by decide +kernel

private def word4Chunk44 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word4State45 : PackedMat2 :=
    ⟨⟨⟨((-280930225 : Dyadic) * half ^ 31),
        ((10973365673 : Dyadic) * half ^ 35)⟩,
       ⟨((-8143819465 : Dyadic) * half ^ 34),
        ((3547678153 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-271980623 : Dyadic) * half ^ 34),
        ((11207664153 : Dyadic) * half ^ 35)⟩,
       ⟨((-531108953 : Dyadic) * half ^ 30),
        ((-6660817693 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-1136711615 : Dyadic) * half ^ 33),
        ((8769723871 : Dyadic) * half ^ 35)⟩,
       ⟨((-8934240923 : Dyadic) * half ^ 34),
        ((-8225762625 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((7260521913 : Dyadic) * half ^ 34),
        ((-10391261265 : Dyadic) * half ^ 35)⟩,
       ⟨((232052735 : Dyadic) * half ^ 30),
        ((5896377665 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word4Step44 :
    word4Chunk44.foldl (fun acc a => a.applyPacked acc)
      word4State44 = word4State45 := by decide +kernel

private def word4Chunk45 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word4State46 : PackedMat2 :=
    ⟨⟨⟨((18845204515 : Dyadic) * half ^ 35),
        ((49454725 : Dyadic) * half ^ 30)⟩,
       ⟨((9797979601 : Dyadic) * half ^ 35),
        ((336636109 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((21952849201 : Dyadic) * half ^ 35),
        ((-2428254613 : Dyadic) * half ^ 35)⟩,
       ⟨((-15076617781 : Dyadic) * half ^ 35),
        ((-1120072095 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((21952849201 : Dyadic) * half ^ 35),
        ((-2428254613 : Dyadic) * half ^ 35)⟩,
       ⟨((15076617781 : Dyadic) * half ^ 35),
        ((1120072095 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-18845204515 : Dyadic) * half ^ 35),
        ((-49454725 : Dyadic) * half ^ 30)⟩,
       ⟨((9797979601 : Dyadic) * half ^ 35),
        ((336636109 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word4Step45 :
    word4Chunk45.foldl (fun acc a => a.applyPacked acc)
      word4State45 = word4State46 := by decide +kernel

private def word4Chunk46 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word4State47 : PackedMat2 :=
    ⟨⟨⟨((-3084550493 : Dyadic) * half ^ 36),
        ((14733816587 : Dyadic) * half ^ 36)⟩,
       ⟨((21499931469 : Dyadic) * half ^ 36),
        ((-3567101345 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((12475931973 : Dyadic) * half ^ 36),
        ((18697256677 : Dyadic) * half ^ 35)⟩,
       ⟨((20621983993 : Dyadic) * half ^ 36),
        ((-12981259937 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((20621983993 : Dyadic) * half ^ 36),
        ((-12981259937 : Dyadic) * half ^ 36)⟩,
       ⟨((12475931973 : Dyadic) * half ^ 36),
        ((18697256677 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-21499931469 : Dyadic) * half ^ 36),
        ((3567101345 : Dyadic) * half ^ 35)⟩,
       ⟨((3084550493 : Dyadic) * half ^ 36),
        ((-14733816587 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word4Step46 :
    word4Chunk46.foldl (fun acc a => a.applyPacked acc)
      word4State46 = word4State47 := by decide +kernel

private def word4Chunk47 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word4State48 : PackedMat2 :=
    ⟨⟨⟨((3642389827 : Dyadic) * half ^ 37),
        ((-51357271355 : Dyadic) * half ^ 37)⟩,
       ⟨((43069687587 : Dyadic) * half ^ 37),
        ((23717923587 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((10471862057 : Dyadic) * half ^ 37),
        ((9210785897 : Dyadic) * half ^ 36)⟩,
       ⟨((42478602059 : Dyadic) * half ^ 37),
        ((-48233509929 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((66655081723 : Dyadic) * half ^ 37),
        ((-16003370001 : Dyadic) * half ^ 37)⟩,
       ⟨((29811938135 : Dyadic) * half ^ 37),
        ((-13237616029 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((98793118529 : Dyadic) * half ^ 37),
        ((1232103055 : Dyadic) * half ^ 33)⟩,
       ⟨((-3921424181 : Dyadic) * half ^ 37),
        ((23356038707 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word4Step47 :
    word4Chunk47.foldl (fun acc a => a.applyPacked acc)
      word4State47 = word4State48 := by decide +kernel

private def word4Chunk48 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word4State49 : PackedMat2 :=
    ⟨⟨⟨((-47065708089 : Dyadic) * half ^ 36),
        ((2220026291 : Dyadic) * half ^ 37)⟩,
       ⟨((44021111059 : Dyadic) * half ^ 37),
        ((-13354577781 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((9358557279 : Dyadic) * half ^ 36),
        ((13267652395 : Dyadic) * half ^ 35)⟩,
       ⟨((-41176383987 : Dyadic) * half ^ 37),
        ((4771451249 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-41176383987 : Dyadic) * half ^ 37),
        ((4771451249 : Dyadic) * half ^ 37)⟩,
       ⟨((9358557279 : Dyadic) * half ^ 36),
        ((13267652395 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-44021111059 : Dyadic) * half ^ 37),
        ((13354577781 : Dyadic) * half ^ 37)⟩,
       ⟨((47065708089 : Dyadic) * half ^ 36),
        ((-2220026291 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word4Step48 :
    word4Chunk48.foldl (fun acc a => a.applyPacked acc)
      word4State48 = word4State49 := by decide +kernel

private def word4Chunk49 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word4State50 : PackedMat2 :=
    ⟨⟨⟨((-168004193285 : Dyadic) * half ^ 38),
        ((-125102316135 : Dyadic) * half ^ 39)⟩,
       ⟨((-53430646589 : Dyadic) * half ^ 37),
        ((125426326755 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((5901035799 : Dyadic) * half ^ 36),
        ((78579099815 : Dyadic) * half ^ 39)⟩,
       ⟨((-114779538819 : Dyadic) * half ^ 38),
        ((82499778675 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-5901035799 : Dyadic) * half ^ 36),
        ((-78579099815 : Dyadic) * half ^ 39)⟩,
       ⟨((-114779538819 : Dyadic) * half ^ 38),
        ((82499778675 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-168004193285 : Dyadic) * half ^ 38),
        ((-125102316135 : Dyadic) * half ^ 39)⟩,
       ⟨((53430646589 : Dyadic) * half ^ 37),
        ((-125426326755 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word4Step49 :
    word4Chunk49.foldl (fun acc a => a.applyPacked acc)
      word4State49 = word4State50 := by decide +kernel

private def word4Chunk50 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word4State51 : PackedMat2 :=
    ⟨⟨⟨((-389166736769 : Dyadic) * half ^ 39),
        ((176554890345 : Dyadic) * half ^ 40)⟩,
       ⟨((-17178588529 : Dyadic) * half ^ 38),
        ((-215363653429 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-22474773745 : Dyadic) * half ^ 36),
        ((-372815023129 : Dyadic) * half ^ 40)⟩,
       ⟨((-80447032691 : Dyadic) * half ^ 39),
        ((71120870387 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-150847076371 : Dyadic) * half ^ 39),
        ((-260245222651 : Dyadic) * half ^ 40)⟩,
       ⟨((-110983973379 : Dyadic) * half ^ 38),
        ((-99351157269 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((9702190771 : Dyadic) * half ^ 38),
        ((423523913827 : Dyadic) * half ^ 40)⟩,
       ⟨((-195959271887 : Dyadic) * half ^ 39),
        ((354809559711 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word4Step50 :
    word4Chunk50.foldl (fun acc a => a.applyPacked acc)
      word4State50 = word4State51 := by decide +kernel

private def word4Chunk51 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word4State52 : PackedMat2 :=
    ⟨⟨⟨((16308129339 : Dyadic) * half ^ 37),
        ((-245924474861 : Dyadic) * half ^ 40)⟩,
       ⟨((-392164290079 : Dyadic) * half ^ 39),
        ((-66243621725 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-64502703345 : Dyadic) * half ^ 38),
        ((-107676798439 : Dyadic) * half ^ 40)⟩,
       ⟨((70122354299 : Dyadic) * half ^ 38),
        ((-88782997357 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((64502703345 : Dyadic) * half ^ 38),
        ((107676798439 : Dyadic) * half ^ 40)⟩,
       ⟨((70122354299 : Dyadic) * half ^ 38),
        ((-88782997357 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((16308129339 : Dyadic) * half ^ 37),
        ((-245924474861 : Dyadic) * half ^ 40)⟩,
       ⟨((392164290079 : Dyadic) * half ^ 39),
        ((66243621725 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word4Step51 :
    word4Chunk51.foldl (fun acc a => a.applyPacked acc)
      word4State51 = word4State52 := by decide +kernel

private def word4Chunk52 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word4State53 : PackedMat2 :=
    ⟨⟨⟨((-170329157431 : Dyadic) * half ^ 41),
        ((137095790035 : Dyadic) * half ^ 40)⟩,
       ⟨((112945738801 : Dyadic) * half ^ 41),
        ((-1299503170307 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-117431295763 : Dyadic) * half ^ 41),
        ((424052948771 : Dyadic) * half ^ 41)⟩,
       ⟨((-854837560825 : Dyadic) * half ^ 41),
        ((-142292094339 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((708637137449 : Dyadic) * half ^ 41),
        ((368703132531 : Dyadic) * half ^ 41)⟩,
       ⟨((-139468760093 : Dyadic) * half ^ 41),
        ((243067214147 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-1573694750377 : Dyadic) * half ^ 41),
        ((35409362029 : Dyadic) * half ^ 39)⟩,
       ⟨((-1025311590237 : Dyadic) * half ^ 41),
        ((-28691709315 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word4Step52 :
    word4Chunk52.foldl (fun acc a => a.applyPacked acc)
      word4State52 = word4State53 := by decide +kernel

private def word4Chunk53 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word4State54 : PackedMat2 :=
    ⟨⟨⟨((3637262292671 : Dyadic) * half ^ 42),
        ((-25947699487 : Dyadic) * half ^ 38)⟩,
       ⟨((161236054921 : Dyadic) * half ^ 42),
        ((-543019262853 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((374532765879 : Dyadic) * half ^ 42),
        ((164173496517 : Dyadic) * half ^ 42)⟩,
       ⟨((-1133376303289 : Dyadic) * half ^ 42),
        ((-677675785309 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-1519525067135 : Dyadic) * half ^ 42),
        ((-94244316823 : Dyadic) * half ^ 39)⟩,
       ⟨((-1191178074101 : Dyadic) * half ^ 42),
        ((-379421768705 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((127856071061 : Dyadic) * half ^ 42),
        ((1738013118875 : Dyadic) * half ^ 42)⟩,
       ⟨((958182454645 : Dyadic) * half ^ 42),
        ((-474812293449 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word4Step53 :
    word4Chunk53.foldl (fun acc a => a.applyPacked acc)
      word4State53 = word4State54 := by decide +kernel

private def word4Chunk54 : List Letter := [.s, .t, .h, .s]
private def word4State55 : PackedMat2 :=
    ⟨⟨⟨((470094189413 : Dyadic) * half ^ 41),
        ((596329824495 : Dyadic) * half ^ 40)⟩,
       ⟨((-353596379685 : Dyadic) * half ^ 41),
        ((-106648355479 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-5919465099 : Dyadic) * half ^ 36),
        ((8371387825 : Dyadic) * half ^ 37)⟩,
       ⟨((-885257381205 : Dyadic) * half ^ 41),
        ((1251942994691 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((5919465099 : Dyadic) * half ^ 36),
        ((-8371387825 : Dyadic) * half ^ 37)⟩,
       ⟨((-885257381205 : Dyadic) * half ^ 41),
        ((1251942994691 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((470094189413 : Dyadic) * half ^ 41),
        ((596329824495 : Dyadic) * half ^ 40)⟩,
       ⟨((353596379685 : Dyadic) * half ^ 41),
        ((106648355479 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word4Step54 :
    word4Chunk54.foldl (fun acc a => a.applyPacked acc)
      word4State54 = word4State55 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word4_check : check word4 4 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word4 = word4State55.toMatrix := by
    unfold evalRingPacked
    change ((
      word4Chunk0 ++ word4Chunk1 ++ word4Chunk2 ++ word4Chunk3 ++
      word4Chunk4 ++ word4Chunk5 ++ word4Chunk6 ++ word4Chunk7 ++
      word4Chunk8 ++ word4Chunk9 ++ word4Chunk10 ++ word4Chunk11 ++
      word4Chunk12 ++ word4Chunk13 ++ word4Chunk14 ++ word4Chunk15 ++
      word4Chunk16 ++ word4Chunk17 ++ word4Chunk18 ++ word4Chunk19 ++
      word4Chunk20 ++ word4Chunk21 ++ word4Chunk22 ++ word4Chunk23 ++
      word4Chunk24 ++ word4Chunk25 ++ word4Chunk26 ++ word4Chunk27 ++
      word4Chunk28 ++ word4Chunk29 ++ word4Chunk30 ++ word4Chunk31 ++
      word4Chunk32 ++ word4Chunk33 ++ word4Chunk34 ++ word4Chunk35 ++
      word4Chunk36 ++ word4Chunk37 ++ word4Chunk38 ++ word4Chunk39 ++
      word4Chunk40 ++ word4Chunk41 ++ word4Chunk42 ++ word4Chunk43 ++
      word4Chunk44 ++ word4Chunk45 ++ word4Chunk46 ++ word4Chunk47 ++
      word4Chunk48 ++ word4Chunk49 ++ word4Chunk50 ++ word4Chunk51 ++
      word4Chunk52 ++ word4Chunk53 ++ word4Chunk54
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word4Step0, word4Step1, word4Step2, word4Step3, word4Step4,
      word4Step5, word4Step6, word4Step7, word4Step8, word4Step9,
      word4Step10, word4Step11, word4Step12, word4Step13, word4Step14,
      word4Step15, word4Step16, word4Step17, word4Step18, word4Step19,
      word4Step20, word4Step21, word4Step22, word4Step23, word4Step24,
      word4Step25, word4Step26, word4Step27, word4Step28, word4Step29,
      word4Step30, word4Step31, word4Step32, word4Step33, word4Step34,
      word4Step35, word4Step36, word4Step37, word4Step38, word4Step39,
      word4Step40, word4Step41, word4Step42, word4Step43, word4Step44,
      word4Step45, word4Step46, word4Step47, word4Step48, word4Step49,
      word4Step50, word4Step51, word4Step52, word4Step53, word4Step54]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
