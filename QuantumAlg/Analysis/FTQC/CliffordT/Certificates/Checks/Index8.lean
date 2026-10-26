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
private def word8Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word8State1 : PackedMat2 :=
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
private lemma word8Step0 :
    word8Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word8State1 := by decide +kernel

private def word8Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word8State2 : PackedMat2 :=
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
private lemma word8Step1 :
    word8Chunk1.foldl (fun acc a => a.applyPacked acc)
      word8State1 = word8State2 := by decide +kernel

private def word8Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word8State3 : PackedMat2 :=
    ⟨⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word8Step2 :
    word8Chunk2.foldl (fun acc a => a.applyPacked acc)
      word8State2 = word8State3 := by decide +kernel

private def word8Chunk3 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word8State4 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word8Step3 :
    word8Chunk3.foldl (fun acc a => a.applyPacked acc)
      word8State3 = word8State4 := by decide +kernel

private def word8Chunk4 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word8State5 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((-5 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word8Step4 :
    word8Chunk4.foldl (fun acc a => a.applyPacked acc)
      word8State4 = word8State5 := by decide +kernel

private def word8Chunk5 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word8State6 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 2),
        ((-5 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((9 : Dyadic) * half ^ 4)⟩,
       ⟨(0 : Dyadic),
        ((-3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((-9 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-5 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word8Step5 :
    word8Chunk5.foldl (fun acc a => a.applyPacked acc)
      word8State5 = word8State6 := by decide +kernel

private def word8Chunk6 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word8State7 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word8Step6 :
    word8Chunk6.foldl (fun acc a => a.applyPacked acc)
      word8State6 = word8State7 := by decide +kernel

private def word8Chunk7 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word8State8 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 5),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((-9 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((29 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((29 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 5),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((9 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word8Step7 :
    word8Chunk7.foldl (fun acc a => a.applyPacked acc)
      word8State7 = word8State8 := by decide +kernel

private def word8Chunk8 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word8State9 : PackedMat2 :=
    ⟨⟨⟨((11 : Dyadic) * half ^ 5),
        ((-19 : Dyadic) * half ^ 6)⟩,
       ⟨((3 : Dyadic) * half ^ 5),
        ((11 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-15 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((7 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((-7 : Dyadic) * half ^ 4)⟩,
       ⟨((15 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 5),
        ((11 : Dyadic) * half ^ 6)⟩,
       ⟨((11 : Dyadic) * half ^ 5),
        ((-19 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word8Step8 :
    word8Chunk8.foldl (fun acc a => a.applyPacked acc)
      word8State8 = word8State9 := by decide +kernel

private def word8Chunk9 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word8State10 : PackedMat2 :=
    ⟨⟨⟨((-13 : Dyadic) * half ^ 6),
        ((-17 : Dyadic) * half ^ 5)⟩,
       ⟨((-3 : Dyadic) * half ^ 5),
        ((11 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 4),
        ((23 : Dyadic) * half ^ 7)⟩,
       ⟨((7 : Dyadic) * half ^ 4),
        ((-17 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 6),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-45 : Dyadic) * half ^ 6),
        ((-7 : Dyadic) * half ^ 7)⟩,
       ⟨((23 : Dyadic) * half ^ 6),
        ((19 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word8Step9 :
    word8Chunk9.foldl (fun acc a => a.applyPacked acc)
      word8State9 = word8State10 := by decide +kernel

private def word8Chunk10 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word8State11 : PackedMat2 :=
    ⟨⟨⟨((-37 : Dyadic) * half ^ 6),
        ((-25 : Dyadic) * half ^ 8)⟩,
       ⟨((-19 : Dyadic) * half ^ 7),
        ((-63 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 4),
        ((61 : Dyadic) * half ^ 8)⟩,
       ⟨((-35 : Dyadic) * half ^ 7),
        ((101 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-81 : Dyadic) * half ^ 7),
        ((27 : Dyadic) * half ^ 8)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((-43 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-11 : Dyadic) * half ^ 5),
        ((-93 : Dyadic) * half ^ 8)⟩,
       ⟨((19 : Dyadic) * half ^ 7),
        ((-55 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word8Step10 :
    word8Chunk10.foldl (fun acc a => a.applyPacked acc)
      word8State10 = word8State11 := by decide +kernel

private def word8Chunk11 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word8State12 : PackedMat2 :=
    ⟨⟨⟨((-13 : Dyadic) * half ^ 8),
        ((-169 : Dyadic) * half ^ 9)⟩,
       ⟨(0 : Dyadic),
        ((-201 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-143 : Dyadic) * half ^ 8),
        ((41 : Dyadic) * half ^ 9)⟩,
       ⟨((47 : Dyadic) * half ^ 7),
        ((39 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 5),
        ((-49 : Dyadic) * half ^ 9)⟩,
       ⟨((1 : Dyadic) * half ^ 8),
        ((-237 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((185 : Dyadic) * half ^ 8),
        ((13 : Dyadic) * half ^ 9)⟩,
       ⟨((-1 : Dyadic) * half ^ 4),
        ((13 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word8Step11 :
    word8Chunk11.foldl (fun acc a => a.applyPacked acc)
      word8State11 = word8State12 := by decide +kernel

private def word8Chunk12 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word8State13 : PackedMat2 :=
    ⟨⟨⟨((-57 : Dyadic) * half ^ 8),
        ((199 : Dyadic) * half ^ 9)⟩,
       ⟨((-73 : Dyadic) * half ^ 7),
        ((-5 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((63 : Dyadic) * half ^ 9),
        ((-37 : Dyadic) * half ^ 8)⟩,
       ⟨((-197 : Dyadic) * half ^ 9),
        ((-31 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-63 : Dyadic) * half ^ 9),
        ((37 : Dyadic) * half ^ 8)⟩,
       ⟨((-197 : Dyadic) * half ^ 9),
        ((-31 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-57 : Dyadic) * half ^ 8),
        ((199 : Dyadic) * half ^ 9)⟩,
       ⟨((73 : Dyadic) * half ^ 7),
        ((5 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word8Step12 :
    word8Chunk12.foldl (fun acc a => a.applyPacked acc)
      word8State12 = word8State13 := by decide +kernel

private def word8Chunk13 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word8State14 : PackedMat2 :=
    ⟨⟨⟨((-21 : Dyadic) * half ^ 10),
        ((523 : Dyadic) * half ^ 10)⟩,
       ⟨((-289 : Dyadic) * half ^ 10),
        ((-103 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((99 : Dyadic) * half ^ 8),
        ((1 : Dyadic) * half ^ 7)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((-343 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-335 : Dyadic) * half ^ 10),
        ((115 : Dyadic) * half ^ 9)⟩,
       ⟨((351 : Dyadic) * half ^ 10),
        ((83 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-105 : Dyadic) * half ^ 8),
        ((155 : Dyadic) * half ^ 10)⟩,
       ⟨((-313 : Dyadic) * half ^ 9),
        ((-67 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word8Step13 :
    word8Chunk13.foldl (fun acc a => a.applyPacked acc)
      word8State13 = word8State14 := by decide +kernel

private def word8Chunk14 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word8State15 : PackedMat2 :=
    ⟨⟨⟨((1023 : Dyadic) * half ^ 11),
        ((241 : Dyadic) * half ^ 11)⟩,
       ⟨((-1287 : Dyadic) * half ^ 11),
        ((15 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((417 : Dyadic) * half ^ 11),
        ((213 : Dyadic) * half ^ 10)⟩,
       ⟨((735 : Dyadic) * half ^ 11),
        ((-367 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-417 : Dyadic) * half ^ 11),
        ((-213 : Dyadic) * half ^ 10)⟩,
       ⟨((735 : Dyadic) * half ^ 11),
        ((-367 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((1023 : Dyadic) * half ^ 11),
        ((241 : Dyadic) * half ^ 11)⟩,
       ⟨((1287 : Dyadic) * half ^ 11),
        ((-15 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word8Step14 :
    word8Chunk14.foldl (fun acc a => a.applyPacked acc)
      word8State14 = word8State15 := by decide +kernel

private def word8Chunk15 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word8State16 : PackedMat2 :=
    ⟨⟨⟨((855 : Dyadic) * half ^ 11),
        ((327 : Dyadic) * half ^ 12)⟩,
       ⟨((235 : Dyadic) * half ^ 11),
        ((-887 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((239 : Dyadic) * half ^ 11),
        ((163 : Dyadic) * half ^ 10)⟩,
       ⟨((-49 : Dyadic) * half ^ 10),
        ((579 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 5),
        ((337 : Dyadic) * half ^ 12)⟩,
       ⟨((-371 : Dyadic) * half ^ 9),
        ((-141 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-607 : Dyadic) * half ^ 11),
        ((-155 : Dyadic) * half ^ 10)⟩,
       ⟨((-35 : Dyadic) * half ^ 8),
        ((545 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word8Step15 :
    word8Chunk15.foldl (fun acc a => a.applyPacked acc)
      word8State15 = word8State16 := by decide +kernel

private def word8Chunk16 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word8State17 : PackedMat2 :=
    ⟨⟨⟨((-1315 : Dyadic) * half ^ 12),
        ((1517 : Dyadic) * half ^ 13)⟩,
       ⟨((-143 : Dyadic) * half ^ 9),
        ((2163 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-395 : Dyadic) * half ^ 10),
        ((-3251 : Dyadic) * half ^ 13)⟩,
       ⟨((1541 : Dyadic) * half ^ 12),
        ((-433 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((1541 : Dyadic) * half ^ 12),
        ((-433 : Dyadic) * half ^ 13)⟩,
       ⟨((-395 : Dyadic) * half ^ 10),
        ((-3251 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((143 : Dyadic) * half ^ 9),
        ((-2163 : Dyadic) * half ^ 13)⟩,
       ⟨((1315 : Dyadic) * half ^ 12),
        ((-1517 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word8Step16 :
    word8Chunk16.foldl (fun acc a => a.applyPacked acc)
      word8State16 = word8State17 := by decide +kernel

private def word8Chunk17 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word8State18 : PackedMat2 :=
    ⟨⟨⟨((-645 : Dyadic) * half ^ 12),
        ((5763 : Dyadic) * half ^ 14)⟩,
       ⟨((1039 : Dyadic) * half ^ 13),
        ((-6873 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-2379 : Dyadic) * half ^ 13),
        ((-5683 : Dyadic) * half ^ 14)⟩,
       ⟨((-359 : Dyadic) * half ^ 11),
        ((-735 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((359 : Dyadic) * half ^ 11),
        ((735 : Dyadic) * half ^ 14)⟩,
       ⟨((2379 : Dyadic) * half ^ 13),
        ((5683 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((1039 : Dyadic) * half ^ 13),
        ((-6873 : Dyadic) * half ^ 14)⟩,
       ⟨((-645 : Dyadic) * half ^ 12),
        ((5763 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word8Step17 :
    word8Chunk17.foldl (fun acc a => a.applyPacked acc)
      word8State17 = word8State18 := by decide +kernel

private def word8Chunk18 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word8State19 : PackedMat2 :=
    ⟨⟨⟨((-135 : Dyadic) * half ^ 9),
        ((5825 : Dyadic) * half ^ 14)⟩,
       ⟨((-2237 : Dyadic) * half ^ 12),
        ((-279 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-5191 : Dyadic) * half ^ 14),
        ((-945 : Dyadic) * half ^ 14)⟩,
       ⟨((-51 : Dyadic) * half ^ 14),
        ((-5619 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-1641 : Dyadic) * half ^ 12),
        ((-2621 : Dyadic) * half ^ 14)⟩,
       ⟨((2337 : Dyadic) * half ^ 13),
        ((-1285 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-3593 : Dyadic) * half ^ 14),
        ((3317 : Dyadic) * half ^ 13)⟩,
       ⟨((-8057 : Dyadic) * half ^ 14),
        ((-1157 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word8Step18 :
    word8Chunk18.foldl (fun acc a => a.applyPacked acc)
      word8State18 = word8State19 := by decide +kernel

private def word8Chunk19 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word8State20 : PackedMat2 :=
    ⟨⟨⟨((14761 : Dyadic) * half ^ 15),
        ((-975 : Dyadic) * half ^ 13)⟩,
       ⟨((12895 : Dyadic) * half ^ 15),
        ((-1147 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((6323 : Dyadic) * half ^ 15),
        ((2657 : Dyadic) * half ^ 13)⟩,
       ⟨((-19761 : Dyadic) * half ^ 15),
        ((-261 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-6323 : Dyadic) * half ^ 15),
        ((-2657 : Dyadic) * half ^ 13)⟩,
       ⟨((-19761 : Dyadic) * half ^ 15),
        ((-261 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((14761 : Dyadic) * half ^ 15),
        ((-975 : Dyadic) * half ^ 13)⟩,
       ⟨((-12895 : Dyadic) * half ^ 15),
        ((1147 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word8Step19 :
    word8Chunk19.foldl (fun acc a => a.applyPacked acc)
      word8State19 = word8State20 := by decide +kernel

private def word8Chunk20 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word8State21 : PackedMat2 :=
    ⟨⟨⟨((-1291 : Dyadic) * half ^ 13),
        ((9189 : Dyadic) * half ^ 16)⟩,
       ⟨((5839 : Dyadic) * half ^ 14),
        ((22037 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((2879 : Dyadic) * half ^ 12),
        ((-1811 : Dyadic) * half ^ 14)⟩,
       ⟨((4277 : Dyadic) * half ^ 15),
        ((-5033 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((1411 : Dyadic) * half ^ 15),
        ((18755 : Dyadic) * half ^ 16)⟩,
       ⟨((8655 : Dyadic) * half ^ 15),
        ((-27309 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((803 : Dyadic) * half ^ 12),
        ((8421 : Dyadic) * half ^ 15)⟩,
       ⟨((15613 : Dyadic) * half ^ 15),
        ((3257 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word8Step20 :
    word8Chunk20.foldl (fun acc a => a.applyPacked acc)
      word8State20 = word8State21 := by decide +kernel

private def word8Chunk21 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word8State22 : PackedMat2 :=
    ⟨⟨⟨((-11527 : Dyadic) * half ^ 16),
        ((-29313 : Dyadic) * half ^ 17)⟩,
       ⟨((3713 : Dyadic) * half ^ 15),
        ((-33643 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-9737 : Dyadic) * half ^ 15),
        ((52907 : Dyadic) * half ^ 17)⟩,
       ⟨((25713 : Dyadic) * half ^ 16),
        ((36645 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((25713 : Dyadic) * half ^ 16),
        ((36645 : Dyadic) * half ^ 17)⟩,
       ⟨((-9737 : Dyadic) * half ^ 15),
        ((52907 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-3713 : Dyadic) * half ^ 15),
        ((33643 : Dyadic) * half ^ 17)⟩,
       ⟨((11527 : Dyadic) * half ^ 16),
        ((29313 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word8Step21 :
    word8Chunk21.foldl (fun acc a => a.applyPacked acc)
      word8State21 = word8State22 := by decide +kernel

private def word8Chunk22 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word8State23 : PackedMat2 :=
    ⟨⟨⟨((-30957 : Dyadic) * half ^ 17),
        ((-26339 : Dyadic) * half ^ 17)⟩,
       ⟨((19447 : Dyadic) * half ^ 17),
        ((-3679 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-5969 : Dyadic) * half ^ 16),
        ((-1703 : Dyadic) * half ^ 16)⟩,
       ⟨((-4659 : Dyadic) * half ^ 16),
        ((84191 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((5969 : Dyadic) * half ^ 16),
        ((1703 : Dyadic) * half ^ 16)⟩,
       ⟨((-4659 : Dyadic) * half ^ 16),
        ((84191 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-30957 : Dyadic) * half ^ 17),
        ((-26339 : Dyadic) * half ^ 17)⟩,
       ⟨((-19447 : Dyadic) * half ^ 17),
        ((3679 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word8Step22 :
    word8Chunk22.foldl (fun acc a => a.applyPacked acc)
      word8State22 = word8State23 := by decide +kernel

private def word8Chunk23 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word8State24 : PackedMat2 :=
    ⟨⟨⟨((-135361 : Dyadic) * half ^ 18),
        ((1065 : Dyadic) * half ^ 18)⟩,
       ⟨((-19869 : Dyadic) * half ^ 18),
        ((12195 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-7895 : Dyadic) * half ^ 14),
        ((-5519 : Dyadic) * half ^ 15)⟩,
       ⟨((-1373 : Dyadic) * half ^ 13),
        ((118145 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((73993 : Dyadic) * half ^ 18),
        ((-10641 : Dyadic) * half ^ 15)⟩,
       ⟨((-162297 : Dyadic) * half ^ 18),
        ((-5149 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-3315 : Dyadic) * half ^ 16),
        ((77615 : Dyadic) * half ^ 18)⟩,
       ⟨((5565 : Dyadic) * half ^ 17),
        ((28873 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word8Step23 :
    word8Chunk23.foldl (fun acc a => a.applyPacked acc)
      word8State23 = word8State24 := by decide +kernel

private def word8Chunk24 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word8State25 : PackedMat2 :=
    ⟨⟨⟨((-104321 : Dyadic) * half ^ 19),
        ((-47927 : Dyadic) * half ^ 17)⟩,
       ⟨((-67035 : Dyadic) * half ^ 19),
        ((-136949 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((90993 : Dyadic) * half ^ 19),
        ((-122765 : Dyadic) * half ^ 18)⟩,
       ⟨((90101 : Dyadic) * half ^ 19),
        ((-75893 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-90993 : Dyadic) * half ^ 19),
        ((122765 : Dyadic) * half ^ 18)⟩,
       ⟨((90101 : Dyadic) * half ^ 19),
        ((-75893 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-104321 : Dyadic) * half ^ 19),
        ((-47927 : Dyadic) * half ^ 17)⟩,
       ⟨((67035 : Dyadic) * half ^ 19),
        ((136949 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word8Step24 :
    word8Chunk24.foldl (fun acc a => a.applyPacked acc)
      word8State24 = word8State25 := by decide +kernel

private def word8Chunk25 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word8State26 : PackedMat2 :=
    ⟨⟨⟨((-17701 : Dyadic) * half ^ 19),
        ((-29691 : Dyadic) * half ^ 20)⟩,
       ⟨((27159 : Dyadic) * half ^ 18),
        ((-609 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((100035 : Dyadic) * half ^ 18),
        ((-454383 : Dyadic) * half ^ 20)⟩,
       ⟨((-256257 : Dyadic) * half ^ 19),
        ((-352833 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((50451 : Dyadic) * half ^ 16),
        ((56187 : Dyadic) * half ^ 20)⟩,
       ⟨((50775 : Dyadic) * half ^ 19),
        ((-456327 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-7575 : Dyadic) * half ^ 18),
        ((36617 : Dyadic) * half ^ 20)⟩,
       ⟨((-14541 : Dyadic) * half ^ 19),
        ((-72019 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word8Step25 :
    word8Chunk25.foldl (fun acc a => a.applyPacked acc)
      word8State25 = word8State26 := by decide +kernel

private def word8Chunk26 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word8State27 : PackedMat2 :=
    ⟨⟨⟨((-62807 : Dyadic) * half ^ 18),
        ((51583 : Dyadic) * half ^ 18)⟩,
       ⟨((-171713 : Dyadic) * half ^ 19),
        ((-172649 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-12289 : Dyadic) * half ^ 20),
        ((308463 : Dyadic) * half ^ 19)⟩,
       ⟨((-1599 : Dyadic) * half ^ 20),
        ((-19641 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-12289 : Dyadic) * half ^ 20),
        ((308463 : Dyadic) * half ^ 19)⟩,
       ⟨((1599 : Dyadic) * half ^ 20),
        ((19641 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((62807 : Dyadic) * half ^ 18),
        ((-51583 : Dyadic) * half ^ 18)⟩,
       ⟨((-171713 : Dyadic) * half ^ 19),
        ((-172649 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word8Step26 :
    word8Chunk26.foldl (fun acc a => a.applyPacked acc)
      word8State26 = word8State27 := by decide +kernel

private def word8Chunk27 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word8State28 : PackedMat2 :=
    ⟨⟨⟨((216471 : Dyadic) * half ^ 19),
        ((288127 : Dyadic) * half ^ 20)⟩,
       ⟨((2183 : Dyadic) * half ^ 14),
        ((-880813 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((514679 : Dyadic) * half ^ 21),
        ((200759 : Dyadic) * half ^ 21)⟩,
       ⟨((690657 : Dyadic) * half ^ 21),
        ((-515705 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-514679 : Dyadic) * half ^ 21),
        ((-200759 : Dyadic) * half ^ 21)⟩,
       ⟨((690657 : Dyadic) * half ^ 21),
        ((-515705 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((216471 : Dyadic) * half ^ 19),
        ((288127 : Dyadic) * half ^ 20)⟩,
       ⟨((-2183 : Dyadic) * half ^ 14),
        ((880813 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word8Step27 :
    word8Chunk27.foldl (fun acc a => a.applyPacked acc)
      word8State27 = word8State28 := by decide +kernel

private def word8Chunk28 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word8State29 : PackedMat2 :=
    ⟨⟨⟨((-404705 : Dyadic) * half ^ 22),
        ((342889 : Dyadic) * half ^ 21)⟩,
       ⟨((-33045 : Dyadic) * half ^ 22),
        ((2632389 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((968195 : Dyadic) * half ^ 22),
        ((520187 : Dyadic) * half ^ 22)⟩,
       ⟨((-186365 : Dyadic) * half ^ 22),
        ((373239 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((968195 : Dyadic) * half ^ 22),
        ((520187 : Dyadic) * half ^ 22)⟩,
       ⟨((186365 : Dyadic) * half ^ 22),
        ((-373239 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((404705 : Dyadic) * half ^ 22),
        ((-342889 : Dyadic) * half ^ 21)⟩,
       ⟨((-33045 : Dyadic) * half ^ 22),
        ((2632389 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word8Step28 :
    word8Chunk28.foldl (fun acc a => a.applyPacked acc)
      word8State28 = word8State29 := by decide +kernel

private def word8Chunk29 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word8State30 : PackedMat2 :=
    ⟨⟨⟨((-3886773 : Dyadic) * half ^ 23),
        ((1303603 : Dyadic) * half ^ 22)⟩,
       ⟨((4020577 : Dyadic) * half ^ 23),
        ((532115 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-1048757 : Dyadic) * half ^ 23),
        ((-19117 : Dyadic) * half ^ 20)⟩,
       ⟨((4027791 : Dyadic) * half ^ 23),
        ((1944941 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((1048757 : Dyadic) * half ^ 23),
        ((19117 : Dyadic) * half ^ 20)⟩,
       ⟨((4027791 : Dyadic) * half ^ 23),
        ((1944941 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-3886773 : Dyadic) * half ^ 23),
        ((1303603 : Dyadic) * half ^ 22)⟩,
       ⟨((-4020577 : Dyadic) * half ^ 23),
        ((-532115 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word8Step29 :
    word8Chunk29.foldl (fun acc a => a.applyPacked acc)
      word8State29 = word8State30 := by decide +kernel

private def word8Chunk30 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word8State31 : PackedMat2 :=
    ⟨⟨⟨((747511 : Dyadic) * half ^ 22),
        ((-1735015 : Dyadic) * half ^ 22)⟩,
       ⟨((-370119 : Dyadic) * half ^ 23),
        ((2043467 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-2240921 : Dyadic) * half ^ 22),
        ((-1723073 : Dyadic) * half ^ 24)⟩,
       ⟨((-228285 : Dyadic) * half ^ 19),
        ((-1140475 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-291299 : Dyadic) * half ^ 23),
        ((-414641 : Dyadic) * half ^ 23)⟩,
       ⟨((715887 : Dyadic) * half ^ 22),
        ((4067201 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((5513497 : Dyadic) * half ^ 23),
        ((-1865141 : Dyadic) * half ^ 24)⟩,
       ⟨((-1426563 : Dyadic) * half ^ 23),
        ((1124903 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word8Step30 :
    word8Chunk30.foldl (fun acc a => a.applyPacked acc)
      word8State30 = word8State31 := by decide +kernel

private def word8Chunk31 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word8State32 : PackedMat2 :=
    ⟨⟨⟨((-11051783 : Dyadic) * half ^ 24),
        ((-2819963 : Dyadic) * half ^ 25)⟩,
       ⟨((2308629 : Dyadic) * half ^ 22),
        ((-6539823 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((434465 : Dyadic) * half ^ 24),
        ((-883149 : Dyadic) * half ^ 25)⟩,
       ⟨((-1498109 : Dyadic) * half ^ 22),
        ((-4941259 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-728051 : Dyadic) * half ^ 22),
        ((-5557971 : Dyadic) * half ^ 25)⟩,
       ⟨((2029055 : Dyadic) * half ^ 24),
        ((6426901 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((4679893 : Dyadic) * half ^ 24),
        ((1817267 : Dyadic) * half ^ 25)⟩,
       ⟨((-929965 : Dyadic) * half ^ 23),
        ((20286299 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word8Step31 :
    word8Chunk31.foldl (fun acc a => a.applyPacked acc)
      word8State31 = word8State32 := by decide +kernel

private def word8Chunk32 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word8State33 : PackedMat2 :=
    ⟨⟨⟨((125081 : Dyadic) * half ^ 22),
        ((-36678447 : Dyadic) * half ^ 26)⟩,
       ⟨((9737355 : Dyadic) * half ^ 25),
        ((-6707489 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((2019657 : Dyadic) * half ^ 24),
        ((25238809 : Dyadic) * half ^ 26)⟩,
       ⟨((306009 : Dyadic) * half ^ 25),
        ((222025 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-12730417 : Dyadic) * half ^ 25),
        ((-4345323 : Dyadic) * half ^ 26)⟩,
       ⟨((-1563549 : Dyadic) * half ^ 22),
        ((-3733305 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-2711621 : Dyadic) * half ^ 22),
        ((10738003 : Dyadic) * half ^ 26)⟩,
       ⟨((-14985479 : Dyadic) * half ^ 25),
        ((-8736707 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word8Step32 :
    word8Chunk32.foldl (fun acc a => a.applyPacked acc)
      word8State32 = word8State33 := by decide +kernel

private def word8Chunk33 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word8State34 : PackedMat2 :=
    ⟨⟨⟨((-6375329 : Dyadic) * half ^ 26),
        ((-48422079 : Dyadic) * half ^ 27)⟩,
       ⟨((-308841 : Dyadic) * half ^ 20),
        ((-21455065 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-585609 : Dyadic) * half ^ 25),
        ((-14975401 : Dyadic) * half ^ 27)⟩,
       ⟨((10738791 : Dyadic) * half ^ 26),
        ((-69870359 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((10738791 : Dyadic) * half ^ 26),
        ((-69870359 : Dyadic) * half ^ 27)⟩,
       ⟨((-585609 : Dyadic) * half ^ 25),
        ((-14975401 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((308841 : Dyadic) * half ^ 20),
        ((21455065 : Dyadic) * half ^ 27)⟩,
       ⟨((6375329 : Dyadic) * half ^ 26),
        ((48422079 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word8Step33 :
    word8Chunk33.foldl (fun acc a => a.applyPacked acc)
      word8State33 = word8State34 := by decide +kernel

private def word8Chunk34 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word8State35 : PackedMat2 :=
    ⟨⟨⟨((-8071717 : Dyadic) * half ^ 25),
        ((1047637 : Dyadic) * half ^ 24)⟩,
       ⟨((-2871607 : Dyadic) * half ^ 25),
        ((-34146119 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-74098713 : Dyadic) * half ^ 27),
        ((21503733 : Dyadic) * half ^ 27)⟩,
       ⟨((-24255235 : Dyadic) * half ^ 27),
        ((-60678915 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((74098713 : Dyadic) * half ^ 27),
        ((-21503733 : Dyadic) * half ^ 27)⟩,
       ⟨((-24255235 : Dyadic) * half ^ 27),
        ((-60678915 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-8071717 : Dyadic) * half ^ 25),
        ((1047637 : Dyadic) * half ^ 24)⟩,
       ⟨((2871607 : Dyadic) * half ^ 25),
        ((34146119 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word8Step34 :
    word8Chunk34.foldl (fun acc a => a.applyPacked acc)
      word8State34 = word8State35 := by decide +kernel

private def word8Chunk35 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word8State36 : PackedMat2 :=
    ⟨⟨⟨((102347333 : Dyadic) * half ^ 28),
        ((-9822241 : Dyadic) * half ^ 27)⟩,
       ⟨((-124834341 : Dyadic) * half ^ 28),
        ((-63784247 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((34975833 : Dyadic) * half ^ 28),
        ((-2519351 : Dyadic) * half ^ 27)⟩,
       ⟨((-183970115 : Dyadic) * half ^ 28),
        ((31394617 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-36433319 : Dyadic) * half ^ 28),
        ((54736487 : Dyadic) * half ^ 27)⟩,
       ⟨((-26355915 : Dyadic) * half ^ 28),
        ((74497141 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-44139765 : Dyadic) * half ^ 28),
        ((-113590837 : Dyadic) * half ^ 28)⟩,
       ⟨((-83428729 : Dyadic) * half ^ 28),
        ((-702719 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word8Step35 :
    word8Chunk35.foldl (fun acc a => a.applyPacked acc)
      word8State35 = word8State36 := by decide +kernel

private def word8Chunk36 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word8State37 : PackedMat2 :=
    ⟨⟨⟨((173830659 : Dyadic) * half ^ 29),
        ((85002793 : Dyadic) * half ^ 28)⟩,
       ⟨((-41210651 : Dyadic) * half ^ 29),
        ((-90029521 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((60513447 : Dyadic) * half ^ 29),
        ((24013445 : Dyadic) * half ^ 28)⟩,
       ⟨((-396741277 : Dyadic) * half ^ 29),
        ((91164275 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-60513447 : Dyadic) * half ^ 29),
        ((-24013445 : Dyadic) * half ^ 28)⟩,
       ⟨((-396741277 : Dyadic) * half ^ 29),
        ((91164275 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((173830659 : Dyadic) * half ^ 29),
        ((85002793 : Dyadic) * half ^ 28)⟩,
       ⟨((41210651 : Dyadic) * half ^ 29),
        ((90029521 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word8Step36 :
    word8Chunk36.foldl (fun acc a => a.applyPacked acc)
      word8State36 = word8State37 := by decide +kernel

private def word8Chunk37 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word8State38 : PackedMat2 :=
    ⟨⟨⟨((121015329 : Dyadic) * half ^ 29),
        ((431974095 : Dyadic) * half ^ 30)⟩,
       ⟨((18454501 : Dyadic) * half ^ 29),
        ((-99832427 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((286385561 : Dyadic) * half ^ 29),
        ((4457397 : Dyadic) * half ^ 27)⟩,
       ⟨((31429819 : Dyadic) * half ^ 26),
        ((-60298433 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-31429819 : Dyadic) * half ^ 26),
        ((60298433 : Dyadic) * half ^ 28)⟩,
       ⟨((-286385561 : Dyadic) * half ^ 29),
        ((-4457397 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((18454501 : Dyadic) * half ^ 29),
        ((-99832427 : Dyadic) * half ^ 30)⟩,
       ⟨((121015329 : Dyadic) * half ^ 29),
        ((431974095 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word8Step37 :
    word8Chunk37.foldl (fun acc a => a.applyPacked acc)
      word8State37 = word8State38 := by decide +kernel

private def word8Chunk38 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word8State39 : PackedMat2 :=
    ⟨⟨⟨((237239199 : Dyadic) * half ^ 30),
        ((101505887 : Dyadic) * half ^ 31)⟩,
       ⟨((295474375 : Dyadic) * half ^ 30),
        ((-430230117 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((273877039 : Dyadic) * half ^ 29),
        ((-67366743 : Dyadic) * half ^ 30)⟩,
       ⟨((164856267 : Dyadic) * half ^ 30),
        ((536350905 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((37732353 : Dyadic) * half ^ 26),
        ((-382897811 : Dyadic) * half ^ 31)⟩,
       ⟨((234492081 : Dyadic) * half ^ 29),
        ((712610345 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((132934001 : Dyadic) * half ^ 29),
        ((-7279397 : Dyadic) * half ^ 28)⟩,
       ⟨((164362115 : Dyadic) * half ^ 30),
        ((-266356787 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word8Step38 :
    word8Chunk38.foldl (fun acc a => a.applyPacked acc)
      word8State38 = word8State39 := by decide +kernel

private def word8Chunk39 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word8State40 : PackedMat2 :=
    ⟨⟨⟨((176892795 : Dyadic) * half ^ 30),
        ((769975029 : Dyadic) * half ^ 32)⟩,
       ⟨((-357847185 : Dyadic) * half ^ 31),
        ((-380247173 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-67103619 : Dyadic) * half ^ 28),
        ((-78699541 : Dyadic) * half ^ 32)⟩,
       ⟨((1915930263 : Dyadic) * half ^ 31),
        ((-235251069 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-1915930263 : Dyadic) * half ^ 31),
        ((235251069 : Dyadic) * half ^ 32)⟩,
       ⟨((67103619 : Dyadic) * half ^ 28),
        ((78699541 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-357847185 : Dyadic) * half ^ 31),
        ((-380247173 : Dyadic) * half ^ 32)⟩,
       ⟨((176892795 : Dyadic) * half ^ 30),
        ((769975029 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word8Step39 :
    word8Chunk39.foldl (fun acc a => a.applyPacked acc)
      word8State39 = word8State40 := by decide +kernel

private def word8Chunk40 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word8State41 : PackedMat2 :=
    ⟨⟨⟨((603048989 : Dyadic) * half ^ 31),
        ((-682470431 : Dyadic) * half ^ 32)⟩,
       ⟨((65256861 : Dyadic) * half ^ 31),
        ((-331205163 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-2569740905 : Dyadic) * half ^ 32),
        ((-775019805 : Dyadic) * half ^ 32)⟩,
       ⟨((-577216093 : Dyadic) * half ^ 32),
        ((1874549695 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((549764945 : Dyadic) * half ^ 31),
        ((-1573478499 : Dyadic) * half ^ 32)⟩,
       ⟨((-662392375 : Dyadic) * half ^ 30),
        ((-498131203 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((1344880757 : Dyadic) * half ^ 32),
        ((-334152925 : Dyadic) * half ^ 31)⟩,
       ⟨((20060105 : Dyadic) * half ^ 32),
        ((-4201501 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word8Step40 :
    word8Chunk40.foldl (fun acc a => a.applyPacked acc)
      word8State40 = word8State41 := by decide +kernel

private def word8Chunk41 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word8State42 : PackedMat2 :=
    ⟨⟨⟨((-2072670677 : Dyadic) * half ^ 33),
        ((3743057999 : Dyadic) * half ^ 33)⟩,
       ⟨((-2688463579 : Dyadic) * half ^ 33),
        ((-663488257 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-1103337239 : Dyadic) * half ^ 33),
        ((-1890940137 : Dyadic) * half ^ 32)⟩,
       ⟨((-26739493 : Dyadic) * half ^ 33),
        ((-669765467 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((1103337239 : Dyadic) * half ^ 33),
        ((1890940137 : Dyadic) * half ^ 32)⟩,
       ⟨((-26739493 : Dyadic) * half ^ 33),
        ((-669765467 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-2072670677 : Dyadic) * half ^ 33),
        ((3743057999 : Dyadic) * half ^ 33)⟩,
       ⟨((2688463579 : Dyadic) * half ^ 33),
        ((663488257 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word8Step41 :
    word8Chunk41.foldl (fun acc a => a.applyPacked acc)
      word8State41 = word8State42 := by decide +kernel

private def word8Chunk42 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word8State43 : PackedMat2 :=
    ⟨⟨⟨((382326735 : Dyadic) * half ^ 31),
        ((839808213 : Dyadic) * half ^ 32)⟩,
       ⟨((-4363915765 : Dyadic) * half ^ 33),
        ((1472516327 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-4108353533 : Dyadic) * half ^ 33),
        ((-5004129687 : Dyadic) * half ^ 34)⟩,
       ⟨((-45316301 : Dyadic) * half ^ 33),
        ((-170288869 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((45316301 : Dyadic) * half ^ 33),
        ((170288869 : Dyadic) * half ^ 34)⟩,
       ⟨((4108353533 : Dyadic) * half ^ 33),
        ((5004129687 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-4363915765 : Dyadic) * half ^ 33),
        ((1472516327 : Dyadic) * half ^ 32)⟩,
       ⟨((382326735 : Dyadic) * half ^ 31),
        ((839808213 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word8Step42 :
    word8Chunk42.foldl (fun acc a => a.applyPacked acc)
      word8State42 = word8State43 := by decide +kernel

private def word8Chunk43 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word8State44 : PackedMat2 :=
    ⟨⟨⟨((4156401875 : Dyadic) * half ^ 34),
        ((797594379 : Dyadic) * half ^ 35)⟩,
       ⟨((6467396097 : Dyadic) * half ^ 33),
        ((-1302404049 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((6361398505 : Dyadic) * half ^ 34),
        ((-1723227501 : Dyadic) * half ^ 35)⟩,
       ⟨((-3957831369 : Dyadic) * half ^ 33),
        ((-3094287947 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-3957831369 : Dyadic) * half ^ 33),
        ((-3094287947 : Dyadic) * half ^ 35)⟩,
       ⟨((6361398505 : Dyadic) * half ^ 34),
        ((-1723227501 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-6467396097 : Dyadic) * half ^ 33),
        ((1302404049 : Dyadic) * half ^ 35)⟩,
       ⟨((-4156401875 : Dyadic) * half ^ 34),
        ((-797594379 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word8Step43 :
    word8Chunk43.foldl (fun acc a => a.applyPacked acc)
      word8State43 = word8State44 := by decide +kernel

private def word8Chunk44 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word8State45 : PackedMat2 :=
    ⟨⟨⟨((780561839 : Dyadic) * half ^ 34),
        ((-30566780309 : Dyadic) * half ^ 36)⟩,
       ⟨((2896841647 : Dyadic) * half ^ 35),
        ((24150237511 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-2282451055 : Dyadic) * half ^ 35),
        ((7899173277 : Dyadic) * half ^ 36)⟩,
       ⟨((-302395255 : Dyadic) * half ^ 29),
        ((217607009 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((302395255 : Dyadic) * half ^ 29),
        ((-217607009 : Dyadic) * half ^ 36)⟩,
       ⟨((2282451055 : Dyadic) * half ^ 35),
        ((-7899173277 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((2896841647 : Dyadic) * half ^ 35),
        ((24150237511 : Dyadic) * half ^ 36)⟩,
       ⟨((780561839 : Dyadic) * half ^ 34),
        ((-30566780309 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word8Step44 :
    word8Chunk44.foldl (fun acc a => a.applyPacked acc)
      word8State44 = word8State45 := by decide +kernel

private def word8Chunk45 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word8State46 : PackedMat2 :=
    ⟨⟨⟨((-14811419411 : Dyadic) * half ^ 35),
        ((-1978572445 : Dyadic) * half ^ 36)⟩,
       ⟨((10826485523 : Dyadic) * half ^ 35),
        ((-392168705 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((54610978507 : Dyadic) * half ^ 36),
        ((-1723395575 : Dyadic) * half ^ 36)⟩,
       ⟨((-5273115445 : Dyadic) * half ^ 36),
        ((-13174727019 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((54610978507 : Dyadic) * half ^ 36),
        ((-1723395575 : Dyadic) * half ^ 36)⟩,
       ⟨((5273115445 : Dyadic) * half ^ 36),
        ((13174727019 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((14811419411 : Dyadic) * half ^ 35),
        ((1978572445 : Dyadic) * half ^ 36)⟩,
       ⟨((10826485523 : Dyadic) * half ^ 35),
        ((-392168705 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word8Step45 :
    word8Chunk45.foldl (fun acc a => a.applyPacked acc)
      word8State45 = word8State46 := by decide +kernel

private def word8Chunk46 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word8State47 : PackedMat2 :=
    ⟨⟨⟨((-36924748979 : Dyadic) * half ^ 37),
        ((-9920898781 : Dyadic) * half ^ 37)⟩,
       ⟨((-10702862393 : Dyadic) * half ^ 37),
        ((16600832687 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((3904197883 : Dyadic) * half ^ 32),
        ((-3982708841 : Dyadic) * half ^ 37)⟩,
       ⟨((3916514767 : Dyadic) * half ^ 35),
        ((4929874179 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-15736787875 : Dyadic) * half ^ 37),
        ((-35150097831 : Dyadic) * half ^ 36)⟩,
       ⟨((23702205557 : Dyadic) * half ^ 37),
        ((-27317068297 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((3339966953 : Dyadic) * half ^ 36),
        ((-11906902843 : Dyadic) * half ^ 36)⟩,
       ⟨((-6630432867 : Dyadic) * half ^ 35),
        ((-13110943293 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word8Step46 :
    word8Chunk46.foldl (fun acc a => a.applyPacked acc)
      word8State46 = word8State47 := by decide +kernel

private def word8Chunk47 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word8State48 : PackedMat2 :=
    ⟨⟨⟨((-24804994237 : Dyadic) * half ^ 38),
        ((-36622539191 : Dyadic) * half ^ 37)⟩,
       ⟨((-128657415861 : Dyadic) * half ^ 38),
        ((-16641052333 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-34334339143 : Dyadic) * half ^ 38),
        ((121815668227 : Dyadic) * half ^ 38)⟩,
       ⟨((127448576709 : Dyadic) * half ^ 38),
        ((881225723 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-34334339143 : Dyadic) * half ^ 38),
        ((121815668227 : Dyadic) * half ^ 38)⟩,
       ⟨((-127448576709 : Dyadic) * half ^ 38),
        ((-881225723 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((24804994237 : Dyadic) * half ^ 38),
        ((36622539191 : Dyadic) * half ^ 37)⟩,
       ⟨((-128657415861 : Dyadic) * half ^ 38),
        ((-16641052333 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word8Step47 :
    word8Chunk47.foldl (fun acc a => a.applyPacked acc)
      word8State47 = word8State48 := by decide +kernel

private def word8Chunk48 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word8State49 : PackedMat2 :=
    ⟨⟨⟨((-4419089393 : Dyadic) * half ^ 34),
        ((-54721060687 : Dyadic) * half ^ 39)⟩,
       ⟨((-44535078921 : Dyadic) * half ^ 37),
        ((-121011036317 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((13148314515 : Dyadic) * half ^ 38),
        ((-56413997819 : Dyadic) * half ^ 38)⟩,
       ⟨((-21853365575 : Dyadic) * half ^ 37),
        ((75297613937 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((207009225693 : Dyadic) * half ^ 38),
        ((-56855045665 : Dyadic) * half ^ 39)⟩,
       ⟨((94181230055 : Dyadic) * half ^ 38),
        ((-30558416635 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((33144987815 : Dyadic) * half ^ 38),
        ((9182363777 : Dyadic) * half ^ 38)⟩,
       ⟨((43933024251 : Dyadic) * half ^ 37),
        ((79887794065 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word8Step48 :
    word8Chunk48.foldl (fun acc a => a.applyPacked acc)
      word8State48 = word8State49 := by decide +kernel

private def word8Chunk49 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word8State50 : PackedMat2 :=
    ⟨⟨⟨((41749186895 : Dyadic) * half ^ 39),
        ((26678718509 : Dyadic) * half ^ 37)⟩,
       ⟨((5453538467 : Dyadic) * half ^ 38),
        ((-1665246151 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-391061828451 : Dyadic) * half ^ 39),
        ((157182564397 : Dyadic) * half ^ 40)⟩,
       ⟨((149733021627 : Dyadic) * half ^ 39),
        ((366535329917 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-13084547845 : Dyadic) * half ^ 36),
        ((-270397425039 : Dyadic) * half ^ 39)⟩,
       ⟨((-261858947157 : Dyadic) * half ^ 39),
        ((30166100853 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-53322656925 : Dyadic) * half ^ 37),
        ((-30842109961 : Dyadic) * half ^ 40)⟩,
       ⟨((34780093 : Dyadic) * half ^ 37),
        ((52656263829 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word8Step49 :
    word8Chunk49.foldl (fun acc a => a.applyPacked acc)
      word8State49 = word8State50 := by decide +kernel

private def word8Chunk50 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word8State51 : PackedMat2 :=
    ⟨⟨⟨((453202035307 : Dyadic) * half ^ 40),
        ((35747500917 : Dyadic) * half ^ 38)⟩,
       ⟨((-271540506577 : Dyadic) * half ^ 40),
        ((-70740210381 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-331983486457 : Dyadic) * half ^ 39),
        ((8734478355 : Dyadic) * half ^ 35)⟩,
       ⟨((-13123948483 : Dyadic) * half ^ 36),
        ((-209265689097 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-331983486457 : Dyadic) * half ^ 39),
        ((8734478355 : Dyadic) * half ^ 35)⟩,
       ⟨((13123948483 : Dyadic) * half ^ 36),
        ((209265689097 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-453202035307 : Dyadic) * half ^ 40),
        ((-35747500917 : Dyadic) * half ^ 38)⟩,
       ⟨((-271540506577 : Dyadic) * half ^ 40),
        ((-70740210381 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word8Step50 :
    word8Chunk50.foldl (fun acc a => a.applyPacked acc)
      word8State50 = word8State51 := by decide +kernel

private def word8Chunk51 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word8State52 : PackedMat2 :=
    ⟨⟨⟨((662276560083 : Dyadic) * half ^ 41),
        ((631128589917 : Dyadic) * half ^ 41)⟩,
       ⟨((678758643137 : Dyadic) * half ^ 41),
        ((-493447538387 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-190275902957 : Dyadic) * half ^ 39),
        ((551674224145 : Dyadic) * half ^ 41)⟩,
       ⟨((-52451772749 : Dyadic) * half ^ 38),
        ((-200679200751 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((251042578859 : Dyadic) * half ^ 41),
        ((295179448455 : Dyadic) * half ^ 40)⟩,
       ⟨((-1354391027149 : Dyadic) * half ^ 41),
        ((85372357459 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((68840525765 : Dyadic) * half ^ 40),
        ((335258800805 : Dyadic) * half ^ 40)⟩,
       ⟨((70286008019 : Dyadic) * half ^ 37),
        ((-8241041527 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word8Step51 :
    word8Chunk51.foldl (fun acc a => a.applyPacked acc)
      word8State51 = word8State52 := by decide +kernel

private def word8Chunk52 : List Letter := [.t, .h, .s]
private def word8State53 : PackedMat2 :=
    ⟨⟨⟨((1433845392921 : Dyadic) * half ^ 41),
        ((1081890742075 : Dyadic) * half ^ 42)⟩,
       ⟨((-261280440633 : Dyadic) * half ^ 39),
        ((1439862254965 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((29113342879 : Dyadic) * half ^ 40),
        ((-82344968691 : Dyadic) * half ^ 42)⟩,
       ⟨((-171588213087 : Dyadic) * half ^ 41),
        ((242662378091 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-29113342879 : Dyadic) * half ^ 40),
        ((82344968691 : Dyadic) * half ^ 42)⟩,
       ⟨((-171588213087 : Dyadic) * half ^ 41),
        ((242662378091 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((1433845392921 : Dyadic) * half ^ 41),
        ((1081890742075 : Dyadic) * half ^ 42)⟩,
       ⟨((261280440633 : Dyadic) * half ^ 39),
        ((-1439862254965 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word8Step52 :
    word8Chunk52.foldl (fun acc a => a.applyPacked acc)
      word8State52 = word8State53 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word8_check : check word8 8 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word8 = word8State53.toMatrix := by
    unfold evalRingPacked
    change ((
      word8Chunk0 ++ word8Chunk1 ++ word8Chunk2 ++ word8Chunk3 ++
      word8Chunk4 ++ word8Chunk5 ++ word8Chunk6 ++ word8Chunk7 ++
      word8Chunk8 ++ word8Chunk9 ++ word8Chunk10 ++ word8Chunk11 ++
      word8Chunk12 ++ word8Chunk13 ++ word8Chunk14 ++ word8Chunk15 ++
      word8Chunk16 ++ word8Chunk17 ++ word8Chunk18 ++ word8Chunk19 ++
      word8Chunk20 ++ word8Chunk21 ++ word8Chunk22 ++ word8Chunk23 ++
      word8Chunk24 ++ word8Chunk25 ++ word8Chunk26 ++ word8Chunk27 ++
      word8Chunk28 ++ word8Chunk29 ++ word8Chunk30 ++ word8Chunk31 ++
      word8Chunk32 ++ word8Chunk33 ++ word8Chunk34 ++ word8Chunk35 ++
      word8Chunk36 ++ word8Chunk37 ++ word8Chunk38 ++ word8Chunk39 ++
      word8Chunk40 ++ word8Chunk41 ++ word8Chunk42 ++ word8Chunk43 ++
      word8Chunk44 ++ word8Chunk45 ++ word8Chunk46 ++ word8Chunk47 ++
      word8Chunk48 ++ word8Chunk49 ++ word8Chunk50 ++ word8Chunk51 ++
      word8Chunk52
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word8Step0, word8Step1, word8Step2, word8Step3, word8Step4,
      word8Step5, word8Step6, word8Step7, word8Step8, word8Step9,
      word8Step10, word8Step11, word8Step12, word8Step13, word8Step14,
      word8Step15, word8Step16, word8Step17, word8Step18, word8Step19,
      word8Step20, word8Step21, word8Step22, word8Step23, word8Step24,
      word8Step25, word8Step26, word8Step27, word8Step28, word8Step29,
      word8Step30, word8Step31, word8Step32, word8Step33, word8Step34,
      word8Step35, word8Step36, word8Step37, word8Step38, word8Step39,
      word8Step40, word8Step41, word8Step42, word8Step43, word8Step44,
      word8Step45, word8Step46, word8Step47, word8Step48, word8Step49,
      word8Step50, word8Step51, word8Step52]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
