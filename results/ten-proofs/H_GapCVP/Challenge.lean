import Lean
import Mathlib

section

noncomputable section

open StateTransition (EvalsToInTime)

namespace GapCVP

section

open Computability

abbrev BitLanguage := List Bool → Bool

abbrev bitEncoding : List Bool → List Bool := id

def pairBitEncoding : (List Bool × List Bool) →
    List (Bool ⊕ Bool) :=
  (Computability.encodingProd
    (Computability.encodingList Bool)
    (Computability.encodingList Bool)).encode

abbrev BitTM (f : List Bool → List Bool) :=
  Turing.TM2ComputableInPolyTime bitEncoding bitEncoding f

abbrev VerifierTM (verifier : List Bool × List Bool → Bool) :=
  Turing.TM2ComputableInPolyTime
    pairBitEncoding Computability.encodeBool verifier

noncomputable def IsNP (L : BitLanguage) : Bool :=
  @decide (
  ∃ (bound : Polynomial ℕ) (verifier : List Bool × List Bool → Bool),
    Nonempty (VerifierTM verifier) ∧
      ∀ x : List Bool,
        L x ↔ ∃ certificate : List Bool,
          certificate.length ≤ bound.eval x.length ∧
            verifier (x, certificate) = true
  ) (Classical.propDecidable _)

end

noncomputable section

open scoped BigOperators

namespace Comparator

export GapCVP (BitLanguage bitEncoding pairBitEncoding IsNP)

structure PromiseProblem where
  yes : BitLanguage
  no : BitLanguage
  disjoint : ∀ bits, yes bits → no bits → False

def gapCVP400Promise : PromiseProblem := by
  sorry

noncomputable def binaryNearestCodewordPromise : PromiseProblem := by
  sorry

noncomputable def binarySyndromeDecodingPromise : PromiseProblem := by
  sorry

noncomputable def finitePGapCVPPromise (p : ℚ) (hp : 1 ≤ p) : PromiseProblem := by
  sorry

structure PromiseReduction (language : BitLanguage) (problem : PromiseProblem) where
  map : List Bool → List Bool
  polynomial_time : Nonempty
    (BitTM map)
  completeness : ∀ input, language input → problem.yes (map input)
  soundness : ∀ input, ¬ language input → problem.no (map input)

def IsNPHardPromise (problem : PromiseProblem) : Bool :=
  @decide
    (∀ language : BitLanguage,
      IsNP language → Nonempty (PromiseReduction language problem))
    (Classical.propDecidable _)

theorem gapCVP400IsNPHard : IsNPHardPromise gapCVP400Promise := by
  sorry

theorem binaryNearestCodewordIsNPHard :
    IsNPHardPromise binaryNearestCodewordPromise := by
  sorry

theorem binarySyndromeDecodingIsNPHard :
    IsNPHardPromise binarySyndromeDecodingPromise := by
  sorry

theorem finitePNormGapCVPIsNPHard (p : ℚ) (hp : 1 ≤ p) :
    IsNPHardPromise (finitePGapCVPPromise p hp) := by
  sorry

end Comparator

end

end GapCVP

end

end

#check GapCVP.Comparator.gapCVP400IsNPHard
#check GapCVP.Comparator.binaryNearestCodewordIsNPHard
#check GapCVP.Comparator.binarySyndromeDecodingIsNPHard
#check GapCVP.Comparator.finitePNormGapCVPIsNPHard
#check GapCVP.Comparator.gapCVP400Promise
#check GapCVP.Comparator.binaryNearestCodewordPromise
#check GapCVP.Comparator.binarySyndromeDecodingPromise
#check GapCVP.Comparator.finitePGapCVPPromise
