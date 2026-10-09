import Lean
import Mathlib

namespace Ehrhart.BergmanJetDiagonalObservableLatticeIdentity
end Ehrhart.BergmanJetDiagonalObservableLatticeIdentity
namespace Ehrhart.BergmanJetDualGradientInverseTransport
end Ehrhart.BergmanJetDualGradientInverseTransport
namespace Ehrhart.BergmanJetPartitionEndpoint
end Ehrhart.BergmanJetPartitionEndpoint
namespace Ehrhart.BergmanJetPortmanteauActualVolumeBridge
end Ehrhart.BergmanJetPortmanteauActualVolumeBridge
namespace Ehrhart.BergmanJetRadialHaarWeakProbabilityLift
end Ehrhart.BergmanJetRadialHaarWeakProbabilityLift
namespace Ehrhart.BergmanJetTriangularLatticeConvergence
end Ehrhart.BergmanJetTriangularLatticeConvergence
namespace Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence
end Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence
namespace Ehrhart.BergmanMonomials
end Ehrhart.BergmanMonomials
namespace Ehrhart.BergmanNormalization
end Ehrhart.BergmanNormalization
namespace Ehrhart.LaplaceAsymptotics
end Ehrhart.LaplaceAsymptotics
namespace Ehrhart.LatticeAsymptotics
end Ehrhart.LatticeAsymptotics
namespace Ehrhart.MomentFirstVariation
end Ehrhart.MomentFirstVariation
namespace Ehrhart.MomentOptimizer
end Ehrhart.MomentOptimizer
namespace Ehrhart.MomentRegularity
end Ehrhart.MomentRegularity
namespace Ehrhart.MomentTargetGeodesic
end Ehrhart.MomentTargetGeodesic
namespace Ehrhart.MomentWeakFirstVariation
end Ehrhart.MomentWeakFirstVariation
namespace Ehrhart.TorusCharacters
end Ehrhart.TorusCharacters
section

noncomputable section

namespace Ehrhart

open Set MeasureTheory

open scoped BigOperators ENNReal

abbrev Space (n : ℕ) := Fin n → ℝ

def integerPoint (n : ℕ) (z : Fin n → ℤ) : Space n :=
  fun i => (z i : ℝ)

def standardSimplex (n : ℕ) : Set (Space n) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1}

def simplexDilation (n : ℕ) (x : Space n) : Space n :=
  fun i => ((n : ℝ) + 1) * x i - 1

def centeredSimplex (n : ℕ) : Set (Space n) :=
  simplexDilation n '' standardSimplex n

def normalizedVolume {n : ℕ} (K : Set (Space n)) : ℝ :=
  ((volume : Measure (Space n)) K).toReal

def barycenter {n : ℕ} (K : Set (Space n)) : Space n :=
  (normalizedVolume K)⁻¹ • ∫ x in K, x ∂(volume : Measure (Space n))

def interiorLatticePoints {n : ℕ} (K : Set (Space n)) : Set (Fin n → ℤ) :=
  {z | integerPoint n z ∈ interior K}

structure CenteredBody (n : ℕ) where
  carrier : Set (Space n)
  convex : Convex ℝ carrier
  compact : IsCompact carrier
  fullDimensional : (interior carrier).Nonempty
  centered : barycenter carrier = 0
  uniqueInteriorLatticePoint : interiorLatticePoints carrier = {0}

def sharpConstant (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ n / (n.factorial : ℝ)

namespace SimplexVolume

open Set MeasureTheory

open scoped BigOperators ENNReal Pointwise

theorem normalizedVolume_centeredSimplex (n : ℕ) (_hn : 0 < n) :
    normalizedVolume (centeredSimplex n) =
      sharpConstant n := by
  sorry

theorem barycenter_centeredSimplex (n : ℕ) :
    barycenter (centeredSimplex n) = 0 := by
  sorry

theorem exists_centeredBody_sharp (n : ℕ) (hn : 0 < n) :
    ∃ K : CenteredBody n,
      normalizedVolume K.carrier = sharpConstant n := by
  sorry

end SimplexVolume

namespace Volume

open Set Function Filter MeasureTheory

open TorusCharacters LatticeAsymptotics BergmanMonomials BergmanNormalization LaplaceAsymptotics

open MomentOptimizer MomentWeakFirstVariation MomentFirstVariation MomentTargetGeodesic

open MomentRegularity BergmanJetPartitionEndpoint BergmanJetTriangularLatticeConvergence

open BergmanJetDiagonalObservableLatticeIdentity BergmanJetDualGradientInverseTransport

open BergmanJetUpperTaggedMonomialObservableConvergence BergmanJetPortmanteauActualVolumeBridge

open BergmanJetRadialHaarWeakProbabilityLift

open scoped BigOperators ENNReal NNReal Topology BoundedContinuousFunction

theorem ehrhart_volume_inequality_for_sets {n : ℕ} (hn : 0 < n)
    (S : Set (Space n)) (hconvex : Convex ℝ S)
    (hcompact : IsCompact S) (hinterior : (interior S).Nonempty)
    (hcentered : barycenter S = 0)
    (hlattice : interiorLatticePoints S = {0}) :
    normalizedVolume S ≤ ((n : ℝ) + 1) ^ n / (n.factorial : ℝ) := by
  sorry

end Volume

end Ehrhart

end

end

#check Ehrhart.Volume.ehrhart_volume_inequality_for_sets
#check Ehrhart.SimplexVolume.exists_centeredBody_sharp
#check Ehrhart.SimplexVolume.barycenter_centeredSimplex
#check Ehrhart.SimplexVolume.normalizedVolume_centeredSimplex
