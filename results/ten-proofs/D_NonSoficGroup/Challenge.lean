import Lean
import Mathlib

namespace SoficGroups.KunLiteralNineSourceFiniteModels
end SoficGroups.KunLiteralNineSourceFiniteModels
namespace SoficGroups.SourceTopLevelCompression
end SoficGroups.SourceTopLevelCompression
section

noncomputable section

namespace SoficGroups

section

open Filter Topology

universe u v w

open scoped Pointwise commutatorElement symmDiff

def normalizedHamming {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p q : Equiv.Perm Y) : ℝ :=
  (hammingDist (fun y => p y) (fun y => q y) : ℝ) / Fintype.card Y

structure PermutationModel (G : Type*) [Group G] where
  size : ℕ
  size_pos : 0 < size
  action : G → Equiv.Perm (Fin size)
  map_one : action 1 = 1

structure GoodOn {G : Type*} [Group G]
    (M : PermutationModel G) (F : Finset G) (ε : ℝ) : Prop where
  multiplicative : ∀ g ∈ F, ∀ h ∈ F,
    normalizedHamming (M.action (g * h)) (M.action g * M.action h) < ε
  separated : ∀ g ∈ F, g ≠ 1 →
    1 - ε < normalizedHamming (M.action g) 1

class Sofic (G : Type*) [Group G] : Prop where
  approximation : ∀ (F : Finset G) (ε : ℝ), 0 < ε → ε < 1 →
    ∃ M : PermutationModel G, GoodOn M F ε

universe u₁ u₂ u₃

end

namespace SourceTopLevelCompressionFinal

open SoficGroups.SourceTopLevelCompression

open SoficGroups.KunLiteralNineSourceFiniteModels

theorem exists_finitelyPresented_nonsofic_group :
    ∃ (G : Type) (_ : Group G),
      Group.IsFinitelyPresented G ∧ ¬ SoficGroups.Sofic G := by
  sorry

end SourceTopLevelCompressionFinal

end SoficGroups

end

end

#check SoficGroups.SourceTopLevelCompressionFinal.exists_finitelyPresented_nonsofic_group
