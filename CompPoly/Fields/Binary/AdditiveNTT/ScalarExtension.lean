/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Executable

/-!
# Scalar extension of additive encoders

Twiddles commute with field embeddings. A coordinate projection linear over
that embedding commutes with each butterfly and with the complete encoder.
-/

@[expose] public section

namespace AdditiveNTT

section Twiddles

variable {K E : Type} [Field K] [Field E] {r ell rate : Nat}

/-- Binary subspace enumeration commutes with a field embedding. -/
theorem getUElements_map (φ : K →+* E) (β : Fin r → K) (i : Fin r) :
    getUElements (ℓ := ell) (R_rate := rate) (φ ∘ β) i =
      (getUElements (ℓ := ell) (R_rate := rate) β i).map φ := by
  simp only [getUElements, List.map_map, Function.comp_def]
  congr 1
  funext k
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  split <;> simp only [map_zero]

/-- Vanishing-polynomial evaluation commutes with field embeddings. -/
theorem evalWAt_map (φ : K →+* E) (β : Fin r → K) (i : Fin r) (x : K) :
    evalWAt (ℓ := ell) (R_rate := rate) (φ ∘ β) i (φ x) =
      φ (evalWAt (ℓ := ell) (R_rate := rate) β i x) := by
  unfold evalWAt
  rw [getUElements_map (ell := ell) (rate := rate)]
  simp only [List.map_map, Function.comp_def, map_list_prod, map_sub]

/-- Normalization commutes with the same embedding, including the denominator inverse. -/
theorem evalNormalizedWAt_map (φ : K →+* E) (β : Fin r → K) (i : Fin r) (x : K) :
    evalNormalizedWAt (ℓ := ell) (R_rate := rate) (φ ∘ β) i (φ x) =
      φ (evalNormalizedWAt (ℓ := ell) (R_rate := rate) β i x) := by
  simp only [evalNormalizedWAt, Function.comp_apply, evalWAt_map, map_mul, map_inv₀]

/-- The generic encoder's twiddle is preserved by scalar extension. -/
theorem computableTwiddleFactor_map (φ : K →+* E) (β : Fin r → K)
    (hd : ell + rate < r) (i : Fin ell) (u : Fin (2 ^ (ell + rate - i.val - 1))) :
    computableTwiddleFactor (ℓ := ell) (R_rate := rate) (φ ∘ β) hd i u =
      φ (computableTwiddleFactor (ℓ := ell) (R_rate := rate) β hd i u) := by
  simp only [computableTwiddleFactor, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  split
  · exact evalNormalizedWAt_map φ β _ _
  · exact (map_zero φ).symm

end Twiddles

section Projection

variable {K E F : Type} [Field K] [Field E] [Field F]
variable [Algebra F K] [Algebra F E] {r ell rate : Nat}
variable {β : Fin r → K} [Fact (LinearIndependent F β)]
variable (φ : K →+* E) [Fact (LinearIndependent F (φ ∘ β))]

/-- A scalar-linear projection commutes with a generic additive stage. -/
theorem computableNTTStage_project (π : E → K)
    (ha : ∀ a b, π (a + b) = π a + π b)
    (hm : ∀ a b, π (φ a * b) = a * π b)
    (hd : ell + rate < r) (i : Fin ell) (a : Fin (2 ^ (ell + rate)) → E) :
    π ∘ computableNTTStage (𝔽q := F) (φ ∘ β) hd i a =
      computableNTTStage (𝔽q := F) β hd i (π ∘ a) := by
  funext j
  simp only [computableNTTStage, Function.comp_apply,
    computableTwiddleFactor_map, apply_dite, ha, hm, ← map_one φ, ← map_add φ]
  split <;> rfl

/-- Coordinate projection commutes with the complete generic additive encoder. -/
theorem computableAdditiveNTT_project (π : E → K)
    (ha : ∀ a b, π (a + b) = π a + π b)
    (hm : ∀ a b, π (φ a * b) = a * π b)
    (hd : ell + rate < r) (a : Fin (2 ^ ell) → E) :
    π ∘ computableAdditiveNTT (𝔽q := F) (φ ∘ β) hd a =
      computableAdditiveNTT (𝔽q := F) β hd (π ∘ a) := by
  unfold computableAdditiveNTT
  simp only [Fin.foldl_eq_finRange_foldl]
  apply (List.foldl_hom (fun a => π ∘ a) _).symm
  intro b i
  exact (computableNTTStage_project φ π ha hm hd _ b).symm

end Projection

end AdditiveNTT
