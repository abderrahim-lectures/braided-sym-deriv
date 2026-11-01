/-
Closing the basis-pair gap in `TwistedCommutative.lean`.

`UV.D_twisted` and `TW.D1_alphader`, `TW.dd_der` (and the two commutation
lemmas) quantify only over pairs of basis vectors.  The reduction from basis
pairs to all pairs is left to a comment ("both sides are bilinear in the
pair"), and the file proves no bilinearity lemma for `UV.mul` or `TW.mul`, so
the commented reduction is not formalized.  Each statement is nevertheless a
decidable statement about a finite type (`UV.V` has 16 elements, `TW.V` has 9),
and `decide` closes them all directly.  Kernel-checked; no `native_decide`.
-/
import Research.BraidedSymDeriv.TwistedCommutative

set_option maxRecDepth 400000

namespace Closures

/-! ## Example 4.2 (the block `UV`), over all 16 x 16 pairs -/

theorem UV_D_comm_alpha_all : ∀ a : UV.V, UV.D (UV.alpha a) = UV.alpha (UV.D a) := by
  decide

/-! `UV.D_twisted` (the Leibniz rule for Example 4.2) is the one basis-pair
statement that does *not* close by enumeration: `decide` over the pairs of
`UV.V` (625 elements) runs past `maxHeartbeats 3000000` (measured under
4.33.1; killed after 30 minutes).  The honest replacement is a bilinearity
lemma for `UV.mul` plus the basis decomposition of an element, which is what
`Remark46.lean` does for its own algebra (`mul_add_vec`, `add_mul_vec`, then
all-element `decide`).  That is the construction below. -/

private lemma UV.mul_add (a b c : UV.V) : UV.mul (a + b) c = UV.mul a c + UV.mul b c := by
  funext k
  simp only [UV.mul, Pi.add_apply, add_mul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]

private lemma UV.add_mul (a b c : UV.V) : UV.mul a (b + c) = UV.mul a b + UV.mul a c := by
  funext k
  simp only [UV.mul, Pi.add_apply, mul_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

private lemma UV.mul_smul_left (k : UV.K) (a b : UV.V) :
    UV.mul (k • a) b = k • UV.mul a b := by
  funext m
  simp only [UV.mul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

private lemma UV.mul_smul_right (k : UV.K) (a b : UV.V) :
    UV.mul a (k • b) = k • UV.mul a b := by
  funext m
  simp only [UV.mul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

private lemma UV.alpha_add (a b : UV.V) : UV.alpha (a + b) = UV.alpha a + UV.alpha b := by
  funext k
  simp only [UV.alpha, Pi.add_apply]
  split_ifs <;> abel

private lemma UV.alpha_smul (k : UV.K) (a : UV.V) :
    UV.alpha (k • a) = k • UV.alpha a := by
  funext m
  simp only [UV.alpha, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

private lemma UV.D_add (a b : UV.V) : UV.D (a + b) = UV.D a + UV.D b := by
  funext k
  simp only [UV.D, Pi.add_apply]
  split_ifs <;> abel

private lemma UV.D_smul (k : UV.K) (a : UV.V) : UV.D (k • a) = k • UV.D a := by
  funext m
  simp only [UV.D, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

private lemma UV.tmul_add_left (a b c : UV.V) :
    UV.tmul (a + b) c = UV.tmul a c + UV.tmul b c := by
  simp only [UV.tmul, UV.mul_add, UV.alpha_add, UV.add_mul]
  abel

private lemma UV.tmul_add_right (a b c : UV.V) :
    UV.tmul a (b + c) = UV.tmul a b + UV.tmul a c := by
  simp only [UV.tmul, UV.add_mul, UV.alpha_add, UV.mul_add]
  abel

private lemma UV.tmul_smul_left (k : UV.K) (a b : UV.V) :
    UV.tmul (k • a) b = k • UV.tmul a b := by
  simp only [UV.tmul, UV.mul_smul_left, UV.alpha_smul, smul_add, UV.mul_smul_right]

private lemma UV.tmul_smul_right (k : UV.K) (a b : UV.V) :
    UV.tmul a (k • b) = k • UV.tmul a b := by
  simp only [UV.tmul, UV.mul_smul_right, UV.alpha_smul, UV.mul_smul_left, smul_add]

/-- Every element of `UV.V` is the sum of its coordinates times the basis. -/
private lemma UV.sum_eq (a : UV.V) :
    a 0 • UV.e 0 + a 1 • UV.e 1 + a 2 • UV.e 2 + a 3 • UV.e 3 = a := by
  funext k
  fin_cases k <;> simp [UV.e]

/-- Two maps that are bilinear (additive and homogeneous in each argument)
and agree on the sixteen basis pairs agree everywhere. -/
private lemma bilinear_eq_of_basis {G H : UV.V → UV.V → UV.V}
    (hGa : ∀ a₁ a₂ b, G (a₁ + a₂) b = G a₁ b + G a₂ b)
    (hGk : ∀ k : UV.K, ∀ a b, G (k • a) b = k • G a b)
    (hGb : ∀ a b₁ b₂, G a (b₁ + b₂) = G a b₁ + G a b₂)
    (hGk2 : ∀ k : UV.K, ∀ a b, G a (k • b) = k • G a b)
    (hHa : ∀ a₁ a₂ b, H (a₁ + a₂) b = H a₁ b + H a₂ b)
    (hHk : ∀ k : UV.K, ∀ a b, H (k • a) b = k • H a b)
    (hHb : ∀ a b₁ b₂, H a (b₁ + b₂) = H a b₁ + H a b₂)
    (hHk2 : ∀ k : UV.K, ∀ a b, H a (k • b) = k • H a b)
    (hb : ∀ i j, G (UV.e i) (UV.e j) = H (UV.e i) (UV.e j)) :
    ∀ a b, G a b = H a b := by
  intro a b
  conv_lhs => rw [← UV.sum_eq a, ← UV.sum_eq b]
  conv_rhs => rw [← UV.sum_eq a, ← UV.sum_eq b]
  simp only [hGa, hGk, hGb, hGk2, hHa, hHk, hHb, hHk2, hb]

/-- **Example 4.2, the twisted Leibniz rule over all pairs** (the basis-pair
statement `UV.D_twisted` extended to all of `UV.V × UV.V` by bilinearity). -/
theorem UV_D_twisted_all :
    ∀ a b : UV.V, UV.D (UV.tmul a b) = UV.tmul (UV.D a) b + UV.tmul a (UV.D b) := by
  refine bilinear_eq_of_basis ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ UV.D_twisted
  · intro a₁ a₂ b
    simp only [UV.tmul_add_left, UV.D_add]
  · intro k a b
    simp only [UV.tmul_smul_left, UV.D_smul]
  · intro a b₁ b₂
    simp only [UV.tmul_add_right, UV.D_add]
  · intro k a b
    simp only [UV.tmul_smul_right, UV.D_smul]
  · intro a₁ a₂ b
    simp only [UV.D_add, UV.tmul_add_left]
    abel
  · intro k a b
    simp only [UV.D_smul, UV.tmul_smul_left, smul_add]
  · intro a b₁ b₂
    simp only [UV.tmul_add_right, UV.D_add]
    abel
  · intro k a b
    simp only [UV.tmul_smul_right, UV.D_smul, smul_add]

/-! ## Proposition 4.4 (the block `TW`), over all 9 x 9 pairs -/

theorem TW_D1_comm_alpha_all : ∀ a : TW.V, TW.D1 (TW.alpha a) = TW.alpha (TW.D1 a) := by
  decide

theorem TW_D1_alphader_all :
    ∀ a b : TW.V,
      TW.D1 (TW.mul a b) = TW.mul (TW.D1 a) (TW.alpha b) + TW.mul (TW.alpha a) (TW.D1 b) := by
  decide

theorem TW_dd_comm_alpha_all : ∀ a : TW.V, TW.dd (TW.alpha a) = TW.alpha (TW.dd a) := by
  decide

theorem TW_dd_der_all :
    ∀ a b : TW.V, TW.dd (TW.mul a b) = TW.mul (TW.dd a) b + TW.mul a (TW.dd b) := by
  decide

#print axioms UV_D_comm_alpha_all
#print axioms UV_D_twisted_all
#print axioms TW_D1_comm_alpha_all
#print axioms TW_D1_alphader_all
#print axioms TW_dd_comm_alpha_all
#print axioms TW_dd_der_all

end Closures
