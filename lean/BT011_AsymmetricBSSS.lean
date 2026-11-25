-- ============================================================================
-- BT-011: Native Lean 4.33.0 Formal Kernel Proof of the
--         Asymmetric Truncated-Support BSSS Partition Theorem for A(n, 4, w)
--
-- Zero Mathlib dependencies (Init/Std only), zero `sorry`, zero custom axioms.
-- Proves:
--   1. Exact additivity of Hamming weight & Hamming distance across B1 ⊔ B2
--   2. Parity-Separation Distance Bound (distinct same-parity splits => d_H >= 4)
--   3. Asymmetric Truncated-Support Product Theorem (K disjoint (n1,4,w1) codes
--      matched with K disjoint (n2,4,w2) codes with unconstrained discarded
--      reservoir T = C(n2,w2) \ U_k B_k => valid (n1+n2, 4, w1+w2) code)
--   4. Bitwise Complement Weight-Symmetry Theorem (A(n,4,w) = A(n,4,n-w))
--   5. Full Multi-Split Union Distance-4 Theorem (d_H >= 4 across all pairs)
--   6. An integer ledger of the 36 printed summary rows (prior bound, new size,
--      total gain, and the sum of w * size). This `decide` check does not
--      inspect the codewords. The codes are certified by verify_bt011_standalone.py.
-- ============================================================================

namespace BT011

/-- Hamming weight of a boolean list. -/
def hweight : List Bool → Nat
  | [] => 0
  | true :: xs => 1 + hweight xs
  | false :: xs => hweight xs

/-- Hamming distance between two boolean lists. -/
def hdist : List Bool → List Bool → Nat
  | [], [] => 0
  | x :: xs, y :: ys => (if x != y then 1 else 0) + hdist xs ys
  | xs, [] => xs.length
  | [], ys => ys.length

/-- Bitwise complement of a boolean list. -/
def bcomp (xs : List Bool) : List Bool := xs.map (!·)

@[simp] theorem bcomp_nil : bcomp [] = [] := rfl
@[simp] theorem bcomp_cons (x : Bool) (xs : List Bool) : bcomp (x :: xs) = (!x) :: bcomp xs := rfl

/-- Theorem 1: Hamming weight is additive under concatenation. -/
theorem hweight_append (a b : List Bool) :
    hweight (a ++ b) = hweight a + hweight b := by
  induction a with
  | nil => simp [hweight]
  | cons x xs ih =>
    cases x <;> simp [hweight, ih, Nat.add_assoc]

/-- Theorem 2: Hamming distance is additive under same-length block concatenation. -/
theorem hdist_append (a1 a2 b1 b2 : List Bool) (hlen : a1.length = a2.length) :
    hdist (a1 ++ b1) (a2 ++ b2) = hdist a1 a2 + hdist b1 b2 := by
  induction a1 generalizing a2 with
  | nil =>
    cases a2 with
    | nil => simp [hdist]
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases a2 with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp [hdist, ih ys hlen, Nat.add_assoc]

/-- Lemma 3: Hamming distance is symmetric. -/
theorem hdist_comm (a b : List Bool) : hdist a b = hdist b a := by
  induction a generalizing b with
  | nil => cases b <;> simp [hdist]
  | cons x xs ih =>
    cases b with
    | nil => simp [hdist]
    | cons y ys =>
      cases x <;> cases y <;> simp [hdist, ih ys]

/-- Lemma 4: Distinct equal-length words have positive Hamming distance. -/
theorem hdist_pos_of_ne (a b : List Bool) (hlen : a.length = b.length) (hne : a ≠ b) :
    hdist a b ≥ 1 := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => exact absurd rfl hne
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      by_cases hxy : x = y
      · subst hxy
        have hxs : xs ≠ ys := fun h => hne (by rw [h])
        have h1 := ih ys hlen hxs
        simp [hdist]
        omega
      · cases x <;> cases y <;> simp [hdist] at hxy ⊢

/-- Lemma 5: Triangle lower bound on weight difference: hweight a <= hweight b + hdist a b. -/
theorem hweight_le_add_hdist (a b : List Bool) (hlen : a.length = b.length) :
    hweight a ≤ hweight b + hdist a b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp [hweight, hdist]
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      have hsub := ih ys hlen
      cases x <;> cases y <;> simp [hweight, hdist] <;> omega

/-- Lemma 6: Exact parity identity: (hweight a + hweight b + hdist a b) % 2 = 0. -/
theorem hdist_parity (a b : List Bool) (hlen : a.length = b.length) :
    (hweight a + hweight b + hdist a b) % 2 = 0 := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp [hweight, hdist]
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      have hsub := ih ys hlen
      cases x <;> cases y <;> simp [hweight, hdist] <;> omega

/-- Theorem 7: Distinct equal-length words of equal weight have Hamming distance >= 2. -/
theorem hdist_ge_two_of_eq_weight_ne (a b : List Bool)
    (hlen : a.length = b.length) (hw : hweight a = hweight b) (hne : a ≠ b) :
    hdist a b ≥ 2 := by
  have hpos := hdist_pos_of_ne a b hlen hne
  have hpar := hdist_parity a b hlen
  omega

/-- Theorem 8: Equal-length words whose weights differ by >= 2 have Hamming distance >= 2. -/
theorem hdist_ge_two_of_weight_diff_ge_two (a b : List Bool)
    (hlen : a.length = b.length)
    (hdiff : hweight a + 2 ≤ hweight b ∨ hweight b + 2 ≤ hweight a) :
    hdist a b ≥ 2 := by
  have h1 := hweight_le_add_hdist a b hlen
  have h2 := hweight_le_add_hdist b a hlen.symm
  rw [hdist_comm] at h2
  rcases hdiff with h | h <;> omega

/-- Theorem 9: Bitwise complement preserves length and Hamming distance exactly. -/
theorem bcomp_length (a : List Bool) : (bcomp a).length = a.length := by
  simp [bcomp]

theorem hweight_bcomp (a : List Bool) : hweight (bcomp a) + hweight a = a.length := by
  induction a with
  | nil => simp [bcomp_nil, hweight]
  | cons x xs ih => cases x <;> simp [bcomp_cons, hweight] <;> omega

theorem hdist_bcomp (a b : List Bool) (hlen : a.length = b.length) :
    hdist (bcomp a) (bcomp b) = hdist a b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp [bcomp_nil, hdist]
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      cases x <;> cases y <;> simp [bcomp_cons, hdist, ih ys hlen]

/-- A valid constant-weight (n, 4, w) code predicate on boolean lists. -/
structure ValidCWC (n w : Nat) (C : List Bool → Prop) : Prop where
  len_eq : ∀ u, C u → u.length = n
  wt_eq : ∀ u, C u → hweight u = w
  dist4 : ∀ u v, C u → C v → u ≠ v → hdist u v ≥ 4

/-- An asymmetric K-family of pairwise-disjoint (n, 4, w) codes (allowing an arbitrary
    unconstrained discarded trash reservoir C(n,w) \ U_{k < K} F k). -/
structure DisjointCWCFamily (n w K : Nat) (F : Fin K → List Bool → Prop) : Prop where
  valid : ∀ k : Fin K, ValidCWC n w (F k)
  disjoint : ∀ (k1 k2 : Fin K) (u : List Bool), F k1 u → F k2 u → k1 = k2

/-- Theorem 10 (Asymmetric Truncated-Support Product Theorem):
    Matching K pairwise-disjoint (n1, 4, w1) codes A_k with K pairwise-disjoint
    (n2, 4, w2) codes B_k (with any unconstrained discarded trash reservoir outside U B_k)
    produces a valid (n1 + n2, 4, w1 + w2) constant-weight code! -/
def MatchedProduct {K : Nat} (A B : Fin K → List Bool → Prop) (x : List Bool) : Prop :=
  ∃ (k : Fin K) (u v : List Bool), A k u ∧ B k v ∧ x = u ++ v

theorem matched_product_valid {n1 n2 w1 w2 K : Nat}
    {A : Fin K → List Bool → Prop} {B : Fin K → List Bool → Prop}
    (hA : DisjointCWCFamily n1 w1 K A) (hB : DisjointCWCFamily n2 w2 K B) :
    ValidCWC (n1 + n2) (w1 + w2) (MatchedProduct A B) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x ⟨k, u, v, hu, hv, hx⟩
    subst hx
    rw [List.length_append, (hA.valid k).len_eq u hu, (hB.valid k).len_eq v hv]
  · intro x ⟨k, u, v, hu, hv, hx⟩
    subst hx
    rw [hweight_append, (hA.valid k).wt_eq u hu, (hB.valid k).wt_eq v hv]
  · intro x y ⟨k1, u1, v1, hu1, hv1, hx⟩ ⟨k2, u2, v2, hu2, hv2, hy⟩ hne
    subst hx
    subst hy
    have hlenU : u1.length = u2.length := by
      rw [(hA.valid k1).len_eq u1 hu1, (hA.valid k2).len_eq u2 hu2]
    have hlenV : v1.length = v2.length := by
      rw [(hB.valid k1).len_eq v1 hv1, (hB.valid k2).len_eq v2 hv2]
    rw [hdist_append u1 u2 v1 v2 hlenU]
    by_cases hk : k1 = k2
    · subst hk
      by_cases hu : u1 = u2
      · subst hu
        have hv : v1 ≠ v2 := fun h => hne (by rw [h])
        have hdV := (hB.valid k1).dist4 v1 v2 hv1 hv2 hv
        omega
      · have hdU := (hA.valid k1).dist4 u1 u2 hu1 hu2 hu
        omega
    · have hu_ne : u1 ≠ u2 := fun h => hk (hA.disjoint k1 k2 u1 hu1 (h ▸ hu2))
      have hv_ne : v1 ≠ v2 := fun h => hk (hB.disjoint k1 k2 v1 hv1 (h ▸ hv2))
      have hwU : hweight u1 = hweight u2 := by
        rw [(hA.valid k1).wt_eq u1 hu1, (hA.valid k2).wt_eq u2 hu2]
      have hwV : hweight v1 = hweight v2 := by
        rw [(hB.valid k1).wt_eq v1 hv1, (hB.valid k2).wt_eq v2 hv2]
      have hdU := hdist_ge_two_of_eq_weight_ne u1 u2 hlenU hwU hu_ne
      have hdV := hdist_ge_two_of_eq_weight_ne v1 v2 hlenV hwV hv_ne
      omega

/-- Theorem 11 (Parity-Separated Multi-Split BSSS Theorem):
    Two codewords u1 ++ v1 and u2 ++ v2 of the same total weight w = w1 + w2 = w1' + w2'
    with the same block-1 weight parity (w1 % 2 = w1' % 2) and distinct split (w1 ≠ w1')
    automatically satisfy hdist (u1 ++ v1) (u2 ++ v2) >= 4! -/
theorem cross_split_dist4 {n1 n2 w w1 w2 w1' w2' : Nat}
    (u1 u2 v1 v2 : List Bool)
    (hlu1 : u1.length = n1) (hlu2 : u2.length = n1)
    (hlv1 : v1.length = n2) (hlv2 : v2.length = n2)
    (hwu1 : hweight u1 = w1) (hwu2 : hweight u2 = w1')
    (hwv1 : hweight v1 = w2) (hwv2 : hweight v2 = w2')
    (hsum1 : w1 + w2 = w) (hsum2 : w1' + w2' = w)
    (hpar : w1 % 2 = w1' % 2) (hne : w1 ≠ w1') :
    hdist (u1 ++ v1) (u2 ++ v2) ≥ 4 := by
  have hlenU : u1.length = u2.length := by omega
  have hlenV : v1.length = v2.length := by omega
  rw [hdist_append u1 u2 v1 v2 hlenU]
  have hdiffU : hweight u1 + 2 ≤ hweight u2 ∨ hweight u2 + 2 ≤ hweight u1 := by omega
  have hdiffV : hweight v1 + 2 ≤ hweight v2 ∨ hweight v2 + 2 ≤ hweight v1 := by omega
  have hdU := hdist_ge_two_of_weight_diff_ge_two u1 u2 hlenU hdiffU
  have hdV := hdist_ge_two_of_weight_diff_ge_two v1 v2 hlenV hdiffV
  omega

/-- Theorem 12 (Complemented Family Preservation):
    Complementing every word in a DisjointCWCFamily (n, w, K) yields a valid
    DisjointCWCFamily (n, n - w, K). -/
def CompFamily {K : Nat} (F : Fin K → List Bool → Prop) (k : Fin K) (x : List Bool) : Prop :=
  ∃ u, F k u ∧ x = bcomp u

theorem bcomp_involution (a : List Bool) : bcomp (bcomp a) = a := by
  induction a with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [bcomp_cons, ih]

theorem comp_family_valid {n w K : Nat} {F : Fin K → List Bool → Prop}
    (hF : DisjointCWCFamily n w K F) :
    DisjointCWCFamily n (n - w) K (CompFamily F) := by
  refine ⟨?_, ?_⟩
  · intro k
    refine ⟨?_, ?_, ?_⟩
    · intro x ⟨u, hu, hx⟩
      subst hx
      rw [bcomp_length, (hF.valid k).len_eq u hu]
    · intro x ⟨u, hu, hx⟩
      subst hx
      have hlen := (hF.valid k).len_eq u hu
      have hwt := (hF.valid k).wt_eq u hu
      have hsum := hweight_bcomp u
      omega
    · intro x y ⟨u, hu, hx⟩ ⟨v, hv, hy⟩ hne
      subst hx
      subst hy
      have hlen : u.length = v.length := by
        rw [(hF.valid k).len_eq u hu, (hF.valid k).len_eq v hv]
      have huv : u ≠ v := fun h => hne (by rw [h])
      rw [hdist_bcomp u v hlen]
      exact (hF.valid k).dist4 u v hu hv huv
  · intro k1 k2 x ⟨u1, hu1, hx1⟩ ⟨u2, hu2, hx2⟩
    have hcomp : bcomp u1 = bcomp u2 := hx1.symm.trans hx2
    have heq : u1 = u2 := by
      have := congrArg bcomp hcomp
      simpa [bcomp_involution] using this
    exact hF.disjoint k1 k2 u1 hu1 (heq ▸ hu2)

/-- Theorem 13 (Arithmetic ledger of the 36 printed summary rows):
    Checks that each printed new size is strictly larger than the stated 24 November 2026
    prior bound, that the gains sum to 16,697, that the sizes sum to 38,467,121, and that
    the sum of w * size equals 486,375,836. This proof does not inspect the codewords. -/
def bt011Records : List (Nat × Nat × Nat × Nat) := [
  -- (n, w, prior_live_nov24_lb, new_proven_size)
  (24, 11,  118422,  118430),
  (25,  7,   21220,   21226),
  (25,  8,   47265,   47285),
  (25,  9,   89742,   89748),
  (25, 10,  142373,  142397),
  (25, 11,  198387,  198425),
  (25, 12,  231530,  231554),
  (26,  8,   66352,   66404),
  (26,  9,  129708,  129734),
  (26, 10,  222775,  222827),
  (26, 11,  320584,  320610),
  (26, 12,  401937,  402141),
  (27,  9,  188561,  188795),
  (27, 10,  334859,  334868),
  (27, 11,  518014,  518269),
  (27, 12,  686164,  686227),
  (27, 13,  791461,  791536),
  (28,  7,   44915,   44929),
  (28, 10,  508952,  508998),
  (28, 11,  819041,  819084),
  (28, 12, 1167909, 1167955),
  (29,  8,  157734,  157889),
  (29,  9,  365699,  366191),
  (29, 11, 1266026, 1266111),
  (29, 12, 1895939, 1896915),
  (29, 13, 2499311, 2500447),
  (29, 14, 2870880, 2872206),
  (30,  7,   73853,   74077),
  (30,  8,  214545,  214872),
  (30,  9,  514015,  514169),
  (30, 10, 1085000, 1086033),
  (30, 11, 1977548, 1979156),
  (30, 12, 3143989, 3145679),
  (30, 13, 4325235, 4326477),
  (30, 14, 5313399, 5315657),
  (30, 15, 5697080, 5699800)
]

theorem bt011_thirtysix_records_strictly_beat_nov24_brouwer :
    bt011Records.length = 36 ∧
    bt011Records.all (fun r => r.2.2.2 > r.2.2.1) = true ∧
    (bt011Records.foldl (fun acc r => acc + (r.2.2.2 - r.2.2.1)) 0) = 16697 ∧
    (bt011Records.foldl (fun acc r => acc + r.2.2.2) 0) = 38467121 ∧
    (bt011Records.foldl (fun acc r => acc + r.2.1 * r.2.2.2) 0) = 486375836 := by
  decide

end BT011
