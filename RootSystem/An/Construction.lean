import Mathlib

abbrev Zn (n : ℕ) [NeZero n] := Fin n → ℤ
abbrev Zn_dual (n : ℕ) [NeZero n] := Module.Dual ℤ (Zn n)

def e_transpose {n : ℕ} [NeZero n] (k : Fin n) : Zn_dual n :=
  { toFun := fun t => t k
    map_add' := by intro t s; rfl
    map_smul' := by intro a t; rfl }

def Ae {n : ℕ} [NeZero n] (k : Fin n) : Zn n :=
  fun t =>
    if t = k then 2
    else if (k : ℕ) + 1 = (t : ℕ) ∨ (t : ℕ) + 1 = (k : ℕ) then -1
    else 0

structure SignedInterval (n : ℕ) where
  i : Fin n
  j : Fin n
  hij : i ≤ j
  ε : Bool

def SignedInterval.sign {n : ℕ} (J : SignedInterval n) : ℤ :=
  if J.ε then 1 else -1

def α {n : ℕ} [NeZero n] (J : SignedInterval n) : Zn n :=
  J.sign • Finset.sum (Finset.Icc J.i J.j) (fun k => Ae k)

def α_dual {n : ℕ} [NeZero n] (J : SignedInterval n) : Zn_dual n :=
  J.sign • Finset.sum (Finset.Icc J.i J.j) (fun k => e_transpose k)

/-- The reflection permutation for signed intervals.
    For positive intervals J = [i,j] and K = [k,l]:
    - If (i,j) = (k,l): returns -[k,l]
    - If i = l+1: returns [k,j]   (merge: K then J)
    - If k = j+1: returns [i,l]   (merge: J then K)
    - If i = k, j > l: returns -[l+1, j]
    - If i = k, j < l: returns [j+1, l]
    - If i < k, j = l: returns -[i, k-1]
    - If i > k, j = l: returns [k, i-1]
    - Otherwise: returns [k,l]
    Then s_{-J} = s_J and s_J(-K) = -s_J(K). -/
def s {n : ℕ} [NeZero n] (J K : SignedInterval n) : SignedInterval n :=
  -- The sign of the output: if K is negative, flip the unsigned result sign
  let signAdj (b : Bool) : Bool := if K.ε then b else !b
  if h₀ : J.i = K.i ∧ J.j = K.j then
    { i := K.i, j := K.j, hij := K.hij, ε := signAdj false }
  else if h₁ : (J.i : ℕ) = (K.j : ℕ) + 1 then
    { i := K.i
      j := J.j
      hij := by
        have hKi : (K.i : ℕ) ≤ K.j := Fin.le_iff_val_le_val.mp K.hij
        have hJi : (J.i : ℕ) ≤ J.j := Fin.le_iff_val_le_val.mp J.hij
        exact Fin.le_iff_val_le_val.mpr (by omega)
      ε := signAdj true }
  else if h₂ : (K.i : ℕ) = (J.j : ℕ) + 1 then
    { i := J.i
      j := K.j
      hij := by
        have hJi : (J.i : ℕ) ≤ J.j := Fin.le_iff_val_le_val.mp J.hij
        have hKj : (K.i : ℕ) ≤ K.j := Fin.le_iff_val_le_val.mp K.hij
        exact Fin.le_iff_val_le_val.mpr (by omega)
      ε := signAdj true }
  else if h₃ : J.i = K.i ∧ (J.j : ℕ) > (K.j : ℕ) then
    { i := ⟨(K.j : ℕ) + 1, by have := J.j.isLt; omega⟩
      j := J.j
      hij := by simp only [Fin.le_iff_val_le_val, Fin.val_mk]; omega
      ε := signAdj false }
  else if h₄ : J.i = K.i ∧ (J.j : ℕ) < (K.j : ℕ) then
    { i := ⟨(J.j : ℕ) + 1, by have := K.j.isLt; omega⟩
      j := K.j
      hij := by simp only [Fin.le_iff_val_le_val, Fin.val_mk]; omega
      ε := signAdj true }
  else if h₅ : (J.i : ℕ) < (K.i : ℕ) ∧ J.j = K.j then
    { i := J.i
      j := ⟨(K.i : ℕ) - 1, by have := K.i.isLt; omega⟩
      hij := by simp only [Fin.le_iff_val_le_val, Fin.val_mk]; omega
      ε := signAdj false }
  else if h₆ : (J.i : ℕ) > (K.i : ℕ) ∧ J.j = K.j then
    { i := K.i
      j := ⟨(J.i : ℕ) - 1, by have := J.i.isLt; omega⟩
      hij := by simp only [Fin.le_iff_val_le_val, Fin.val_mk]; omega
      ε := signAdj true }
  else
    { i := K.i, j := K.j, hij := K.hij, ε := signAdj true }

noncomputable abbrev Zn_pairing (n : ℕ) [NeZero n] : Zn n →ₗ[ℤ] Zn_dual n →ₗ[ℤ] ℤ :=
  Module.Dual.eval ℤ (Zn n)

-- Helper: SignedInterval extensional equality
@[ext]
theorem SignedInterval.ext' {n : ℕ} {J K : SignedInterval n}
    (hi : J.i = K.i) (hj : J.j = K.j) (hε : J.ε = K.ε) : J = K := by
  cases J; cases K; simp_all

/-
s is involutive
-/
theorem s_involutive {n : ℕ} [NeZero n] (J K : SignedInterval n) :
    s J (s J K) = K := by
  cases J ; cases K ; simp +decide [ s ];
  rename_i k l hk hl;
  rename_i i j hij ε;
  by_cases hi : i.val = l.val + 1 <;> by_cases hj : k.val = j.val + 1 <;> simp +decide [ hi, hj ];
  · grind;
  · grind +locals;
  · grind;
  · by_cases hi : i = k <;> by_cases hj : j = l <;> simp +decide [ hi, hj ] at *;
    · by_cases h : l < j <;> by_cases h' : j < l <;> simp +decide [ h, h' ] at *;
      · grind;
      · grind;
      · grind;
      · grind;
    · by_cases h : i < k <;> simp +decide [ h ] at *;
      · grind;
      · grind;
    · aesop

/-
The key formula: sum of Ae columns over an interval [p,q] evaluated at t
    gives δ_{t,p} + δ_{t,q} - δ_{t+1,p} - δ_{q+1,t} (using ℕ comparisons).
-/
theorem Ae_sum_eq {n : ℕ} [NeZero n] (p q : Fin n) (hpq : p ≤ q) (t : Fin n) :
    (∑ u ∈ Finset.Icc p q, Ae u) t =
    (if t = p then 1 else 0) + (if t = q then 1 else 0)
    - (if (t : ℕ) + 1 = (p : ℕ) then 1 else 0)
    - (if (q : ℕ) + 1 = (t : ℕ) then 1 else 0) := by
  induction' q with q hq generalizing p t;
  induction' q with q ih generalizing p t;
  · rcases t with ⟨ _ | _ | t, ht ⟩ <;> simp_all +decide [ Ae ];
  · by_cases hpq' : p = ⟨ q + 1, hq ⟩ <;> simp_all +decide [ Finset.sum_apply, Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
    · unfold Ae; split_ifs <;> simp_all +decide [ Fin.ext_iff ] ;
      linarith;
    · rw [ show ( Finset.Icc p ⟨ q + 1, hq ⟩ : Finset ( Fin n ) ) = Finset.Icc p ⟨ q, by linarith ⟩ ∪ { ⟨ q + 1, hq ⟩ } from ?_, Finset.sum_union ] <;> norm_num;
      · rw [ ih ( by linarith ) p ( Nat.le_of_lt_succ ( hpq.lt_of_ne hpq' ) ) t ];
        unfold Ae; simp +decide [ Fin.ext_iff ] ;
        grind;
      · grind

/-
Key consequence of Ae_sum_eq: α(J)(t) expressed in terms of Kronecker deltas
-/
theorem α_eval {n : ℕ} [NeZero n] (J : SignedInterval n) (t : Fin n) :
    α J t = J.sign * ((if t = J.i then 1 else 0) + (if t = J.j then 1 else 0)
    - (if (t : ℕ) + 1 = (J.i : ℕ) then 1 else 0)
    - (if (J.j : ℕ) + 1 = (t : ℕ) then 1 else 0)) := by
  have := @Ae_sum_eq;
  convert congr_arg ( fun x : ℤ => J.sign * x ) ( this J.i J.j J.hij t ) using 1

/-
Key consequence: α_dual(J) evaluated on a test function
-/
theorem α_dual_eval {n : ℕ} [NeZero n] (J : SignedInterval n) (f : Zn n) :
    α_dual J f = J.sign * ∑ v ∈ Finset.Icc J.i J.j, f v := by
  unfold α_dual; simp +decide [ Finset.mul_sum _ _ _, mul_assoc ] ; ring;
  rfl

/-
Pairing computation: L(α K, α^v J) in terms of interval endpoints
-/
theorem pairing_formula {n : ℕ} [NeZero n] (J K : SignedInterval n) :
    (Zn_pairing n (α K)) (α_dual J) = J.sign * K.sign *
    ((if J.i = K.i then 1 else 0) + (if J.j = K.j then 1 else 0)
    - (if (J.i : ℕ) = (K.j : ℕ) + 1 then 1 else 0)
    - (if (K.i : ℕ) = (J.j : ℕ) + 1 then 1 else 0)) := by
  -- By definition of $α_dual$, we know that $\alpha_dual J (α K) = J.sign * \sum_{v \in [J.i, J.j]} (α K)(v)$.
  have h_dual : (Zn_pairing n (α K)) (α_dual J) = J.sign * ∑ v ∈ Finset.Icc J.i J.j, (α K) v := by
    convert α_dual_eval J ( α K ) using 1;
  simp_all +decide [ mul_assoc, α_eval ];
  have h_simplify3 : ∑ x ∈ Finset.Icc J.i J.j, (if (x : ℕ) + 1 = (K.i : ℕ) then 1 else 0) = if (J.i : ℕ) + 1 ≤ (K.i : ℕ) ∧ (K.i : ℕ) ≤ (J.j : ℕ) + 1 then 1 else 0 := by
    split_ifs <;> simp_all +decide [ Finset.sum_ite ];
    · rw [ Finset.card_eq_one ];
      use ⟨ K.i - 1, by
        exact lt_of_le_of_lt ( Nat.pred_le _ ) ( Fin.is_lt _ ) ⟩
      generalize_proofs at *;
      grind +locals;
    · grind;
  have h_simplify4 : ∑ x ∈ Finset.Icc J.i J.j, (if (K.j : ℕ) + 1 = (x : ℕ) then 1 else 0) = if (K.j : ℕ) + 1 ≥ (J.i : ℕ) ∧ (K.j : ℕ) + 1 ≤ (J.j : ℕ) then 1 else 0 := by
    split_ifs <;> simp_all +decide [ Finset.sum_ite ];
    · rw [ Finset.card_eq_one ];
      use ⟨ K.j + 1, by linarith [ Fin.is_lt K.j, Fin.is_lt J.j, show ( K.j : ℕ ) < J.j from by tauto ] ⟩ ; ext; aesop;
    · lia;
  rw [ ← Finset.mul_sum _ _ _ ] ; simp_all +decide [ Finset.sum_add_distrib, Finset.sum_sub_distrib ] ;
  grind +suggestions

-- α is injective
theorem α_injective {n : ℕ} [NeZero n] : Function.Injective (α (n := n)) := by
  sorry

/-
α_dual is injective
-/
theorem α_dual_injective {n : ℕ} [NeZero n] : Function.Injective (α_dual (n := n)) := by
  intro J K h
  have h_sign : J.sign = K.sign ∨ J.sign = -K.sign := by
    apply_fun fun f => f ( fun i => if i = J.i then 1 else 0 ) at h ; simp_all +decide [ α_dual ] ;
    simp_all +decide [ Finset.sum_apply, e_transpose ];
    split_ifs at h <;> simp_all +decide [ SignedInterval.sign ];
    · grind;
    · split_ifs at h ; contradiction;
    · exact absurd ‹_› ( not_lt_of_ge J.hij )
  generalize_proofs at *; (
  cases h_sign <;> simp_all +decide [ funext_iff, LinearMap.ext_iff, α_dual ];
  · -- Since these two sums are equal for all x, the intervals must be equal.
    have h_interval : Finset.Icc J.i J.j = Finset.Icc K.i K.j := by
      ext x; specialize h ( fun i => if i = x then 1 else 0 ) ; simp_all +decide [ e_transpose ] ;
      split_ifs at h <;> simp_all +decide [ SignedInterval.sign ] ;
      · split_ifs at h ; norm_num at h;
      · split_ifs at h ; contradiction;
      · grind +ring
    generalize_proofs at *; (
    cases J ; cases K ; simp_all +decide [ Finset.ext_iff ];
    rename_i i j hij ε i' j' hij' ε' h; have := h_interval i; have := h_interval j; have := h_interval i'; have := h_interval j'; simp_all +decide [ SignedInterval.sign ] ;
    grind +ring);
  · have := h ( fun i => if i = J.i then 1 else 0 ) ; simp_all +decide [ e_transpose ] ; (
    split_ifs at this <;> simp_all +decide [ SignedInterval.sign ] ;
    · split_ifs at this ; norm_num at this;
    · split_ifs at this ; norm_num at this;
    · split_ifs at this ; norm_num at this;
    · exact absurd ‹J.j < J.i› ( not_lt_of_ge J.hij )));

/-
root_coroot_two
-/
theorem root_coroot_two' {n : ℕ} [NeZero n] (J : SignedInterval n) :
    (Zn_pairing n) (α J) (α_dual J) = 2 := by
  -- By definition of $Ae$, we know that $Ae u v = 2$ if $u = v$ and $-1$ if $u$ and $v$ are adjacent.
  have h_Ae : ∀ (u v : Fin n), (Ae u) v = if u = v then 2 else if (u.val + 1 = v.val ∨ v.val + 1 = u.val) then -1 else 0 := by
    unfold Ae; aesop;
  -- By definition of $α$ and $α_dual$, we can expand the pairing.
  have h_expand : (Zn_pairing n) (α J) (α_dual J) = J.sign * J.sign * ∑ u ∈ Finset.Icc J.i J.j, ∑ v ∈ Finset.Icc J.i J.j, (Ae u) v := by
    simp +decide [ Zn_pairing, α, α_dual ];
    unfold e_transpose; simp +decide [ Finset.mul_sum _ _ _, Finset.sum_mul ] ;
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
  -- By definition of $Ae$, we can simplify the double sum.
  have h_simplify : ∑ u ∈ Finset.Icc J.i J.j, ∑ v ∈ Finset.Icc J.i J.j, (Ae u) v = ∑ u ∈ Finset.Icc J.i J.j, (2 - (if u = J.i then 0 else 1) - (if u = J.j then 0 else 1)) := by
    refine' Finset.sum_congr rfl fun u hu => _;
    split_ifs <;> simp_all +decide [ Finset.sum_ite ];
    · simp +decide [ Finset.filter_eq, Finset.filter_ne ];
    · rw [ show ( Finset.filter ( fun x => J.i = x ) ( Finset.Icc J.i J.j ) ) = { J.i } from Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ le_rfl, hu ⟩, rfl ⟩, fun x hx => Finset.mem_filter.mp hx |>.2.symm ⟩ ] ; norm_num;
      rw [ show ( Finset.filter ( fun x : Fin n => ( J.i : ℕ ) + 1 = x ∨ ( x : ℕ ) + 1 = J.i ) ( Finset.filter ( fun x : Fin n => ¬J.i = x ) ( Finset.Icc J.i J.j ) ) ) = { ⟨ J.i + 1, by
            grind ⟩ } from ?_ ] ; norm_num;
      grind +splitImp;
    · rw [ show ( Finset.filter ( fun x => J.j = x ) ( Finset.Icc J.i J.j ) ) = { J.j } from Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hu, le_rfl ⟩, rfl ⟩, fun x hx => Finset.mem_filter.mp hx |>.2.symm ⟩ ] ; norm_num;
      rw [ Finset.card_eq_one.mpr ] ; norm_num;
      use ⟨ J.j.val - 1, by
        exact lt_of_le_of_lt ( Nat.pred_le _ ) ( Fin.is_lt _ ) ⟩ ; ext; simp +decide [ Fin.ext_iff ] ; omega;
    · rw [ show ( Finset.filter ( fun x => u = x ) ( Finset.Icc J.i J.j ) ) = { u } by ext; aesop ] ; norm_num;
      rw [ show ( Finset.filter ( fun x : Fin n => ( u : ℕ ) + 1 = x ∨ x + 1 = ( u : ℕ ) ) ( Finset.filter ( fun x : Fin n => ¬u = x ) ( Finset.Icc J.i J.j ) ) ) = { ⟨ u + 1, by
            lia ⟩, ⟨ u - 1, by
            exact lt_of_le_of_lt ( Nat.pred_le _ ) ( Fin.is_lt _ ) ⟩ } from ?_ ]
      --generalize_proofs at *;
      · grind +suggestions;
      · grind;
  nontriviality;
  rcases J with ⟨ i, j, hij, ε ⟩ ; simp_all +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq' ] ; ring;
  cases ε <;> simp +decide [ SignedInterval.sign ] <;> omega;

-- · rw [ Nat.cast_sub ] <;> push_cast <;> linarith [ show ( i : ℕ ) ≤ j from hij ];
 -- · rw [ Nat.cast_sub ] <;> push_cast <;> linarith [ show ( i : ℕ ) ≤ j from hij ]

-- reflection formula for roots
-- Proof sketch: ext t, rewrite using α_eval and pairing_formula on both sides,
-- then unfold s, case-split on signs and s-conditions, close with omega.
theorem reflectionPerm_root' {n : ℕ} [NeZero n] (J K : SignedInterval n) :
    α K - (Zn_pairing n (α K)) (α_dual J) • α J = α (s J K) := by
  sorry

-- Pairing symmetry: L(α J, α^v K) = L(α K, α^v J)
theorem pairing_symm {n : ℕ} [NeZero n] (J K : SignedInterval n) :
    (Zn_pairing n (α J)) (α_dual K) = (Zn_pairing n (α K)) (α_dual J) := by
  rw [pairing_formula J K, pairing_formula K J]
  obtain ⟨Ji, Jj, _, Jε⟩ := J
  obtain ⟨Ki, Kj, _, Kε⟩ := K
  unfold SignedInterval.sign
  cases Jε <;> cases Kε <;> simp only [ite_true] <;> split_ifs <;> omega

-- reflection formula for coroots
-- Proof sketch: ext f, rewrite using α_dual_eval, pairing_symm, and pairing_formula,
-- then unfold s, case-split on signs and s-conditions, close with omega.
theorem reflectionPerm_coroot' {n : ℕ} [NeZero n] (J K : SignedInterval n) :
    α_dual K - (Zn_pairing n (α J)) (α_dual K) • α_dual J = α_dual (s J K) := by
  sorry

noncomputable def An (n : ℕ) [NeZero n] : RootPairing (SignedInterval n) ℤ (Zn n) (Zn_dual n) where
  toLinearMap := Zn_pairing n
  root :=
    { toFun := fun J => α J
      inj' := α_injective
    }
  coroot :=
    { toFun := fun J => α_dual J
      inj' := α_dual_injective
    }
  root_coroot_two := by
    intro J
    exact root_coroot_two' J
  reflectionPerm := fun J =>
    { toFun := fun K => s J K
      invFun := fun K => s J K
      left_inv := by
        intro K
        exact s_involutive J K
      right_inv := by
        intro K
        exact s_involutive J K }
  reflectionPerm_root := by
    intro J K
    exact reflectionPerm_root' J K
  reflectionPerm_coroot := by
    intro J K
    exact reflectionPerm_coroot' J K
