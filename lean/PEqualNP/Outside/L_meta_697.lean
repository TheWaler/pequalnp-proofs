import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_697_aux

open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge

-- The wire evaluation lemmas follow the fold calculation of L-meta-613.
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

private theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

private theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

private theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

private theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

private theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

private theorem pair_or {P L : ℕ} {C : Circuit} {g a b : ℕ}
    (base : P + L ≤ g) (ha : a < g) (hb : b < g)
    (hg : C.gates[g-(P+L)]? = some ⟨GateOp.or,[a,b]⟩)
    (p : Fin P) (w : Fin L) :
    wireVal C (pointLineInput P L p w) g =
      (wireVal C (pointLineInput P L p w) a || wireVal C (pointLineInput P L p w) b) := by
  let x := pointLineInput P L p w
  have hl : x.length = P + L := by simp [x, pointLineInput, restrictInput]
  obtain ⟨hj, hgate⟩ := List.getElem?_eq_some_iff.mp hg
  have he := gate_value C.gates x (g-(P+L)) hj
  have idx : x.length + (g - (P+L)) = g := by omega
  rw [idx, hgate] at he
  simpa [wireVal, wires_eq, x, ha, hb, GateOp.eval] using he

private theorem lies_on {P L : ℕ} {inc : Fin P → Fin L → Bool} {C : Circuit}
    {g : ℕ} {w : Fin L} (low : IsLow P L inc C g w) (p : Fin P)
    (hp : wireVal C (pointLineInput P L p w) g = true) : inc p w = true := by
  have h := low (fun q => decide (q = p)) hp
  simpa [lineSum] using h

end PEqualNP.Outside.L_meta_697_aux

open PEqualNP.LowMerge PEqualNP.Outside.L_meta_697_aux in
theorem PEqualNP.Outside.L_meta_697 : ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ), (∀ (p p' : Fin P) (w w' : Fin L), p ≠ p' → w ≠ w' → ¬ (inc p w = true ∧ inc p w' = true ∧ inc p' w = true ∧ inc p' w' = true)) → (∀ (x : Fin P → Bool) (y y' : Fin L → Bool), (C.wires (List.ofFn x ++ List.ofFn y)).getD g false = (C.wires (List.ofFn x ++ List.ofFn y')).getD g false) → ∀ (w w' : Fin L), PEqualNP.LowMerge.IsLowMerge P L inc C g w → PEqualNP.LowMerge.IsLowMerge P L inc C g w' → w = w' := by
  intro P L inc C g unique independent w w' first second
  obtain ⟨base,a,ha,b,hb,hgate,low,hleft,hright⟩ := first
  obtain ⟨_,_,_,_,_,_,low',_,_⟩ := second
  obtain ⟨p,hp,hpb⟩ := Finset.not_subset.mp hleft
  obtain ⟨q,hq,hqa⟩ := Finset.not_subset.mp hright
  have hne : p ≠ q := by rintro rfl; exact hpb hq
  have hpval : wireVal C (pointLineInput P L p w) g = true := by
    have hv := (Finset.mem_filter.mp hp).2
    rw [pair_or base ha hb hgate p w]
    simp [hv]
  have hqval : wireVal C (pointLineInput P L q w) g = true := by
    have hv := (Finset.mem_filter.mp hq).2
    rw [pair_or base ha hb hgate q w]
    simp [hv]
  have same (r : Fin P) : wireVal C (pointLineInput P L r w) g =
      wireVal C (pointLineInput P L r w') g :=
    independent (fun i => decide (i = r)) (fun j => decide (j = w)) (fun j => decide (j = w'))
  by_contra diff
  exact unique p q w w' hne diff ⟨lies_on low p hpval, lies_on low' p ((same p).symm.trans hpval),
    lies_on low q hqval, lies_on low' q ((same q).symm.trans hqval)⟩
