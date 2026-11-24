import Mathlib
import PEqualNP.Defs

-- Stop at the output gate. The four remaining gate counts use 512-bit truth tables.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2966_2
    (small : ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : ℕ × Bool) (x6 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   x1 ≤ (10 : ℕ) →     (∀ (x8 : Fin x1), (x3 x8).1 < (10 : ℕ) + ↑x8 ∧ (x4 x8).1 < (10 : ℕ) + ↑x8) →       x5.1 < (10 : ℕ) + x1 →         (∀ (x10 : Fin (9 : ℕ) → Bool) (x11 : Fin (9 : ℕ)), x6 x10 ↑x11 = x10 x11) →           (∀ (x11 : Fin (9 : ℕ) → Bool), x6 x11 (9 : ℕ) = Bool.false) →             (∀ (x12 : Fin (9 : ℕ) → Bool) (x13 : Fin x1),                 have x14 : ℕ × Bool → Bool := fun (x14 : ℕ × Bool) => x6 x12 x14.1 ^^ x14.2;                 x6 x12 ((10 : ℕ) + ↑x13) = if x2 x13 = Bool.true then x14 (x3 x13) && x14 (x4 x13) else x14 (x3 x13) || x14 (x4 x13)) →               ∃ (x13 : Fin (9 : ℕ) → Bool), (x6 x13 x5.1 ^^ x5.2) ≠ (x13 (0 : Fin (9 : ℕ)) && x13 (1 : Fin (9 : ℕ)) || x13 (1 : Fin (9 : ℕ)) && x13 (2 : Fin (9 : ℕ)) || x13 (2 : Fin (9 : ℕ)) && x13 (3 : Fin (9 : ℕ)) || x13 (3 : Fin (9 : ℕ)) && x13 (4 : Fin (9 : ℕ)) || x13 (4 : Fin (9 : ℕ)) && x13 (0 : Fin (9 : ℕ)) || x13 (0 : Fin (9 : ℕ)) && x13 (5 : Fin (9 : ℕ)) || x13 (1 : Fin (9 : ℕ)) && x13 (6 : Fin (9 : ℕ)) || x13 (2 : Fin (9 : ℕ)) && x13 (7 : Fin (9 : ℕ)) || x13 (3 : Fin (9 : ℕ)) && x13 (8 : Fin (9 : ℕ)) || x13 (5 : Fin (9 : ℕ)) && x13 (7 : Fin (9 : ℕ)) || x13 (6 : Fin (9 : ℕ)) && x13 (8 : Fin (9 : ℕ)) || x13 (8 : Fin (9 : ℕ)) && x13 (5 : Fin (9 : ℕ))))
    (words : ∀ (m : Fin 15), 11 ≤ m.val →
      ∀ (op : Fin m.val → Bool) (a b : Fin m.val → Fin 24 × Bool)
        (signed : Finset (Fin 24)) (w : Fin 24 → BitVec 512),
      signed.card ≤ 3 → m.val + signed.card ≤ 14 →
      (∀ j, (a j).1.val < 10 + j.val ∧ (b j).1.val < 10 + j.val) →
      (∀ j, (a j).2 = true → (a j).1 = 0 ∨ (a j).1 = 9 ∨ (a j).1 ∈ signed) →
      (∀ j, (b j).2 = true → (b j).1 = 0 ∨ (b j).1 = 9 ∨ (b j).1 ∈ signed) →
      (∀ i : Fin 9, w ⟨i.val, by omega⟩ = (fun (f : Fin 512 → Bool) => (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn (f := f))) (fun r => r.val.testBit i.val)) →
      w 9 = 0 →
      (∀ j, let rd := fun (q : Fin 24 × Bool) => if q.2 then ~~~(w q.1) else w q.1
            w ⟨10 + j.val, by omega⟩ = if op j then rd (a j) &&& rd (b j) else rd (a j) ||| rd (b j)) →
      w ⟨9 + m.val, by omega⟩ ≠ (0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8 : BitVec 512)) :
    ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : ℕ × Bool) (x6 : Finset ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   x6.card ≤ (3 : ℕ) →     x1 + x6.card ≤ (14 : ℕ) →       (∀ (x10 : Fin x1), (x3 x10).1 < (10 : ℕ) + ↑x10 ∧ (x4 x10).1 < (10 : ℕ) + ↑x10) →         x5.1 < (10 : ℕ) + x1 →           x5.2 = Bool.false →             (have x13 : ℕ × Bool → Prop := fun (x13 : ℕ × Bool) => x13.2 = Bool.true → x13.1 = (0 : ℕ) ∨ x13.1 = (9 : ℕ) ∨ x13.1 ∈ x6;               x13 x5 ∧ ∀ (x14 : Fin x1), x13 (x3 x14) ∧ x13 (x4 x14)) →               (∀ (x14 : Fin (9 : ℕ) → Bool) (x15 : Fin (9 : ℕ)), x7 x14 ↑x15 = x14 x15) →                 (∀ (x15 : Fin (9 : ℕ) → Bool), x7 x15 (9 : ℕ) = Bool.false) →                   (∀ (x16 : Fin (9 : ℕ) → Bool) (x17 : Fin x1),                       have x18 : ℕ × Bool → Bool := fun (x18 : ℕ × Bool) => x7 x16 x18.1 ^^ x18.2;                       x7 x16 ((10 : ℕ) + ↑x17) = if x2 x17 = Bool.true then x18 (x3 x17) && x18 (x4 x17) else x18 (x3 x17) || x18 (x4 x17)) →                     ∃ (x17 : Fin (9 : ℕ) → Bool), (x7 x17 x5.1 ^^ x5.2) ≠ (x17 (0 : Fin (9 : ℕ)) && x17 (1 : Fin (9 : ℕ)) || x17 (1 : Fin (9 : ℕ)) && x17 (2 : Fin (9 : ℕ)) || x17 (2 : Fin (9 : ℕ)) && x17 (3 : Fin (9 : ℕ)) || x17 (3 : Fin (9 : ℕ)) && x17 (4 : Fin (9 : ℕ)) || x17 (4 : Fin (9 : ℕ)) && x17 (0 : Fin (9 : ℕ)) || x17 (0 : Fin (9 : ℕ)) && x17 (5 : Fin (9 : ℕ)) || x17 (1 : Fin (9 : ℕ)) && x17 (6 : Fin (9 : ℕ)) || x17 (2 : Fin (9 : ℕ)) && x17 (7 : Fin (9 : ℕ)) || x17 (3 : Fin (9 : ℕ)) && x17 (8 : Fin (9 : ℕ)) || x17 (5 : Fin (9 : ℕ)) && x17 (7 : Fin (9 : ℕ)) || x17 (6 : Fin (9 : ℕ)) && x17 (8 : Fin (9 : ℕ)) || x17 (8 : Fin (9 : ℕ)) && x17 (5 : Fin (9 : ℕ))) := by
  intro n op left right out S value hcard hbudget htop hout hpol hsigned hinput hzero hgate
  classical
  let m := out.1 + 1 - 10
  have hm : m ≤ n := by dsimp [m]; omega
  have hmo : out.1 < 10 + m := by dsimp [m]; omega
  let up (j : Fin m) : Fin n := ⟨j.val, by omega⟩
  by_cases short : m ≤ 10
  · exact small m (fun j => op (up j)) (fun j => left (up j)) (fun j => right (up j)) out value short
      (fun j => htop (up j)) hmo hinput hzero (fun x j => hgate x (up j))
  have h14 : m ≤ 14 := by omega
  have last : out.1 = 9 + m := by dsimp [m] at *; omega
  let k : Fin 15 := ⟨m, by omega⟩
  let bound (q : ℕ × Bool) : Fin 24 × Bool := (⟨q.1 % 24, Nat.mod_lt _ (by decide)⟩, q.2)
  have bound_val (q : ℕ × Bool) (hq : q.1 < 24) : (bound q).1.val = q.1 := Nat.mod_eq_of_lt hq
  let a := fun j : Fin m => bound (left (up j))
  let b := fun j : Fin m => bound (right (up j))
  have earlier (j : Fin m) : (left (up j)).1 < 10 + j.val ∧ (right (up j)).1 < 10 + j.val := htop (up j)
  have addr (j : Fin m) : (a j).1.val = (left (up j)).1 ∧ (b j).1.val = (right (up j)).1 := by
    have hh := earlier j
    exact ⟨bound_val _ (by omega), bound_val _ (by omega)⟩
  let U := S.image (fun t => (⟨t % 24, Nat.mod_lt _ (by decide)⟩ : Fin 24))
  have cnt : U.card ≤ S.card := Finset.card_image_le
  have sign (q : ℕ × Bool) (hs : q.2 = true → q.1 = 0 ∨ q.1 = 9 ∨ q.1 ∈ S) :
      (bound q).2 = true → (bound q).1 = 0 ∨ (bound q).1 = 9 ∨ (bound q).1 ∈ U := by
    intro hp
    rcases hs hp with h | h | h
    · left; apply Fin.ext; simp [bound, h]
    · right; left; apply Fin.ext; simp [bound, h]
    · right; right; exact Finset.mem_image.mpr ⟨q.1, h, rfl⟩
  let pack : (Fin 512 → Bool) → BitVec 512 := (fun (f : Fin 512 → Bool) => (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn (f := f)))
  have bit (f : Fin 512 → Bool) (r : ℕ) (hr : r < 512) : (pack f).getLsbD r = f ⟨r,hr⟩ := by
    simp only [pack, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hr, Option.getD_some]
  let input (r : Fin 512) (i : Fin 9) : Bool := r.val.testBit i.val
  let w (i : Fin 24) : BitVec 512 := pack fun r => value (input r) i.val
  have wb (i : Fin 24) (r : ℕ) (hr : r < 512) : (w i).getLsbD r = value (input ⟨r,hr⟩) i.val := bit _ _ _
  have bad := words k (by change 11 ≤ m; omega) (fun j => op (up j)) a b U w
    (by omega) (by change m + U.card ≤ 14; omega)
    (fun j => by rw [(addr j).1, (addr j).2]; exact earlier j)
    (fun j => sign _ (hsigned.2 (up j)).1)
    (fun j => sign _ (hsigned.2 (up j)).2)
    (fun i => by apply congrArg pack; funext r; exact hinput (input r) i)
    (by apply BitVec.eq_of_getLsbD_eq; intro r hr; exact (wb 9 r hr).trans ((hzero _).trans BitVec.getLsbD_zero.symm))
    (by
      intro j
      dsimp only
      apply BitVec.eq_of_getLsbD_eq
      intro r hr
      let x := input ⟨r,hr⟩
      have read (q : ℕ × Bool) (hq : q.1 < 24) :
          (if (bound q).2 then ~~~(w (bound q).1) else w (bound q).1).getLsbD r = (value x q.1 ^^ q.2) := by
        have wq : (w (bound q).1).getLsbD r = value x q.1 := by rw [wb _ _ hr, bound_val _ hq]
        change (if q.2 then ~~~(w (bound q).1) else w (bound q).1).getLsbD r = _
        cases q.2
        · simpa only [Bool.false_eq_true, ite_false, Bool.xor_false] using wq
        · simpa only [ite_true, BitVec.getLsbD_not, hr, decide_true, Bool.true_and, Bool.xor_true] using congrArg Bool.not wq
      have ha := read (left (up j)) (by have := earlier j; omega)
      have hb := read (right (up j)) (by have := earlier j; omega)
      change ((if (a j).2 then ~~~(w (a j).1) else w (a j).1).getLsbD r) = _ at ha
      change ((if (b j).2 then ~~~(w (b j).1) else w (b j).1).getLsbD r) = _ at hb
      rw [wb _ _ hr]
      have step := hgate x (up j)
      change value x (10+j.val) = if op (up j) then _ else _ at step
      cases mode : op (up j) <;> simpa only [mode, Bool.false_eq_true, ite_false, ite_true,
        BitVec.getLsbD_and, BitVec.getLsbD_or, ha, hb] using step)
  by_contra! correct
  apply bad
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  rw [wb _ _ hr]
  change value (input ⟨r,hr⟩) (9+m) = _
  rw [← last]
  have row := correct (input ⟨r,hr⟩)
  rw [hpol, Bool.xor_false] at row
  rw [row]
  exact (show ∀ z : Fin 512, (z.val.testBit 0 && z.val.testBit 1 || z.val.testBit 1 && z.val.testBit 2 || z.val.testBit 2 && z.val.testBit 3 || z.val.testBit 3 && z.val.testBit 4 || z.val.testBit 4 && z.val.testBit 0 || z.val.testBit 0 && z.val.testBit 5 || z.val.testBit 1 && z.val.testBit 6 || z.val.testBit 2 && z.val.testBit 7 || z.val.testBit 3 && z.val.testBit 8 || z.val.testBit 5 && z.val.testBit 7 || z.val.testBit 6 && z.val.testBit 8 || z.val.testBit 8 && z.val.testBit 5) = (0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8 : BitVec 512).getLsbD z.val from by decide +kernel) ⟨r,hr⟩
