inductive swap_once: list nat → list nat → Prop
| swap : ∀ (h1 h2 : nat) (t : list nat), swap_once (h1 :: h2 :: t) (h2 :: h1 :: t)
| delegate : ∀ (h : nat) (t1 t2 : list nat), swap_once t1 t2 → swap_once (h :: t1) (h :: t2)

inductive is_odd_permutation: list nat → list nat → Prop
| OddPermutation1: forall l1 l2, swap_once l1 l2 -> is_odd_permutation l1 l2
| OddPermutation2: forall l1 l2 l3 l4, swap_once l1 l2 -> swap_once l2 l3 -> is_odd_permutation l3 l4 -> is_odd_permutation l1 l4

inductive no_dup: list nat → Prop
| empty: no_dup []
| first_appear: ∀ (h : nat) (l : list nat), (h ∉ l) → no_dup (h :: l)

lemma eq_len (l1 l2 : list nat) : l1 = l2 → list.length l1 = list.length l2 :=
match l1, l2 with
| list.nil, list.nil := by intros; refl
| list.nil, (h :: t) := by intros; contradiction
| (h :: t), list.nil := by intros; contradiction
| (h1 :: t1), (h2 :: t2) := by intros; simp * at *
end

lemma equals_even (l1 l2 : list nat) : l1 = l2 → no_dup l1 → ¬ is_odd_permutation l1 l2 :=
match l1, l2 with
| list.nil, _ :=
    begin
        intros,
        intro h_n,
        cases h_n; cases h_n_a,
    end
| (h :: t), list.nil := by intros; simp * at *
| (ha :: t1), (hb :: t2) :=
    begin
        intros,
        intro h_n,
        have h_tail_eq : t1 = t2,
            simp * at *,
        have h_head_eq : ha = hb,
            simp * at *,
        have h_tail_no_dup : no_dup t1,
            simp * at *,
        have h_even_sub : ¬ is_odd_permutation t1 t2,
            from _match t1 t2 h_tail_eq h_tail_no_dup,
        cases h_n,
            cases h_n_a,
                have: ¬ no_dup (ha :: hb :: h_n_a_t),
                    intro sub_no_dup,
                    cases sub_no_dup,
                    simp * at *,
                contradiction,
            have : is_odd_permutation t1 t2,
                from is_odd_permutation.OddPermutation1 t1 t2 h_n_a_a,
            contradiction,
        sorry
    end
end

example : ∀ (l1 l2 : list nat), no_dup l1 → is_odd_permutation l1 l2 -> l1 ≠ l2 :=
begin
    intros l1 l2 h_dp h_odd equiv,
    have: ¬ is_odd_permutation l1 l2,
        from absurd h_odd (equals_even l1 l2 equiv h_dp),
    contradiction,
end
