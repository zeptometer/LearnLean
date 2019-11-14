inductive swap_once: list nat → list nat → Prop
| swap : ∀ (h1 h2 : nat) (t : list nat), swap_once (h1 :: h2 :: t) (h2 :: h1 :: t)
| delegate : ∀ (h : nat) (t1 t2 : list nat), swap_once (h :: t1) (h :: t2)

inductive is_odd_permutation: list nat → list nat → Prop
| OddPermutation1: forall l1 l2, swap_once l1 l2 -> is_odd_permutation l1 l2
| OddPermutation2: forall l1 l2 l3 l4, swap_once l1 l2 -> swap_once l2 l3 -> is_odd_permutation l3 l4 -> is_odd_permutation l1 l4

inductive no_dup: list nat → Prop
| empty: no_dup []
| first_appear: ∀ (h : nat) (l : list nat), (h ∉ l) → no_dup (h :: l)

lemma equals_even: ∀ (l1 l2 : list nat), no_dup l1 → l1 = l2 → ¬ is_odd_permutation l1 l2 := sorry

example : ∀ (l1 l2 : list nat), no_dup l1 → is_odd_permutation l1 l2 -> l1 ≠ l2 :=
begin
    intros l1 l2 h_dp h_odd equiv,
    have: ¬ is_odd_permutation l1 l2, from absurd h_odd (equals_even l1 l2 a equiv),
    contradiction,
end
