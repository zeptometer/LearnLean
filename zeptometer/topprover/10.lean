def prefix_sum : ℕ → list ℕ → list ℕ
| sum []             := [sum]
| sum (head :: tail) := sum :: (prefix_sum (sum + head) tail)

def plus_list : list ℕ → list ℕ → list ℕ
| [] _ := []
| _ [] := []
| (h1 :: t1) (h2 :: t2) := (h1 + h2) :: (plus_list t1 t2)

lemma plus_list_nil_l : ∀l, plus_list [] l = [] :=
begin
    intro l,
    cases l;
    simp [plus_list]
end

lemma plus_list_nil_r : ∀l, plus_list l [] = [] :=
begin
    intro l,
    cases l;
    simp [plus_list]
end

lemma plus_list_prefix_sum_comm : ∀l1 l2: list ℕ, ∀n m: ℕ, 
    prefix_sum (n + m) (plus_list l1 l2) 
    = plus_list (prefix_sum n l1) (prefix_sum m l2) :=
begin
    intro l1,
    induction l1,
        intro l2,
        induction l2,
            intros n m,
            simp [plus_list, prefix_sum, plus_list_nil_l, plus_list_nil_r],
        intros n m,
        simp [plus_list, prefix_sum, plus_list_nil_l, plus_list_nil_r],
    intro l2,
    induction l2,
        intros n m,
        simp [plus_list, prefix_sum, plus_list_nil_l, plus_list_nil_r],
    intros n m,
    simp [plus_list, prefix_sum, plus_list_nil_l, plus_list_nil_r],
    have h : (l1_hd + (l2_hd + (n + m))) = (n + l1_hd) + (m + l2_hd) := by simp,
    rw h,
    sorry
end

example : ∀l1 l2: list ℕ, prefix_sum 0 (plus_list l1 l2) 
            = plus_list (prefix_sum 0 l1) (prefix_sum 0 l2) :=
begin
    intros l1 l2,
    cases l1,
        cases l2,
            simp [plus_list, prefix_sum],
            simp [plus_list, prefix_sum, plus_list_nil_l],
        cases l2,
            simp [plus_list, prefix_sum, plus_list_nil_r],
            simp [plus_list, prefix_sum],

end