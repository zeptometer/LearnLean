example : ∀ (l : list ℕ), list.append l (0 :: list.nil) ≠ list.nil :=
by intros; induction l; simp *
