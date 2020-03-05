variable f : nat -> bool.

def downward_closed :=
  forall m n, m <= n -> f n = tt -> f m = tt.

lemma l1: downward_closed f → ∀ (r n: ℕ), f r = ff → f n = tt → n < r :=
begin
    intros h r n h1 h2,
    have: ¬ n ≥ r,
        intro,
        have: f r = tt,
            apply h,
            apply a,
            assumption,
        simp * at *,
    sorry,
end

-- k: an extra parameter to convince termination checker
def binsearch : nat → nat → nat → nat
| l r 0 := match decidable.to_bool (nat.succ l = r) with
    | tt := l
    | ff := r
    end
| l r (k + 1) := match decidable.to_bool (nat.succ l = r) with
    | tt := l
    | ff :=
        let m := (l + r) / 2 in
        if f m then binsearch m r k else binsearch l m k
end

lemma success : downward_closed f → ∀ (l r : nat), l < r → f l = tt → f r = ff → f (binsearch f l r (r - l)) = tt :=
sorry

example: downward_closed f →
    ∀ (l r : nat), l < r → f l = tt → f r = ff →
        ∃ (k : nat), ∀ n, f n = tt ↔ n ≤ (binsearch f l r k) :=
begin
    intros h l r h_l_lt_r h_low h_up,
    fapply exists.intro,
        exact (r - l),
    intro n,
    split,
        intro h2,
        induction (r - l),
            unfold binsearch,
            cases (to_bool (nat.succ l = r)),
                unfold binsearch._match_1,
                sorry,
            unfold binsearch._match_1,
            sorry,
        sorry,
    sorry
end
