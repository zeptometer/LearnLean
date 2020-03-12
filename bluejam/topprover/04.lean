lemma at_most_two : ∀ (f : bool → bool) b x y z,
    x = f b → y = f x → z = f y → z = x :=
begin
    intros f b x y z h1 h2 h3,
    induction b,
        induction x,
            rw ←h1 at h2,
            rw h2 at h3,
            simp [h3],
            rw ←h1,
        rw h1,
        induction y,
            assumption,
        simp * at *,
        rw ←h2,
    induction x,
        induction y,
            rw ←h2 at h3,
            assumption,
        rw h3,
        rw ←h1,
    rw ←h1 at h2,
    rw [h2, ←h1] at h3,
    assumption,
end

example : ∀ (f : bool → bool) b, f (f (f b)) = f b :=
by intros; apply at_most_two; refl
