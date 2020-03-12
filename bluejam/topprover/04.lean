lemma at_most_two : ∀ (f : bool → bool) b x y z,
    x = f b → y = f x → z = f y → z = x :=
    sorry

example : ∀ (f : bool → bool) b, f (f (f b)) = f b :=
by intros; apply at_most_two; refl
