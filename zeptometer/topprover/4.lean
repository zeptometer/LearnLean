lemma hoge : ∀ (f : bool → bool) (x y z w : bool), (x = f y) → (y = f z) → (z = f w) → x = z := begin
    intros,
    cases x,
    cases y,
    cases z,
    cases w,
    refl,
    refl,
    cases w,
    rewrite a,
    rewrite a_2,
    have h: ff = tt, from calc
        ff = f tt : by rw a_1
        ... = tt : by rw ←a_2,
    assumption,
    cases z,
    refl,
    have h: ff = tt, from calc 
        ff = f tt : by rw a
        ... = tt : by rw ←a_1,
    assumption,
    cases z,
    cases y,
    have h: tt = ff, from calc
        tt = f ff : by rw a
        ... = ff : by rw ←a_1,
    assumption,
    cases w,
    have h: tt = ff, by rw [a_1, ←a_2],
    assumption,
    have h: tt = ff, by rw [a, ←a_2],
    assumption,
    refl
end

example : ∀ (f: bool → bool) (b : bool), f (f (f b)) = f b := begin
    intros,
    apply (hoge f (f (f (f b))) (f (f b)) (f b) b);
    refl
end