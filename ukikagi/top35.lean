definition NtoB := nat -> bool.

definition NtoB_eqv (g h : NtoB) : Prop := ∀ i, g i = h i.

constant f: nat -> NtoB
axiom f_surjective: ∀ g : NtoB, ∃ n, NtoB_eqv (f n) g

example: false 
:=
begin
    let g := λ n: nat, bnot (f n n),
    cases f_surjective (λ n: nat, bnot (f n n)) with n,
    have hn: f n n = g n, from h n,
    simp [g] at hn,
    cases f n n with b; contradiction,
end
