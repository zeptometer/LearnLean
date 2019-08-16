variables (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) :
  false :=
begin
  have hb : shaves barber barber ↔ ¬ shaves barber barber, from h barber,
  have : ¬ shaves barber barber, from (
    begin
      apply not.intro,
      intro,
      have : ¬ shaves barber barber, from hb.mp a,
      contradiction
    end
  ),
  have : shaves barber barber, from hb.mpr this,
  contradiction
end
