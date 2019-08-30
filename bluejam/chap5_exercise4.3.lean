    
variables (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) :
  false :=
begin
  have hb : shaves barber barber ↔ ¬ shaves barber barber,
    apply h,
  have : ¬ shaves barber barber,
    apply not.intro,
    intro,
    have : ¬ shaves barber barber,
      apply hb.mp,
    assumption,
    contradiction,
  have : shaves barber barber,
    apply hb.mpr,
    assumption,
  contradiction
end
