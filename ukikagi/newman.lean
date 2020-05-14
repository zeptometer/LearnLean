inductive rtc {α : Type} (r : α → α → Prop) : α → α → Prop
| base  : ∀ a, rtc a a
| trans : ∀ {a b c}, r a b → rtc b c → rtc a c

lemma rtc_is_transitive {α : Type} {a b c: α} {r : α → α → Prop}:
  rtc r a b → rtc r b c → rtc r a c
:=
begin
  intros hab hbc,
  induction hab with a a p b hap hpb hbcpc,
  exact hbc,
  exact rtc.trans hap (hbcpc hbc)
end

definition weak_cr {α : Type} (r : α → α → Prop): Prop
:= ∀ {a b c: α}, r a b → r a c → ∃ d: α, rtc r b d ∧ rtc r c d
 
definition cr {α : Type} (r : α → α → Prop): Prop
:= ∀ a b c: α, rtc r a b → rtc r a c → ∃ d: α, rtc r b d ∧ rtc r c d
 
constant α: Type
constant r: α → α → Prop
definition ir (a b: α) := r b a
constant r_wf: well_founded ir
constant r_weak_cr: weak_cr r
 
lemma newmann: cr r
:=
begin
  intros x,
  apply well_founded.induction r_wf x _,
  clear x,
  intros a ih b c hab hac,
  simp [ir] at ih,
  cases hab with _ _ p _ hap hpb,
    existsi c,
    split,
      exact hac,
    exact rtc.base r c,
  cases hac with _ _ q _ haq hqc,
    existsi b,
    split,
      exact rtc.base r b,
    exact rtc.trans hap hpb,
  cases r_weak_cr hap haq with s hs,
  cases hs with hps hqs,
  cases ih q haq s c hqs hqc with t ht,
  cases ht with hst hct,
  have hpt: rtc r p t, from rtc_is_transitive hps hst,
  cases ih p hap b t hpb hpt with d hd,
  cases hd with hbd htd,
  clear hap hpb haq hqc hps hqs hst hpt p q s,
  have hcd: rtc r c d, from rtc_is_transitive hct htd,
  existsi d,
  exact ⟨hbd, hcd⟩ 
end
