(* The family found by the critic for the braid monoid <a, b | aba = bab>
   is a theorem.  The critic's tactic (induction, simp, metis) does not find
   the proof; with the commutation lemma funpow_swap1 metis does. *)
theory Ex3_Braid_Family
  imports Main
begin

typedecl T
consts a :: "T \<Rightarrow> T"
       b :: "T \<Rightarrow> T"
axiomatization where ab: "a (b (a x)) = b (a (b x))"

lemma braid_family:
  "a ((b ^^ Suc (Suc n)) (a (b x))) = b (a (b (b ((a ^^ Suc n) x))))"
  apply (induction n arbitrary: x)
   apply (simp_all add: funpow_swap1)
  by (metis ab)+

end
