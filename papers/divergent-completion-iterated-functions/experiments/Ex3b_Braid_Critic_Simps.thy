(* Example 3b: the braid monoid <a, b | aba = bab> with the lemma
   funpow_swap1 added to the critic's default tactic.  The critic proves the
   family a b^(n+2) a b -> b a b b a^(n+1) and completion terminates with
   two rules, whose instances form the infinite convergent system of
   Hirokawa et al. (FSCD 2017, Example 1).  The same can be obtained with
     tower_critic_method
       \<open>exponent_induct; (simp_all add: funpow_swap1)?; metis critic_rules\<close> *)
theory Ex3b_Braid_Critic_Simps
  imports IsaLibs
begin

typedecl T
consts a :: "T \<Rightarrow> T"
       b :: "T \<Rightarrow> T"
axiomatization where ab: "a (b (a x)) = b (a (b x))"

declare funpow_swap1 [critic_simps]
declare [[generate_cps = true]]

complete "a (b (a x)) = b (a (b x))"
  by (rule ab)

thm compl
(* a ((b ^^ Suc (Suc ?n)) (a (b ?x))) = b (a (b (b ((a ^^ Suc ?n) ?x)))),
   a (b (a ?x)) = b (a (b ?x)) *)

end
