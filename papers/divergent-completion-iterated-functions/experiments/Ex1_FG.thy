(* Example 1: the single self-overlapping rule f (g (f x)) = f (g x).
   Plain completion generates f (g^n (f x)) = f (g^n x) for every n >= 1. *)
theory Ex1_FG
  imports IsaLibs
begin

typedecl T
consts f :: "T \<Rightarrow> T"
       g :: "T \<Rightarrow> T"
axiomatization where fg: "f (g (f x)) = f (g x)"

declare [[generate_cps = true]]   (* divergence_critic is true by default *)

complete "f (g (f x)) = f (g x)"
  by (rule fg)

thm compl
(* f ((g ^^ Suc ?n) (f ?x)) = f ((g ^^ Suc ?n) ?x) *)

end
