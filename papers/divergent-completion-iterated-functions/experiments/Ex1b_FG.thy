(* Example 1b: f (g (f x)) = g (f x); completion generates
   f (g^n (f x)) = g^n (f x) for every n >= 1. *)
theory Ex1b_FG
  imports IsaLibs
begin

typedecl T
consts f :: "T \<Rightarrow> T"
       g :: "T \<Rightarrow> T"
axiomatization where fg: "f (g (f x)) = g (f x)"

declare [[generate_cps = true]]

complete "f (g (f x)) = g (f x)"
  by (rule fg)

thm compl

end
