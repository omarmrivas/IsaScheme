(* Example 2b: Denzinger's example with the orientations of the LPO
   c > b > a > d > f > e used in the literature.  Plain completion generates
   a (b^n (c x)) = d^n x and a (b^n (e x)) = d^n (f x) for every n >= 1. *)
theory Ex2b_Denzinger_LPO
  imports IsaLibs
begin

typedecl T
consts a :: "T \<Rightarrow> T"  b :: "T \<Rightarrow> T"  c :: "T \<Rightarrow> T"
       d :: "T \<Rightarrow> T"  e :: "T \<Rightarrow> T"  f :: "T \<Rightarrow> T"
axiomatization where
  e1: "a (c x) = x" and
  e2: "c (f x) = e x" and
  e3: "a (e x) = f x" and
  e4: "c (d x) = b (c x)"

orient_rules "c (f ?x) = e ?x"
orient_rules "c (d ?x) = b (c ?x)"

declare [[generate_cps = true]]

complete "a (c x) = x" by (rule e1)
complete "c (f x) = e x" by (rule e2)
complete "a (e x) = f x" by (rule e3)
complete "c (d x) = b (c x)" by (rule e4)

thm compl

end
