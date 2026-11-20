(* Example 2: Denzinger's example, as reported by Burghardt and Heinz
   (arXiv:1404.0953, Fig. 48).  With the orientations chosen by IsaScheme
   completion terminates with a finite system. *)
theory Ex2_Denzinger
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

declare [[generate_cps = true]]

complete "a (c x) = x" by (rule e1)
complete "c (f x) = e x" by (rule e2)
complete "a (e x) = f x" by (rule e3)
complete "c (d x) = b (c x)" by (rule e4)

thm compl

end
