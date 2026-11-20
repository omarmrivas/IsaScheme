(* Example 6: the "signed binary trees" of H. Kirchner (TCS 67, 1989,
   Example 2.1).  The infinite families grow in nested binary terms, so the
   critic does not apply.  Open this theory in jEdit and interrupt it. *)
theory Ex6_Kirchner
  imports IsaLibs
begin

typedecl T
consts neg :: "T \<Rightarrow> T"
       f :: "T \<Rightarrow> T \<Rightarrow> T"
axiomatization where
  r1: "neg (neg x) = x" and
  r2: "neg (f x y) = f (neg y) (neg x)" and
  r3: "f (f y x) (neg x) = y" and
  r4: "f (neg x) (f x y) = y"

declare [[generate_cps = true]]

complete "neg (neg x) = x" by (rule r1)
complete "neg (f x y) = f (neg y) (neg x)" by (rule r2)
complete "f (f y x) (neg x) = y" by (rule r3)
complete "f (neg x) (f x y) = y" by (rule r4)

end
