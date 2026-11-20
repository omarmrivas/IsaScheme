(* Example 3: the braid monoid <a, b | aba = bab>, which has no finite
   convergent presentation over {a, b} (Kapur and Narendran, 1985).
   Strings are encoded as compositions of unary functions.  The critic finds
   the family a b^(n+2) a b -> b a b b a^(n+1) but does not prove it, so
   completion does not terminate.  Open this theory in jEdit and interrupt it. *)
theory Ex3_Braid
  imports IsaLibs
begin

typedecl T
consts a :: "T \<Rightarrow> T"
       b :: "T \<Rightarrow> T"
axiomatization where ab: "a (b (a x)) = b (a (b x))"

declare [[generate_cps = true]]

complete "a (b (a x)) = b (a (b x))"
  by (rule ab)

end
