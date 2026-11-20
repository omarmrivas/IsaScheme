(* Example 4: associativity of Peano addition defined by recursion on the
   second argument (Dershowitz, "Completion and its applications", 1989).
   Completion generates plus (S^n (plus x y)) z = plus x (plus (S^n y) z). *)
theory Ex4_Peano_Assoc
  imports IsaLibs
begin

datatype N = Z | S N

fun plus :: "N \<Rightarrow> N \<Rightarrow> N" where
  "plus x Z = x"
| "plus x (S y) = S (plus x y)"

declare [[generate_cps = true]]

complete "plus (plus x y) z = plus x (plus y z)"
  by (induction z, auto)

thm compl

end
