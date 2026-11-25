theory ABC
  imports IsaLibs
  keywords "abc_faults" "abc_repair" :: diag and "axioms" "true" "false"
begin

text \<open>
An extension of IsaScheme with the fault diagnosis and the repair operations of the
ABC system (A. Bundy, The ABC System for Repairing Faulty Logical Theories,
section 5). The commands

  abc_faults axioms "clause" ... true "atom" ... false "atom" ...
  abc_repair axioms "clause" ... true "atom" ... false "atom" ...

read a Horn theory and a preferred structure written in Isabelle's syntax. The first
one lists the incompatibilities and insufficiencies, and the second one also searches,
breadth first, for the smallest sequences of repair operations that leave a theory
without faults. The options abc_max_depth, abc_max_proofs, abc_max_repairs and
abc_max_solutions bound the search.
\<close>

ML_file "abc.ML"

end
