theory IsaLibs
(*imports Complex_Main*)
imports "~~/src/HOL/TPTP/THF_Arith"
keywords "rec_complete" :: thy_decl and
         "complete" :: thy_goal and
         "orient_rules" :: thy_decl and
         "schematic_lemma" :: thy_decl
begin
  
ML {*
  structure PropSchemes = Named_Thms
  (val name = @{binding "prop_scheme"}
   val description = "Propositional Schemes")
*}
  
ML_file "$ISABELLE_HOME/src/HOL/TPTP/sledgehammer_tactics.ML"
(*ML_file "html.ML"*)
ML_file "const_names.ML"
ML_file "tables.ML"
ML_file "utils.ML"
ML_file "inst_utils.ML"
ML_file "oriented_rules.ML"
ML_file "schematic_lemmas.ML"
ML_file "smt.ML"
ML_file "latex.ML"
ML_file "orders.ML"
ML_file "sat_interface.ML"
ML_file "dependency_pair.ML"
ML_file "random_terms.ML"
ML_file "counter_example.ML"
ML_file "equivalence_terms.ML"
ML_file "counting_terms.ML"
ML_file "enumerated_terms.ML"
ML_file "aprove.ML"
ML_file "prover.ML"
ML_file "ground_completion.ML"
ML_file "induct_tacs4.ML"
ML_file "proof_tools.ML"
ML_file "induct_tacs.ML"
ML_file "commands.ML"
ML_file "meta_gp_hol.ML"
ML_file "exhaust.ML"
ML_file "gnuplot.ML"
ML_file "mysql.ML"
ML_file "papers/ml_database.ML"
ML_file "papers/ESWA2016.ML"
ML_file "papers/rectilinear_crossing.ML"

section {* Theorem Attributes *}
  
attribute_setup prop_scheme = 
  {* Attrib.add_del (Thm.declaration_attribute PropSchemes.add_thm) 
                    (Thm.declaration_attribute PropSchemes.del_thm) *}
  "maintaining a list of proppositional schemes"
  
(*lemma eval_Suc_nat [code_post]:
   "Suc 0 = 1"
   "Suc 1 = 2"
   "Suc (numeral n) = numeral (Num.inc n)"
   unfolding One_nat_def numeral_inc by simp_all

 declare Num.inc.simps [code_post]

value "Suc 42"
value [code] "Suc 42"
value [nbe] "Suc 42"
value [simp] "Suc 42"*)

setup {*
DB_Counter_Example.setup_use_quickcheck #>
DB_Counter_Example.setup_use_nitpick #>
DB_Counter_Example.setup_simp_before #>
DB_Counter_Example.setup_max_time_in_counter_ex #>
DB_Utils.setup_max_time_normalization #>
DB_EQ_Terms.setup_max_random_terms #>

DB_Prover.setup_max_time_in_proof #>
DB_Proof_Tools.setup_max_depth_in_meta_induction #>
DB_Proof_Tools.setup_max_num_generalizations #>
DB_Proof_Tools.setup_max_consts_in_generalizations #>
DB_Random_Terms.setup_max_lambda_size #>
DB_Proof_Tools.setup_use_metis #>

DB_Aprove.setup_use_aprove #>
DB_DPair.setup_max_time_in_termination #>

DB_Completion.setup_generate_cps #>

DB_GP.setup_max_time_in_fitness #>

Completion_Rules.setup
*}

declare [[
  use_quickcheck = true,
  use_nitpick = false,
  simp_before = false,
  max_time_in_counter_ex = 25,
  max_time_in_proof = 30,
  max_time_normalization = 5,
  max_lambda_size = 5,
  max_random_terms = 10,
  max_time_in_termination = 20,
  max_time_in_fitness = 15,
  max_depth_in_meta_induction = 10,
  max_num_generalizations = 3,
  max_consts_in_generalizations = 4,
  use_metis = false,
  quickcheck_quiet = true,
  use_aprove=true,
  
  generate_cps=false,
  linarith_split_limit = 10,
  eta_contract = false
  ]]

text {* Associative operators must be oriented this way to avoid non-termination
        in case they are also Commutative operators. *}
orient_rules "?X (?X (?x :: ?'a) (?y :: ?'a)) (?z :: ?'a) = ?X ?x (?X ?y ?z)"
orient_rules "?X (?X (?x :: ?'a) (?y :: ?'a)) (?z :: ?'a) = ?X ?x (?X ?z ?y)"
orient_rules "?X (?X (?x :: ?'a) (?y :: ?'a)) (?z :: ?'a) = ?X ?y (?X ?x ?z)"
orient_rules "?X (?X (?x :: ?'a) (?y :: ?'a)) (?z :: ?'a) = ?X ?y (?X ?z ?x)"
orient_rules "?X (?X (?x :: ?'a) (?y :: ?'a)) (?z :: ?'a) = ?X ?z (?X ?x ?y)"
orient_rules "?X (?X (?x :: ?'a) (?y :: ?'a)) (?z :: ?'a) = ?X ?z (?X ?y ?x)"
  
definition associativity where
  [prop_scheme]: "associativity R \<equiv> \<forall>x y z. R (R x y) z = R x (R y z)"

definition commutativity where
  [prop_scheme]: "commutativity R \<equiv> \<forall>x y. R x y = R y x"

definition sssociativity_commutativity where
  [prop_scheme]: "sssociativity_commutativity R \<equiv> \<forall>x y z. R x (R y z) = R y (R x z)"

definition left_identity where
  [prop_scheme]: "left_identity R e \<equiv> \<forall>x. R e x = x"
  
definition right_identity where
  [prop_scheme]: "right_identity R e \<equiv> \<forall>x. R x e = x"
  
definition absorbing_element where
  [prop_scheme]: "absorbing_element R e \<equiv> R e = e"
  
definition left_absorbing_element where
  [prop_scheme]: "left_absorbing_element R e \<equiv> \<forall>x. R e x = e"
  
definition right_absorbing_element where
  [prop_scheme]: "right_absorbing_element R e \<equiv> \<forall>x. R x e = e"

definition idempotent where
  [prop_scheme]: "idempotent R \<equiv> \<forall>x. R x x = x"

definition distributive where
  [prop_scheme]: "distributive f g h i \<equiv> \<forall>x y. f (g x y) = h (i x) (i y)"
  
definition left_distributive where
  [prop_scheme]: "left_distributive f g h i \<equiv> \<forall>x y z. f x (g y z) = h (i x y) (i x z)"
  
definition right_distributive where
  [prop_scheme]: "right_distributive f g h i \<equiv> \<forall>x y z. f (g x y) z = h (i x z) (i y z)"
  
ML {*
(*  val p1 = Multithreading.max_threads_value ()*)
  val p2 = Thread.numProcessors ()
  val _ = Future.ML_statistics := false
*}
 
(*
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/list_Interleave.smt2 - list_Interleave.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/list_weird_concat_map_bind.smt2 - list_weird_concat_map_bind.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/list_weird_is_normal.smt2 - list_weird_is_normal.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/mccarthy91_M1.smt2 - mccarthy91_M1.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/mccarthy91_M2.smt2 - mccarthy91_M2.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/mod_same.smt2 - mod_same.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/polyrec_seq_index.smt2 - polyrec_seq_index.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/propositional_AndCommutative.smt2 - propositional_AndCommutative.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/propositional_AndIdempotent.smt2 - propositional_AndIdempotent.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/propositional_AndImplication.smt2 - propositional_AndImplication.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/propositional_Okay.smt2 - propositional_Okay.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/propositional_Sound.smt2 - propositional_Sound.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/rotate_mod.smt2 - rotate_mod.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_BSortCount.smt2 - sort_BSortCount.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_BSortIsSort.smt2 - sort_BSortIsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_BSortPermutes.smt2 - sort_BSortPermutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_BSortSorts.smt2 - sort_BSortSorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_BubSortCount.smt2 - sort_BubSortCount.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_BubSortIsSort.smt2 - sort_BubSortIsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_BubSortPermutes.smt2 - sort_BubSortPermutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_BubSortSorts.smt2 - sort_BubSortSorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_HSortCount.smt2 - sort_HSortCount.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_HSortIsSort.smt2 - sort_HSortIsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_HSortPermutes.smt2 - sort_HSortPermutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_HSortSorts.smt2 - sort_HSortSorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortBU2Count.smt2 - sort_MSortBU2Count.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortBU2IsSort.smt2 - sort_MSortBU2IsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortBU2Permutes.smt2 - sort_MSortBU2Permutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortBU2Sorts.smt2 - sort_MSortBU2Sorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortBUCount.smt2 - sort_MSortBUCount.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortBUIsSort.smt2 - sort_MSortBUIsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortBUPermutes.smt2 - sort_MSortBUPermutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortBUSorts.smt2 - sort_MSortBUSorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortTDCount.smt2 - sort_MSortTDCount.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortTDIsSort.smt2 - sort_MSortTDIsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortTDPermutes.smt2 - sort_MSortTDPermutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortTDSorts.smt2 - sort_MSortTDSorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NMSortTDCount.smt2 - sort_NMSortTDCount.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NMSortTDIsSort.smt2 - sort_NMSortTDIsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NMSortTDPermutes.smt2 - sort_NMSortTDPermutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NMSortTDSorts.smt2 - sort_NMSortTDSorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NStoogeSort2Count.smt2 - sort_NStoogeSort2Count.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NStoogeSort2IsSort.smt2 - sort_NStoogeSort2IsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NStoogeSort2Permutes.smt2 - sort_NStoogeSort2Permutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NStoogeSort2Sorts.smt2 - sort_NStoogeSort2Sorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NStoogeSortCount.smt2 - sort_NStoogeSortCount.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NStoogeSortIsSort.smt2 - sort_NStoogeSortIsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NStoogeSortPermutes.smt2 - sort_NStoogeSortPermutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NStoogeSortSorts.smt2 - sort_NStoogeSortSorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_QSortCount.smt2 - sort_QSortCount.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_QSortIsSort.smt2 - sort_QSortIsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_QSortPermutes.smt2 - sort_QSortPermutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_QSortSorts.smt2 - sort_QSortSorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_SSortCount.smt2 - sort_SSortCount.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_SSortIsSort.smt2 - sort_SSortIsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_SSortPermutes.smt2 - sort_SSortPermutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_SSortSorts.smt2 - sort_SSortSorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_StoogeSort2Count.smt2 - sort_StoogeSort2Count.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_StoogeSort2IsSort.smt2 - sort_StoogeSort2IsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_StoogeSort2Permutes.smt2 - sort_StoogeSort2Permutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_StoogeSort2Sorts.smt2 - sort_StoogeSort2Sorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_StoogeSortCount.smt2 - sort_StoogeSortCount.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_StoogeSortIsSort.smt2 - sort_StoogeSortIsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_StoogeSortPermutes.smt2 - sort_StoogeSortPermutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_StoogeSortSorts.smt2 - sort_StoogeSortSorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/subst_SubstFreeNo.smt2 - subst_SubstFreeNo.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/subst_SubstFreeYes.smt2 - subst_SubstFreeYes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/tree_Flatten1.smt2 - tree_Flatten1.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/tree_Flatten1List.smt2 - tree_Flatten1List.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/tree_Flatten3.smt2 - tree_Flatten3.thy 
val it = [(), (), (), (), (), (), (), (), (), (), ...]: unit list
*)
  
datatype Bin = One | ZeroAnd (ZeroAnd_0: "Bin") | OneAnd (OneAnd_0: "Bin")

fun s :: "Bin => Bin" where
"(s One) = (ZeroAnd One)"|
"(s (ZeroAnd xs)) = (OneAnd xs)"|
"(s (OneAnd ys)) = (ZeroAnd (s ys))"

fun plusa :: "Bin => Bin => Bin" where
"(plusa One y) = (s y)"|
"(plusa (ZeroAnd z) One) = (s (ZeroAnd z))"|
"(plusa (ZeroAnd z) (ZeroAnd ys)) = (ZeroAnd (plusa z ys))"|
"(plusa (ZeroAnd z) (OneAnd xs)) = (OneAnd (plusa z xs))"|
"(plusa (OneAnd x2) One) = (s (OneAnd x2))"|
"(plusa (OneAnd x2) (ZeroAnd zs)) = (OneAnd (plusa x2 zs))"|
"(plusa (OneAnd x2) (OneAnd ys2)) = (ZeroAnd (s (plusa x2 ys2)))"  

fun timesa :: "Bin => Bin => Bin" where
"(timesa One y) = y"|
"(timesa (ZeroAnd xs) y) = (ZeroAnd (timesa xs y))"|
"(timesa (OneAnd ys) y) = (plusa (ZeroAnd (timesa ys y)) y)"

lemma TRS: 
  "timesa One y \<equiv> y"
  "timesa x One \<equiv> x"
  "s One \<equiv> ZeroAnd One"
  "plusa One y \<equiv> s y"
  "plusa x One \<equiv> s x"
  "plusa xa xa \<equiv> ZeroAnd xa"
  "s (ZeroAnd xs) \<equiv> OneAnd xs"
  "plusa y x \<equiv> plusa x y"
  "s (OneAnd ys) \<equiv> ZeroAnd (s ys)"
  "plusa y (ZeroAnd One) \<equiv> s (s y)"
  "timesa (ZeroAnd xs) y \<equiv> ZeroAnd (timesa xs y)"
  "timesa y (ZeroAnd xs) \<equiv> ZeroAnd (timesa y xs)"
  "plusa x (s y) \<equiv> s (plusa x y)"
  "timesa y (OneAnd One) \<equiv> plusa y (ZeroAnd y)"
  "timesa (s y) z \<equiv> plusa z (timesa y z)"
  "plusa (ZeroAnd z) (ZeroAnd ys) \<equiv> ZeroAnd (plusa z ys)"
  "plusa x (OneAnd xa) \<equiv> s (plusa x (ZeroAnd xa))"
  "plusa ya (plusa x ya) \<equiv> plusa x (ZeroAnd ya)"
  "plusa (OneAnd x2) (ZeroAnd zs) \<equiv> OneAnd (plusa x2 zs)"
  "timesa (OneAnd ys) y \<equiv> plusa (ZeroAnd (timesa ys y)) y"
  "plusa y (plusa y (ZeroAnd x)) \<equiv> ZeroAnd (plusa x y)"
  "timesa y (OneAnd (ZeroAnd One)) \<equiv> plusa y (ZeroAnd (ZeroAnd y))"
  "plusa x (ZeroAnd (s y)) \<equiv> s (s (plusa x (ZeroAnd y)))"
  "timesa ys (OneAnd (ZeroAnd (ZeroAnd One))) \<equiv> plusa ys (ZeroAnd (ZeroAnd (ZeroAnd ys)))"
  "plusa (ZeroAnd One) (plusa x (ZeroAnd (ZeroAnd xa))) \<equiv> plusa x (ZeroAnd (OneAnd xa))"
  "plusa (ZeroAnd (ZeroAnd One)) (plusa x (ZeroAnd (ZeroAnd (ZeroAnd xa)))) \<equiv> plusa x (ZeroAnd (ZeroAnd (OneAnd xa)))"
  sorry
  
lemma R: "plusa (OneAnd One) (plusa y (ZeroAnd (ZeroAnd z))) \<equiv> plusa (s y) (ZeroAnd (OneAnd z))"
  sorry
    
ML {*
  val _ = DB_Completion.completion_debug := false
  val thy = @{theory}
  val prop = @{prop "((timesa x (plusa y z)) = (plusa (timesa x y) (timesa x z)))"}
  val def_lemmas = Utils.get_definitional_rewrites thy prop
  val ctxt_nodefs = @{context} delsimps def_lemmas
  val terminates = Aprove.memoized_terminates ctxt_nodefs
  val TRS = @{thms TRS}
  val e = @{thm R}
  val result = Ground_Completion.run_completion [] ctxt_nodefs terminates TRS e
*}
  
end
