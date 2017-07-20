theory IsaLibs
imports Main
begin
ML_file "$ISABELLE_HOME/src/HOL/TPTP/sledgehammer_tactics.ML"
ML_file "const_names.ML"
ML_file "utils.ML"
ML_file "counter_example.ML"
ML_file "def_utils.ML"
ML_file "enumerated_terms.ML"
ML_file "induct_tacs.ML"
ML_file "proof_tools.ML"

setup {*
DB_Counter_Example.setup_use_quickcheck #>
DB_Counter_Example.setup_use_nitpick #>
DB_Counter_Example.setup_simp_before #>
DB_Counter_Example.setup_max_time_in_counter_ex #>

DB_Proof_Tools.setup_max_time_in_proof #>
DB_Proof_Tools.setup_use_metis
*}

declare [[
  use_quickcheck = true,
  use_nitpick = true,
  simp_before = false,
  max_time_in_counter_ex = 50,
  max_time_in_proof = 20,
  use_metis = false,
  quickcheck_quiet = true
  ]]

fun le::"nat\<Rightarrow>nat list\<Rightarrow>bool" where
  "le a []     = True"|
  "le a (x#xs) = (a <= x & le a xs)"
  
fun sorted::"nat list\<Rightarrow>bool" where
  "sorted []     = True"|
  "sorted (x#xs) = (le x xs & sorted xs)"

fun count :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "count []     y = 0"|
  "count (x#xs) y = (if x=y then Suc(count xs y) else count xs y)"

fun merge :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "merge (x#xs) (y#ys) = (if x <= y then x # merge xs (y#ys) else y # merge (x#xs) ys)"|
  "merge xs   []   = xs"|
  "merge []   ys   = ys"

thm merge.simps
lemma [simp]: "merge [] xs = xs"
by (induction xs, simp_all)

lemma temp[simp]: "Suc (Suc 0) = 2"
by auto

fun msort :: "nat list \<Rightarrow>  nat list" where
  "msort []  = []"|
  "msort [x] = [x]"|
  "msort xs  = merge (msort(take (size xs div (Suc (Suc 0))) xs)) (msort(drop (size xs div (Suc (Suc 0))) xs))"

declare temp[simp del]

datatype dt = Num int | Infinity

fun plus :: "dt \<Rightarrow> dt \<Rightarrow> dt"
   where
     "plus Infinity _ = Infinity"
   | "plus _ Infinity = Infinity"
   | "plus (Num a) (Num b) = Num (a + b)"

ML {*
  val fails = Unsynchronized.ref Net.empty : term Net.net Unsynchronized.ref
    *}

ML {*
  val tms = Utils.generalizations @{theory} 2 (Net.content (!fails))
  val _ = map (tracing o (Syntax.string_of_term @{context})) tms
*}

(*lemma [simp]: "(case x of (0::nat) \<Rightarrow> y | Suc _ \<Rightarrow> y) = y"
apply (induction x)
by auto

lemma [simp]: "(case x of 0 \<Rightarrow> y | Suc 0 \<Rightarrow> y | Suc _ \<Rightarrow> y) = y"
apply (induction x)
apply auto
done

lemma [simp]: "x < y \<Longrightarrow> min y x = (x::nat)"
apply (induction x)
by auto

lemma [simp]: "x < y \<Longrightarrow> min x y = (x::nat)"
apply (induction x)
by auto*)

ML {*
val r = DB_Proof_Tools.find_lemma fails @{context} 10 2 2 
  [@{prop "sorted (msort xs)"}, 
   @{prop "drop x xa = drop (case x of 0 \<Rightarrow> x | Suc 0 \<Rightarrow> x | Suc _ \<Rightarrow> x) xa"}, 
   @{prop "sorted xa = ((\<lambda>x2. x2) \<le> Suc)"},
   @{prop "IsaLibs.sorted xa = IsaLibs.sorted (merge (merge (merge xa xa) xa) xa)"},
   @{prop "sorted xa = IsaLibs.sorted (merge (merge xa (merge xa xa)) xa)"},
   @{prop "sorted xa = IsaLibs.sorted (merge xa xa)"},
   @{prop "sorted xa = IsaLibs.sorted (merge xa (merge xa xa))"},
   @{prop "sorted xa = IsaLibs.sorted (merge (merge xa xa) xa)"}]
*}

ML {*
  val SOME (term, _, _) = r
  val _ = tracing (Syntax.string_of_term @{context} term)
*}

lemma algo: "sorted (msort xs)"
apply (tactic {* DB_InductiveTacs.induct_auto_tac fails @{context} *})
(*apply (tactic {* DB_InductiveTacs.computational_induction_tac (Unsynchronized.ref set) @{context} 1 *})*)
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back

(*apply (tactic {* DB_InductiveTacs.test_tac (Unsynchronized.ref set) @{context} 1 *})*)
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
back
(*apply (tactic {* DB_InductiveTacs.cases_tac @{context} 1 *})
apply auto*)

by (tactic {*(List.foldl (op THEN_ALL_NEW) (fn i => all_tac)
                 (List.map (Induct_Tacs.case_tac @{context}) ["a", "b"]) 1)*})
      simp_all
apply (cases a rule: dt.exhaust[case_product dt.exhaust])
apply simp_all
apply (induction a b rule: plus.induct)
apply (cases a)
apply (cases b)
apply auto

   
   
ML {* 
fun check_counter_tac ctxt =
   SUBGOAL (fn (goal, _) =>
     if is_none (Quickcheck.test_terms ctxt (true, true) [] [(goal, [])])
     then all_tac else no_tac)
*}

theorem "sorted (msort xs)"
apply (induction xs rule: msort.induct)
apply (tactic 
    {* (fn ctxt =>
      SUBGOAL (fn (goal, _) =>
      let
        val _ = tracing ("Sub - Goal: " ^ Syntax.string_of_term_global @{theory} goal)
      in
        all_tac
      end)) @{context} 2 *})
apply auto
apply (induction "msort xs" rule: sorted.induct)
apply auto
apply (induction "msort xs" arbitrary: xs rule: sorted.induct)
apply auto
apply (induction "msort xs" rule: sorted.induct)
apply auto
apply (induction xs rule: msort.induct)
apply auto*)

ML {* 
  structure k = InductiveTacs
*}

ML {*
val result = DB_InductiveTacs.inductive_applications @{theory} @{term "\<forall>xs. IsaLibs.sorted (msort xs)"}
      
*}

end
