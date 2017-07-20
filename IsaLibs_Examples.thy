theory IsaLibs_Examples
imports IsaLibs
begin

section {* Introduction *}

text {*
IsaLibs is a theory exploration tool that helps in the verification of recursive algorithms.
It uses techniques from different fields ranging from inductive theorem proving to term 
rewriting systems. This tutorial is an example-guided introduction to the practical use
of the package.

We assume that you have mastered the fundamentals of Isabelle/HOL and are able to write basic 
specifications and proofs.
*}

section {* Inductive Proof Automation *}

text {* Theorems about inductively defined data structures and recursive functions usually require 
mathematical induction. Inductive proving is in general undecidable and the failure of cut elimination 
for inductive theories implies that new lemmas or generalizations, also known as eureka steps, 
are often needed. We present an automated theorem proving tool supporting the automated discovery 
of eureka steps. *}

subsection {* Induction Schemes in Isabelle *}

text {* Isabelle provides induction schemes for ML-style inductive datatypes, namely {\em structural 
induction} rules. Inductive datatypes are implemented by the datatype package. Common types such as 
naturals, lists or trees can be defined as inductive datatypes in Isabelle. For example, the naturals 
can be defined with the command: *}

datatype nat = zero ("0") | suc nat

text {* Isabelle will automatically derive the appropriate induction scheme for the datatype. For 
example, the theorem representing the induction scheme for this datatype is: 

?P 0 \<Longrightarrow> (\<And>nat. ?P nat \<Longrightarrow> ?P (suc nat)) \<Longrightarrow> ?P ?nat

*}

thm nat.induct

text {* Recall that variables prefixed by question mark are meta-variables that and are allowed to 
be instantiated by unification, \<And> is universal quantification and \<Longrightarrow> stands for meta-implication. 

Isabelle also provides induction schemes following the recursive structure of functions, namely 
{\em computational induction} rules. This is implemented by the function package. The definition 
of recursive functions is similar to other definitions in Isabelle. For example, addition for natural 
numbers can be defined with the following command:
*}

fun add :: "nat\<Rightarrow>nat\<Rightarrow>nat" where
"add 0 y = y" |
"add (suc x) y = suc (add x y)"

text {* The function package will automatically derive an induction scheme for this definition 
which is:

(\<And>y. ?P 0 y) \<Longrightarrow> (\<And>x y. ?P x y \<Longrightarrow> ?P (suc x) y) \<Longrightarrow> ?P ?a0.0 ?a1.0
 *}

thm add.induct

text {* The {\em induct_tac} tactic can be used to apply these schemes in Isabelle. The parameters 
of this tactic comprise a list of subterms in the goal on which induction is to be performed, 
together with an induction scheme. Althouh {\em induct_tac} performs induction on a subterm of
the goal, provided the induction scheme is appropriate for the subterm's type, it is commonly used 
only on variables of the goal. This tactic tries to unify the conclusion of the induction rule with 
the goal. If successful, it yields new subgoals given by the antecedents of the rule. For instance, 
if the induction scheme for the naturals is applied to x on the goal $x + y = y + x$, the induction 
tactic leaves the subgoals $0 + y = y + 0$ and $\<And>n. n + y = y + n \<Longrightarrow> suc n + y = y + suc n$ 
(instantiating $P$ to $\lambda a. a + y = y + a$) *}

lemma "add x y = add y (x::nat)"
apply (induct_tac x)
oops

text {* The {\em induct_tac} method is of great help for interactive theorem proving because of the 
freedom it provides to the user, but it can be problematic when used in an automated proof method.
The reason is that unification can produce more than one unifier of the foal with the conclusion of 
the induction rule, hence producing a combinatorial explosion. For example, unification in the above 
application of {\em induct_tac} does not produce a unique unifier $P$ to $\lambda a. a + y = y + a$.
In fact, it produces different ones such as, for example $P$ to $\lambda a. x + y = y + a$ which 
produces the subgoals $x + y = y + 0$ and $\<And>n. x + y = y + n \<Longrightarrow> x + y = y + suc n$. The former 
subgoal is obviously false and a proof cannot be found. *}

subsection {* The Induction and Simplification Tactic *}

text {* The top-level tactic {\em induct_auto} essentially performs induction and then simplification 
in a best-first search. Best-first search is implemented by Isabelle's tactival ASTAR which we guide 
by a heuristic given by the number of pending goals. The induction tactic first collects all variables 
in the conclusion of the goal that are of an inductively defined type and performs structural induction 
on them. The tactic then traverses all subterms $f \hat{v}$ in the conclusion of the goal. It 
performs computational induction on $\hat{v}$ using the recursion induction rule for $f$ if $f$ is
defined by recursion and $\hat{v}$ is a list of variables. After induction is completed, the tactic 
calls Isabelle's {\em auto_tac} performing rewriting on all pending goals. *}

lemma "add x y = add y (x::nat)"
by induct_auto

text {* Paradoxically, it is sometimes necessary to generalize a conjecture in order for an inductive
proof to succeed. The reason is simple: if the goal is too specific, the induction hypotesis is too
week to allow the induction step to go through. Generalization is however problematic since it also requires the {\em cut rule} of
inference. Generalization therefore introduces an infinite branching point into the search space. In
choosing the cut formula we must guard against over generalization, i.e. attempting to prove a 
non-theorem. Let us illustrate the idea with an example. 

Function {\em rev} has quadratic worst-case running time because it calls {\em append} for each element
in the list and append is linear in its first argument. A linear time version of {\em rev} requires
an extra argument where the result is accumulated gradually, using only #: *}

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys" |
"itrev (x # xs) ys = itrev xs (x # ys)"

text {* The recursive function {\em itrev} reverses its first argument by stacking its elements onto
the second argument, and it returns that second argument when the first one becomes empty. Note that 
{\em itrev} is tail-recursive: it can be compiled into a loop; no stack is necessary for executing it. 

Naturally, we would like to show that {\em itrev} does indeed reverse its first argument provided 
the second one is empty: *}

lemma "itrev xs [] = rev xs"
apply (induct_tac xs)
apply auto
oops

text {* Unfortunatelly, this attempt does not prove the induction step: 

\<And>a list. itrev list [] = rev list \<Longrightarrow> itrev list [a] = rev list @ [a]

The induction hypothesis is too weak. The fixed argument, [], prevents it from rewriting the 
conclusion. This example suggests a heuristic: generalize goals for induction by replacing 
constants by variables.

Of course one cannot do this naively: $itrev xs ys = rev xs$ is just not true. The correct 
generalization is $itrev xs ys = rev xs @ ys$ which can be proved automatically with the tactic
{\em induct_auto}.
*}

lemma "itrev xs ys = rev xs @ ys"
by induct_auto

text {* Other situations can require a good deal of creativity. For this reason we provide the 
following Isabelle command. *}

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app [] ys = ys" |
"app (x # xs) ys = x # app xs ys"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev [] = []" |
"rev (x # xs) = app (rev xs) [x]"

rec_complete "itrev xs [] = rev xs"

(*
Additions: app ?x [] =
           ?x, itrev ?list ?x = app (IsaLibs_Examples.rev ?list) ?x, app (app ?x ?xa) ?ys = app ?x (app ?xa ?ys) 
Deletions: itrev (?xb # ?xsb) ?ysc = itrev ?xsb (?xb # ?ysc), itrev [] ?ysb = ?ysb
*)

thm compl

end
