structure Str_Tab = Table(type key = string val ord = string_ord)

structure Term_Tab = Table(type key = term val ord = Term_Ord.term_ord)

structure Term_List_Tab = Table(type key = term list val ord = list_ord Term_Ord.term_ord)

(* experimental theory exploration table *)
structure Type_Term_List_Tab = Table(type key = typ * term list val ord = prod_ord Term_Ord.typ_ord (list_ord Term_Ord.term_ord))

structure Type_Tab = Table(type key = typ val ord = Term_Ord.typ_ord)

structure IntType_Tab = Table(type key = int * typ val ord = prod_ord int_ord Term_Ord.typ_ord)

structure Int_Tab = Table(type key = int val ord = int_ord)

structure Thm_List_Tab = Table(type key = thm list val ord = list_ord (Term_Ord.term_ord o apply2 Thm.full_prop_of))

structure Thm_Thm_List_Tab = Table(
  type key = thm * thm list 
  val ord = prod_ord (Term_Ord.term_ord o apply2 Thm.full_prop_of) (list_ord (Term_Ord.term_ord o apply2 Thm.full_prop_of)))

structure Term_Term_List_Tab = Table(
  type key = term * term list 
  val ord = prod_ord Term_Ord.term_ord (list_ord Term_Ord.term_ord))

structure Completion_Rules = Named_Thms
  (val name = @{binding "compl"}
   val description = "Theorems for IsaLib")

