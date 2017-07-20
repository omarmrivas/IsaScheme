(*  Title:      src/latex.ML
    ID:         $Id: latex.ML,v 1.010 2011/03/09 22:40:00 omar Exp $
    Author:     Omar Montano Rivas, University of Edinburgh School of Informatics
    Copyright   University of Edinburgh 2010

Some latex functions.
*)

signature LATEX_UTILS =
sig
  val latex_table : string -> real -> string list list -> string
  val latex_tree : real -> real -> term -> string
  val latex_tree_with_pos : real -> real -> term -> string
end

structure DB_Latex_Utils
(* : LATEX_UTILS *)
= struct

fun latex_table table space data =
  let val columns = (length o hd) data
      val space_str = " & \\hspace*{" ^ string_of_real space ^ "cm}"
      val start_ = 1 upto columns
                    |> map (fn _ => "c")
                    |> space_implode ""
                    |> (fn str => "\\begin{"^ table ^"}{" ^ str ^ "}\n")
      val body = data |> map (space_implode space_str)
                      |> space_implode "\\\\\n"
      val end_ = "\\end{"^ table ^"}\n"
  in start_ ^ body ^ end_ end

fun latex_tree' (s $ t) = "\\pstree{\\TR{\\bullet}}{" ^
                             (latex_tree' s) ^ (latex_tree' t) ^ "}"
  | latex_tree' (s as Abs (x, T, _)) = "\\pstree{\\TR{\\lambda " ^
                                          x ^ "}}{" ^ (latex_tree' (Term.betapply (s,Free(x,T)))) ^ "}"
  | latex_tree' (Free (n, _)) = "\\TR{" ^ n ^ "}"
  | latex_tree' (Var ((n,i), _)) = "\\TR{" ^ n ^ string_of_int i ^ "}"
  | latex_tree' (Const (n, _)) = "\\TR{" ^ n ^ "}"
  | latex_tree' (Bound _) = raise ERROR "Invalid term"

fun latex_tree levelsep nodesep t =
  "\\psset{levelsep=" ^ string_of_real levelsep ^ ",nodesep=" ^ string_of_real nodesep ^ "pt}" ^
  latex_tree' (Utils.unique_names t)

fun latex_tree_pos' r p (s $ t) = "\\pstree{\\TR{\\bullet}"^
                                     r ^"{"^
                                     (space_implode "" p)^"}}{" ^ 
                                     (latex_tree_pos' "^" (p @ ["0"]) s) ^ 
                                     (latex_tree_pos' "_" (p @ ["1"]) t) ^ "}"
  | latex_tree_pos' r p (s as Abs (x, T, _)) = "\\pstree{\\TR{\\lambda " ^ 
                                                  x ^ "}"^ r ^"{"^(space_implode "" p)^"}}{" ^ 
                                                  (latex_tree_pos' "_" (p @ ["0"]) (Term.betapply (s,Free(x,T)))) ^ "}"
  | latex_tree_pos' r p (Free (n, _)) = "\\TR{" ^ n ^ "}"^ r ^"{"^(space_implode "" p)^"}"
  | latex_tree_pos' r p (Var ((n,i), _)) = "\\TR{" ^ n ^ string_of_int i ^ "}"^ r ^"{"^(space_implode "" p)^"}"
  | latex_tree_pos' r p (Const (n, _)) = "\\TR{" ^ n ^ "}"^ r ^"{"^(space_implode "" p)^"}"
  | latex_tree_pos' _ _ (Bound _) = raise ERROR "Invalid term"

fun latex_tree_with_pos' (s $ t) = "\\pstree{\\TR{\\stackrel{\\varepsilon}{\\bullet}}}{" ^ 
                                     (latex_tree_pos' "^" ["0"] s) ^ 
                                     (latex_tree_pos' "_" ["1"] t) ^ "}"
  | latex_tree_with_pos' (s as Abs (x, T, _)) = "\\pstree{\\TR{\\stackrel{\\varepsilon}{\\lambda " ^ x ^ "}}}{" ^ 
                                                  (latex_tree_pos' "_" ["0"] (Term.betapply (s,Free(x,T)))) ^ "}"
  | latex_tree_with_pos' (Free (n, _)) = "\\TR{\\stackrel{\\varepsilon}{" ^ n ^ "}}"
  | latex_tree_with_pos' (Var ((n,i), _)) = "\\TR{\\stackrel{\\varepsilon}{" ^ n ^ string_of_int i^ "}}"
  | latex_tree_with_pos' (Const (n, _)) = "\\TR{\\stackrel{\\varepsilon}{" ^ n ^ "}}"
  | latex_tree_with_pos' (Bound _) = raise ERROR "Invalid term"

fun latex_tree_with_pos levelsep nodesep t =
  "\\psset{levelsep=" ^ string_of_real levelsep ^ ",nodesep=" ^ string_of_real nodesep ^ "pt}" ^
  latex_tree_with_pos' (Utils.unique_names t)

end

structure Latex_Utils : LATEX_UTILS = DB_Latex_Utils
