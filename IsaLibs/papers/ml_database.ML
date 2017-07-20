(*  Title:      util/const_names.ML
    ID:         $Id: const_names.ML,v 1.00 2015/15/01 13:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

Names for important Pure and HOL constants.
*)

signature ML_DATABASE =
sig

datatype column_type = Nat | Int | String | Real

val load_file : Proof.context -> column_type list -> string -> term list list

end

structure DB_ML_Database
(* : ML_DATABASE *)
= struct

datatype column_type = Nat | Int | String | Real

fun make_type ctxt typ data =
  case typ of
      Nat => Syntax.read_term ctxt (data ^ " :: nat")
    | Int => Syntax.read_term ctxt (data ^ " :: int")
    | String => Syntax.read_term ctxt ("''" ^ data ^ "'' :: string")
    | Real => Syntax.read_term ctxt (data ^ " :: real")

fun isComment line =
  let val line = Utils.trim line
  in
    String.isPrefix "%%" line orelse
    String.isPrefix "@" line orelse
    line = ""
  end

fun row_to_types ctxt typs row =
  if isComment row
  then NONE
  else  row |> Utils.trim
            |> space_explode ","
            |> map2 (make_type ctxt) typs
            |> SOME

fun load_file ctxt typs filename =
  filename |> Path.explode
           |> File.read_lines
           |> map_filter (row_to_types ctxt typs)

end

structure ML_Database : ML_DATABASE = DB_ML_Database

