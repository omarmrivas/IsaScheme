(*  Title:      util/const_names.ML
    ID:         $Id: const_names.ML,v 1.00 2015/15/01 13:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

Names for important Pure and HOL constants.
*)

signature CONST_NAMES =
sig
  (* Names for important HOL constants *)
  val meta_forall                      : string
  val meta_imp                         : string
  val meta_eq                          : string
  val protectC_name                    : string
  val hol_trueprop                     : string
  val hol_forall                       : string
  val hol_exists                       : string
  val hol_eq                           : string
  val hol_implies                      : string
  val hol_not                          : string
  val hol_conj                         : string
  val hol_disj                         : string
  val hol_if                           : string
  val hol_true                         : string
  val hol_false                        : string

  val hol_less                         : string

  val Bit0                             : string
  val Bit1                             : string
  val One                              : string
  val One_class                        : string
  val Zero_class                       : string
  val Minus                            : string
  val Numeral                          : string
  val divide_class                     : string
  val power_class                      : string
  val list_nil                         : string
  val list_cons                        : string
  val product_type                     : string

  val undefined_name                   : string
  val schematic_and                    : string

end

structure DB_Const_Names
(* : CONST_NAMES *)
= struct

val (Const (meta_forall, _) $ _) =   @{term "\<And>x. x"}
val Const (meta_imp, _) = @{term "Pure.imp"}
val Const (meta_eq, _) $ _ $ _ = @{prop "x \<equiv> y"}
val Const (protectC_name, _) = Logic.protectC
val Const (hol_trueprop, _) = @{term "HOL.Trueprop"}
val Const (hol_forall, _) = @{term "HOL.All"}
val Const (hol_exists, _) = @{term "HOL.Ex"}
val Const (hol_eq, _) = @{term "HOL.eq"}
val Const (hol_implies, _) = @{term "HOL.implies"}
val Const (hol_not, _) = @{term "HOL.Not"}
val Const (hol_conj, _) = @{term "HOL.conj"}
val Const (hol_disj, _) = @{term "HOL.disj"}
val hol_if = @{const_name If}
val hol_true = @{const_name True}
val hol_false = @{const_name False}

val Const (Bit0, _) = @{const "Num.num.Bit0"}
val Const (Bit1, _) = @{const "Num.num.Bit1"}
val Const (One, _) = @{const "Num.num.One"}
val Const (One_class, _) = @{term "1::int"}
val Const (Zero_class, _) = @{term "0::int"}
val Const (Minus, _) $ _ = @{term "-1::int"}
val Const (Numeral, _) $ _ = @{term "2::int"}

val Const (list_cons, _) = @{term "op #"}
val Const (list_nil, _) = @{term "[]"}
val Const (product_type, _) $ _ $ _ = @{term "(x,y)"}


val Const (divide_class, _) $ _ $ ((Const (power_class, _) $ _) $ _) = @{term "4.723 :: real"}

(* SAT *)
val Const (hol_less, _) = @{term "Orderings.ord_class.less"}

(* Partial Functions *)
val Const (undefined_name, _) = @{term "undefined"}

(* schematic goals *)
val Const (schematic_and, _) = @{term "op &&&"}

end

structure Const_Names : CONST_NAMES = DB_Const_Names

