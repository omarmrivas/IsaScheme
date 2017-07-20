(*  Title:      src/rectilinear_crossing.ML
    ID:         $Id: rectilinear_crossing.ML,v 2.010 2013/01/11 10:32:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Politecnica de San Luis Potosi
    Copyright   Universidad Politecnica de San Luis Potosi.

    Rectilinear Crossing Problem.
*)

signature RECTILINEAR =
sig

type vertex = Rat.rat * Rat.rat
type vertex_pair = vertex * vertex

exception INVALID_GRAPH of vertex

end

structure DB_Rectilinear
(* : Rectilinear *)
= struct

type vertex = Rat.rat * Rat.rat
type vertex_pair = vertex * vertex

exception INVALID_GRAPH of vertex

datatype planar_graph = PGraph of
         {vertices: vertex list,
          edges : vertex_pair list,
          quadrilaterals: vertex list list,
          crossing_number: int
         }

val empty_graph = PGraph {vertices = [],
                          edges = [],
                          quadrilaterals = [],
                          crossing_number = 0}

fun is_collinear (x, y) ((x1, y1), (x2, y2)) =
    let val numerator = Rat.add y2 (Rat.neg y1)
        val denominator = Rat.add x2 (Rat.neg x1)
    in if denominator = Rat.of_int 0
       then x = x1
       else
         let val m = Rat.mult numerator (Rat.inv denominator)
             val y' = Rat.add (Rat.mult m (Rat.add x (Rat.neg x1))) y1
         in y = y' end
    end

fun cross_product2D ((vx, vy), (wx, wy)) = Rat.add (Rat.mult vx wy) (Rat.neg (Rat.mult vy wx))

fun minus_vector ((vx, vy), (wx, wy)) = (Rat.add wx (Rat.neg vx), Rat.add wy (Rat.neg vy))

fun intersect_edges (edge1, edge2) =
    let val p = fst edge1
        val q = fst edge2
        val r = minus_vector edge1
        val s = minus_vector edge2
        val q_minus_p = minus_vector (p, q)
        val r_cross_s = cross_product2D (r, s)
        val zero = Rat.of_int 0
        val one = Rat.of_int 1
    in if r_cross_s = Rat.of_int 0 (* parallel edges *)
       then false
       else let val t = Rat.mult (cross_product2D (q_minus_p, s)) (Rat.inv r_cross_s)
            in if Rat.le t zero orelse Rat.le one t
               then false
               else let val u = Rat.mult (cross_product2D (q_minus_p, r)) (Rat.inv r_cross_s)
                    in if Rat.le u zero orelse Rat.le one u
                       then false
                       else true
                    end
            end
    end

fun intersect_quadrilateral [v1, v2, v3, v4] =
    exists intersect_edges [((v1, v2), (v3, v4)), ((v1, v3), (v2, v4)), ((v1, v4), (v2, v3))]
  | intersect_quadrilateral _ = raise ERROR "Must be a list of 4 vertex"

fun add_vertex (NONE, _) = NONE
  | add_vertex (SOME (PGraph {vertices, edges, quadrilaterals, crossing_number}), vertex) =
    if exists (is_collinear vertex) edges then NONE
    else if length vertices <= 3 then
      let val vertices = vertices @ [vertex]
          val size = length vertices
          val edges = (0 upto (Utils.binomial_coefficient size 2 - 1)) |> map (Utils.choose vertices 2)
                                                                       |> map (fn [v1, v2] => (v1, v2)
                                                                         | _ => raise ERROR "Impossible to raise this exception")
      in SOME (PGraph {vertices = vertices, edges = edges, quadrilaterals = quadrilaterals, crossing_number = crossing_number}) end
    else let val size = length vertices
             val edges = edges @ map (fn v => (v, vertex)) vertices
             val new_quadrilaterals = map (Utils.choose vertices 3) (0 upto (Utils.binomial_coefficient size 3 - 1))
                                    |> map (fn l => vertex :: l)
             val crossing_number' = Library.foldl (fn (c, quad) => if intersect_quadrilateral quad 
                                                                   then c + 1
                                                                   else c) (0, new_quadrilaterals)
             val vertices' =  vertices @ [vertex]
         in SOME (PGraph {vertices = vertices', edges = edges, quadrilaterals = quadrilaterals @ new_quadrilaterals, crossing_number = crossing_number + crossing_number'}) end

fun construct_graph vertices =
  Library.foldl add_vertex ((SOME empty_graph), vertices)

end

structure Rectilinear : RECTILINEAR = DB_Rectilinear
