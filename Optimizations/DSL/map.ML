(*  Title:      Optimizations/DSL/map.ML
    Author:     Brae Webb

Simple inefficient map data stucture.
*)

signature MAP =
sig
type (''k, 'v) map = (''k list * (''k -> 'v option))

val insert: (''k, 'v) map -> (''k * 'v) -> (''k, 'v) map
val lookup: (''k, 'v) map -> ''k -> 'v option
val values: (''k, 'v) map -> 'v list
val empty: (''k, 'v) map
val merge: (''k, 'v) map -> (''k, 'v) map -> (''k, 'v) map

end

structure Map : MAP =
struct
type ('k, 'v) map = ('k list * ('k -> 'v option))

fun add_if_not xs x =
  if member (op =) xs x then xs else cons x xs

fun insert xs (key, value) =
  (add_if_not (fst xs) key, fn x => (if x = key then SOME value else (snd xs) x))

fun lookup xs key =
  (snd xs) key

fun only_some vs =
  List.foldr (fn (v, xs) => case v of NONE => xs | SOME x => ([x] @ xs)) [] vs

fun values (keys, lookup) =
  only_some (map lookup keys)

val empty = ([], fn _ => NONE)

fun merge (lhs_keys, lhs) (rhs_keys, rhs) =
  ((rhs_keys @ lhs_keys), (fn x => (if member (op =) lhs_keys x then lhs x else rhs x)))

end