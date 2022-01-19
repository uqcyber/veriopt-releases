(*  Title:      Optimizations/DSL/map.ML
    Author:     Brae Webb

Simple inefficient map data stucture.
*)

signature MAP =
sig
type (''k, 'v) map = (''k list * (''k -> 'v option))

val insert: (''k, 'v) map -> (''k * 'v) -> (''k, 'v) map
val lookup: (''k, 'v) map -> ''k -> 'v option
val empty: (''k, 'v) map

end

structure Map : MAP =
struct
type ('k, 'v) map = ('k list * ('k -> 'v option))

fun insert xs (key, value) = (*: ('k, 'v) map -> ('k * 'v) -> ('k, 'v) map =*)
  ((cons key (fst xs)), fn x => (if x = key then SOME value else (snd xs) x))

fun lookup xs key =
  (snd xs) key

val empty = ([], fn _ => NONE)

end