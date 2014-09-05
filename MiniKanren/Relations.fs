module MiniKanren.Relations

open Substitution
open Goal

///Tries goal an unbounded number of times.
let rec anyo goal =
    recurse (fun () -> goal ||| anyo goal)

///Goal that succeeds an unbounded number of times.
let alwayso = anyo (equiv <@ true @> <@ true @>)

///Goal that fails an unbounded number of times.
let nevero = anyo (equiv <@ true @> <@ false @>)

///Relates l,s and out so that l @ s = out
let rec appendo xs ys out = 
    recurse (fun () ->
        equiv <@ [] @> xs &&& equiv ys out
        ||| let x,xs',res = fresh(),fresh(),fresh() in
            equiv <@ %x::%xs' @> xs
            &&& appendo xs' ys res
            &&& equiv <@ %x::%res @> out)
