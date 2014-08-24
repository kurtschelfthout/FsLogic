module MiniKanren.Relations

open Substitution
open Goal

///Tries goal an unbounded number of times.
let rec anyo goal =
    recurse (fun () -> goal ||| anyo goal)

///Goal that succeeds an unbounded number of times.
let alwayso = anyo (equiv Nil Nil)

///Goal that fails an unbounded number of times.
let nevero = anyo (equiv (Atom true) (Atom false))

///Appends l and s together to give out.
let rec appendo l s out = 
    recurse (fun () ->
        equiv Nil l &&& equiv s out
        ||| let a,d = fresh(),fresh() in
            equiv (List (a,d)) l
            &&& let res = fresh() in
                appendo d s res
                &&& equiv (List (a,res)) out)
