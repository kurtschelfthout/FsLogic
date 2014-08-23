module MiniKanren.Relations

open Substitution
open Goal

///Tries goal an unbounded number of times.
let rec anyo goal =
    conde <| seq { yield goal,[]; yield anyo goal,[] }

///Goal that succeeds an unbounded number of times.
let alwayso = anyo (equiv Nil Nil)

///Goal that fails an unbounded number of times.
let nevero = anyo (equiv (Atom true) (Atom false))

///Appends l and s together to give out.
let appendo l s out = 
    let appendoF appendo (l:Term,s:Term,out:Term) =
        equiv Nil l => equiv s out
        .| (let a,d = newVar(),newVar()
            equiv (List (a,d)) l
            .& (let res = newVar() 
                appendo (d,s,res) //causes stackoverflow without fix
                .& equiv (List (a,res)) out))
    fix appendoF (l,s,out)
