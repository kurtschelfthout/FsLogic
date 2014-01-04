// Learn more about F# at http://fsharp.net. See the 'F# Tutorial' project
// for more guidance on F# programming.

#load "CoreMiniKanren.fs"
open MiniKanren

//tests
let bla = run 5 (fun myvar -> let x = newVar() in (equiv x (Atom 3)) .& (equiv myvar x))

let g = run 5 (fun x -> equiv x (Atom 1))

let g2 = run 5 (fun q -> 
            let (x,y,z) = newVar(),newVar(),newVar()
            equiv (Term.FromSeq [x; y; z; x]) q
            .| equiv (Term.FromSeq [z; y; x; z]) q)

let g3 = run 1(fun q-> 
            let x,y = newVar(),newVar()
            equiv y q
            .& equiv (Atom 3) y)


let g4 = run 5 (fun q -> 
            let x,y,z = newVar(),newVar(),newVar()
            equiv (List (x, y)) q
            .| equiv (List (y, y)) q)


let infinite = run 9 (fun q ->  
                let rec loop() =
                    conde <|
                        seq { yield equiv (Atom false) q,[]
                              yield equiv (Atom true) q, []
                              yield loop(),[] }
                loop())

//anyo tries g an unbounded number of times
let rec anyo g =
    conde <| seq { yield g,[]; yield anyo g,[] }

let anyTest = run 5 (fun q -> anyo (equiv (Atom false) q)
                              .| equiv (Atom true) q)

let anyTest2 =  
    run 5 (fun q -> 
        anyo (equiv (Atom 1) q
              .| equiv (Atom 2) q
              .| equiv (Atom 3) q))

let alwayso = anyo (equiv Nil Nil)

let alwaysoTest =
    run 15 (fun x ->
        (equiv (Atom true) x .| equiv (Atom false) x)
        .& alwayso
        .& equiv (Atom false) x)

let alwaysoTest2 =
    run 3 (fun q ->
        let nevero = anyo (equiv (Atom true) (Atom false))
        equiv (Atom 1) q
        .| nevero
        .| (equiv (Atom 2) q
            .| nevero
            .| equiv (Atom 3) q)) 


let appendo l s out = 
    let appendoF appendo (l:Term,s:Term,out:Term) =
        equiv Nil l => equiv s out
        .| (let a,d = newVar(),newVar()
            equiv (List (a,d)) l
            .& (let res = newVar() 
                appendo (d,s,res) //causes stackoverflow without fix
                .& equiv (List (a,res)) out))
    fix appendoF (l,s,out)

let appendoTest =
    run 1 (fun q -> appendo q (List (Atom 5, List(Atom 4,Nil))) (List (Atom 3, List (Atom 5, List(Atom 4, Nil)))))

let appendoTest2 =
    run 3 (fun q -> 
        let l,s = newVar(),newVar()
        appendo l s (List (Atom 1, List(Atom 2,Nil)))
        .& equiv (List (l,s)) q)

let (|Int|) (x:obj) = x :?> int32

let projectTest = 
    run 5 (fun q -> 
        let x = newVar()
        equiv (Atom 5) x
        .& (project x (fun (Int xv) -> equiv (Atom (xv*xv)) q)))

