namespace MiniKanren

module NumericLiteralZ =
    open System
    open Goal

    let FromZero() = prim 0
    let FromOne() = prim 1
    let FromInt32 (a:int) = prim a
    let FromInt64 (a:int64) = prim (int a)
    let FromString (s:string) = prim (Int32.Parse s)

module Relations =

    open Substitution
    open Goal

    let True = prim true
    let False = prim false

    ///Tries goal an unbounded number of times.
    let rec anyo goal =
        recurse (fun () -> goal ||| anyo goal)

    ///Goal that succeeds an unbounded number of times.
    let alwayso = anyo (True *=* True)

    ///Goal that fails an unbounded number of times.
    let nevero = anyo (True *=* False)

    ///Non-relational. The given goal succeeds at most once.
    let onceo goal = condu [ [ goal ] ]

    //---lists----

    ///Relates l with the empty lst.
    let emptyo l = equiv l nil

    ///Relates h and t with the list l such that (h::t) = l.
    let conso h t l = equiv (cons h t) l

    ///Relates h with the list l such that (h::_) = l.
    let heado h l =
        let t = fresh()
        conso h t l

    ///Relates t with the list l such that (_::t) = l.
    let tailo t l =
        let h = fresh()
        conso h t l

    ///Relates l,s and out so that l @ s = out
    let rec appendo l s out = 
        emptyo l &&& equiv s out
        ||| let a,d = fresh(),fresh() in
            conso a d l
            &&& let res = fresh() in
                conso a res out
                &&& recurse (fun () -> appendo d s res)
