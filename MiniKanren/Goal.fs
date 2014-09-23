module MiniKanren.Goal

open MiniKanren.Substitution
open System
open Microsoft.FSharp.Quotations

//a good explantion of the need for all these cases is in the uKanren paper.
type Stream<'a> =
    | MZero
    | Unit of 'a
    | Choice of 'a * Stream<'a>
    | Inc of Lazy<Stream<'a>>

//A goal is a function that maps a substitution to an
//ordered sequence of zero or more values.
type Goal = Subst -> Stream<Subst>

let equiv (u:'a) (v:'a) : Goal =
    fun a -> 
        unify u v a
        |> Option.map Unit
        |> Option.defaultTo MZero

//this trick for unification overloading doesn't
//reallly work well in all cases.
type Equiv = Equiv with
    static member (?<-)(Equiv, l, v) = 
        equiv l <@ v @>
    static member (?<-)(Equiv, v, r) = 
        equiv <@ v @> r
    static member (?<-)(Equiv, l:Quotations.Expr<'a>,r:Quotations.Expr<'a>) =
        equiv l r
 
let inline (-=-) l r = Equiv ? (l) <- r

let rec mplus a b =
    match a with
    | MZero -> b
    | Unit a -> Choice (a,b)
    | Choice(a,b') -> Choice (a,mplus b b') //interesting - interleaving of the results here
    | Inc a' -> Inc (lazy mplus b a'.Value) 

let rec bind s g =
    match s with
    | MZero -> MZero
    | Unit a -> g a
    | Choice (a,b) -> mplus (g a) (bind b g)
    | Inc f -> Inc (lazy bind f.Value g)

let rec mplusMany streams =
    match streams with
    | [] -> MZero
    | [g] -> g
    | (g::gs) -> mplus g (mplusMany gs)

let rec bindMany str goals =
    match goals with
    | [] -> str
    | (g::gs) -> bindMany (bind str g) gs

let conde (goals:#seq<list<Goal>>) : Goal =
    fun a -> 
        Inc (lazy (mplusMany (goals |> Seq.map (fun (g::gs) -> bindMany (g a) gs) |> Seq.toList)))

//let (=>) g1 g2 = 
//    fun a -> bind (g1 a) g2

let (|||) g1 g2 =
    fun a -> mplus (g1 a) (g2 a)

let (&&&) g1 g2 = 
    fun a -> bind (g1 a) g2

let inline recurse fg =
    fun a -> Inc (lazy fg() a)

let rec fix f x = fun a -> Inc (lazy (f (fix f) x a))

let rec take n f =
    if n = 0 then 
        []
    else
        match f with
        | MZero -> []
        | Inc (Lazy s) -> take n s
        | Unit a -> [a]
        | Choice(a,f) ->  a :: take (n-1) f

let inline run n (f: _ -> Goal) =
    Inc (lazy (let x = fresh()
               bind (f x Map.empty) (fun res -> walkMany x res |> Unit)(*(Unit << reify x)*)))
    |> take n

let inline runEval n (f: _ -> Goal) =
    run n f
    |> List.map Swensen.Unquote.Operators.evalRaw

//impure operators
let project (v:Expr<'a>) (f:'a -> Goal) : Goal =
    fun s -> 
        //assume atom here..otherwise fail
        let x = walkMany v s
        f (Swensen.Unquote.Operators.evalRaw x) s
