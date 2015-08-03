module ArithmeticTest

open Xunit
open Swensen.Unquote
open MiniKanren.Substitution
open MiniKanren.Goal
open MiniKanren.Arithmetic
open Microsoft.FSharp.Quotations

[<Fact>]
let xor() =
    let res = runEval -1 (fun q ->
        let x,y,r = fresh3()
        bitXoro x y r
        &&& equiv q <@ %x, %y, %r @>
    )
    res =? [0,0,0
            1,1,0
            1,0,1
            0,1,1
            ]

[<Fact>]
let ``and``() =
    let res = runEval -1 (fun q ->
        let x,y,r = fresh3()
        bitAndo x y r
        &&& equiv q <@ %x, %y, %r @>
    )
    res =? [0,0,0
            1,1,1
            0,1,0
            1,0,0
            ]

[<Fact>]
let ``poso fails for 0``() =
    let res = runEval -1 (fun q -> poso <@ [] @>)
    res =? []    
    
[<Fact>]
let ``poso succeeds for 1``() =
    let res = run -1 (fun q -> poso <@ [1] @>)
    res.Length =? 1

[<Fact>]
let ``>1o fails for 0 and 1``() =
    let res = run -1 (fun q -> ``>1o`` <@ [] @> ||| ``>1o`` <@ [1] @>)
    res =? []    
    
[<Fact>]
let ``>1o succeeds for 2``() =
    let res = run -1 (fun q -> ``>1o`` <@ [0;1] @>)
    res.Length =? 1

[<Fact>]
let halfAdder() =
    let res = runEval -1 (fun q ->
        let x,y,r,c = fresh4()
        halfAddero x y r c
        &&& equiv q <@ %x, %y, %r, %c @>
    )
    res.Length =? 4
    test <@ res |> List.forall (fun (x,y,r,c) -> x + y = r + 2*c) @>

[<Fact>]
let fullAdder() =
    let res = runEval -1 (fun q ->
        let (b,x,y,r),c = fresh4(),fresh()
        fullAddero b x y r c
        &&& equiv q <@ %b, %x, %y, %r, %c @>
    )
    res.Length =? 8
    test <@ res |> List.forall (fun (b,x,y,r,c) -> b + x + y = r + 2*c) @>

[<Fact>]    
let ``0+1=1``() =
    let res = runEval -1 (fun q -> pluso <@ [] @> <@ [1] @> q)
    res =? [[1]]

[<Fact>]    
let ``1+0=1``() =
    let res = runEval -1 (fun q -> pluso <@ [1] @> <@ [] @> q)
    res =? [[1]]

[<Fact>]    
let ``1+1=2``() =
    let res = runEval -1 (fun q -> pluso <@ [1] @> <@ [1] @> q)
    res =? [[0;1]]

[<Fact>]    
let ``1+2=3``() =
    let res = runEval -1 (fun q -> pluso <@ [1] @> <@ [0;1] @> q)
    res =? [[1;1]]

[<Fact>]    
let ``2+1=3``() =
    let res = runEval -1 (fun q -> pluso <@ [0;1] @> <@ [1] @> q)
    res =? [[1;1]]

[<Fact>]    
let ``2+2=4``() =
    let res = runEval -1 (fun q -> pluso <@ [0;1] @> <@ [0;1] @> q)
    res =? [[0;0;1]]

[<Fact>]    
let ``2+3=5``() =
    let res = runEval -1 (fun q -> pluso <@ [0;1] @> <@ [1;1] @> q)
    res =? [[1;0;1]]

[<Fact>]    
let ``3+2=5``() =
    let res = runEval -1 (fun q -> pluso <@ [1;1] @> <@ [0;1] @> q)
    res =? [[1;0;1]]

[<Fact>]    
let ``3+3=6``() =
    let res = runEval -1 (fun q -> pluso <@ [1;1] @> <@ [1;1] @> q)
    res =? [[0;1;1]]

[<Fact>]    
let ``3+6=9``() =
    let res = runEval -1 (fun q -> pluso <@ [1;1] @> <@ [0;1;1] @> q)
    res =? [[1;0;0;1]]

[<Fact>]
let ``2+?=5``() =
    let res = runEval -1 (fun q -> pluso <@ [0;1] @> q <@ [1;0;1] @>)
    res =? [[1;1]]

[<Fact>]
let ``generate numbers addition``() =
    let res = runShow 9  (fun q -> let x,y,z = fresh3() in pluso x y z &&& equiv <@ %x,%y,%z @> q)
    printf "%s" res