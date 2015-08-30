module FsLogic.Test.ArithmeticTest

open Xunit
open Swensen.Unquote
open FsLogic.Substitution
open FsLogic
open FsLogic.Goal
open FsLogic.Arithmetic
open Microsoft.FSharp.Quotations

[<Fact>]
let xor() =
    let res = run -1 (fun q ->
        let x,y,r = fresh()
        bitXoro x y r
        &&& q *=* ~~(x, y, r)
    )
    res =!([0,0,0
            1,1,0
            1,0,1
            0,1,1
            ]  |> List.map Some)

[<Fact>]
let ``and``() =
    let res = run -1 (fun q ->
        let x,y,r = fresh()
        bitAndo x y r
        &&& q *=* ~~(x, y, r)
    )
    res =! ([0,0,0
             1,1,1
             0,1,0
             1,0,0
            ] |> List.map Some)

[<Fact>]
let ``poso fails for 0``() =
    let res = run -1 (fun q -> poso nil)
    res =! []    
    
[<Fact>]
let ``poso succeeds for 1``() =
    let res = run -1 (fun q -> poso ~~[1Z])
    res.Length =! 1

[<Fact>]
let ``>1o fails for 0 and 1``() =
    let res = run -1 (fun q -> ``>1o`` nil ||| ``>1o`` ~~[1Z])
    res =! []    
    
[<Fact>]
let ``>1o succeeds for 2``() =
    let res = run -1 (fun q -> ``>1o`` ~~[0Z;1Z])
    res.Length =! 1

[<Fact>]
let halfAdder() =
    let res = run -1 (fun q ->
        let x,y,r,c = fresh()
        halfAddero x y r c
        &&& q *=* ~~(x, y, r, c)
    )
    res.Length =! 4
    test <@ res |> List.forall (fun (Some (x,y,r,c)) -> x + y = r + 2*c) @>


[<Fact>]
let fullAdder() =
    let res = run -1 (fun q ->
        let b,x,y,r,c = fresh()
        fullAddero b x y r c
        &&& q *=* ~~(b, x, y, r, c)
    )
    res.Length =! 8
    test <@ res |> List.forall (fun (Some (b,x,y,r,c)) -> b + x + y = r + 2*c) @>

[<Fact>]    
let ``0+1=1``() =
    let res = run -1 (fun q -> pluso nil ~~[1] q)
    res =! [Some [1]]

[<Fact>]    
let ``1+0=1``() =
    let res = run -1 (fun q -> pluso ~~[1] nil q)
    res =! [Some [1]]

[<Fact>]    
let ``1+1=2``() =
    let res = run -1 (fun q -> pluso ~~[1] ~~[1] q)
    res =! [Some [0;1]]

[<Fact>]    
let ``1+2=3``() =
    let res = run -1 (fun q -> pluso ~~[1] ~~[0;1] q)
    res =! [Some [1;1]]

[<Fact>]    
let ``2+1=3``() =
    let res = run -1 (fun q -> pluso ~~[0;1] ~~[1] q)
    res =! [Some [1;1]]

[<Fact>]    
let ``2+2=4``() =
    let res = run -1 (fun q -> pluso ~~[0;1] ~~[0;1] q)
    res =! [Some [0;0;1]]

[<Fact>]    
let ``2+3=5``() =
    let res = run -1 (fun q -> pluso ~~[0;1] ~~[1;1] q)
    res =! [Some [1;0;1]]

[<Fact>]    
let ``3+2=5``() =
    let res = run -1 (fun q -> pluso ~~[1;1] ~~[0;1] q)
    res =! [Some [1;0;1]]

[<Fact>]    
let ``3+3=6``() =
    let res = run -1 (fun q -> pluso ~~[1;1] ~~[1;1] q)
    res =! [Some [0;1;1]]

[<Fact>]    
let ``3+6=9``() =
    let res = run -1 (fun q -> pluso ~~[1;1] ~~[0;1;1] q)
    res =! [Some [1;0;0;1]]

[<Fact>]
let ``2+?=5``() =
    let res = run -1 (fun q -> pluso ~~[0;1] q ~~[1;0;1])
    res =! [Some [1;1]]

[<Fact>]
let ``generate numbers addition``() =
    let res = run 9  (fun q -> let x,y,z = fresh() in pluso x y z &&& ~~(x,y,z) *=* q)
    printf "%A" res
