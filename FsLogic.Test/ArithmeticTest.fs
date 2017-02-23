module FsLogic.Test.ArithmeticTest

open Expecto
open Swensen.Unquote
open FsLogic
open FsLogic.Substitution
open FsLogic.Goal
open FsLogic.Arithmetic

#nowarn "25"

let (|Unbox|_|) (a:obj) : 'a option =
    match a with | :? 'a as at -> Some at | _ -> None

[<Tests>]
let tests =
    testList "Arithmetic" [

        testCase "xor" (fun _ ->
            let res = run -1 (fun q ->
                let x,y,r = fresh()
                bitXoro x y r
                &&& q *=* ~~(x, y, r)
            )
            res =!([0,0,0
                    1,1,0
                    1,0,1
                    0,1,1
                    ]  |> List.map (box >> Det))
        )

        testCase "and" (fun _ ->
            let res = run -1 (fun q ->
                let x,y,r = fresh()
                bitAndo x y r
                &&& q *=* ~~(x, y, r)
            )
            res =! ([0,0,0
                     1,1,1
                     0,1,0
                     1,0,0
                    ] |> List.map (box >> Det))
        )

        testCase "poso fails for 0" (fun _ ->
            let res = run -1 (fun _ -> poso nil)
            res =! []
        )

        testCase "poso succeeds for 1" (fun _ ->
            let res = run -1 (fun _ -> poso ~~[1Z])
            res.Length =! 1
        )

        testCase ">1o fails for 0 and 1" (fun _ ->
            let res = run -1 (fun _ -> ``>1o`` nil ||| ``>1o`` ~~[1Z])
            res =! []
        )

        testCase ">1o succeeds for 2" (fun _ ->
            let res = run -1 (fun _ -> ``>1o`` ~~[0Z;1Z])
            res.Length =! 1
        )

        testCase "halfAdder" (fun _ ->
            let res = run -1 (fun q ->
                let x,y,r,c = fresh()
                halfAddero x y r c
                &&& q *=* ~~(x, y, r, c)
            )
            res.Length =! 4
            test <@ res |> List.forall (fun (Det (Unbox (x,y,r,c))) -> x + y = r + 2*c) @>
        )

        testCase "fullAdder" (fun _ ->
            let res = run -1 (fun q ->
                let b,x,y,r,c = fresh()
                fullAddero b x y r c
                &&& q *=* ~~(b, x, y, r, c)
            )
            res.Length =! 8
            test <@ res |> List.forall (fun (Det (Unbox (b,x,y,r,c))) -> b + x + y = r + 2*c) @>
        )

        testCase "0+1=1" (fun _ ->
            let res = run -1 (fun q -> pluso nil ~~[1] q)
            res =! [Det [1]]
        )

        testCase "1+0=1" (fun _ ->
            let res = run -1 (fun q -> pluso ~~[1] nil q)
            res =! [Det [1]]
        )

        testCase "1+1=2" (fun _ ->
            let res = run -1 (fun q -> pluso ~~[1] ~~[1] q)
            res =! [Det [0;1]]
        )

        testCase "1+2=3" (fun _ ->
            let res = run -1 (fun q -> pluso ~~[1] ~~[0;1] q)
            res =! [Det [1;1]]
        )

        testCase "2+1=3" (fun _ ->
            let res = run -1 (fun q -> pluso ~~[0;1] ~~[1] q)
            res =! [Det [1;1]]
        )

        testCase "2+2=4" (fun _ ->
            let res = run -1 (fun q -> pluso ~~[0;1] ~~[0;1] q)
            res =! [Det [0;0;1]]
        )

        testCase "2+3=5" (fun _ ->
            let res = run -1 (fun q -> pluso ~~[0;1] ~~[1;1] q)
            res =! [Det [1;0;1]]
        )

        testCase "3+2=5" (fun _ ->
            let res = run -1 (fun q -> pluso ~~[1;1] ~~[0;1] q)
            res =! [Det [1;0;1]]
        )

        testCase "3+3=6" (fun _ ->
            let res = run -1 (fun q -> pluso ~~[1;1] ~~[1;1] q)
            res =! [Det [0;1;1]]
        )

        testCase "3+6=9" (fun _ ->
            let res = run -1 (fun q -> pluso ~~[1;1] ~~[0;1;1] q)
            res =! [Det [1;0;0;1]]
        )

        testCase "2+?=5" (fun _ ->
            let res = run -1 (fun q -> pluso ~~[0;1] q ~~[1;0;1])
            res =! [Det [1;1]]
        )

        testCase "?+?=?" (fun _ ->
            let res = run 9 (fun q -> let x,y,z = fresh() in pluso x y z &&& ~~(x,y,z) *=* q)
            res.[0] =! Half [Free -1; Det List.empty<int>; Free -1]
            res.[1] =! Half [Det List.empty<int>; Half [Free -2; Free -3]; Half [Free -2; Free -3]]
            res.[2] =! Det ([1], [1], [0; 1])
            res.[3] =! Half [Half [Det 0; Free -2; Free -3]; Det [1]; Half [Det 1; Free -2; Free -3]]
            res.[4] =! Half [Det [1]; Half [Det 0; Free -2; Free -3]; Half [Det 1; Free -2; Free -3]]
            res.[5] =! Det ([1; 1], [1], [0; 0; 1])
            res.[6] =! Det ([1], [1; 1], [0; 0; 1])
            res.[7] =! Half [Half [Det 1; Det 0; Free -2; Free -3]; Det [1]; Half [Det 0; Det 1; Free -2; Free -3]]
            res.[8] =! Half [Det [1]; Half [Det 1; Det 0; Free -2; Free -3]; Half [Det 0; Det 1; Free -2; Free -3]]
        )

    ]