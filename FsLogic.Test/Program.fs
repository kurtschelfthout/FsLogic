module FsLogic.Test.Program

open Fuchu
open System
open System.Diagnostics

let markers = [
    typeof<UnificationTest.Marker>
    typeof<RelationsTest.Marker>
    typeof<ArithmeticTest.Marker>
    ]

[<Tests>]
let tests =
    markers
    |> Seq.map (fun marker ->
        testList marker.DeclaringType.Name <|
            (marker.DeclaringType.GetMethods()
            |> Seq.filter (fun m -> m.IsStatic && m.GetParameters().Length = 0)
            |> Seq.map (fun m -> testCase m.Name (fun _ -> m.Invoke(null,[||]) |> ignore))))
    |> testList "FsLogic"


[<EntryPoint>]
let main args =
    let r = defaultMainThisAssembly args
    if Debugger.IsAttached then Console.ReadKey() |> ignore
    r
