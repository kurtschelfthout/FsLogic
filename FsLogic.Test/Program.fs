module FsLogic.Test.Program

open Expecto
open System
open System.Diagnostics

[<EntryPoint>]
let main args =
    runTestsInAssembly defaultConfig args
    //if Debugger.IsAttached then Console.ReadKey() |> ignore
    
